module

public import Riftbound.Invariant.CleanupDeath

/-!
# Strict decrease for simultaneous Cleanup deaths

When a group of deaths leaves the Board count equal, the resolver still heals a lethal
root. The remaining roots and their replacements cannot increase damage or add off-Board
tokens on a step with the same Board count.
-/

@[expose] public section

namespace Riftbound

private theorem boardIdentifiers_nodup {s : GameState} (wf : s.WF) : s.inPlay.Nodup := by
  rw [GameState.inPlay_eq_flatMap, List.Nodup, List.pairwise_flatMap]
  refine ⟨fun zone _ => GameState.zone_nodup_any wf zone, ?_⟩
  apply List.Pairwise.imp _ s.inPlayZones_nodup
  intro first second distinct x hfirst y hsecond
  exact fun eq => ne_of_mem_other_zone wf hfirst hsecond distinct.symm eq.symm

private def objectDamage (s : GameState) (id : ObjId) : Nat :=
  ((s.obj? id).map (·.damage)).getD 0

private theorem damagedCount_lt_of_healed {s t : GameState} (wf : t.WF)
    (kept : t.inPlay ⊆ s.inPlay)
    (damage : ∀ id ∈ t.inPlay, objectDamage t id ≤ objectDamage s id)
    {id : ObjId} (live : id ∈ s.inPlay) (damaged : 0 < objectDamage s id)
    (healed : objectDamage t id = 0) : t.dmgC < s.dmgC := by
  let now := t.inPlay.filter (fun x => decide (0 < objectDamage t x))
  let before := s.inPlay.filter (fun x => decide (0 < objectDamage s x))
  have smaller : now ⊆ before.erase id := by
    intro x mem
    obtain ⟨onBoard, positive⟩ := List.mem_filter.mp mem
    simp only [decide_eq_true_eq] at positive
    have ne : x ≠ id := by
      intro same
      subst x
      omega
    apply (List.mem_erase_of_ne ne).mpr
    exact List.mem_filter.mpr ⟨kept onBoard, decide_eq_true
      (Nat.lt_of_lt_of_le positive (damage x onBoard))⟩
  have known : id ∈ before := List.mem_filter.mpr ⟨live, decide_eq_true damaged⟩
  have unique : now.Nodup := (boardIdentifiers_nodup wf).filter _
  have count := unique.length_le_of_subset smaller
  have difference := List.length_erase_of_mem known
  have positive := List.length_pos_of_mem known
  have compare : now.length < before.length := by omega
  simp only [GameState.dmgC, List.countP_eq_length_filter]
  exact compare

private theorem killObj_eq_of_samePot {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none)
    (same : (killObj s id).1.pot = s.pot) : (killObj s id).1 = s := by
  cases found : s.obj? id with
  | none => simp [killObj, sendObj, found]
  | some o =>
    have live : id ∈ s.inPlay := target.resolve_right (by simp [found])
    have invalid : ¬ o.owner.n < s.playerCount := by
      intro valid
      have entire : ∀ x, s.obj? id = some x → x.owner.n < s.playerCount := by
        intro x get
        have eq := Option.some.inj (found.symm.trans get)
        simpa [← eq] using valid
      have drop := killObj_pot_lt wf entire live
      omega
    have noMove (k : ZoneKind) :
        moveObj s id (.player o.owner (s.ownerDestination id o k)) = none := by
      cases move : moveObj s id (.player o.owner (s.ownerDestination id o k)) with
      | none => rfl
      | some r =>
        obtain ⟨t, new⟩ := r
        obtain ⟨src, dst, spec, obj, looked, norm⟩ := moveObj_spec_dst move
        have eq := Option.some.inj (found.symm.trans looked)
        subst obj
        rw [Zone.normalize_owner] at norm
        subst dst
        exact False.elim (invalid (Zone.lt_of_valid_player spec.dst_mem))
    simp [killObj, sendObj, found, noMove, noteDeath, noteDeathContext, noteIf]
    split <;> rfl

private theorem recall_keeps_offBoard_zones {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) {z : Zone} (nonBoard : z.isBoard = false) :
    (recallFx true s id).1.zone z = s.zone z := by
  apply recallFx_zone_of_not_mem true nonBoard
  intro present
  rcases target with live | absent
  · obtain ⟨source, onBoard, contains⟩ := GameState.mem_inPlay_zone live
    have different : source ≠ z := by intro eq; rw [eq, nonBoard] at onBoard; contradiction
    exact ne_of_mem_other_zone wf present contains different rfl
  · obtain ⟨o, found⟩ := GameState.obj_of_mem wf present
    rw [absent] at found
    contradiction

private theorem obj_map_modObj {α : Type} (s : GameState) (id x : ObjId) (f : Object → Object)
    (p : Object → α) (keeps : ∀ o, p (f o) = p o) :
    ((s.modObj id f).obj? x).map p = (s.obj? x).map p := by
  rcases obj?_modObj_cases s id f x with same | ⟨o, before, after⟩
  · rw [same]
  · rw [before, after, Option.map_some, Option.map_some, keeps]

private theorem recall_obj_map {α : Type} {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) (x : ObjId) (p : Object → α)
    (loc : ∀ o : Object, p { o with loc := none } = p o)
    (exhausted : ∀ o : Object, p { o with exhausted := true } = p o) :
    ((recallFx true s id).1.obj? x).map p = (s.obj? x).map p := by
  let moved := (sendHome s id).1
  have tired : ((setExhausted true moved id).1.obj? x).map p = (moved.obj? x).map p := by
    unfold setExhausted
    split
    · exact obj_map_modObj moved id x _ p exhausted
    · rfl
  change ((setExhausted true moved id).1.obj? x).map p = _
  rw [tired]
  unfold moved sendHome
  cases found : s.obj? id with
  | none => rfl
  | some o =>
    dsimp only
    cases step : moveObj s id (.player o.controller .base) with
    | none => rfl
    | some r =>
      obtain ⟨t, new⟩ := r
      dsimp only
      rw [obj_map_modObj t new x _ p loc]
      have live : id ∈ s.inPlay := target.resolve_right (by simp [found])
      obtain ⟨zone, isBoard, mem⟩ := GameState.mem_inPlay_zone live
      have placed := GameState.locate_eq wf (GameState.zone_valid_of_mem wf mem) mem
      unfold GameState.obj?
      exact congrArg (fun objects => (objects[x.n]?).map p)
        (move_board_objects step placed isBoard (show (Zone.player o.controller .base).isBoard = true from rfl)).1

private theorem recall_damage {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) (x : ObjId) :
    objectDamage (recallFx true s id).1 x = objectDamage s x :=
  congrArg (fun o : Option Nat => o.getD 0)
    (recall_obj_map wf target x Object.damage (fun _ => rfl) (fun _ => rfl))

private theorem recall_offBoard_tokens {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) :
    (recallFx true s id).1.tokC = s.tokC := by
  let next := (recallFx true s id).1
  have cfg : next.config = s.config := (recallFx_safe true s id).same.config
  have nonBoard : next.nbZones = s.nbZones := by
    simp [next, GameState.nbZones, GameState.playerCount, show (recallFx true s id).1.config = s.config from cfg]
  have token : next.isTok = s.isTok := by
    funext x
    let isToken (o : Object) := match o.kind with | .token _ => true | _ => false
    have anyMap (o : Option Object) : o.any isToken = (o.map isToken).getD false := by cases o <;> rfl
    change (next.obj? x).any isToken = (s.obj? x).any isToken
    rw [anyMap, anyMap]
    exact congrArg (fun o : Option Bool => o.getD false)
      (recall_obj_map wf target x isToken (fun _ => rfl) (fun _ => rfl))
  change next.tokC = s.tokC
  unfold GameState.tokC
  rw [nonBoard]
  congr 1
  apply flatMap_congr_mem
  intro z inZones
  have isOff : z.isBoard = false := by
    have := (List.mem_filter.mp inZones).2
    simpa using this
  change (next.zone z).filter next.isTok = (s.zone z).filter s.isTok
  rw [show next.zone z = s.zone z from recall_keeps_offBoard_zones wf target isOff]
  rw [token]

/-- The parts of the Cleanup measure which can decrease when the Board count stays fixed. -/
private structure CleanupDamageChange (s t : GameState) : Prop where
  tokens : t.tokC = s.tokC
  damage : ∀ id, objectDamage t id ≤ objectDamage s id

namespace CleanupDamageChange

private theorem refl (s : GameState) : CleanupDamageChange s s :=
  ⟨rfl, fun _ => Nat.le_refl _⟩

private theorem trans {s t u : GameState} (first : CleanupDamageChange s t)
    (second : CleanupDamageChange t u) : CleanupDamageChange s u :=
  ⟨second.tokens.trans first.tokens, fun id => Nat.le_trans (second.damage id) (first.damage id)⟩

private theorem of_sameBoard {s t : GameState} (config : t.config = s.config)
    (zones : t.zones = s.zones) (objects : t.objects = s.objects) : CleanupDamageChange s t := by
  refine ⟨?_, fun id => ?_⟩
  · simp [GameState.tokC, GameState.nbZones, GameState.playerCount, GameState.zone, GameState.isTok,
      GameState.obj?, config, zones, objects]
  · simp [objectDamage, GameState.obj?, objects]

end CleanupDamageChange

private theorem heal_damage_change (s : GameState) (id : ObjId) (f : Object → Object)
    (kind : ∀ o, (f o).kind = o.kind) (heals : ∀ o, (f o).damage = 0) :
    CleanupDamageChange s (s.modObj id f) ∧ objectDamage (s.modObj id f) id = 0 := by
  refine ⟨⟨tokC_modObj s id f kind, fun x => ?_⟩, ?_⟩
  · rcases obj?_modObj_cases s id f x with h | ⟨_, _, h⟩
    · simp [objectDamage, h]
    · simp [objectDamage, h, heals]
  · unfold objectDamage
    simp only [GameState.obj?_modObj, ↓reduceIte]
    cases s.obj? id <;> simp [heals]

private theorem completeDeathSave_damages {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) (m : Option TurnEffect) (p : PlayerId) (c : Bool) :
    CleanupDamageChange s (completeDeathSave s id m p c).1 ∧
      objectDamage (completeDeathSave s id m p c).1 id = 0 := by
  let heal := fun o : Object => { o with damage := 0 }
  let healed := s.modObj id heal
  let recalled := (recallFx true healed id).1
  obtain ⟨got, zero⟩ := heal_damage_change s id heal (fun _ => rfl) (fun _ => rfl)
  have healedWf := (Safe.modObj s id (f := heal) (fun _ => rfl) (fun _ => rfl)).wf wf
  have healedTarget : id ∈ healed.inPlay ∨ healed.obj? id = none := by
    rcases target with live | absent
    · exact Or.inl (inPlay_modObj s id heal ▸ live)
    · exact Or.inr (by simp [healed, GameState.obj?_modObj, absent])
  have recalledChange : CleanupDamageChange healed recalled :=
    ⟨recall_offBoard_tokens healedWf healedTarget,
      fun x => Nat.le_of_eq (recall_damage healedWf healedTarget x)⟩
  change CleanupDamageChange s (finishDeathSave recalled id p m c) ∧ objectDamage recalled id = 0
  exact ⟨got.trans (recalledChange.trans (CleanupDamageChange.of_sameBoard rfl rfl rfl)),
    (recall_damage healedWf healedTarget id).trans zero⟩

private theorem killObj_stable_damage {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) (same : (killObj s id).1.pot = s.pot) :
    CleanupDamageChange s (killObj s id).1 ∧
      ((∀ o, s.obj? id = some o → o.owner.n < s.playerCount) → objectDamage (killObj s id).1 id = 0) := by
  have equal := killObj_eq_of_samePot wf target same
  rw [equal]
  refine ⟨CleanupDamageChange.refl s, fun valid => ?_⟩
  rcases target with live | absent
  · have drop := killObj_pot_lt wf valid live
    omega
  · simp [objectDamage, absent]

private theorem killOrSaveFrom_stable_damage (root : ObjId) (fuel : Nat) {s : GameState} (wf : s.WF)
    {id : ObjId} (used : List (ObjId × Bool)) (live : id ∈ s.inPlay)
    (same : (killOrSaveFrom root fuel s id used).1.pot = s.pot) :
    CleanupDamageChange s (killOrSaveFrom root fuel s id used).1 ∧
      ((∀ o, s.obj? id = some o → o.owner.n < s.playerCount) →
        objectDamage (killOrSaveFrom root fuel s id used).1 id = 0) := by
  induction fuel generalizing s id used with
  | zero =>
    have res := killObj_stable_damage ((prepareNestedDeath_safe s root id used).wf wf) (Or.inl live)
      (show (killObj (prepareNestedDeath s root id used) id).1.pot =
        (prepareNestedDeath s root id used).pot from same)
    exact ⟨(CleanupDamageChange.of_sameBoard (s := s)
      (t := prepareNestedDeath s root id used) rfl rfl rfl).trans res.1, res.2⟩
  | succ fuel ih =>
    unfold killOrSaveFrom at same ⊢
    dsimp only at same ⊢
    cases found : (prepareNestedDeath s root id used).deathSaveFor id used with
    | none =>
      simp only [found] at same ⊢
      have res := killObj_stable_damage ((prepareNestedDeath_safe s root id used).wf wf) (Or.inl live)
        (show (killObj (prepareNestedDeath s root id used) id).1.pot =
          (prepareNestedDeath s root id used).pot from same)
      exact ⟨(CleanupDamageChange.of_sameBoard (s := s)
      (t := prepareNestedDeath s root id used) rfl rfl rfl).trans res.1, res.2⟩
    | some save =>
      simp only [found] at same ⊢
      let paid := (save.cost.elim (s, []) (fun cost => killOrSaveFrom root fuel s cost
        (save.useKey id :: used))).1
      have payment : CleanupDeathChange s paid := by
        cases save with
        | mk mode cost =>
          cases cost with
          | none => exact CleanupDeathChange.refl s
          | some next =>
            have member : next ∈ (prepareNestedDeath s root id used).inPlay :=
              GameState.deathSaveFor_cost_mem found
            exact killOrSaveFrom_cleanupChange root fuel wf _ member
      have paymentWf : paid.WF := by
        cases cost : save.cost with
        | none => simpa [paid, cost] using wf
        | some next => simpa [paid, cost] using
            (killOrSaveFrom_safe root fuel s next (save.useKey id :: used)).wf wf
      let mark := (prepareNestedDeath s root id used).deathSaveMark id save.isSacrifice save.cost used
      let owner := ((s.obj? id).map (·.controller)).getD ⟨0⟩
      have settled := completeDeathSave_damages paymentWf (payment.inPlay_or_absent live) mark owner used.isEmpty
      have settledPot := (completeDeathSave_cleanupChange paymentWf (payment.inPlay_or_absent live) mark owner used.isEmpty).pot
      have equal : paid.pot = s.pot := by
        change (completeDeathSave paid id mark owner used.isEmpty).1.pot = s.pot at same
        have paidPot := payment.pot
        omega
      have paidDamage : CleanupDamageChange s paid := by
        cases save with
        | mk mode cost =>
          cases cost with
          | none => exact CleanupDamageChange.refl s
          | some next =>
            have member : next ∈ (prepareNestedDeath s root id used).inPlay :=
              GameState.deathSaveFor_cost_mem found
            exact (ih wf _ member equal).1
      exact ⟨paidDamage.trans settled.1, fun _ => settled.2⟩

private theorem killOrSave_stable_damage {s : GameState} (wf : s.WF) {id : ObjId}
    (live : id ∈ s.inPlay) (same : (killOrSave s id).1.pot = s.pot) :
    CleanupDamageChange s (killOrSave s id).1 ∧
      ((∀ o, s.obj? id = some o → o.owner.n < s.playerCount) →
        objectDamage (killOrSave s id).1 id = 0) := by
  let raw := (killOrSaveFrom id (2 * s.inPlay.length) s id []).1
  have facts := killOrSaveFrom_stable_damage id (2 * s.inPlay.length) wf [] live
    (show raw.pot = s.pot from same)
  change CleanupDamageChange s (finishNestedDeaths raw id) ∧ _
  exact ⟨facts.1.trans (CleanupDamageChange.of_sameBoard rfl rfl rfl), facts.2⟩

private theorem saveUnit_stable_damage {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) (old : id.n < s.nextId) (cost : Option ObjId)
    (costLive : ∀ gear, cost = some gear → gear ∈ s.inPlay)
    (same : (saveUnit s id cost).1.pot = s.pot) :
    CleanupDamageChange s (saveUnit s id cost).1 ∧ objectDamage (saveUnit s id cost).1 id = 0 := by
  let paid := (cost.elim (s, []) (killObj s)).1
  have payment : CleanupDeathChange s paid := by
    cases cost with
    | none => exact CleanupDeathChange.refl s
    | some gear => exact killObj_cleanupChange wf (Or.inl (costLive gear rfl))
  have paymentWf : paid.WF := by
    cases cost with
    | none => exact wf
    | some gear => exact (killObj_safe s gear).wf wf
  have paidTarget : id ∈ paid.inPlay ∨ paid.obj? id = none :=
    target.elim payment.inPlay_or_absent (fun absent => Or.inr (payment.absent id old absent))
  let mark := s.deathSaveMark id (cost.isSome && cost == s.selectedDeathSacrifice id) cost
  let p := ((s.obj? id).map (·.controller)).getD ⟨0⟩
  have alias : (saveUnit s id cost).1 = (completeDeathSave paid id mark p true).1 := by
    cases cost <;> rfl
  rw [alias] at same ⊢
  have stable : paid.pot = s.pot := by
    have finished := (completeDeathSave_cleanupChange paymentWf paidTarget mark p true).pot
    have atMost := payment.pot
    omega
  have paidSame : paid = s := by
    cases cost with
    | none => rfl
    | some gear => exact killObj_eq_of_samePot wf (Or.inl (costLive gear rfl)) stable
  rw [paidSame]
  exact completeDeathSave_damages wf target mark p true

private theorem cleanupResolveDeath_stable_damage {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) (old : id.n < s.nextId)
    (same : (cleanupResolveDeath s id).1.pot = s.pot) :
    CleanupDamageChange s (cleanupResolveDeath s id).1 ∧
      ((∀ o, s.obj? id = some o → o.owner.n < s.playerCount) →
        objectDamage (cleanupResolveDeath s id).1 id = 0) := by
  have kill := killObj_stable_damage wf target
  have save {cost} (members : ∀ gear, cost = some gear → gear ∈ s.inPlay)
      (same : (saveUnit s id cost).1.pot = s.pot) :
      CleanupDamageChange s (saveUnit s id cost).1 ∧
        ((∀ o, s.obj? id = some o → o.owner.n < s.playerCount) → objectDamage (saveUnit s id cost).1 id = 0) := by
    obtain ⟨change, healed⟩ := saveUnit_stable_damage wf target old cost members same
    exact ⟨change, fun _ => healed⟩
  unfold cleanupResolveDeath at same ⊢
  by_cases nested : hasNestedDeath s id = true
  · simp only [nested] at same ⊢
    suffices live : id ∈ s.inPlay from killOrSave_stable_damage wf live same
    refine target.resolve_right ?_
    intro absent
    have noneSaved : s.deathSaveFor id [] = none := by
      simp [GameState.deathSaveFor, GameState.cardDef?, absent]
    simp [hasNestedDeath, noneSaved] at nested
  · simp only [nested] at same ⊢
    change (cleanupKillCore s id).1.pot = s.pot at same
    change CleanupDamageChange s (cleanupKillCore s id).1 ∧
      ((∀ o, s.obj? id = some o → o.owner.n < s.playerCount) →
        objectDamage (cleanupKillCore s id).1 id = 0)
    unfold cleanupKillCore at same ⊢
    cases selected : s.deathSaver id with
    | none => simpa only [selected] using kill (by simpa only [selected] using same)
    | some ro =>
      cases ro with
      | some gear =>
        simp only [selected] at same ⊢
        by_cases use : (gear != id && (s.obj? gear).any (fun o => decide (o.owner.n < s.playerCount))) = true
        · simp only [use] at same ⊢
          exact save (fun g eq => (Option.some.inj eq) ▸ GameState.deathSaver_cost_mem selected) same
        · simp only [use] at same ⊢
          exact kill same
      | none =>
        simp only [selected] at same ⊢
        by_cases onField : (decide (id ∈ s.zone .battlefieldZone) &&
            (s.obj? id).any (fun o => decide (o.controller.n < s.playerCount))) = true
        · simp only [onField] at same ⊢
          exact save (cost := none) (fun _ eq => nomatch eq) same
        · simp only [onField] at same ⊢
          by_cases hasDamage : (!decide (id ∈ s.zone .battlefieldZone) &&
              (s.obj? id).any (fun o => decide (0 < o.damage))) = true
          · simp only [hasDamage]
            obtain ⟨healed, zero⟩ := heal_damage_change s id (fun o => { o with damage := 0, exhausted := true })
              (fun _ => rfl) (fun _ => rfl)
            exact ⟨healed.trans (CleanupDamageChange.of_sameBoard rfl rfl rfl), fun _ => zero⟩
          · simp only [hasDamage] at same ⊢
            exact kill same
private theorem automaticPlan_has_first (s : GameState) {group : List ObjId}
    (nonempty : group ≠ []) (g : GameState → ObjId → GameState × List Event) :
    ∃ entry rest, (planDeathGroup group none g group.length s group [] (s.deathGroupPrefix group)
      none []).1 = entry :: rest := by
  obtain ⟨fuel, size⟩ : ∃ fuel, group.length = fuel + 1 := by
    cases group with
    | nil => contradiction
    | cons _ tail => exact ⟨tail.length, rfl⟩
  rw [size, planDeathGroup.eq_2]
  simp only [Option.bind_none, ite_self, Option.isSome_none, Bool.false_eq_true, ite_false,
    List.length_nil, Bool.false_and]
  let candidates := deathGroupCandidates s group group 0 []
  have empty : candidates.filter (fun _ => false) = [] := by simp
  rw [show (deathGroupCandidates s group group 0 []).filter (fun _ => false) = [] from empty]
  simp only [List.isEmpty_nil, ite_true]
  let ordered := sortDeathGroupCandidates s candidates
  have length : ordered.length = group.length := by
    simp [ordered, sortDeathGroupCandidates, candidates, deathGroupCandidates]
  have head : ordered.head? ≠ none := by
    intro noHead
    have empty := List.head?_eq_none_iff.mp noHead
    rw [empty, List.length_nil, size] at length
    omega
  let forced := (s.deathGroupPrefix group).head?.bind fun unit => candidates.find? (·.unit == unit) <|>
      (deathGroupCandidates s group [unit] 0 []).head?
  generalize chosen : (forced <|> ordered.head?) = selected
  cases selected with
  | none =>
    cases pinned : forced with
    | none =>
      rw [pinned] at chosen
      exact False.elim (head chosen)
    | some _ =>
      rw [pinned] at chosen
      contradiction
  | some c =>
    by_cases last : (fuel == 0) = true <;> simp [last]

private theorem cleanupDeathGroup_first_lethal {s : GameState} {result : GameState × List Event}
    (resolved : cleanupResolveDeathGroup s = some result) :
    let group := cleanupDeathGroup s
    ∃ entry rest, (planDeathGroup group none cleanupResolveDeath group.length s group []
      (s.deathGroupPrefix group) none []).1 = entry :: rest ∧
      entry.unit ∈ s.inPlay ∧ s.lethal entry.unit = true := by
  dsimp only
  have nonempty : cleanupDeathGroup s ≠ [] := by
    intro empty
    simp [cleanupResolveDeathGroup, empty] at resolved
  obtain ⟨entry, rest, starts⟩ := automaticPlan_has_first s nonempty cleanupResolveDeath
  have member : entry ∈ (planDeathGroup (cleanupDeathGroup s) none cleanupResolveDeath
      (cleanupDeathGroup s).length s (cleanupDeathGroup s) [] (s.deathGroupPrefix (cleanupDeathGroup s))
      none []).1 := by rw [starts]; simp
  have pinned : s.deathGroupPrefix (cleanupDeathGroup s) ⊆ cleanupDeathGroup s := by
    intro id h
    exact List.contains_iff_mem.mp (List.mem_filter.mp h).2
  have root := planDeathGroup_entries_mem cleanupResolveDeath _ _ _ _ _ _ _ (fun _ h => h) pinned member
  unfold cleanupDeathGroup at root
  split at root
  · simp at root
  · have ⟨live, lethal⟩ := List.mem_filter.mp root
    simp only [Bool.and_eq_true] at lethal
    exact ⟨entry, rest, starts, live, lethal.2⟩

private theorem resolveRoot_pot_eq {s : GameState} (wf : s.WF) (group : List ObjId)
    (entry : DeathGroupEntry) (target : entry.unit ∈ s.inPlay ∨ s.obj? entry.unit = none)
    (old : entry.unit.n < s.nextId) :
    let next := (applyGroupDeath group cleanupResolveDeath s entry).1
    CleanupDeathChange s next ∧ (next.pot = s.pot →
      CleanupDamageChange s next ∧
      ((∀ o, s.obj? entry.unit = some o → o.owner.n < s.playerCount) →
        objectDamage next entry.unit = 0)) := by
  let ready := entry.prepare group s
  have ⟨config, zones, objects, counter⟩ := entry.prepare_board group s
  change ready.config = s.config at config
  change ready.zones = s.zones at zones
  change ready.objects = s.objects at objects
  change ready.nextId = s.nextId at counter
  have readyWf := wf.congr config objects zones counter
  have prep := CleanupDeathChange.of_sameBoard config zones objects counter
  have unprep := CleanupDeathChange.of_sameBoard config.symm zones.symm objects.symm counter.symm
  have readyPot : ready.pot = s.pot := Nat.le_antisymm prep.pot unprep.pot
  have readyTarget : entry.unit ∈ ready.inPlay ∨ ready.obj? entry.unit = none := by
    rcases target with live | absent
    · exact prep.inPlay_or_absent live
    · exact Or.inr (prep.absent _ old absent)
  have onBoard := prep.trans wf (cleanupResolveDeath_cleanupChange readyWf readyTarget (counter ▸ old))
  have other := CleanupDamageChange.of_sameBoard config zones objects
  have ownerFromSource (valid : ∀ o, s.obj? entry.unit = some o → o.owner.n < s.playerCount) :
      ∀ o, ready.obj? entry.unit = some o → o.owner.n < ready.playerCount := by
    intro o found
    simpa [GameState.playerCount, config] using valid o (by simpa [GameState.obj?, objects] using found)
  have plateau (same : (cleanupResolveDeath ready entry.unit).1.pot = s.pot) :=
    cleanupResolveDeath_stable_damage readyWf readyTarget (counter ▸ old) (same.trans readyPot.symm)
  unfold applyGroupDeath
  dsimp only
  split
  · exact ⟨onBoard, fun same => ⟨other.trans (plateau same).1,
      fun valid => (plateau same).2 (ownerFromSource valid)⟩⟩
  · exact ⟨onBoard.trans wf (CleanupDeathChange.of_sameBoard rfl rfl rfl rfl),
      fun same => ⟨other.trans ((plateau same).1.trans (CleanupDamageChange.of_sameBoard rfl rfl rfl)),
        fun valid => (plateau same).2 (ownerFromSource valid)⟩⟩

private theorem cleanupBatch_stable_damage {initial s : GameState} (initialWf : initial.WF)
    (wf : s.WF) (group : List ObjId) (applied : CleanupDeathChange initial s)
    (entries : List DeathGroupEntry) (roots : ∀ entry ∈ entries, entry.unit ∈ initial.inPlay) :
    let next := (applyEach (applyGroupDeath group cleanupResolveDeath) s entries).1
    CleanupDeathChange s next ∧ (next.pot = s.pot → CleanupDamageChange s next) := by
  induction entries generalizing s with
  | nil => exact ⟨CleanupDeathChange.refl s, fun _ => CleanupDamageChange.refl s⟩
  | cons entry rest ih =>
    have live := roots entry (by simp)
    have older := Nat.lt_of_lt_of_le (GameState.inPlay_lt_nextId initialWf live) applied.next
    have one := resolveRoot_pot_eq wf group entry (applied.inPlay_or_absent live) older
    have midWf := (applyGroupDeath_safe group cleanupResolveDeath_safe s entry).wf wf
    have tail := ih midWf (applied.trans initialWf one.1)
      (fun root h => roots root (List.mem_cons_of_mem _ h))
    refine ⟨one.1.trans wf tail.1, fun same => ?_⟩
    have fromStart := one.1.pot
    have toEnd := tail.1.pot
    change (applyEach (applyGroupDeath group cleanupResolveDeath)
      (applyGroupDeath group cleanupResolveDeath s entry).1 rest).1.pot = s.pot at same
    have oneEq : (applyGroupDeath group cleanupResolveDeath s entry).1.pot = s.pot := by omega
    exact (one.2 oneEq).1.trans (tail.2 (same.trans oneEq.symm))

/-- A simultaneous Cleanup group always decreases the Cleanup measure. Whenever no
object leaves and the Board count stays equal, a lethal root loses its damage while no new
damaged object or off-Board token is created. -/
theorem cleanupResolveDeathGroup_decreases {s : GameState} (wf : s.WF)
    {result : GameState × List Event} (resolved : cleanupResolveDeathGroup s = some result) :
    MeasLt result.1.cleanupMeasure s.cleanupMeasure := by
  let board := cleanupResolveDeathGroup_cleanupChange wf resolved
  by_cases shrink : result.1.pot < s.pot
  · exact MeasLt.at1 shrink
  have equal := Nat.le_antisymm board.pot (Nat.le_of_not_gt shrink)
  obtain ⟨entry, rest, plan, alreadyLive, lethal⟩ := cleanupDeathGroup_first_lethal resolved
  let group := cleanupDeathGroup s
  have groupRoots {id : ObjId} (mem : id ∈ group) : id ∈ s.inPlay := by
    unfold group cleanupDeathGroup at mem
    split at mem
    · simp at mem
    · exact (List.mem_filter.mp mem).1
  have pinned : s.deathGroupPrefix group ⊆ group := by
    intro id h
    exact List.contains_iff_mem.mp (List.mem_filter.mp h).2
  have tailRoots : ∀ e ∈ rest, e.unit ∈ s.inPlay := by
    intro e m
    apply groupRoots
    apply planDeathGroup_entries_mem cleanupResolveDeath group.length s group [] (s.deathGroupPrefix group)
      none [] (fun _ h => h) pinned
    change (planDeathGroup group none cleanupResolveDeath group.length s group []
      (s.deathGroupPrefix group) none []).1 = entry :: rest at plan
    rw [plan]
    exact List.mem_cons_of_mem _ m
  let afterFirst := (applyGroupDeath group cleanupResolveDeath s entry).1
  let afterAll := (applyEach (applyGroupDeath group cleanupResolveDeath) afterFirst rest).1
  let batch := applyEach (applyGroupDeath group cleanupResolveDeath) s (entry :: rest)
  let corrected := { afterAll with turnFx := deathGroupContextNotes s afterAll group batch.2 }
  have resultBoard : result.1 = clearDeathOrder corrected group := by
    unfold cleanupResolveDeathGroup at resolved
    dsimp only at resolved
    split at resolved
    · cases resolved
      unfold resolveDeathGroupWith
      dsimp only
      rw [plan]
      rfl
    · contradiction
  have first := resolveRoot_pot_eq wf group entry (Or.inl alreadyLive) (GameState.inPlay_lt_nextId wf alreadyLive)
  have firstWf := (applyGroupDeath_safe group cleanupResolveDeath_safe s entry).wf wf
  have restFacts := cleanupBatch_stable_damage wf firstWf group first.1 rest tailRoots
  have afterAllEq : afterAll.pot = s.pot := by
    rw [resultBoard] at equal
    exact equal
  have initialPot : afterFirst.pot = s.pot := by
    have down := first.1.pot
    have final := restFacts.1.pot
    change afterAll.pot ≤ afterFirst.pot at final
    change afterFirst.pot ≤ s.pot at down
    omega
  obtain ⟨firstDamage, healed⟩ := first.2 initialPot
  have restDamage := restFacts.2 (afterAllEq.trans initialPot.symm)
  have damage : CleanupDamageChange s result.1 := by
    rw [resultBoard]
    exact firstDamage.trans (restDamage.trans (CleanupDamageChange.of_sameBoard rfl rfl rfl))
  have zero : objectDamage result.1 entry.unit = 0 := by
    rw [resultBoard]
    have noMore := restDamage.damage entry.unit
    have gone := healed (lethal_owner lethal)
    change objectDamage afterAll entry.unit ≤ objectDamage afterFirst entry.unit at noMore
    change objectDamage afterFirst entry.unit = 0 at gone
    change objectDamage afterAll entry.unit = 0
    omega
  have hadDamage : 0 < objectDamage s entry.unit := by
    unfold GameState.lethal at lethal
    split at lethal
    · rename_i o found
      simp only [Bool.and_eq_true, decide_eq_true_eq] at lethal
      simpa [objectDamage, found] using lethal.1.2
    · contradiction
  have fewer := damagedCount_lt_of_healed ((cleanupResolveDeathGroup_safe resolved).wf wf)
    board.live (fun id _ => damage.damage id) alreadyLive hadDamage zero
  exact MeasLt.at2 equal (by rw [damage.tokens]; omega)

end Riftbound

end
