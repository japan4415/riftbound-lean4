module

public import Riftbound.Invariant.Cleanup

/-!
# Board changes during nested Cleanup deaths

A replacement may Kill another permanent before healing and recalling its original target.
Each nested step can move a permanent within the Board or take it out of play. An identifier
that left the Board must stay retired while the remaining replacements finish.
-/

@[expose] public section

namespace Riftbound

/-- Board and identity facts preserved by the operations that resolve a Cleanup death. -/
structure CleanupDeathChange (s t : GameState) : Prop where
  /-- The Board contribution to the Cleanup measure does not grow. -/
  pot : t.pot ≤ s.pot
  /-- A surviving Board object was already on the Board. -/
  live : t.inPlay ⊆ s.inPlay
  /-- Removing a Board object retires its old identifier and decreases the Board count. -/
  retired : ∀ id ∈ s.inPlay, id ∉ t.inPlay → t.obj? id = none ∧ t.pot < s.pot
  /-- A previously retired identifier is not reused. -/
  absent : ∀ id : ObjId, id.n < s.nextId → s.obj? id = none → t.obj? id = none
  /-- Any later allocation uses an identifier at or above the old counter. -/
  next : s.nextId ≤ t.nextId

/-- Objects on the Board have identifiers below the fresh-identifier counter. -/
theorem GameState.inPlay_lt_nextId {s : GameState} (wf : s.WF) {id : ObjId}
    (live : id ∈ s.inPlay) : id.n < s.nextId := by
  obtain ⟨zone, _, mem⟩ := GameState.mem_inPlay_zone live
  exact wf.lt_nextId id (GameState.mem_zoneIds (GameState.zone_valid_of_mem wf mem) mem)

namespace CleanupDeathChange

theorem refl (s : GameState) : CleanupDeathChange s s :=
  ⟨Nat.le_refl _, fun _ h => h, fun _ h notLive => False.elim (notLive h),
    fun _ _ absent => absent, Nat.le_refl _⟩

private theorem inPlay_eq_of_zones {s t : GameState} (config : t.config = s.config)
    (zone : t.zone = s.zone) : t.inPlay = s.inPlay := by
  simp [GameState.inPlay, GameState.players, GameState.playerCount, config, zone]

private theorem pot_eq_of_zones {s t : GameState} (config : t.config = s.config)
    (zone : t.zone = s.zone) : t.pot = s.pot := by
  simp [GameState.pot, GameState.legendCount, GameState.legendZones,
    GameState.players, GameState.playerCount, config, zone, inPlay_eq_of_zones config zone]

private theorem of_sameZones {s t : GameState} (config : t.config = s.config)
    (zone : t.zone = s.zone) (next : t.nextId = s.nextId)
    (keepAbsent : ∀ id, s.obj? id = none → t.obj? id = none) : CleanupDeathChange s t := by
  refine ⟨Nat.le_of_eq (pot_eq_of_zones config zone), ?_, ?_,
    fun id _ absent => keepAbsent id absent, Nat.le_of_eq next.symm⟩
  · rw [inPlay_eq_of_zones config zone]
    exact fun _ h => h
  · rw [inPlay_eq_of_zones config zone]
    exact fun _ h notLive => False.elim (notLive h)

theorem of_sameBoard {s t : GameState} (config : t.config = s.config)
    (zones : t.zones = s.zones) (objects : t.objects = s.objects) (next : t.nextId = s.nextId) :
    CleanupDeathChange s t :=
  of_sameZones config (by funext z; simp [GameState.zone, zones]) next
    (fun id absent => by simpa [GameState.obj?, objects] using absent)

theorem trans {s t u : GameState} (wf : s.WF)
    (first : CleanupDeathChange s t) (second : CleanupDeathChange t u) :
    CleanupDeathChange s u := by
  refine ⟨Nat.le_trans second.pot first.pot, fun _ h => first.live (second.live h), ?_, ?_,
    Nat.le_trans first.next second.next⟩
  · intro id was notLive
    by_cases there : id ∈ t.inPlay
    · obtain ⟨gone, drop⟩ := second.retired id there notLive
      exact ⟨gone, Nat.lt_of_lt_of_le drop first.pot⟩
    · obtain ⟨gone, drop⟩ := first.retired id was there
      exact ⟨second.absent id (Nat.lt_of_lt_of_le (GameState.inPlay_lt_nextId wf was) first.next) gone,
        Nat.lt_of_le_of_lt second.pot drop⟩
  · intro id below absent
    exact second.absent id (Nat.lt_of_lt_of_le below first.next) (first.absent id below absent)

theorem inPlay_or_absent {s t : GameState} (change : CleanupDeathChange s t)
    {id : ObjId} (old : id ∈ s.inPlay) :
    id ∈ t.inPlay ∨ t.obj? id = none := by
  by_cases live : id ∈ t.inPlay
  · exact Or.inl live
  · exact Or.inr (change.retired id old live).1

end CleanupDeathChange

private theorem inPlayZones_same {s t : GameState} (config : t.config = s.config) :
    t.inPlayZones = s.inPlayZones := by
  simp [GameState.inPlayZones, GameState.players, GameState.playerCount, config]

private theorem mem_moved_board {s t : GameState} {id id' x : ObjId} {pos : Pos}
    {src dst : Zone} (move : MoveSpec s t id id' pos src dst)
    (source : src ∈ s.inPlayZones) (destination : dst ∈ s.inPlayZones → id' = id)
    (live : x ∈ t.inPlay) : x ∈ s.inPlay := by
  simp only [GameState.inPlay_eq_flatMap, inPlayZones_same move.config, List.mem_flatMap] at live ⊢
  obtain ⟨zone, onBoard, member⟩ := live
  by_cases atDest : zone = dst
  · subst zone
    rw [move.zone_dst] at member
    have alternatives : x = id' ∨ x ∈ s.zone dst :=
      List.mem_cons.mp ((Pos.insert_perm pos id' (s.zone dst)).subset member)
    rcases alternatives with rfl | stayed
    · rw [destination onBoard]
      exact ⟨src, source, move.id_mem⟩
    · exact ⟨dst, onBoard, stayed⟩
  · refine ⟨zone, onBoard, ?_⟩
    by_cases atSource : zone = src
    · subst zone
      rw [move.zone_src] at member
      exact List.mem_of_mem_erase member
    · rwa [move.zone_other atSource atDest] at member

private theorem move_absent {s t : GameState} {id id' x : ObjId} {pos : Pos}
    {src dst : Zone} (wf : s.WF) (move : MoveSpec s t id id' pos src dst)
    (below : x.n < s.nextId) (absent : s.obj? x = none) : t.obj? x = none := by
  have notSource : x.n ≠ id.n := by
    intro eq
    obtain ⟨o, found⟩ := GameState.obj_of_mem wf move.id_mem
    change s.objects[x.n]? = none at absent
    rw [eq, ← GameState.obj?, found] at absent
    contradiction
  have notDest : x.n ≠ id'.n := by
    rcases move.fresh with rfl | fresh
    · exact notSource
    · omega
  exact (move.objects_other x.n notSource notDest).trans absent

private theorem move_remove_old {s t : GameState} {id id' : ObjId} {pos : Pos}
    {src dst : Zone} (move : MoveSpec s t id id' pos src dst) (fresh : id'.n ≠ id.n) :
    t.obj? id = none := by
  apply Std.ExtTreeMap.getElem?_eq_none
  intro mem
  rcases (move.objects id.n).mp mem with ⟨_, h⟩ | h
  · exact h rfl
  · exact fresh h.symm

theorem move_board_objects {s t : GameState} {id id' : ObjId} {pos : Pos}
    {src dst : Zone} (step : moveObj s id dst pos = some (t, id'))
    (origin : s.locate id = some src) (sourceBoard : src.isBoard = true)
    (destBoard : dst.isBoard = true) : t.objects = s.objects ∧ t.nextId = s.nextId := by
  unfold moveObj at step
  rw [origin] at step
  cases found : s.obj? id with
  | none => simp [found] at step
  | some o =>
    simp only [found] at step
    have normalized : Zone.normalize o.owner dst = dst := by
      cases dst <;> simp_all [Zone.normalize]
    rw [normalized] at step
    simp only [Zone.crosses, sourceBoard, destBoard, Bool.and_self, Bool.not_true,
      Bool.false_eq_true, ite_false] at step
    split at step
    · contradiction
    · cases step
      exact ⟨rfl, rfl⟩

private theorem obj_none_iff {s : GameState} (wf : s.WF) (id : ObjId) :
    s.obj? id = none ↔ id ∉ s.zoneIds := by
  constructor
  · intro absent member
    have table := wf.table_of_zone id member
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at table
    change s.objects[id.n]? = none at absent
    simp [absent] at table
  · intro absent
    apply Std.ExtTreeMap.getElem?_eq_none
    intro member
    obtain ⟨other, present, eq⟩ := wf.zone_of_table id.n member
    exact absent ((objId_eq_of_n eq) ▸ present)

private theorem change_of_same_zones {s t : GameState} (before : s.WF) (after : t.WF)
    (config : t.config = s.config) (zones : t.zone = s.zone) (next : t.nextId = s.nextId) :
    CleanupDeathChange s t := by
  have ids : t.zoneIds = s.zoneIds := by
    simp [GameState.zoneIds, GameState.playerCount, config, zones]
  exact CleanupDeathChange.of_sameZones config zones next (fun id absent => by
    rwa [obj_none_iff after, ids, ← obj_none_iff before])

private theorem noteIf_nextId (s : GameState) (b : Bool) (f : GameState → GameState)
    (keep : ∀ t, (f t).nextId = t.nextId) :
    (noteIf b f s).nextId = s.nextId := by
  unfold noteIf
  split
  · exact keep s
  · rfl

private theorem noteDeath_nextId (s : GameState) (o : Object) (isUnit marked mighty : Bool)
    (moved : Option ObjId) (banisher : Option ObjId) :
    (noteDeath s o isUnit marked mighty moved banisher).nextId = s.nextId := by
  have count (t : GameState) : (t.noteUnitDied o.controller).nextId = t.nextId := by
    unfold GameState.noteUnitDied
    split <;> rfl
  cases moved <;> simp only [noteDeath]
  all_goals
    repeat (rw [noteIf_nextId] <;> first | rfl | exact count | exact fun _ => rfl | skip)

private theorem noteAlone_nextId (s : GameState) (o : Object) (moved : Option ObjId)
    (alone : Bool) : (noteAlone s o moved alone).nextId = s.nextId := by
  cases moved with
  | none => rfl
  | some id => exact noteIf_nextId _ _ _ (fun _ => rfl)

private theorem killObj_send_positions (s : GameState) (id : ObjId) :
    let sent := (sendObj (if s.banishedOnDeath id then .banishment else .trash) s id).1
    (killObj s id).1.zone = sent.zone ∧ (killObj s id).1.nextId = sent.nextId := by
  unfold killObj
  dsimp only
  generalize sendObj (if s.banishedOnDeath id then .banishment else .trash) s id = sent
  cases s.obj? id with
  | none => exact ⟨rfl, rfl⟩
  | some o =>
    dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨by funext z; rw [noteAlone_zone, noteDeath_zone],
        by rw [noteAlone_nextId, noteDeath_nextId]⟩

private theorem inPlay_zone_isBoard {s : GameState} {z : Zone}
    (mem : z ∈ s.inPlayZones) : z.isBoard = true := by
  simp only [GameState.inPlayZones, List.mem_append, List.mem_map, List.mem_singleton] at mem
  rcases mem with ⟨p, _, rfl⟩ | rfl <;> rfl

/-- A Kill in a Cleanup group never grows the Board. It either takes the current target
off the Board under a fresh identifier, or has no zone move. -/
theorem killObj_cleanupChange {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) : CleanupDeathChange s (killObj s id).1 := by
  let k : ZoneKind := if s.banishedOnDeath id then .banishment else .trash
  have kTypes : k = .trash ∨ k = .banishment := by unfold k; split <;> simp
  have ⟨zoneEq, nextEq⟩ := killObj_send_positions s id
  change (killObj s id).1.zone = (sendObj k s id).1.zone at zoneEq
  change (killObj s id).1.nextId = (sendObj k s id).1.nextId at nextEq
  have configEq := (killObj_safe s id).same.config.trans (sendObj_safe k s id).same.config.symm
  have notes := change_of_same_zones ((sendObj_safe k s id).wf wf) ((killObj_safe s id).wf wf)
    configEq zoneEq nextEq
  cases found : s.obj? id with
  | none =>
    have sent : (sendObj k s id).1 = s := by simp [sendObj, found]
    rwa [sent] at notes
  | some o =>
    have live : id ∈ s.inPlay := target.resolve_right (by simp [found])
    obtain ⟨origin, source, member⟩ :=
      List.mem_flatMap.mp (GameState.inPlay_eq_flatMap s ▸ live)
    let dest := s.ownerDestination id o k
    have outside : (Zone.player o.owner dest).isBoard = false := by
      change (Zone.player o.owner (s.ownerDestination id o k)).isBoard = false
      rcases s.ownerDestination_trash_or_banishment id o kTypes with h | h <;> rw [h] <;> rfl
    cases step : moveObj s id (.player o.owner dest) with
    | none =>
      change moveObj s id (.player o.owner (s.ownerDestination id o k)) = none at step
      have sent : (sendObj k s id).1 = s := by simp [sendObj, found, step]
      rwa [sent] at notes
    | some result =>
      obtain ⟨middle, new⟩ := result
      change moveObj s id (.player o.owner (s.ownerDestination id o k)) = some (middle, new) at step
      have sent : (sendObj k s id).1 = middle := by simp [sendObj, found, step]
      change moveObj s id (.player o.owner dest) = some (middle, new) at step
      rw [sent] at notes
      obtain ⟨src, dst, move, obj, actual, normalized⟩ := moveObj_spec_dst step
      have objEq := Option.some.inj (actual.symm.trans found)
      subst obj
      rw [Zone.normalize_owner] at normalized
      subst dst
      have loc := GameState.locate_eq wf (GameState.zone_valid_of_mem wf member) member
      have srcEq := Option.some.inj (move.locate.symm.trans loc)
      subst src
      have offBoard : Zone.player o.owner dest ∉ s.inPlayZones :=
        fun h => by
          have board := inPlay_zone_isBoard h
          simp [outside] at board
      have owner : ∀ value, s.obj? id = some value → value.owner.n < s.playerCount := by
        intro value equal
        rw [found] at equal
        cases equal
        exact Zone.lt_of_valid_player move.dst_mem
      have movedFresh : new.n = s.nextId := by
        unfold moveObj at step
        rw [loc, found] at step
        simp only [Zone.normalize_owner] at step
        split at step
        · contradiction
        · simp [Zone.crosses, inPlay_zone_isBoard source, outside] at step
          exact congrArg ObjId.n step.2.symm
      have removed : middle.obj? id = none := by
        have below := wf.lt_nextId id (GameState.mem_zoneIds move.src_mem move.id_mem)
        exact move_remove_old move (by omega)
      have potDrop : middle.pot < s.pot := by
        have eq : (killObj s id).1.pot = middle.pot := by
          rw [← sent]
          exact CleanupDeathChange.pot_eq_of_zones configEq zoneEq
        rw [← eq]
        exact killObj_pot_lt wf owner live
      have before : CleanupDeathChange s middle := by
        refine ⟨Nat.le_of_lt potDrop, fun _ => mem_moved_board move source (fun h => False.elim (offBoard h)),
          ?_, fun _ => move_absent wf move, move.next.1⟩
        · intro x original absent
          by_cases same : x = id
          · exact ⟨same ▸ removed, potDrop⟩
          · exfalso
            apply absent
            have original' := killObj_mem_inPlay_ne wf same original owner live
            have inPlay : (killObj s id).1.inPlay = middle.inPlay := by
              rw [← sent]
              exact CleanupDeathChange.inPlay_eq_of_zones configEq zoneEq
            exact inPlay ▸ original'
      exact before.trans wf notes

private theorem modObj_cleanupChange (s : GameState) (id : ObjId) (f : Object → Object) :
    CleanupDeathChange s (s.modObj id f) :=
  CleanupDeathChange.of_sameZones rfl (funext (GameState.zone_modObj s id f)) rfl
    (fun x absent => by
      rcases obj?_modObj_cases s id f x with same | ⟨_, found, _⟩
      · exact same.trans absent
      · rw [absent] at found
        contradiction)

private theorem stays_on_moved_board {s t : GameState} {id x : ObjId} {pos : Pos}
    {src dst : Zone} (move : MoveSpec s t id id pos src dst)
    (destination : dst ∈ s.inPlayZones) (live : x ∈ s.inPlay) : x ∈ t.inPlay := by
  simp only [GameState.inPlay_eq_flatMap, inPlayZones_same move.config, List.mem_flatMap] at live ⊢
  by_cases same : x = id
  · exact ⟨dst, destination, same ▸ move.id'_mem⟩
  · obtain ⟨zone, onBoard, member⟩ := live
    refine ⟨zone, onBoard, ?_⟩
    by_cases atDest : zone = dst
    · subst zone
      rw [move.zone_dst]
      exact (Pos.insert_perm pos id (s.zone dst)).symm.subset (List.mem_cons_of_mem _ member)
    · by_cases atSource : zone = src
      · subst zone
        rw [move.zone_src]
        exact (List.mem_erase_of_ne same).mpr member
      · rwa [move.zone_other atSource atDest]

private theorem sendHome_cleanupChange {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) : CleanupDeathChange s (sendHome s id).1 := by
  unfold sendHome
  cases found : s.obj? id with
  | none => exact CleanupDeathChange.refl s
  | some o =>
    dsimp only
    have live : id ∈ s.inPlay := target.resolve_right (by simp [found])
    cases step : moveObj s id (.player o.controller .base) with
    | none => exact CleanupDeathChange.refl s
    | some result =>
      obtain ⟨t, new⟩ := result
      obtain ⟨origin, source, member⟩ :=
        List.mem_flatMap.mp (GameState.inPlay_eq_flatMap s ▸ live)
      obtain ⟨src, dst, move, obj, actual, dstEq⟩ := moveObj_spec_dst step
      have objEq := Option.some.inj (actual.symm.trans found)
      subst obj
      have normalized : Zone.normalize o.owner (.player o.controller .base) =
          .player o.controller .base := rfl
      rw [normalized] at dstEq
      subst dst
      have loc := GameState.locate_eq wf (GameState.zone_valid_of_mem wf member) member
      have srcEq := Option.some.inj (move.locate.symm.trans loc)
      subst src
      have destination : Zone.player o.controller .base ∈ s.inPlayZones := by
        have seat := Zone.lt_of_valid_player move.dst_mem
        simp only [GameState.inPlayZones, GameState.players, List.mem_append, List.mem_map,
          List.mem_range, List.mem_singleton]
        exact Or.inl ⟨o.controller, ⟨o.controller.n, seat, rfl⟩, rfl⟩
      have srcBoard := inPlay_zone_isBoard source
      have same : new = id := move.crosses.resolve_left (by
        rw [Zone.crosses, srcBoard]
        change false ≠ true
        decide)
      subst new
      obtain ⟨objects, counter⟩ := move_board_objects step loc (inPlay_zone_isBoard source) rfl
      have moved : CleanupDeathChange s t := by
        have pot := sendHome_core wf live found step
        exact ⟨by omega, fun _ => mem_moved_board move source (fun _ => rfl),
          fun _ inPlay notLive => False.elim (notLive (stays_on_moved_board move destination inPlay)),
          fun x _ absent => by simpa [GameState.obj?, objects] using absent, Nat.le_of_eq counter.symm⟩
      exact moved.trans wf (modObj_cleanupChange t id (fun o => { o with loc := none }))

private theorem setExhausted_cleanupChange (s : GameState) (id : ObjId) :
    CleanupDeathChange s (setExhausted true s id).1 := by
  unfold setExhausted
  split
  · exact modObj_cleanupChange s id _
  · exact CleanupDeathChange.refl s

theorem completeDeathSave_cleanupChange {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) (mark : Option TurnEffect)
    (p : PlayerId) (clear : Bool) : CleanupDeathChange s (completeDeathSave s id mark p clear).1 := by
  let heal := fun o : Object => { o with damage := 0 }
  let healed := s.modObj id heal
  have healChange := modObj_cleanupChange s id heal
  have healedTarget : id ∈ healed.inPlay ∨ healed.obj? id = none := by
    rcases target with live | absent
    · exact Or.inl (inPlay_modObj s id heal ▸ live)
    · exact Or.inr (by simp [healed, GameState.obj?_modObj, absent])
  let moved := (sendHome healed id).1
  let recalled := (setExhausted true moved id).1
  have position := healChange.trans wf
    (sendHome_cleanupChange ((Safe.modObj s id (f := heal) (fun _ => rfl) (fun _ => rfl)).wf wf)
      healedTarget)
  have settled := position.trans wf (setExhausted_cleanupChange moved id)
  change CleanupDeathChange s (finishDeathSave recalled id p mark clear)
  exact settled.trans wf (CleanupDeathChange.of_sameBoard rfl rfl rfl rfl)

/-- A nested Kill can only shrink the Board, and replacements can only recall surviving
objects. The result applies to each fuel value used by the real replacement resolver. -/
theorem killOrSaveFrom_cleanupChange (root : ObjId) (fuel : Nat) {s : GameState} (wf : s.WF)
    {id : ObjId} (used : List (ObjId × Bool)) (live : id ∈ s.inPlay) :
    CleanupDeathChange s (killOrSaveFrom root fuel s id used).1 := by
  induction fuel generalizing s id used with
  | zero =>
    have ready : CleanupDeathChange s (prepareNestedDeath s root id used) :=
      CleanupDeathChange.of_sameBoard rfl rfl rfl rfl
    exact ready.trans wf (killObj_cleanupChange ((prepareNestedDeath_safe s root id used).wf wf)
      (Or.inl live))
  | succ fuel ih =>
    unfold killOrSaveFrom
    dsimp only
    split
    · have ready : CleanupDeathChange s (prepareNestedDeath s root id used) :=
        CleanupDeathChange.of_sameBoard rfl rfl rfl rfl
      exact ready.trans wf (killObj_cleanupChange ((prepareNestedDeath_safe s root id used).wf wf)
        (Or.inl live))
    · rename_i save found
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
            exact ih wf _ member
      have paymentWf : paid.WF := by
        cases cost : save.cost with
        | none => simpa [paid, cost] using wf
        | some next => simpa [paid, cost] using
            (killOrSaveFrom_safe root fuel s next (save.useKey id :: used)).wf wf
      exact payment.trans wf (completeDeathSave_cleanupChange paymentWf
        (payment.inPlay_or_absent live) _ _ _)

/-- Identity and Board-size guarantees of a resolved nested Cleanup death. -/
theorem killOrSave_cleanupChange {s : GameState} (wf : s.WF) {id : ObjId} (live : id ∈ s.inPlay) :
    CleanupDeathChange s (killOrSave s id).1 :=
  (killOrSaveFrom_cleanupChange id _ wf [] live).trans wf
    (CleanupDeathChange.of_sameBoard rfl rfl rfl rfl)

private theorem saveUnit_cleanupChange {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) (old : id.n < s.nextId) (cost : Option ObjId)
    (costLive : ∀ gear, cost = some gear → gear ∈ s.inPlay) :
    CleanupDeathChange s (saveUnit s id cost).1 := by
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
  have result := payment.trans wf (completeDeathSave_cleanupChange paymentWf paidTarget
    (s.deathSaveMark id (cost.isSome && cost == s.selectedDeathSacrifice id) cost)
    (((s.obj? id).map (·.controller)).getD ⟨0⟩) true)
  cases cost <;> exact result

/-- All Cleanup death paths obey the same Board and identifier invariants, including
an entry that already left the Board during an earlier replacement. -/
theorem cleanupResolveDeath_cleanupChange {s : GameState} (wf : s.WF) {id : ObjId}
    (target : id ∈ s.inPlay ∨ s.obj? id = none) (old : id.n < s.nextId) :
    CleanupDeathChange s (cleanupResolveDeath s id).1 := by
  unfold cleanupResolveDeath
  split
  · rename_i nested
    suffices live : id ∈ s.inPlay from killOrSave_cleanupChange wf live
    refine target.resolve_right ?_
    intro absent
    have noneSaved : s.deathSaveFor id [] = none := by
      simp [GameState.deathSaveFor, GameState.cardDef?, absent]
    simp [hasNestedDeath, noneSaved] at nested
  · change CleanupDeathChange s (cleanupKillCore s id).1
    unfold cleanupKillCore
    split
    · rename_i gear selected
      split
      · exact saveUnit_cleanupChange wf target old (some gear) (fun g eq =>
          (Option.some.inj eq) ▸ GameState.deathSaver_cost_mem selected)
      · exact killObj_cleanupChange wf target
    · split
      · exact saveUnit_cleanupChange wf target old none (fun _ eq => nomatch eq)
      · split
        · exact (modObj_cleanupChange s id (fun o => { o with damage := 0, exhausted := true })).trans
            wf (CleanupDeathChange.of_sameBoard rfl rfl rfl rfl)
        · exact killObj_cleanupChange wf target
    · exact killObj_cleanupChange wf target

theorem DeathGroupEntry.prepare_board (entry : DeathGroupEntry) (group : List ObjId)
    (s : GameState) :
    let t := entry.prepare group s
    t.config = s.config ∧ t.zones = s.zones ∧ t.objects = s.objects ∧ t.nextId = s.nextId := by
  unfold DeathGroupEntry.prepare
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem applyGroupDeath_cleanupChange {s : GameState} (wf : s.WF) (group : List ObjId)
    (entry : DeathGroupEntry) (target : entry.unit ∈ s.inPlay ∨ s.obj? entry.unit = none)
    (old : entry.unit.n < s.nextId) :
    CleanupDeathChange s (applyGroupDeath group cleanupResolveDeath s entry).1 := by
  let ready := entry.prepare group s
  have ⟨config, zones, objects, counter⟩ := entry.prepare_board group s
  change ready.config = s.config at config
  change ready.zones = s.zones at zones
  change ready.objects = s.objects at objects
  change ready.nextId = s.nextId at counter
  have readyWf := wf.congr config objects zones counter
  have prep := CleanupDeathChange.of_sameBoard config zones objects counter
  have readyTarget : entry.unit ∈ ready.inPlay ∨ ready.obj? entry.unit = none := by
    rcases target with live | absent
    · exact prep.inPlay_or_absent live
    · exact Or.inr (prep.absent _ old absent)
  have result := prep.trans wf (cleanupResolveDeath_cleanupChange readyWf readyTarget (counter ▸ old))
  unfold applyGroupDeath
  dsimp only
  split
  · exact result
  · exact result.trans wf (CleanupDeathChange.of_sameBoard rfl rfl rfl rfl)

private theorem applyCleanupDeaths_change {before s : GameState} (beforeWf : before.WF)
    (wf : s.WF) (group : List ObjId) (applied : CleanupDeathChange before s)
    (entries : List DeathGroupEntry) (roots : ∀ entry ∈ entries, entry.unit ∈ before.inPlay) :
    CleanupDeathChange before (applyEach (applyGroupDeath group cleanupResolveDeath) s entries).1 := by
  induction entries generalizing s with
  | nil => exact applied
  | cons entry rest ih =>
    have live := roots entry (by simp)
    have older := Nat.lt_of_lt_of_le (GameState.inPlay_lt_nextId beforeWf live) applied.next
    have advance := applyGroupDeath_cleanupChange wf group entry (applied.inPlay_or_absent live) older
    have appliedSafe := applyGroupDeath_safe group cleanupResolveDeath_safe s entry
    exact ih (appliedSafe.wf wf) (applied.trans beforeWf advance)
      (fun dropped mem => roots dropped (List.mem_cons_of_mem _ mem))

/-- The actual simultaneous resolver cannot increase the Board contribution of the Cleanup
measure. Its projected choices may still refer to a root removed by an earlier replacement. -/
theorem cleanupResolveDeathGroup_cleanupChange {s : GameState} (wf : s.WF)
    {result : GameState × List Event} (resolved : cleanupResolveDeathGroup s = some result) :
    CleanupDeathChange s result.1 := by
  unfold cleanupResolveDeathGroup at resolved
  dsimp only at resolved
  split at resolved
  · cases resolved
    let group := cleanupDeathGroup s
    have source {id : ObjId} (mem : id ∈ group) : id ∈ s.inPlay := by
      unfold group cleanupDeathGroup at mem
      split at mem
      · simp at mem
      · exact (List.mem_filter.mp mem).1
    have pinned : s.deathGroupPrefix group ⊆ group := by
      intro id h
      exact List.contains_iff_mem.mp (List.mem_filter.mp h).2
    have entries := applyCleanupDeaths_change wf wf group (CleanupDeathChange.refl s)
      (planDeathGroup group none cleanupResolveDeath group.length s group [] (s.deathGroupPrefix group)
        none []).1
      (fun entry h => source (planDeathGroup_entries_mem cleanupResolveDeath _ _ _ _ _ _ _
        (fun _ m => m) pinned h))
    exact entries.trans wf (CleanupDeathChange.of_sameBoard rfl rfl rfl rfl)
  · contradiction

/-- A Cleanup group that removes any Board object strictly decreases the Cleanup measure. -/
theorem cleanupResolveDeathGroup_lt_of_removed {s : GameState} (wf : s.WF)
    {result : GameState × List Event} (resolved : cleanupResolveDeathGroup s = some result)
    {id : ObjId} (before : id ∈ s.inPlay) (after : id ∉ result.1.inPlay) :
    MeasLt result.1.cleanupMeasure s.cleanupMeasure :=
  MeasLt.at1 ((cleanupResolveDeathGroup_cleanupChange wf resolved).retired id before after).2

end Riftbound

end
