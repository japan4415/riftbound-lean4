module
public import Riftbound.Invariant.MightRead

/-!
# Preservation of the derived Might during ordinary trigger work
-/

@[expose] public section

namespace Riftbound

private theorem controllerLookup {s t : GameState} (same : SameMightReads s t)
    {id : ObjId} (old : id.n < s.nextId) :
    (t.obj? id).map Object.controller = (s.obj? id).map Object.controller :=
  same.readObj old (Option.map Object.controller) (by intro o; cases o <;> rfl)

private theorem amountAt_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    {src : ObjId} (old : src.n < s.nextId) (id : ObjId) (sel : Selector) (a : Amount)
    (select : MightRead.selector sel = true) (amount : MightRead.amount a = true) :
    (let p := (t.obj? src).map Object.controller
     p.elim 0 (fun p => if ((sel.eval t p src {}).getD []).contains id
       then ((a.evalS0 t p src {}).getD 0 : Int) else 0)) =
    (let p := (s.obj? src).map Object.controller
     p.elim 0 (fun p => if ((sel.eval s p src {}).getD []).contains id
       then ((a.evalS0 s p src {}).getD 0 : Int) else 0)) := by
  simp only [controllerLookup same old, same.selector_eq wf _ {} old sel select,
    same.amount_eq wf _ {} old a amount]

private theorem modMight_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    {src : ObjId} (old : src.n < s.nextId) (id : ObjId) (tank : t.hasKw id .tank = s.hasKw id .tank)
    (m : StaticMod) (accepted : MightRead.modifier m = true) :
    t.modMight src id m = s.modMight src id m := by
  have amountEq (sel : Selector) (amount : Amount) (selectorOk : MightRead.selector sel = true)
      (amountOk : MightRead.amount amount = true) :
      t.modMight src id (.mightPlus sel amount) = s.modMight src id (.mightPlus sel amount) := by
    have agree := amountAt_eq same wf old id sel amount selectorOk amountOk
    cases left : t.obj? src <;> cases right : s.obj? src <;>
      simp [GameState.modMight, left, right] at agree ⊢ <;> exact agree
  cases m <;> try rfl
  case mightPlus sel amount =>
    simp only [MightRead.modifier, Bool.and_eq_true] at accepted
    exact amountEq sel amount accepted.1 accepted.2
  case mightMinus sel amount =>
    simp only [MightRead.modifier, Bool.and_eq_true] at accepted
    exact congrArg Int.neg (amountEq sel amount accepted.1 accepted.2)
  case mightPlusWithKeyword sel k amount =>
    simp only [MightRead.modifier, Bool.and_eq_true, beq_iff_eq] at accepted
    obtain rfl := accepted.1.2
    have plus := amountEq sel amount accepted.1.1 accepted.2
    change (if t.hasKw id .tank then t.modMight src id (.mightPlus sel amount) else 0) =
      (if s.hasKw id .tank then s.modMight src id (.mightPlus sel amount) else 0)
    rw [tank, plus]

private theorem modFloor_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    {src : ObjId} (old : src.n < s.nextId) (id : ObjId)
    (m : StaticMod) (accepted : MightRead.modifier m = true) :
    t.modFloor src id m = s.modFloor src id m := by
  cases m <;> try rfl
  case mightMinusMin sel amt floor =>
    simp only [MightRead.modifier, Bool.and_eq_true] at accepted
    have controller := controllerLookup same old
    simp only [GameState.modFloor, controller, same.selector_eq wf _ {} old sel accepted.1]
    cases known : t.obj? src <;> cases previous : s.obj? src <;>
      simp only [known, previous, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at controller
    case none.none =>
      cases sel.eval s ((none : Option PlayerId).getD ⟨0⟩) src {} <;> rfl
    case some.some newer older =>
      have arg := same.amount_eq wf older.controller {} old amt accepted.2
      have finish (choices : Option (List ObjId)) :
          (match (some newer : Option Object), choices with
           | some o, some ids =>
             if ids.contains id then (amt.evalS0 t o.controller src {}).map (fun k => (k, floor)) else none
           | _, _ => none) =
          (match (some older : Option Object), choices with
           | some o, some ids =>
             if ids.contains id then (amt.evalS0 s o.controller src {}).map (fun k => (k, floor)) else none
           | _, _ => none) := by
        cases choices
        · rfl
        · change (if _ then (amt.evalS0 t newer.controller src {}).map _ else none) = _
          rw [controller, arg]
      exact finish _

private theorem passiveSources_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF) :
    t.passiveSources = s.passiveSources := by
  unfold GameState.passiveSources
  simp only [same.inPlay, same.players, same.playerZone]
  congr 1
  apply flatMap_congr_mem
  intro p _
  apply List.filter_congr
  intro id member
  exact same.readObj (old_of_zone wf member) (fun view => view.any (fun o => o.reservedBy.all s.inPlay.contains))
    (by intro view; cases view <;> rfl)

private theorem active_accepted {s : GameState} (database : MightRead.database s.cards)
    {src : ObjId} {mod : StaticMod} (active : mod ∈ (s.activeMods src).filter MightRead.relevant) :
    MightRead.modifier mod = true := by
  have relevant := (List.mem_filter.mp active).2
  have found := (List.mem_filter.mp active).1
  unfold GameState.activeMods at found
  cases srcObj : s.obj? src <;> cases srcDef : s.cardDef? src <;>
    simp only [srcObj, srcDef, List.not_mem_nil] at found
  case some.some obj d =>
    obtain ⟨ability, member, picked⟩ := List.mem_flatMap.mp found
    cases ability with
    | passive condition mods =>
      dsimp only at picked
      split at picked
      · have accepted := accepted_appendedAbilities database srcDef (.passive condition mods) member
        simp only [MightRead.ability, Bool.and_eq_true] at accepted
        exact List.all_eq_true.mp accepted.1 mod (List.mem_filter.mpr ⟨picked, relevant⟩)
      · contradiction
    | _ => contradiction

private theorem passiveSource_old {s : GameState} (wf : s.WF) {src : ObjId}
    (member : src ∈ s.passiveSources) : src.n < s.nextId := by
  simp only [GameState.passiveSources, List.mem_append, List.mem_flatMap] at member
  rcases member with board | ⟨_, _, legend⟩
  · exact old_inPlay wf board
  · exact old_of_zone wf (List.mem_filter.mp legend).1

private theorem sum_filter_zero {α : Type} (items : List α) (keep : α → Bool) (value : α → Int)
    (zero : ∀ x ∈ items, keep x = false → value x = 0) :
    (items.map value).sum = ((items.filter keep).map value).sum := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have later := ih (fun x member => zero x (List.mem_cons_of_mem _ member))
    cases picked : keep first
    · simp [picked, later, zero first List.mem_cons_self picked]
    · simp [picked, later]

private theorem filterMap_filter_none {α β : Type} (items : List α) (keep : α → Bool)
    (value : α → Option β) (empty : ∀ x ∈ items, keep x = false → value x = none) :
    items.filterMap value = (items.filter keep).filterMap value := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have later := ih (fun x member => empty x (List.mem_cons_of_mem _ member))
    cases picked : keep first
    · simp [picked, later, empty first List.mem_cons_self picked]
    · simp [picked, List.filterMap_cons, later]

private theorem sum_might_relevant (s : GameState) (src id : ObjId) (mods : List StaticMod) :
    (mods.map (s.modMight src id)).sum = ((mods.filter MightRead.relevant).map (s.modMight src id)).sum := by
  apply sum_filter_zero
  intro m _ irrelevant
  cases m <;> first | rfl | exact False.elim (by contradiction)

private theorem sum_flatMap_eq_on {α : Type} (items : List α) (f g : α → List Int)
    (same : ∀ i ∈ items, (f i).sum = (g i).sum) : (items.flatMap f).sum = (items.flatMap g).sum := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.flatMap_cons, List.sum_append, same _ List.mem_cons_self,
      ih (fun _ h => same _ (List.mem_cons_of_mem _ h))]

private theorem boardMight_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) (id : ObjId) (tank : t.hasKw id .tank = s.hasKw id .tank) :
    (t.passiveSources.flatMap (fun src => (t.activeMods src).map (t.modMight src id))).sum =
      (s.passiveSources.flatMap (fun src => (s.activeMods src).map (s.modMight src id))).sum := by
  rw [passiveSources_eq same wf]
  apply sum_flatMap_eq_on
  intro src member
  have old := passiveSource_old wf member
  rw [sum_might_relevant, sum_might_relevant s, same.activeMods_eq wf database old]
  apply congrArg List.sum
  apply List.map_congr_left
  intro mod active
  exact modMight_eq same wf old id tank mod (active_accepted database active)

private theorem filterMap_floor_relevant (s : GameState) (src id : ObjId) (mods : List StaticMod) :
    mods.filterMap (s.modFloor src id) = (mods.filter MightRead.relevant).filterMap (s.modFloor src id) := by
  apply filterMap_filter_none
  intro m _ irrelevant
  cases m <;> first | rfl | exact False.elim (by contradiction)

private theorem boardFloors_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) (id : ObjId) :
    t.passiveSources.flatMap (fun src => (t.activeMods src).filterMap (t.modFloor src id)) =
      s.passiveSources.flatMap (fun src => (s.activeMods src).filterMap (s.modFloor src id)) := by
  rw [passiveSources_eq same wf]
  apply flatMap_congr_mem
  intro src member
  have old := passiveSource_old wf member
  rw [filterMap_floor_relevant, filterMap_floor_relevant s, same.activeMods_eq wf database old]
  apply filterMap_congr_mem
  intro mod active
  exact modFloor_eq same wf old id mod (active_accepted database active)

private theorem equipment_accepted {db : CardDB} {d : CardDef} (database : MightRead.database db)
    (declared : DeclaredDefinition db d) : d.grants.all MightRead.equipmentAbility = true := by
  obtain ⟨printed, found, _, grants⟩ := declared
  have tested := List.all_eq_true.mp database printed (CardDB.find?_mem found)
  simp only [MightRead.card, Bool.and_eq_true] at tested
  exact grants ▸ tested.2

private def equipmentAdjustment (c : Condition) (unit : ObjId) (m : StaticMod) : Option (ObjId × StaticMod) :=
  match c, m with
  | .cmp .ge .xp (.const _), .mightPlus .self (.const _) => none
  | _, .mightPlus .. | _, .mightPlusWithKeyword .. |
    _, .mightMinus .. | _, .mightMinusMin .. => some (unit, m)
  | _, _ => none

private theorem equipmentAdjustment_wearer {c : Condition} {unit : ObjId} {m : StaticMod}
    {picked : ObjId × StaticMod} (result : equipmentAdjustment c unit m = some picked) :
    picked = (unit, m) ∧ MightRead.relevant m = true ∧
    MightRead.equipmentModifier m = MightRead.wearerModifier m := by
  unfold equipmentAdjustment at result
  split at result <;> first | contradiction | cases result; exact ⟨rfl, rfl, rfl⟩

private def equippedEffects (s : GameState) (p : PlayerId) (unit : ObjId) (grants : List Ability) :
    List (ObjId × StaticMod) :=
  grants.flatMap fun
    | .passive c mods =>
      if c.eval s p unit {} == some true then mods.filterMap (equipmentAdjustment c unit) else []
    | _ => []

private def gearEffects (s : GameState) (gear : ObjId) : List (ObjId × StaticMod) :=
  ((s.obj? gear).bind (·.attached)).elim [] (fun unit =>
    equippedEffects s (s.controllerOf unit) unit (((s.cardDef? gear).map (·.grants)).getD []))

private theorem equipmentMightMods_eq_flatMap (s : GameState) :
    s.equipmentMightMods = s.inPlay.flatMap (gearEffects s) := by
  unfold GameState.equipmentMightMods
  apply flatMap_congr_mem
  intro gear _
  unfold gearEffects equippedEffects
  cases (s.obj? gear).bind (·.attached) <;> rfl

private theorem equippedEffects_source {s : GameState} {p : PlayerId} {unit : ObjId} {grants : List Ability}
    {pair : ObjId × StaticMod} (member : pair ∈ equippedEffects s p unit grants) : pair.1 = unit := by
  obtain ⟨ab, _, produced⟩ := List.mem_flatMap.mp member
  cases ab with
  | passive c mods =>
    dsimp only at produced
    split at produced
    · obtain ⟨_, _, result⟩ := List.mem_filterMap.mp produced
      exact congrArg Prod.fst (equipmentAdjustment_wearer result).1
    · contradiction
  | _ => contradiction

private theorem equipmentMightMods_supported {db : CardDB} {s : GameState} (database : MightRead.database db)
    (registered : ∀ gear d, s.cardDef? gear = some d → DeclaredDefinition db d)
    {unit : ObjId} {mod : StaticMod} (mem : (unit, mod) ∈ s.equipmentMightMods) :
    MightRead.wearerModifier mod = true ∧ MightRead.modifier mod = true := by
  rw [equipmentMightMods_eq_flatMap] at mem
  obtain ⟨gear, _, granted⟩ := List.mem_flatMap.mp mem
  unfold gearEffects at granted
  cases attached : (s.obj? gear).bind (·.attached) with
  | none => simp [attached] at granted
  | some wearer =>
    cases found : s.cardDef? gear with
    | none => simp [attached, found, equippedEffects] at granted
    | some d =>
      simp only [attached, Option.elim_some, found, Option.map_some, Option.getD_some] at granted
      obtain ⟨ab, fromGrants, effect⟩ := List.mem_flatMap.mp granted
      cases ab with
      | passive c mods =>
        dsimp only at effect
        split at effect
        · obtain ⟨picked, member, produced⟩ := List.mem_filterMap.mp effect
          obtain ⟨samePair, relevant, wearerCheck⟩ := equipmentAdjustment_wearer produced
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj samePair
          have declared := registered gear d found
          have checks := List.all_eq_true.mp (equipment_accepted database declared) _ fromGrants
          have abChecks := List.all_eq_true.mp (declared_mightReads database declared) _
            (List.mem_append_right _ fromGrants)
          simp only [MightRead.equipmentAbility] at checks
          simp only [MightRead.ability, Bool.and_eq_true] at abChecks
          exact ⟨wearerCheck ▸ List.all_eq_true.mp checks mod member,
            List.all_eq_true.mp abChecks.1 mod (List.mem_filter.mpr ⟨member, relevant⟩)⟩
        · contradiction
      | _ => contradiction

private theorem equippedEffects_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    {unit : ObjId} (old : unit.n < s.nextId) (grants : List Ability)
    (checked : ∀ ab ∈ grants, MightRead.ability ab = true) :
    equippedEffects t (t.controllerOf unit) unit grants =
      equippedEffects s (s.controllerOf unit) unit grants := by
  unfold equippedEffects GameState.controllerOf
  rw [controllerLookup same old]
  apply flatMap_congr_mem
  intro ab member
  cases ab with
  | passive c mods =>
    dsimp only
    have check := checked (.passive c mods) member
    simp only [MightRead.ability, Bool.and_eq_true] at check
    by_cases active : mods.any MightRead.relevant = true
    · have cond : MightRead.condition c = true := by simpa [active] using check.2
      rw [same.condition_eq wf _ {} old c cond]
    · have empty : mods.filterMap (equipmentAdjustment c unit) = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro mod fromList
        cases outcome : equipmentAdjustment c unit mod with
        | none => rfl
        | some produced =>
          exact False.elim (active (List.any_eq_true.mpr
            ⟨mod, fromList, (equipmentAdjustment_wearer outcome).2.1⟩))
      split <;> split <;> simp only [empty]
  | _ => rfl

private theorem equippedFor_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) {id : ObjId} (old : id.n < s.nextId) :
    (t.equipmentMightMods.filter (·.1 == id)) = (s.equipmentMightMods.filter (·.1 == id)) := by
  rw [equipmentMightMods_eq_flatMap, equipmentMightMods_eq_flatMap s, same.inPlay,
    List.filter_flatMap, List.filter_flatMap]
  apply flatMap_congr_mem
  intro gear onBoard
  have attach := same.readObj (old_inPlay wf onBoard) (fun obj => obj.bind (·.attached))
    (by intro o; cases o <;> rfl)
  unfold gearEffects
  rw [same.cardDef, attach]
  cases (s.obj? gear).bind (·.attached) with
  | none => rfl
  | some wearer =>
    simp only [Option.elim_some]
    by_cases atId : wearer = id
    · subst wearer
      have checks : ∀ ab ∈ (((s.cardDef? gear).map (·.grants)).getD []), MightRead.ability ab = true := by
        intro ab member
        cases found : s.cardDef? gear with
        | none => simp [found] at member
        | some d =>
          exact List.all_eq_true.mp (declared_mightReads database (declared_of_cardDef found)) ab
            (List.mem_append_right _ (by simpa [found] using member))
      rw [equippedEffects_eq same wf old _ checks]
    · have empty (state : GameState) (p : PlayerId) :
          ((equippedEffects state p wearer (((s.cardDef? gear).map (·.grants)).getD [])).filter
            (·.1 == id)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro pair member hit
        exact atId ((equippedEffects_source member).symm.trans (beq_iff_eq.mp hit))
      simp only [empty]

private theorem wearerModifier_zero (s : GameState) {wearer unit : ObjId}
    (different : wearer ≠ unit) (mod : StaticMod) (wears : MightRead.wearerModifier mod = true) :
    s.modMight wearer unit mod = 0 := by
  have ne := Ne.symm different
  cases mod <;> try rfl
  case mightPlus sel _ =>
    cases sel <;> simp only [MightRead.wearerModifier, Bool.false_eq_true] at wears
    cases found : s.obj? wearer <;> simp [GameState.modMight, found, Selector.eval, ne]
  case mightPlusWithKeyword sel _ _ =>
    cases sel <;> simp only [MightRead.wearerModifier, Bool.false_eq_true] at wears
    cases found : s.obj? wearer <;> simp [GameState.modMight, found, Selector.eval, ne]
  case mightMinus sel _ =>
    cases sel <;> simp only [MightRead.wearerModifier, Bool.false_eq_true] at wears
    cases found : s.obj? wearer <;> simp [GameState.modMight, found, Selector.eval, ne]

private theorem wearerModifier_noFloor (s : GameState) {wearer unit : ObjId}
    (different : wearer ≠ unit) (mod : StaticMod) (wears : MightRead.wearerModifier mod = true) :
    s.modFloor wearer unit mod = none := by
  have ne := Ne.symm different
  cases mod <;> try rfl
  case mightMinusMin sel amount floor =>
    cases sel <;> simp only [MightRead.wearerModifier, Bool.false_eq_true] at wears
    cases before : s.obj? wearer <;> simp [GameState.modFloor, before, Selector.eval, ne]

private theorem equipmentMight_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) {id : ObjId} (old : id.n < s.nextId)
    (tank : t.hasKw id .tank = s.hasKw id .tank) :
    (t.equipmentMightMods.map (fun (unit, m) => t.modMight unit id m)).sum =
      (s.equipmentMightMods.map (fun (unit, m) => s.modMight unit id m)).sum := by
  have supportS {unit mod} (member : (unit, mod) ∈ s.equipmentMightMods) :=
    equipmentMightMods_supported database (fun _ _ h => declared_of_cardDef h) member
  have supportT {unit mod} (member : (unit, mod) ∈ t.equipmentMightMods) :=
    equipmentMightMods_supported database (fun gear d h => by
      rw [same.cardDef] at h
      exact declared_of_cardDef h) member
  have pruneS : ∀ pair ∈ s.equipmentMightMods, (pair.1 == id) = false →
      s.modMight pair.1 id pair.2 = 0 := by
    intro ⟨src, mod⟩ member different
    exact wearerModifier_zero s (beq_eq_false_iff_ne.mp different) mod (supportS member).1
  have pruneT : ∀ pair ∈ t.equipmentMightMods, (pair.1 == id) = false →
      t.modMight pair.1 id pair.2 = 0 := by
    intro ⟨src, mod⟩ member different
    exact wearerModifier_zero t (beq_eq_false_iff_ne.mp different) mod (supportT member).1
  rw [sum_filter_zero _ _ _ pruneT, sum_filter_zero _ _ _ pruneS, equippedFor_eq same wf database old]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨unit, mod⟩ relevant
  obtain ⟨member, forId⟩ := List.mem_filter.mp relevant
  have equal : unit = id := beq_iff_eq.mp forId
  subst unit
  exact modMight_eq same wf old id tank mod (supportS member).2

private theorem equipmentFloors_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) {id : ObjId} (old : id.n < s.nextId) :
    t.equipmentMightMods.filterMap (fun (unit, m) => t.modFloor unit id m) =
      s.equipmentMightMods.filterMap (fun (unit, m) => s.modFloor unit id m) := by
  have supportS {unit mod} (member : (unit, mod) ∈ s.equipmentMightMods) :=
    equipmentMightMods_supported database (fun _ _ h => declared_of_cardDef h) member
  have supportT {unit mod} (member : (unit, mod) ∈ t.equipmentMightMods) :=
    equipmentMightMods_supported database (fun gear d h => by
      rw [same.cardDef] at h
      exact declared_of_cardDef h) member
  have pruneS : ∀ pair ∈ s.equipmentMightMods, (pair.1 == id) = false →
      s.modFloor pair.1 id pair.2 = none := by
    intro ⟨src, mod⟩ member different
    exact wearerModifier_noFloor s (beq_eq_false_iff_ne.mp different) mod (supportS member).1
  have pruneT : ∀ pair ∈ t.equipmentMightMods, (pair.1 == id) = false →
      t.modFloor pair.1 id pair.2 = none := by
    intro ⟨src, mod⟩ member different
    exact wearerModifier_noFloor t (beq_eq_false_iff_ne.mp different) mod (supportT member).1
  rw [filterMap_filter_none _ _ _ pruneT, filterMap_filter_none _ _ _ pruneS, equippedFor_eq same wf database old]
  apply filterMap_congr_mem
  intro ⟨unit, mod⟩ relevant
  obtain ⟨member, forId⟩ := List.mem_filter.mp relevant
  have equal : unit = id := beq_iff_eq.mp forId
  subst unit
  exact modFloor_eq same wf old id mod (supportS member).2

private def mightKeyword (kw : KeywordInst) : Bool := MightRead.keyword kw.keyword

private def directGearKws (d : CardDef) : List KeywordInst :=
  d.grants.flatMap fun
    | .passive .always mods =>
      mods.filterMap (fun m => match m with | .keyword .self k => some k | _ => none)
    | _ => []

private def neighborGearKws (d : CardDef) : List KeywordInst :=
  d.grants.flatMap fun
    | .passive .always mods =>
      mods.filterMap (fun m => match m with | .keywordHere k => some k | _ => none)
    | _ => []

private theorem neighborGearKws_empty {d : CardDef}
    (checked : d.grants.all MightRead.equipmentAbility = true) :
    (neighborGearKws d).filter mightKeyword = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro k present relevant
  obtain ⟨ab, inText, produced⟩ := List.mem_flatMap.mp present
  split at produced
  · rename_i mods
    obtain ⟨modifier, available, found⟩ := List.mem_filterMap.mp produced
    split at found
    · rename_i inst
      have passed := List.all_eq_true.mp checked _ inText
      have modCheck := List.all_eq_true.mp passed (.keywordHere inst) available
      have excludes : !(mightKeyword inst) = true := modCheck
      rw [Option.some.inj found, relevant] at excludes
      contradiction
    · contradiction
  · contradiction

private def gearKwsAt (s : GameState) (d : CardDef) (gear : Object) (id : ObjId) : List KeywordInst :=
  (if gear.attached == some id then directGearKws d else []) ++
    match gear.attached.bind s.obj?, s.obj? id with
    | some host, some obj =>
      if host.controller == obj.controller && host.loc == obj.loc && id ∈ s.inPlay &&
          (s.cardDef? id).any (·.hasType .unit) then neighborGearKws d else []
    | _, _ => []

private theorem gearKwsAt_filter (s : GameState) {d : CardDef} (gear : Object) (id : ObjId)
    (checked : d.grants.all MightRead.equipmentAbility = true) :
    (gearKwsAt s d gear id).filter mightKeyword =
      (if gear.attached == some id then (directGearKws d).filter mightKeyword else []) := by
  unfold gearKwsAt
  rw [List.filter_append]
  have noNeighbors : (match gear.attached.bind s.obj?, s.obj? id with
      | some host, some obj =>
        if host.controller == obj.controller && host.loc == obj.loc && id ∈ s.inPlay &&
            (s.cardDef? id).any (fun (cd : CardDef) => cd.hasType .unit) then neighborGearKws d else []
      | _, _ => []).filter mightKeyword = [] := by
    split
    · split
      · exact neighborGearKws_empty checked
      · rfl
    · rfl
  rw [noNeighbors, List.append_nil]
  split <;> rfl

private theorem equipKws_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) (id : ObjId) :
    (t.equipKws id).filter mightKeyword = (s.equipKws id).filter mightKeyword := by
  change ((t.inPlay.flatMap (fun gear => match t.obj? gear, t.cardDef? gear with
    | some gearObj, some d => gearKwsAt t d gearObj id | _, _ => [])).filter mightKeyword) =
    ((s.inPlay.flatMap (fun gear => match s.obj? gear, s.cardDef? gear with
    | some gearObj, some d => gearKwsAt s d gearObj id | _, _ => [])).filter mightKeyword)
  simp only [same.inPlay, same.cardDef, List.filter_flatMap]
  apply flatMap_congr_mem
  intro gear onBoard
  have attached := same.readObj (old_inPlay wf onBoard) (Option.map Object.attached)
    (by intro o; cases o <;> rfl)
  cases found : s.cardDef? gear with
  | none => cases t.obj? gear <;> cases s.obj? gear <;> rfl
  | some d =>
    cases newer : t.obj? gear <;> cases older : s.obj? gear <;>
      simp only [newer, older, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at attached
    case none.none => rfl
    case some.some new prev =>
      change (gearKwsAt t d new id).filter mightKeyword = (gearKwsAt s d prev id).filter mightKeyword
      have checked := equipment_accepted database (declared_of_cardDef found)
      rw [gearKwsAt_filter t new id checked, gearKwsAt_filter s prev id checked, attached]

private def gearOf (s : GameState) (p : PlayerId) (id : ObjId) : List ObjId :=
  s.inPlay.filter (fun g => (s.obj? g).any (fun e => e.controller == p && e.attached == some id) &&
    (s.cardDef? g).any (·.hasType .gear))

private theorem gearOf_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF) (p : PlayerId) (id : ObjId) :
    gearOf t p id = gearOf s p id := by
  simp only [gearOf, same.inPlay, same.cardDef]
  apply List.filter_congr
  intro gear onBoard
  have reads := same.readObj (old_inPlay wf onBoard)
    (fun obj => obj.any (fun e => e.controller == p && e.attached == some id)) (by intro o; cases o <;> rfl)
  rw [reads]

private def passiveKeyword (s : GameState) (p : PlayerId) (src id : ObjId) : StaticMod → List KeywordInst
  | .keyword sel k => match sel.eval s p src {} with
    | some ids => if ids.contains id then [k] else []
    | none => []
  | .equipEach k => (gearOf s p id).map (fun _ => k)
  | _ => []

private theorem passiveKeyword_empty (s : GameState) (p : PlayerId) (src id : ObjId) (m : StaticMod)
    (discard : MightRead.relevant m = false) : (passiveKeyword s p src id m).filter mightKeyword = [] := by
  cases m <;> try rfl
  case keyword sel k =>
    have irrelevant : mightKeyword k = false := discard
    simp only [passiveKeyword]
    split
    · split <;> simp [irrelevant]
    · rfl
  case equipEach k =>
    have irrelevant : mightKeyword k = false := discard
    simp [passiveKeyword, List.filter_map, Function.comp_def, irrelevant]

private theorem flatMap_filter_empty {α β : Type} (items : List α) (keep : α → Bool) (emit : α → List β)
    (empty : ∀ x ∈ items, keep x = false → emit x = []) : items.flatMap emit = (items.filter keep).flatMap emit := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have later := ih (fun x member => empty x (List.mem_cons_of_mem _ member))
    cases picked : keep first
    · simp [picked, later, empty _ List.mem_cons_self picked]
    · simp [picked, later]

private theorem passiveKws_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) (id : ObjId) :
    (t.passiveKws id).filter mightKeyword = (s.passiveKws id).filter mightKeyword := by
  change ((t.passiveSources.flatMap (fun src => match t.obj? src with
    | some o => (t.activeMods src).flatMap (passiveKeyword t o.controller src id) | none => [])).filter mightKeyword) =
    ((s.passiveSources.flatMap (fun src => match s.obj? src with
    | some o => (s.activeMods src).flatMap (passiveKeyword s o.controller src id) | none => [])).filter mightKeyword)
  simp only [passiveSources_eq same wf, List.filter_flatMap]
  apply flatMap_congr_mem
  intro src member
  have old := passiveSource_old wf member
  have controllers := controllerLookup same old
  cases newer : t.obj? src <;> cases older : s.obj? src <;>
    simp only [newer, older, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at controllers
  case none.none => rfl
  case some.some new prev =>
    change ((t.activeMods src).flatMap (passiveKeyword t new.controller src id)).filter mightKeyword =
      ((s.activeMods src).flatMap (passiveKeyword s prev.controller src id)).filter mightKeyword
    rw [controllers, List.filter_flatMap, List.filter_flatMap,
      flatMap_filter_empty _ _ _ (fun m _ => passiveKeyword_empty t prev.controller src id m),
      flatMap_filter_empty _ _ _ (fun m _ => passiveKeyword_empty s prev.controller src id m),
      same.activeMods_eq wf database old]
    apply flatMap_congr_mem
    intro m fromMods
    cases m <;> try rfl
    case keyword sel k =>
      have check := active_accepted database fromMods
      simp only [MightRead.modifier] at check
      simp only [passiveKeyword, same.selector_eq wf _ {} old sel check]
    case equipEach k => simp only [passiveKeyword, gearOf_eq same wf]

private theorem grantedKws_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) {id : ObjId} (old : id.n < s.nextId) :
    (t.grantedKws id).filter mightKeyword = (s.grantedKws id).filter mightKeyword := by
  have temps := same.readObj old (Option.map Object.tempKws) (by intro o; cases o <;> rfl)
  simp only [GameState.grantedKws, List.filter_append, same.attachmentText, temps,
    equipKws_eq same wf database, passiveKws_eq same wf database]

private theorem anyKeyword_filter (keywords : List KeywordInst) (k : Keyword)
    (supported : MightRead.keyword k = true) :
    (keywords.filter mightKeyword).any (·.keyword == k) = keywords.any (·.keyword == k) := by
  rw [List.any_filter]
  apply congrArg (fun read => keywords.any read)
  funext i
  by_cases key : i.keyword = k <;> simp [mightKeyword, key, supported]

private theorem hasTank_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) {id : ObjId} (old : id.n < s.nextId) :
    t.hasKw id .tank = s.hasKw id .tank := by
  have checked : MightRead.keyword .tank = true := rfl
  have autoTank := congrArg (fun kws : List KeywordInst => kws.any (·.keyword == .tank))
    (grantedKws_eq same wf database old)
  simp only [anyKeyword_filter _ _ checked] at autoTank
  have reaction : ((Keyword.tank == .reaction) = false) := rfl
  have action : ((Keyword.tank == .action) = false) := rfl
  simp only [GameState.hasKw, same.cardDef, autoTank, reaction, action, Bool.false_and, Bool.or_false]

private def fixedKeywordAmount (k : Keyword) (i : KeywordInst) : Option Nat :=
  if i.keyword == k then
    match i.arg with
    | .amount n => some n
    | .none => if k == .assault || k == .shield || k == .disarm then some 1 else none
    | _ => none
  else none

private def keywordAmount (instances : List KeywordInst) (k : Keyword) (i : KeywordInst) : Option Nat :=
  if k == .assault && i.keyword == .assault && i.arg == .equalShield then
    some ((instances.filterMap (fixedKeywordAmount .shield)).sum)
  else fixedKeywordAmount k i

private theorem irrelevantKeyword_ne {i : KeywordInst} {k : Keyword}
    (kept : MightRead.keyword k = true) (dropped : mightKeyword i = false) : i.keyword ≠ k := by
  intro eq
  unfold mightKeyword at dropped
  rw [eq, kept] at dropped
  contradiction

private theorem keywordAmounts_eq {a b : List KeywordInst} (same : a.filter mightKeyword = b.filter mightKeyword)
    (k : Keyword) (keep : MightRead.keyword k = true) :
    (a.filterMap (keywordAmount a k)).sum = (b.filterMap (keywordAmount b k)).sum := by
  have shield : MightRead.keyword .shield = true := rfl
  have assault : MightRead.keyword .assault = true := rfl
  have shieldPrune (i : KeywordInst) (dropped : mightKeyword i = false) : fixedKeywordAmount .shield i = none := by
    simp [fixedKeywordAmount, irrelevantKeyword_ne shield dropped]
  have shields : a.filterMap (fixedKeywordAmount .shield) = b.filterMap (fixedKeywordAmount .shield) := by
    rw [filterMap_filter_none a _ _ (fun i _ => shieldPrune i),
      filterMap_filter_none b _ _ (fun i _ => shieldPrune i), same]
  have prune (all : List KeywordInst) (i : KeywordInst) (dropped : mightKeyword i = false) :
      keywordAmount all k i = none := by
    simp [keywordAmount, fixedKeywordAmount, irrelevantKeyword_ne assault dropped, irrelevantKeyword_ne keep dropped]
  rw [filterMap_filter_none a _ _ (fun i _ => prune a i),
     filterMap_filter_none b _ _ (fun i _ => prune b i), same]
  apply congrArg List.sum
  apply filterMap_congr_mem
  intro i _
  simp only [keywordAmount, shields]

private def addCountedAssault (s : GameState) (id : ObjId) (acc : Nat) : StaticMod → Nat
  | .assaultCount sel =>
    acc + (((sel.eval s ((s.obj? id).map (·.controller) |>.getD ⟨0⟩) id {}).map (·.length)).getD 0)
  | _ => acc

private theorem foldl_filter_neutral {α β : Type} (items : List α) (keep : α → Bool)
    (step : β → α → β) (start : β) (ignore : ∀ x, keep x = false → ∀ a, step a x = a) :
    items.foldl step start = (items.filter keep).foldl step start := by
  induction items generalizing start with
  | nil => rfl
  | cons first rest ih =>
    cases kept : keep first
    · simp [kept, ih, ignore _ kept]
    · simp [kept, ih]

private theorem foldl_eq_on {α β : Type} (items : List α) (f g : β → α → β) (init : β)
    (agree : ∀ x ∈ items, ∀ a, f a x = g a x) : items.foldl f init = items.foldl g init := by
  induction items generalizing init with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.foldl_cons, agree _ List.mem_cons_self, ih _ (fun _ h => agree _ (List.mem_cons_of_mem _ h))]

private theorem countedAssault_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) {id : ObjId} (old : id.n < s.nextId) :
    (t.activeMods id).foldl (addCountedAssault t id) 0 = (s.activeMods id).foldl (addCountedAssault s id) 0 := by
  have ignore (state : GameState) (m : StaticMod) (irrelevant : MightRead.relevant m = false) :
      ∀ n, addCountedAssault state id n m = n := by
    intro n
    cases m <;> first | rfl | contradiction
  rw [foldl_filter_neutral _ _ _ _ (ignore t), foldl_filter_neutral (s.activeMods id) _ _ _ (ignore s),
    same.activeMods_eq wf database old]
  apply foldl_eq_on
  intro m member acc
  cases m <;> try rfl
  case assaultCount sel =>
    have check : MightRead.selector sel = true := active_accepted database member
    simp only [addCountedAssault, controllerLookup same old, same.selector_eq wf _ {} old sel check]

private theorem kwAmount_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) {id : ObjId} (old : id.n < s.nextId)
    (k : Keyword) (keep : MightRead.keyword k = true) : t.kwAmount id k = s.kwAmount id k := by
  let instances (state : GameState) := ((state.cardDef? id).map (·.keywords)).getD [] ++ state.grantedKws id
  change ((instances t).filterMap (keywordAmount (instances t) k)).sum +
    (if k == .assault then (t.activeMods id).foldl (addCountedAssault t id) 0 else 0) =
    ((instances s).filterMap (keywordAmount (instances s) k)).sum +
    (if k == .assault then (s.activeMods id).foldl (addCountedAssault s id) 0 else 0)
  have sameInstances : (instances t).filter mightKeyword = (instances s).filter mightKeyword := by
    simp only [instances, List.filter_append, same.cardDef, grantedKws_eq same wf database old]
  rw [keywordAmounts_eq sameInstances k keep, countedAssault_eq same wf database old]

private def combatMightBonus (s : GameState) (id : ObjId) : Nat :=
  match s.combatNow, s.obj? id with
  | some (bf, attacker), some o =>
    if o.loc != some bf || !(s.zone .battlefieldZone).contains id ||
        !(s.cardDef? id).any (·.hasType .unit) then 0
    else if o.controller == attacker then s.kwAmount id .assault
    else if s.combat.isNone || s.combat.any (·.defender == o.controller) then
      s.kwAmount id .shield
    else 0
  | _, _ => 0

private theorem combatMightBonus_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) {id : ObjId} (old : id.n < s.nextId) :
    combatMightBonus t id = combatMightBonus s id := by
  have assault := kwAmount_eq same wf database old .assault rfl
  have shield := kwAmount_eq same wf database old .shield rfl
  simp only [combatMightBonus, same.combatNow, same.fieldZone, same.cardDef, same.combat, assault, shield]
  have lookup := same.objects id old
  generalize t.obj? id = after at lookup ⊢
  generalize s.obj? id = before at lookup ⊢
  apply eraseTriggerBookkeeping_read lookup
  intro o
  cases o with
  | none => rfl
  | some obj =>
    cases s.combatNow with
    | none => rfl
    | some combat => cases combat; rfl

/-- The Might of any existing object is unchanged when the states share the inputs read by
the registered Might rules. This includes Equipment, floors and combat keywords. -/
theorem SameMightReads.mightNow_eq {s t : GameState} (same : SameMightReads s t) (wf : s.WF)
    (database : MightRead.database s.cards) {id : ObjId} (old : id.n < s.nextId) :
    t.mightNow id = s.mightNow id := by
  have tank := hasTank_eq same wf database old
  have passive : t.passiveMight id = s.passiveMight id := by
    unfold GameState.passiveMight
    dsimp only
    rw [boardMight_eq same wf database id tank, equipmentMight_eq same wf database old tank]
  change t.mightWithCombatBonus id (combatMightBonus t id) = s.mightWithCombatBonus id (combatMightBonus s id)
  simp only [GameState.mightWithCombatBonus, combatMightBonus_eq same wf database old, same.mightOf,
    same.equipBonus, same.buffBonus, passive, boardFloors_eq same wf database, equipmentFloors_eq same wf database old]

/-- With a checked card database, automatic trigger finalization keeps every Board object's Might.
It creates no new threshold observations, so the actual step follows the raw dispatcher. -/
theorem workStep_triggers_sameMight (s : GameState) (wf : s.WF) (queue : List PendTrigger)
    (rest : List Frame) (pending : s.pending = .triggers queue :: rest)
    (database : MightRead.database s.cards) : workStep s = microStep0 s := by
  apply workStep_triggers_noMightEvents s wf queue rest pending
  intro outcome
  apply mightyEvents_eq_nil_of_mightNow
  intro id member
  exact ((triggersStep_sameMightReads s wf queue rest pending).mightNow_eq wf database (old_inPlay wf member)).symm

end Riftbound

end
