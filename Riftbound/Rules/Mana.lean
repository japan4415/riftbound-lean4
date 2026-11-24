module

public import Riftbound.Rules.Trigger
public import Riftbound.Rules.Battlefield

/-!
# Add abilities

An ability that adds Energy or Power to the Rune Pool resolves at once, without the Chain, and
players can use it whenever they could pay (CR 430, 164.2). Here the abilities that only exhaust
the object and add: "[Exhaust]: [Add] 1 Energy", "[Exhaust]: [Add] Power of a domain", "[Exhaust]:
[Add] Power of any domain". They are not activated abilities of the Chain: `activatable` refuses
them and `manaReady` lists them.

An Add that can be spent only on some things ("Use only to play spells") is not here.
-/

@[expose] public section

namespace Riftbound

/-- The costs of an Add the model can pay: whether the object is exhausted, and whether it is
killed ("Kill this, [Exhaust]: ..."). -/
def manaPlan : List AbilityCost → Option (Bool × Bool)
  | [] => some (false, false)
  | .exhaustSelf :: cs =>
    match manaPlan cs with
    | some (false, k) => some (true, k)
    | _ => none
  | .killSelf :: cs =>
    match manaPlan cs with
    | some (e, false) => some (e, true)
    | _ => none
  | _ :: _ => none

/-- Kill an object at once; a token that dies ceases to exist (CR 183): the step of the Cleanup that
removes it is done here, since the use of an Add is not followed by a Cleanup. -/
def killNow (s : GameState) (id : ObjId) : GameState :=
  let s1 := (killObj s id).1
  match tokenStep s1 with
  | some r => r.1
  | none => s1

/-- Killing at once is a safe change. -/
theorem killNow_safe (s : GameState) (id : ObjId) : Safe s (killNow s id) := by
  unfold killNow
  dsimp only
  split
  · rename_i r hr
    exact (killObj_safe s id).trans (tokenStep_safe hr)
  · exact killObj_safe s id

/-- The player can use the Add ability at place `idx` of the object `src` (CR 430, 164.2): it is
an ability they control, whose costs are to exhaust the object and to kill it. -/
def manaReady (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) : Bool :=
  s.phase == .main &&
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      o.controller == p && s.usesAbilitiesOf p src &&
        match d.fullAbilities[idx]? with
        | some (Ability.activated costs _ body lim) =>
          match manaPlan costs with
          | some (ex, _) =>
            (!ex || !o.exhausted) && (manaKind body).isSome && limitOk s src idx lim &&
              guardOk s p src body
          | none => false
        | _ => false
    | _, _ => false

/-- The Energy more an Add of the object makes, by passive abilities of objects the player controls
(Chem-Baroness: their Gold adds one more Energy). -/
def GameState.manaBonus (s : GameState) (p : PlayerId) (src : ObjId) : Nat :=
  s.passiveSources.foldl (fun acc g =>
    if (s.sourceOwner g).any (·.controller == p) then
      (s.activeMods g).foldl (fun acc m =>
        match m with
        | .manaExtraEnergy sel n =>
          if s.costSelects p g src sel then acc + ((n.evalS s p g {}).getD 0) else acc
        | _ => acc) acc
    else acc) 0

/-- Use an Add ability: pay (exhaust, kill), and the Pool gets what is added (CR 430.2). -/
def applyMana (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) :
    Option (GameState × List Event) :=
  match s.cardDef? src with
  | some d =>
    match d.fullAbilities[idx]? with
    | some (Ability.activated costs _ body _) =>
      match manaPlan costs, manaKind body with
      | some (ex, kill), some k =>
        let s1 := s.modObj src (useOf idx ex)
        let s2 := if kill then killNow s1 src else s1
        -- Power that only paid for Gear and is spent is no longer noted
        let s2' := s2.trimGear p
        -- the Power that only pays for Gear is noted for the turn
        let s3 := match k with | .gear _ => s2'.addTurnFx p .gearMana | _ => s2'
        some (s3.setPool p ((k.add (s.poolOf p)).addEnergy (s.manaBonus p src)), [])
      | _, _ => none
    | _ => none
  | none => none

/-- The shape of an Add being used: a safe change, and the Pool. -/
theorem applyMana_cases {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (h : applyMana s p src idx = some (s', es)) :
    ∃ s1 pool, Safe s s1 ∧ s' = s1.setPool p pool := by
  unfold applyMana at h
  cases hd : s.cardDef? src with
  | none => simp [hd] at h
  | some d =>
    cases ha : d.fullAbilities[idx]? with
    | none => simp [hd, ha] at h
    | some ab =>
      cases ab with
      | activated costs sp body lim =>
        simp only [hd, ha] at h
        cases hp : manaPlan costs with
        | none => simp [hp] at h
        | some pe =>
          obtain ⟨ex, kill⟩ := pe
          cases hk : manaKind body with
          | none => simp [hp, hk] at h
          | some k =>
            simp only [hp, hk, Option.some.injEq, Prod.mk.injEq] at h
            have h1 : Safe s (s.modObj src (useOf idx ex)) :=
              Safe.modObj s src (fun _ => rfl) (fun _ => rfl)
            refine ⟨_, _, ?_, h.1.symm⟩
            have h2 : Safe s (if kill = true then killNow (s.modObj src (useOf idx ex)) src
                else s.modObj src (useOf idx ex)) := by
              cases kill
              · exact h1
              · exact h1.trans (killNow_safe _ src)
            have h3 := h2.trans (trimGear_safe _ p)
            cases k with
            | gear n => exact h3.trans (addTurnFx_safe _ _ _)
            | energy n => exact h3
            | power d n => exact h3
            | any n => exact h3
      | passive _ _ => simp [hd, ha] at h
      | replacement _ _ _ => simp [hd, ha] at h
      | triggered _ _ _ => simp [hd, ha] at h

/-- Using an Add keeps the game well formed. -/
theorem applyMana_wf {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (hwf : s.WF) (h : applyMana s p src idx = some (s', es)) : s'.WF := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  exact (hs.wf hwf).congr rfl rfl rfl rfl

/-- Using an Add keeps the physical cards. -/
theorem applyMana_physIds {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (hwf : s.WF) (h : applyMana s p src idx = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  have h2 : (s1.setPool p pool).physIds = s1.physIds := rfl
  rw [h2]
  exact hs.phys hwf

/-- Using an Add keeps `OwnerOk`. -/
theorem applyMana_ownerOk {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : applyMana s p src idx = some (s', es)) : s'.OwnerOk := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  exact (hs.own hwf hown).congr rfl rfl

/-- Using an Add changes nothing of the stack, the turn order, the phase, the result or the
rules. -/
theorem applyMana_meta {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (h : applyMana s p src idx = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  exact ⟨hs.same.config, hs.same.turnOrder, hs.same.phase, hs.same.result, hs.same.pending⟩

/-- An Add can be used in the Main Phase only. -/
theorem manaReady_main {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    (h : manaReady s p src idx = true) : s.phase = .main := by
  unfold manaReady at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- A ready Add is an ability of the card of the object. -/
theorem manaReady_ability {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    (h : manaReady s p src idx = true) :
    ∃ d ab, s.cardDef? src = some d ∧ d.fullAbilities[idx]? = some ab := by
  unfold manaReady at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases ho : s.obj? src with
  | none => simp [ho] at h
  | some o =>
    cases hd : s.cardDef? src with
    | none => simp [ho, hd] at h
    | some d =>
      simp only [ho, hd, Bool.and_eq_true] at h
      cases ha : d.fullAbilities[idx]? with
      | none => simp [ha] at h
      | some ab => exact ⟨d, ab, rfl, ha⟩

/-- A ready Add can be used. -/
theorem applyMana_isSome {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    (h : manaReady s p src idx = true) : ∃ r, applyMana s p src idx = some r := by
  unfold manaReady at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases ho : s.obj? src with
  | none => simp [ho] at h
  | some o =>
    cases hd : s.cardDef? src with
    | none => simp [ho, hd] at h
    | some d =>
      simp only [ho, hd, Bool.and_eq_true] at h
      obtain ⟨-, h⟩ := h
      cases ha : d.fullAbilities[idx]? with
      | none => simp [ha] at h
      | some ab =>
        cases ab with
        | activated costs sp body lim =>
          simp only [ha] at h
          cases hp : manaPlan costs with
          | none => simp [hp] at h
          | some pe =>
            obtain ⟨ex, kill⟩ := pe
            simp only [hp, Bool.and_eq_true] at h
            cases hk : manaKind body with
            | none => rw [hk] at h; simp at h
            | some k =>
              have : (applyMana s p src idx).isSome = true := by
                simp [applyMana, hd, ha, hp, hk]
              exact Option.isSome_iff_exists.mp this
        | passive _ _ => simp [ha] at h
        | replacement _ _ _ => simp [ha] at h
        | triggered _ _ _ => simp [ha] at h

/-- Every Add the player can use now, with the objects they use abilities of. -/
def legalManas (s : GameState) (p : PlayerId) : List Action :=
  (s.zone (.player p .base) ++ s.zone (.player p .legendZone) ++ s.zone .battlefieldZone).flatMap
    (fun src =>
      match s.cardDef? src with
      | some d =>
        ((List.range d.fullAbilities.length).filter (fun idx => manaReady s p src idx)).map
          (fun idx => ⟨.player p, .manaAbility src idx⟩)
      | none => [])

/-- The Adds listed are exactly the ones that can be used. -/
theorem mem_legalManas (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalManas s p ↔ ∃ src idx, a = ⟨.player p, .manaAbility src idx⟩ ∧
      manaReady s p src idx = true := by
  constructor
  · intro ha
    unfold legalManas at ha
    simp only [List.mem_flatMap] at ha
    obtain ⟨src, -, ha⟩ := ha
    cases hd : s.cardDef? src with
    | none => simp [hd] at ha
    | some d =>
      simp only [hd, List.mem_map, List.mem_filter] at ha
      obtain ⟨idx, ⟨-, hr⟩, rfl⟩ := ha
      exact ⟨src, idx, rfl, hr⟩
  · rintro ⟨src, idx, rfl, hr⟩
    unfold legalManas
    simp only [List.mem_flatMap]
    have huse : s.usesAbilitiesOf p src = true := by
      unfold manaReady at hr
      simp only [Bool.and_eq_true] at hr
      cases ho : s.obj? src with
      | none => simp [ho] at hr
      | some o =>
        cases hd : s.cardDef? src with
        | none => simp [ho, hd] at hr
        | some d =>
          simp only [ho, hd, Bool.and_eq_true] at hr
          exact hr.2.1.2
    refine ⟨src, ?_, ?_⟩
    · simp only [GameState.usesAbilitiesOf, Bool.or_eq_true, List.contains_iff_mem] at huse
      simp only [List.mem_append]
      exact huse
    · obtain ⟨d, ab, hd, ha⟩ := manaReady_ability hr
      simp only [hd, List.mem_map, List.mem_filter]
      exact ⟨idx, ⟨List.mem_range.mpr (List.getElem?_eq_some_iff.mp ha).1, hr⟩, rfl⟩

end Riftbound

end
