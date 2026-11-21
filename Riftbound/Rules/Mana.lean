module

public import Riftbound.Rules.Trigger

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

/-- The player can use the Add ability at place `idx` of the object `src` (CR 430, 164.2): it is
an ability they control, which only needs the object to exhaust. -/
def manaReady (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) : Bool :=
  s.phase == .main &&
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      o.controller == p && s.usesAbilitiesOf p src &&
        match d.fullAbilities[idx]? with
        | some (Ability.activated costs _ body lim) =>
          match costPlan costs with
          | some (ex, none) =>
            (!ex || !o.exhausted) && (manaKind body).isSome && limitOk s src idx lim
          | _ => false
        | _ => false
    | _, _ => false

/-- Use an Add ability: exhaust the object, and the Pool gets what is added (CR 430.2). -/
def applyMana (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) :
    Option (GameState × List Event) :=
  match s.cardDef? src with
  | some d =>
    match d.fullAbilities[idx]? with
    | some (Ability.activated costs _ body _) =>
      (manaKind body).map (fun k =>
        (((s.modObj src (useOf idx (costExhausts costs))).setPool p
          (k.add (s.poolOf p))), []))
    | _ => none
  | none => none

/-- The shape of an Add being used. -/
theorem applyMana_cases {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (h : applyMana s p src idx = some (s', es)) :
    ∃ f pool, (∀ o, (f o).kind = o.kind ∧ (f o).owner = o.owner) ∧
      s' = (s.modObj src f).setPool p pool := by
  unfold applyMana at h
  cases hd : s.cardDef? src with
  | none => simp [hd] at h
  | some d =>
    cases ha : d.fullAbilities[idx]? with
    | none => simp [hd, ha] at h
    | some ab =>
      cases ab with
      | activated costs sp body lim =>
        simp only [hd, ha, Option.map_eq_some_iff] at h
        obtain ⟨k, -, hr⟩ := h
        simp only [Prod.mk.injEq] at hr
        exact ⟨useOf idx (costExhausts costs), _, fun o => ⟨rfl, rfl⟩, hr.1.symm⟩
      | passive _ _ => simp [hd, ha] at h
      | replacement _ _ _ => simp [hd, ha] at h
      | triggered _ _ _ => simp [hd, ha] at h

/-- Using an Add keeps the game well formed. -/
theorem applyMana_wf {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (hwf : s.WF) (h : applyMana s p src idx = some (s', es)) : s'.WF := by
  obtain ⟨f, pool, hf, rfl⟩ := applyMana_cases h
  exact (GameState.wf_modObj hwf src f).congr rfl rfl rfl rfl

/-- Using an Add keeps the physical cards. -/
theorem applyMana_physIds {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (_hwf : s.WF) (h : applyMana s p src idx = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨f, pool, hf, rfl⟩ := applyMana_cases h
  have h2 : ((s.modObj src f).setPool p pool).physIds = (s.modObj src f).physIds := rfl
  rw [h2, GameState.physIds_modObj s src (fun o => (hf o).1)]

/-- Using an Add keeps `OwnerOk`. -/
theorem applyMana_ownerOk {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (_hwf : s.WF) (hown : s.OwnerOk)
    (h : applyMana s p src idx = some (s', es)) : s'.OwnerOk := by
  obtain ⟨f, pool, hf, rfl⟩ := applyMana_cases h
  exact (GameState.ownerOk_modObj hown src (fun o => (hf o).2)).congr rfl rfl

/-- Using an Add changes nothing of the stack, the turn order, the phase, the result or the
rules, and leaves the hands. -/
theorem applyMana_meta {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {es : List Event} (h : applyMana s p src idx = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending ∧
        ∀ q, s'.zone (.player q .hand) = s.zone (.player q .hand) := by
  obtain ⟨f, pool, hf, rfl⟩ := applyMana_cases h
  have hs2 := GameState.sameMeta_modObj s src f
  exact ⟨hs2.config, hs2.turnOrder, hs2.phase, hs2.result, hs2.pending,
    fun q => GameState.zone_modObj s src f _⟩

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
          cases hp : costPlan costs with
          | none => simp [hp] at h
          | some pe =>
            obtain ⟨ex, pc⟩ := pe
            cases pc with
            | some c => simp [hp] at h
            | none =>
              simp only [hp, Bool.and_eq_true] at h
              cases hk : manaKind body with
              | none => rw [hk] at h; simp at h
              | some k =>
                exact ⟨(((s.modObj src (useOf idx (costExhausts costs))).setPool p
                  (k.add (s.poolOf p))), []), by simp [applyMana, hd, ha, hk]⟩
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
