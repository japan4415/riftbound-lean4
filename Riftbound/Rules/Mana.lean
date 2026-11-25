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

/-- Every way to take Power from the domains, as many of each as the cap says, in the order of the
domains. -/
def powerBags : List (Domain × Nat) → List (List Domain)
  | [] => [[]]
  | (d, c) :: rest =>
    (List.range (c + 1)).flatMap (fun k => (powerBags rest).map (fun l => List.replicate k d ++ l))

/-- The Power a payment can name: each domain as many times as the Pool holds it and any domain
could cover, the domains in a fixed order (fury, calm, mind, body, chaos, order). -/
def RunePool.payBags (p : RunePool) : List (List Domain) :=
  powerBags ([Domain.fury, .calm, .mind, .body, .chaos, .order].map (fun d => (d, p.get d + p.any)))

/-- What using an Add does to the Pool, if the payment is right for it: an Add of an amount takes
no payment; "pay any amount of Power to add that much Energy" takes Power only, and the other way
round takes Energy only (Hextech Anomaly, Ancient Henge). -/
def ManaKind.apply (k : ManaKind) (pool : RunePool) (pay : RunePool.Payment) : Option RunePool :=
  match k with
  | .powerToEnergy =>
    if pay.energy = 0 && !pay.power.isEmpty && decide (pay.power ∈ pool.payBags) then
      (pool.spend pay).map (fun q => q.addEnergy pay.power.length)
    else none
  | .energyToPower =>
    if pay.power.isEmpty && pay.energy ≠ 0 then
      (pool.spend pay).map (fun q => q.addAny pay.energy)
    else none
  | _ => if pay == ⟨0, []⟩ then some (k.add pool) else none

/-- Use an Add ability: pay (exhaust, kill, and what the Add takes), and the Pool gets what is added
(CR 430.2). -/
def applyMana (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (pay : RunePool.Payment) :
    Option (GameState × List Event) :=
  match s.cardDef? src with
  | some d =>
    match d.fullAbilities[idx]? with
    | some (Ability.activated costs _ body _) =>
      match manaPlan costs, manaKind body with
      | some (ex, kill), some k =>
        match k.apply (s.poolOf p) pay with
        | some pool' =>
          let s1 := s.modObj src (useOf idx ex)
          let s2 := if kill then killNow s1 src else s1
          -- Power that only paid for Gear and is spent is no longer noted
          let s2' := s2.trimGear p
          -- the Power that only pays for Gear is noted for the turn
          let s3 := match k with | .gear _ => s2'.addTurnFx p .gearMana | _ => s2'
          let noted := s3.noteGearAbility p d costs
          some (noted.setPool p (pool'.addEnergy (s.manaBonus p src)), [Event.activated p src idx])
        | none => none
      | _, _ => none
    | _ => none
  | none => none

/-- The shape of an Add being used: a safe change, and the Pool. -/
theorem applyMana_cases {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {es : List Event} (h : applyMana s p src idx pay = some (s', es)) :
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
            cases hap : k.apply (s.poolOf p) pay with
            | none => simp [hp, hk, hap] at h
            | some pool' =>
              simp only [hp, hk, hap, Option.some.injEq, Prod.mk.injEq] at h
              have h1 : Safe s (s.modObj src (useOf idx ex)) :=
                Safe.modObj s src (fun _ => rfl) (fun _ => rfl)
              refine ⟨_, _, Safe.trans ?_ (GameState.noteGearAbility_safe _ p d costs), h.1.symm⟩
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
              | powerToEnergy => exact h3
              | energyToPower => exact h3
      | passive _ _ => simp [hd, ha] at h
      | replacement _ _ _ => simp [hd, ha] at h
      | triggered _ _ _ => simp [hd, ha] at h

/-- Using an Add keeps the game well formed. -/
theorem applyMana_wf {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {es : List Event} (hwf : s.WF)
    (h : applyMana s p src idx pay = some (s', es)) : s'.WF := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  exact (hs.wf hwf).congr rfl rfl rfl rfl

/-- Using an Add keeps the physical cards. -/
theorem applyMana_physIds {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {es : List Event} (hwf : s.WF)
    (h : applyMana s p src idx pay = some (s', es)) : s'.physIds.Perm s.physIds := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  have h2 : (s1.setPool p pool).physIds = s1.physIds := rfl
  rw [h2]
  exact hs.phys hwf

/-- Using an Add keeps `OwnerOk`. -/
theorem applyMana_ownerOk {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : applyMana s p src idx pay = some (s', es)) : s'.OwnerOk := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  exact (hs.own hwf hown).congr rfl rfl

/-- Using an Add changes nothing of the stack, the turn order, the phase, the result or the
rules. -/
theorem applyMana_meta {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {es : List Event} (h : applyMana s p src idx pay = some (s', es)) :
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

/-- The payment is the right one for the Add: none for an Add of an amount; for "pay any amount",
Power only or Energy only that the Pool holds. -/
def manaPayOk (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat)
    (pay : RunePool.Payment) : Bool :=
  match (s.cardDef? src).bind (fun d => d.fullAbilities[idx]?) with
  | some (Ability.activated _ _ body _) =>
    match manaKind body with
    | some k => (k.apply (s.poolOf p) pay).isSome
    | none => false
  | _ => false

/-- The player can use the Add with the payment: it is ready, and the payment is the right one. -/
def manaOk (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (pay : RunePool.Payment) :
    Bool :=
  manaReady s p src idx && manaPayOk s p src idx pay

/-- A usable Add is used in the Main Phase. -/
theorem manaOk_main {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} (h : manaOk s p src idx pay = true) : s.phase = .main := by
  unfold manaOk at h
  simp only [Bool.and_eq_true] at h
  exact manaReady_main h.1

/-- A usable Add can be used. -/
theorem applyMana_isSome {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} (h : manaOk s p src idx pay = true) :
    ∃ r, applyMana s p src idx pay = some r := by
  unfold manaOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hr, hp⟩ := h
  unfold manaReady at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨-, hr⟩ := hr
  cases ho : s.obj? src with
  | none => simp [ho] at hr
  | some o =>
    cases hd : s.cardDef? src with
    | none => simp [ho, hd] at hr
    | some d =>
      simp only [ho, hd, Bool.and_eq_true] at hr
      obtain ⟨-, hr⟩ := hr
      cases ha : d.fullAbilities[idx]? with
      | none => simp [ha] at hr
      | some ab =>
        cases ab with
        | activated costs sp body lim =>
          simp only [ha] at hr
          cases hp' : manaPlan costs with
          | none => simp [hp'] at hr
          | some pe =>
            obtain ⟨ex, kill⟩ := pe
            simp only [hp', Bool.and_eq_true] at hr
            cases hk : manaKind body with
            | none => rw [hk] at hr; simp at hr
            | some k =>
              unfold manaPayOk at hp
              simp only [hd, ha, Option.bind_some, hk] at hp
              obtain ⟨pool', hpool⟩ := Option.isSome_iff_exists.mp hp
              have : (applyMana s p src idx pay).isSome = true := by
                simp [applyMana, hd, ha, hp', hk, hpool]
              exact Option.isSome_iff_exists.mp this
        | passive _ _ => simp [ha] at hr
        | replacement _ _ _ => simp [ha] at hr
        | triggered _ _ _ => simp [ha] at hr

/-- Every payment an Add of the object takes that the Pool can make: none for an Add of an amount;
for "pay any amount", every Power the Pool holds, or every amount of Energy. -/
def manaPays (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) : List RunePool.Payment :=
  match (s.cardDef? src).bind (fun d => d.fullAbilities[idx]?) with
  | some (Ability.activated _ _ body _) =>
    match manaKind body with
    | some .powerToEnergy =>
      (s.poolOf p).payBags.filterMap (fun pw => if pw.isEmpty then none else some ⟨0, pw⟩)
    | some .energyToPower => (List.range (s.poolOf p).energy).map (fun i => ⟨i + 1, []⟩)
    | _ => [⟨0, []⟩]
  | _ => []

/-- Every Add the player can use now, with the objects they use abilities of. -/
def legalManas (s : GameState) (p : PlayerId) : List Action :=
  (s.zone (.player p .base) ++ s.zone (.player p .legendZone) ++ s.zone .battlefieldZone).flatMap
    (fun src =>
      match s.cardDef? src with
      | some d =>
        ((List.range d.fullAbilities.length).filter (fun idx => manaReady s p src idx)).flatMap
          (fun idx => ((manaPays s p src idx).filter (fun pay => manaPayOk s p src idx pay)).map
            (fun pay => ⟨.player p, .manaAbility src idx pay⟩))
      | none => [])

/-- The payment an Add takes is one of those listed, when it is the right one. -/
theorem mem_manaPays {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} (h : manaPayOk s p src idx pay = true) :
    pay ∈ manaPays s p src idx := by
  unfold manaPayOk at h
  unfold manaPays
  cases hab : (s.cardDef? src).bind (fun d => d.fullAbilities[idx]?) with
  | none => simp [hab] at h
  | some ab =>
    cases ab with
    | activated costs sp body lim =>
      simp only [hab] at h ⊢
      cases hk : manaKind body with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h ⊢
        cases k with
        | powerToEnergy =>
          simp only [ManaKind.apply] at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
            obtain ⟨⟨he, hne⟩, hsub⟩ := hc
            obtain ⟨en, pw⟩ := pay
            simp only at he hne hsub
            subst he
            simp only [List.mem_filterMap]
            refine ⟨pw, hsub, ?_⟩
            simp [hne]
          · simp at h
        | energyToPower =>
          simp only [ManaKind.apply] at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, List.isEmpty_iff, ne_eq, decide_eq_true_eq] at hc
            obtain ⟨hpw, hen⟩ := hc
            obtain ⟨en, pw⟩ := pay
            simp only at hpw hen
            subst hpw
            cases hsp : (s.poolOf p).spend ⟨en, []⟩ with
            | none => simp [hsp] at h
            | some q =>
              have hle : en ≤ (s.poolOf p).energy := by
                unfold RunePool.spend at hsp
                split at hsp
                · assumption
                · simp at hsp
              simp only [List.mem_map, List.mem_range]
              exact ⟨en - 1, by omega, by simp [Nat.sub_add_cancel (Nat.pos_of_ne_zero hen)]⟩
          · simp at h
        | energy n =>
          simp only [ManaKind.apply] at h
          split at h
          · rename_i hc
            simp only [beq_iff_eq] at hc
            simp [hc]
          · simp at h
        | power d n =>
          simp only [ManaKind.apply] at h
          split at h
          · rename_i hc
            simp only [beq_iff_eq] at hc
            simp [hc]
          · simp at h
        | any n =>
          simp only [ManaKind.apply] at h
          split at h
          · rename_i hc
            simp only [beq_iff_eq] at hc
            simp [hc]
          · simp at h
        | gear n =>
          simp only [ManaKind.apply] at h
          split at h
          · rename_i hc
            simp only [beq_iff_eq] at hc
            simp [hc]
          · simp at h
    | passive _ _ => simp [hab] at h
    | replacement _ _ _ => simp [hab] at h
    | triggered _ _ _ => simp [hab] at h

/-- The Adds listed are exactly the ones that can be used. -/
theorem mem_legalManas (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalManas s p ↔ ∃ src idx pay, a = ⟨.player p, .manaAbility src idx pay⟩ ∧
      manaOk s p src idx pay = true := by
  constructor
  · intro ha
    unfold legalManas at ha
    simp only [List.mem_flatMap] at ha
    obtain ⟨src, -, ha⟩ := ha
    cases hd : s.cardDef? src with
    | none => simp [hd] at ha
    | some d =>
      simp only [hd, List.mem_flatMap, List.mem_map, List.mem_filter] at ha
      obtain ⟨idx, ⟨-, hr⟩, pay, ⟨-, hp⟩, rfl⟩ := ha
      exact ⟨src, idx, pay, rfl, by unfold manaOk; simp [hr, hp]⟩
  · rintro ⟨src, idx, pay, rfl, hok⟩
    unfold manaOk at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hr, hp⟩ := hok
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
      simp only [hd, List.mem_flatMap, List.mem_map, List.mem_filter]
      exact ⟨idx, ⟨List.mem_range.mpr (List.getElem?_eq_some_iff.mp ha).1, hr⟩, pay,
        ⟨mem_manaPays hp, hp⟩, rfl⟩

end Riftbound

end
