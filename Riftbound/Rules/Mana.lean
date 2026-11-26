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

The Pool records resources reserved for a kind of card or ability.
-/

@[expose] public section

namespace Riftbound

/-- The costs of an Add ability, before considering any variable exchange of resources. -/
structure ManaCostPlan where
  /-- Exhaust its source. -/
  exhaust : Bool := false
  /-- Kill its source. -/
  kill : Bool := false
  /-- Select one card in the player's Trash and Banish it as a cost. -/
  banish : Option FilterList := none
  /-- The fixed Energy and Power to pay. -/
  cost : Cost := Cost.zero

/-- Read the fixed costs a resource ability can pay (CR 357, 430). -/
def manaPlan : List AbilityCost → Option ManaCostPlan
  | [] => some {}
  | .exhaustSelf :: cs => do
    let plan ← manaPlan cs
    if plan.exhaust then none else some { plan with exhaust := true }
  | .killSelf :: cs => do
    let plan ← manaPlan cs
    if plan.kill then none else some { plan with kill := true }
  | .banishFromTrash filters :: cs => do
    let plan ← manaPlan cs
    if plan.banish.isSome then none else some { plan with banish := some filters }
  | .pay cost :: cs =>
    (manaPlan cs).map (fun plan => { plan with cost := cost.plus plan.cost })
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
  s.phase != .setup &&
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      o.controller == p && s.usesAbilitiesOf p src &&
        match (s.activationList src d)[idx]? with
        | some (grant, .activated costs speed body lim) =>
          let timing := match s.pending with
            | .chainPass .. :: _ => speed == .reaction
            | .eitherDo _ _ _ first _ _ :: _ => first.isPayment && speed == .reaction
            | .showdown .. :: _ => speed != .normal
            | _ => s.phase == .main
          match manaPlan costs with
          | some plan =>
            timing && (!plan.exhaust || !o.exhausted) && (manaKind body).isSome &&
              limitOk s src (activationUseIndex idx grant) lim (s.activationCopyStamp src grant) &&
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

/-- The fixed payment or a legal resource quantity for an Add that exchanges resources. -/
def ManaKind.payments (k : ManaKind) (pool : RunePool) (d : CardDef)
    (fixed : Cost) : List RunePool.Payment :=
  match k with
  | .powerToEnergy =>
    if fixed.total = 0 then
      pool.payBags.filterMap (fun pw => if pw.isEmpty then none else some ⟨0, pw⟩)
    else []
  | .energyToPower =>
    if fixed.total = 0 then
      (List.range (pool.energyFor (d.hasType .unit))).map (fun i => ⟨i + 1, []⟩)
    else []
  | _ => fixed.payments d.domains

/-- The Pool after paying the Add's eligible costs and receiving its resources (CR 430.2). -/
def GameState.payMana (s : GameState) (p : PlayerId) (d : CardDef) (k : ManaKind)
    (fixed : Cost) (pay : RunePool.Payment) : Option RunePool :=
  if (k.payments (s.poolOf p) d fixed).contains pay then
    (s.spendFor p (d.hasType .gear) pay (d.hasType .unit)).map (fun remaining => k.add remaining pay)
  else none

/-- The costs and resources associated with a card's Add ability. -/
def GameState.manaOffer (s : GameState) (src : ObjId) (idx : Nat) :
    Option (CardDef × ManaCostPlan × ManaKind) := do
  let d ← s.cardDef? src
  let (_, .activated costs _ body _) ← (s.activationList src d)[idx]? | none
  let plan ← manaPlan costs
  let kind ← manaKind body
  return (d, plan, kind)

/-- Valid selections for the part of the Add cost paid with a card in Trash. -/
def GameState.manaBanishOptions (s : GameState) (p : PlayerId) (src : ObjId)
    (plan : ManaCostPlan) : List (Option ObjId) :=
  match plan.banish with
  | none => [none]
  | some filters =>
    ((s.zone (.player p .trash)).filter (fun id =>
      FilterList.holds s src {} id filters == some true)).map some

/-- The Banish choice is separate from the resource payment and has no spell target. -/
def GameState.manaBanishPicks (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) :
    List (Option ObjId) :=
  (s.manaOffer src idx).elim [] (fun (_, plan, _) => s.manaBanishOptions p src plan)

/-- Validate and pay the declared Banish cost, if the ability has one. -/
def payManaBanish (s : GameState) (p : PlayerId) (src : ObjId) (plan : ManaCostPlan)
    (chosen : Option ObjId) : Option (GameState × List Event) :=
  if (s.manaBanishOptions p src plan).contains chosen then
    some (chosen.elim (s, []) (banishObj p s))
  else none

/-- Paying the Banish cost preserves the structural invariants. -/
theorem payManaBanish_safe {s : GameState} {p : PlayerId} {src : ObjId} {plan : ManaCostPlan}
    {chosen : Option ObjId} {r : GameState × List Event}
    (h : payManaBanish s p src plan chosen = some r) : Safe s r.1 := by
  unfold payManaBanish at h
  split at h
  · cases h
    cases chosen
    · exact Safe.refl s
    · exact banishObj_safe _ _ _
  · contradiction

/-- Use an Add ability: pay (exhaust, kill, and what the Add takes), and the Pool gets what is added
(CR 430.2). -/
def applyMana (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (pay : RunePool.Payment)
    (chosen : Option ObjId := none) :
    Option (GameState × List Event) :=
  match s.cardDef? src with
  | some d =>
    match (s.activationList src d)[idx]? with
    | some (grant, .activated costs _ body _) =>
      match manaPlan costs, manaKind body with
      | some plan, some k =>
        match s.payMana p d k plan.cost pay, payManaBanish s p src plan chosen with
        | some pool', some (banished, banishEvents) =>
          let use := useOf (activationUseIndex idx grant) plan.exhaust (s.activationCopyStamp src grant)
          let s1 := banished.modObj src use
          let s2 := if plan.kill then killNow s1 src else s1
          let s2' := (s2.setPool p pool').trimGear p
          let s3 := match k with
            | .gear _ => s2'.addTurnFx p .gearMana
            | .permanent => s2'.addTurnFx p .permanentMana
            | _ => s2'
          let noted := s3.noteGearAbility p d costs
          some (noted.setPool p (pool'.addEnergy (s.manaBonus p src)),
            banishEvents ++ [Event.activated p src idx (baseActivationEnergy costs)])
        | _, _ => none
      | _, _ => none
    | _ => none
  | none => none

/-- The shape of an Add being used: a safe change, and the Pool. -/
theorem applyMana_cases {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {chosen : Option ObjId} {es : List Event}
    (h : applyMana s p src idx pay chosen = some (s', es)) :
    ∃ s1 pool, Safe s s1 ∧ s' = s1.setPool p pool := by
  unfold applyMana at h
  cases hd : s.cardDef? src with
  | none => simp [hd] at h
  | some d =>
    cases ha : (s.activationList src d)[idx]? with
    | none => simp [hd, ha] at h
    | some entry =>
      obtain ⟨grant, ab⟩ := entry
      cases ab with
      | activated costs sp body lim =>
        simp only [hd, ha] at h
        cases hp : manaPlan costs with
        | none => simp [hp] at h
        | some plan =>
          cases hk : manaKind body with
          | none => simp [hp, hk] at h
          | some k =>
            cases hap : s.payMana p d k plan.cost pay with
            | none => simp [hp, hk, hap] at h
            | some pool' =>
              cases hb : payManaBanish s p src plan chosen with
              | none => simp [hp, hk, hap, hb] at h
              | some paidCost =>
                obtain ⟨banished, banishEvents⟩ := paidCost
                simp only [hp, hk, hap, hb, Option.some.injEq, Prod.mk.injEq] at h
                let use := useOf (activationUseIndex idx grant) plan.exhaust (s.activationCopyStamp src grant)
                let used := banished.modObj src use
                have h1 : Safe s used := (payManaBanish_safe hb).trans
                  (Safe.modObj banished src (fun _ => rfl) (fun _ => rfl))
                refine ⟨_, _, Safe.trans ?_ (GameState.noteGearAbility_safe _ p d costs), h.1.symm⟩
                have h2 : Safe s (if plan.kill then killNow used src else used) := by
                  cases plan.kill
                  · exact h1
                  · exact h1.trans (killNow_safe _ src)
                have h3 := h2.trans ((setPool_safe _ p pool').trans (trimGear_safe _ p))
                cases k with
                | gear n => exact h3.trans (addTurnFx_safe _ _ _)
                | permanent => exact h3.trans (addTurnFx_safe _ _ _)
                | energy n | unitEnergy n => exact h3
                | power d n => exact h3
                | any n => exact h3
                | powerToEnergy => exact h3
                | energyToPower => exact h3
      | passive _ _ => simp [hd, ha] at h
      | replacement _ _ _ => simp [hd, ha] at h
      | triggered _ _ _ => simp [hd, ha] at h

/-- Using an Add keeps the game well formed. -/
theorem applyMana_wf {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {chosen : Option ObjId} {es : List Event} (hwf : s.WF)
    (h : applyMana s p src idx pay chosen = some (s', es)) : s'.WF := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  exact (hs.wf hwf).congr rfl rfl rfl rfl

/-- Using an Add keeps the physical cards. -/
theorem applyMana_physIds {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {chosen : Option ObjId} {es : List Event} (hwf : s.WF)
    (h : applyMana s p src idx pay chosen = some (s', es)) : s'.physIds.Perm s.physIds := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  have h2 : (s1.setPool p pool).physIds = s1.physIds := rfl
  rw [h2]
  exact hs.phys hwf

/-- Using an Add keeps `OwnerOk`. -/
theorem applyMana_ownerOk {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {chosen : Option ObjId} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : applyMana s p src idx pay chosen = some (s', es)) : s'.OwnerOk := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  exact (hs.own hwf hown).congr rfl rfl

/-- Using an Add changes nothing of the stack, the turn order, the phase, the result or the
rules. -/
theorem applyMana_meta {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {chosen : Option ObjId} {es : List Event}
    (h : applyMana s p src idx pay chosen = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  exact ⟨hs.same.config, hs.same.turnOrder, hs.same.phase, hs.same.result, hs.same.pending⟩

/-- A resource ability cannot be used during setup. -/
theorem manaReady_not_setup {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    (h : manaReady s p src idx = true) : s.phase ≠ .setup := by
  have ready := (Bool.and_eq_true_iff.mp h).1
  simpa using ready

/-- A ready Add is an ability of the card of the object. -/
theorem manaReady_ability {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    (h : manaReady s p src idx = true) :
    ∃ d grant ab, s.cardDef? src = some d ∧ (s.activationList src d)[idx]? = some (grant, ab) := by
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
      cases ha : (s.activationList src d)[idx]? with
      | none => simp [ha] at h
      | some entry =>
        obtain ⟨grant, ab⟩ := entry
        exact ⟨d, grant, ab, rfl, ha⟩

/-- The Add has a legal payment, covered by the player's eligible resources. -/
def manaPayOk (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat)
    (pay : RunePool.Payment) : Bool :=
  (s.manaOffer src idx).any (fun (d, plan, kind) => (s.payMana p d kind plan.cost pay).isSome)

/-- The player can use the Add with the payment. -/
def manaOk (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (pay : RunePool.Payment)
    (chosen : Option ObjId := none) : Bool :=
  manaReady s p src idx && manaPayOk s p src idx pay && (s.manaBanishPicks p src idx).contains chosen

/-- A usable resource ability is used after setup. -/
theorem manaOk_not_setup {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {chosen : Option ObjId} (h : manaOk s p src idx pay chosen = true) : s.phase ≠ .setup := by
  exact manaReady_not_setup (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

/-- A usable Add can be used. -/
theorem applyMana_isSome {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {chosen : Option ObjId} (h : manaOk s p src idx pay chosen = true) :
    ∃ r, applyMana s p src idx pay chosen = some r := by
  unfold manaOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hr, hp⟩, hb⟩ := h
  obtain ⟨d, _grant, ab, hd, ha⟩ := manaReady_ability hr
  unfold manaPayOk GameState.manaOffer at hp
  cases ab with
  | activated costs speed body lim =>
    cases hplan : manaPlan costs with
    | none => simp [hd, ha, hplan, bind] at hp
    | some plan =>
      cases hk : manaKind body with
      | none => simp [hd, ha, hplan, hk, bind] at hp
      | some kind =>
        have hs : (s.payMana p d kind plan.cost pay).isSome = true := by
          simpa [hd, ha, hplan, hk, bind] using hp
        obtain ⟨pool, hpool⟩ := Option.isSome_iff_exists.mp hs
        have hchosen : (s.manaBanishOptions p src plan).contains chosen = true := by
          simpa [GameState.manaBanishPicks, GameState.manaOffer, hd, ha, hplan, hk, bind] using hb
        have canApply : (applyMana s p src idx pay chosen).isSome = true := by
          simp [applyMana, hd, ha, hplan, hk, hpool, payManaBanish, List.contains_iff_mem.mp hchosen]
        exact Option.isSome_iff_exists.mp canApply
  | passive _ _ => simp [hd, ha, bind] at hp
  | replacement _ _ _ => simp [hd, ha, bind] at hp
  | triggered _ _ _ => simp [hd, ha, bind] at hp

/-- Payments to try when playing an Add. -/
def manaPays (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) : List RunePool.Payment :=
  (s.manaOffer src idx).elim [] (fun (d, plan, kind) =>
    kind.payments (s.poolOf p) d plan.cost)

/-- Every Add the player can use now, with the objects they use abilities of. -/
def legalManas (s : GameState) (p : PlayerId) : List Action :=
  (s.zone (.player p .base) ++ s.zone (.player p .legendZone) ++ s.zone .battlefieldZone).flatMap
    (fun src =>
      match s.cardDef? src with
      | some d =>
        ((List.range (s.activationList src d).length).filter (fun idx => manaReady s p src idx)).flatMap
          (fun idx => ((manaPays s p src idx).filter (fun pay => manaPayOk s p src idx pay)).flatMap
            (fun pay => (s.manaBanishPicks p src idx).map
              (fun chosen => ⟨.player p, .manaAbility src idx pay chosen⟩)))
      | none => [])

/-- Read Add timing as it applies while an effect's play pays its costs (CR 357.1.a). -/
def effectAddView (s : GameState) (p : PlayerId) : GameState :=
  { s with pending := .eitherDo p ⟨0⟩ {} (.payThen Cost.zero .nop) .nop .nil :: s.pending }

/-- Apply one activation from a resource payment, checking its timing and cost again. -/
def EffectAdd.apply (s : GameState) (p : PlayerId) : EffectAdd → Option (GameState × List Event)
  | .rune id recycle =>
    let ab := if recycle then RuneAbility.recycle else .exhaust
    if (s.runesOf p).contains id && runeUsable s p id ab then applyRune s p id ab else none
  | .ability src idx energy power chosen =>
    let pay := ⟨energy, power⟩
    if manaOk (effectAddView s p) p src idx pay chosen then applyMana s p src idx pay chosen else none

/-- An activation of either kind preserves the structural and ownership invariants. -/
theorem EffectAdd.apply_safe {s : GameState} {p : PlayerId} {add : EffectAdd}
    {r : GameState × List Event} (h : add.apply s p = some r) : Safe s r.1 := by
  cases add with
  | rune id recycle =>
    cases recycle <;> simp only [EffectAdd.apply, Bool.false_eq_true, ↓reduceIte] at h <;>
      split at h <;> first | exact applyRune_safe h | contradiction
  | ability src idx energy power chosen =>
    simp only [EffectAdd.apply] at h
    split at h
    · obtain ⟨t, pool, ht, hr⟩ := applyMana_cases (s' := r.1) (es := r.2)
        (show applyMana s p src idx ⟨energy, power⟩ chosen = some (r.1, r.2) from h)
      rw [hr]
      exact ht.trans (setPool_safe t p pool)
    · contradiction

/-- Simulate the choices in order. The caller only publishes the result of a complete payment. -/
def applyEffectAdds (s : GameState) (p : PlayerId) : List EffectAdd → Option (GameState × List Event)
  | [] => some (s, [])
  | a :: rest => do
    let (t, events) ← a.apply s p
    let (done, later) ← applyEffectAdds t p rest
    some (done, events ++ later)

/-- Every successfully applied sequence preserves the game invariants. -/
theorem applyEffectAdds_safe {s : GameState} {p : PlayerId} {adds : List EffectAdd}
    {r : GameState × List Event} (h : applyEffectAdds s p adds = some r) : Safe s r.1 := by
  induction adds generalizing s r with
  | nil =>
    simp only [applyEffectAdds, Option.some.injEq] at h
    subst r
    exact Safe.refl s
  | cons a rest ih =>
    simp only [applyEffectAdds, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨t, events⟩, ha, ⟨done, later⟩, hd, hr⟩ := h
    rw [← hr]
    exact (EffectAdd.apply_safe (r := (t, events)) ha).trans (ih (r := (done, later)) hd)

/-- The ability slots on objects that can provide resources during the payment. -/
def effectAddSlots (s : GameState) (p : PlayerId) : List (ObjId × Nat) :=
  let view := effectAddView s p
  (s.zone (.player p .base) ++ s.zone (.player p .legendZone) ++ s.zone .battlefieldZone).flatMap
    (fun src => ((s.cardDef? src).toList.flatMap (fun d => List.range (s.activationList src d).length)).filterMap
      (fun idx => if manaReady view p src idx then some (src, idx) else none))

/-- Rune activations for a payment. For reachability only, Runes of the same domain and readiness
can be represented by one source. -/
def effectAddRuneUses (s : GameState) (p : PlayerId) (distinct : Bool) : List EffectAdd :=
  let runes := s.runesOf p
  let runes := if distinct then runes else runes.eraseDupsBy (fun a b =>
    ((s.obj? a).map (fun o => (o.runeDomain, o.exhausted))) ==
      ((s.obj? b).map (fun o => (o.runeDomain, o.exhausted))))
  runes.flatMap (fun id =>
    (if runeUsable s p id .exhaust then [.rune id false] else []) ++ [.rune id true])

/-- The possible next activations. Before playing the card, early Rune use only changes what
can be paid if some remaining Add has its own resource cost (including exchanges). -/
def effectAddUses (s : GameState) (p : PlayerId) (includeBasic : Bool := false) : List EffectAdd :=
  let view := effectAddView s p
  let slots := effectAddSlots s p
  let paidAdd := slots.any (fun (src, idx) => (s.manaOffer src idx).any (fun (_, plan, kind) =>
    plan.cost.total != 0 || match kind with | .powerToEnergy | .energyToPower => true | _ => false))
  slots.flatMap (fun (src, idx) =>
    (manaPays view p src idx).flatMap (fun pay =>
      if manaPayOk view p src idx pay then
        (view.manaBanishPicks p src idx).map (fun chosen => .ability src idx pay.energy pay.power chosen)
      else [])) ++
    (if includeBasic || paidAdd then effectAddRuneUses s p includeBasic else [])

/-- Check whether the remaining Add activations can fund the play. The search may use automatic
Rune coverage to witness that the price is reachable. -/
def effectAddReachable (p : PlayerId) (paid : GameState → Bool) : Nat → GameState → Bool
  | 0, s => paid s
  | n + 1, s =>
    paid s || (effectAddUses s p).any (fun a =>
      (a.apply s p).any (fun (t, _) => effectAddReachable p paid n t))

/-- The individual activations after which the chosen finalization can still be paid. -/
def effectAddChoices (s : GameState) (p : PlayerId) (paid : GameState → Bool) : List EffectAdd :=
  let fuel := (effectAddSlots s p).length + 2 * (s.runesOf p).length
  (effectAddUses s p true).filter (fun a =>
    (a.apply s p).any (fun (t, _) => effectAddReachable p paid fuel t))

/-- Allow effect plays to discover and use the same Add abilities as player actions. -/
def effectAddPolicy : EffectAddPolicy :=
  { choices := effectAddChoices, applyAll := applyEffectAdds, safe := applyEffectAdds_safe }

/-- Check the selected targets, mode and non-resource costs before its resource payment. -/
def declaredTriggerOk (s : GameState) (t : PendTrigger) (targets : List ObjId) : TriggerPayment → Bool
  | .skip => false
  | .pay ids mode player banishers =>
    (trigModes s t).contains mode &&
    targetsOk s t.controller t.source s.mightTable (trigChoices s t mode) targets &&
    (trigPlayerOptions s t).contains player &&
    (triggerCostOptions s t false).contains (ids, banishers)

/-- The resources due for a trigger's base cost and any targets with Deflect (CR 383.3.b, 809). -/
def triggerPrice (s : GameState) (t : PendTrigger) (targets : List ObjId) : Cost :=
  let cost := (trigCost s t).resources
  { cost with power := cost.power ++ List.replicate (s.deflectCost t.controller targets) .any }

/-- Add choices that leave the locked trigger's targets and costs payable (CR 357.1.a, 357.3).
The Rune planner is a witness of reachability. The player selects the actual activations. -/
def triggerAdds (s : GameState) (t : PendTrigger) (targets : List ObjId)
    (payment : TriggerPayment) : List EffectAdd :=
  if (triggerPrice s t targets).total == 0 then [] else
    effectAddChoices s t.controller (fun next =>
      declaredTriggerOk next t targets payment &&
      (payByRunes next t.controller t.source (triggerPrice next t targets)).isSome)

/-- Targets, payment and mode reach a valid finalization after the selected Adds. -/
def triggerFundingAdds (s : GameState) (group : List PendTrigger)
    (plan : TriggerFunding) : List EffectAdd := Id.run do
  let some t := group[plan.index]? | return []
  let some (funded, _) := applyEffectAdds s t.controller plan.adds | return []
  return triggerAdds funded t plan.targets plan.payment

/-- Apply a complete resource payment and the remaining costs before the trigger gains priority. -/
def commitTriggerFunding (s : GameState) (group : List PendTrigger) (plan : TriggerFunding) :
    Option (GameState × List Event) := do
  let t ← group[plan.index]?
  let .pay ids mode player banishers := plan.payment | none
  let (funded, adds) ← applyEffectAdds s t.controller plan.adds
  if !declaredTriggerOk funded t plan.targets plan.payment then none else
    let pool ← funded.payNow t.controller t.source (triggerPrice funded t plan.targets)
    let paid := funded.setPoolFor t.controller t.source pool
    let (ready, costs) ← payTriggerCost paid t ids banishers true
    some (putTrigger ready t plan.targets mode player, adds ++ costs)

/-- Committing a trigger's costs preserves the game invariants. -/
theorem commitTriggerFunding_safe {s : GameState} {group : List PendTrigger}
    {plan : TriggerFunding} {r : GameState × List Event}
    (h : commitTriggerFunding s group plan = some r) : Safe s r.1 := by
  unfold commitTriggerFunding at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, _, ht⟩ := h
  cases hp : plan.payment with
  | skip => simp [hp] at ht
  | pay ids mode player banishers =>
    simp only [hp, Option.bind_eq_some_iff] at ht
    obtain ⟨⟨funded, adds⟩, hf, hr⟩ := ht
    split at hr
    · simp at hr
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at hr
      obtain ⟨pool, _, ⟨ready, costs⟩, hc, rfl⟩ := hr
      exact (applyEffectAdds_safe hf).trans ((setPoolFor_safe funded t.controller t.source pool).trans
        ((payTriggerCost_safe hc).trans (putTrigger_safe ready t plan.targets mode player)))

/-- Handle both direct finalization and a finalization whose Add choices have been prepared. -/
def finishTrigger (s : GameState) (group : List PendTrigger) (funding : Option TriggerFunding)
    (index : Nat) (targets : List ObjId) (payment : TriggerPayment) : GameState × List Event :=
  match funding with
  | none => finalizePick s group index targets payment
  | some plan => (commitTriggerFunding s group plan).getD (s, [])

/-- Either kind of trigger finalization preserves the game invariants. -/
theorem finishTrigger_safe (s : GameState) (group : List PendTrigger)
    (funding : Option TriggerFunding) (index : Nat) (targets : List ObjId) (payment : TriggerPayment) :
    Safe s (finishTrigger s group funding index targets payment).1 := by
  cases funding with
  | none => exact finalizePick_safe s group index targets payment
  | some plan =>
    cases h : commitTriggerFunding s group plan with
    | none => simpa [finishTrigger, h] using Safe.refl s
    | some result => simpa [finishTrigger, h] using commitTriggerFunding_safe h

/-- Whether to expose the payment window for a particular target, mode and cost selection. -/
def triggerPreparation (s : GameState) (t : PendTrigger) (targets : List ObjId)
    (payment : TriggerPayment) : Bool :=
  (acceptedTriggers s t false).contains (targets, payment) &&
    !(triggerAdds s t targets payment).isEmpty

/-- Check either the direct finalization or the locked finalization and its projected payment. -/
def triggerFinishOk (s : GameState) (group : List PendTrigger) (funding : Option TriggerFunding)
    (idx : Nat) (targets : List ObjId) (payment : TriggerPayment) : Bool :=
  match funding with
  | none => group[idx]?.any (fun t => trigLegal s t targets payment)
  | some plan => plan.index == idx && plan.targets == targets && plan.payment == payment &&
      (commitTriggerFunding s group plan).isSome

/-- A legal payment of an Add is one of the payments offered. -/
theorem mem_manaPays {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} (h : manaPayOk s p src idx pay = true) :
    pay ∈ manaPays s p src idx := by
  unfold manaPayOk at h
  unfold manaPays
  cases hinfo : s.manaOffer src idx with
  | none => simp [hinfo] at h
  | some info =>
    obtain ⟨d, plan, kind⟩ := info
    simp only [hinfo, Option.any_some, Option.elim_some] at h ⊢
    unfold GameState.payMana at h
    split at h
    · rename_i valid
      exact List.contains_iff_mem.mp valid
    · simp at h

/-- The Adds listed are exactly the ones that can be used. -/
theorem mem_legalManas (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalManas s p ↔ ∃ src idx pay chosen, a = ⟨.player p, .manaAbility src idx pay chosen⟩ ∧
      manaOk s p src idx pay chosen = true := by
  constructor
  · intro ha
    unfold legalManas at ha
    simp only [List.mem_flatMap] at ha
    obtain ⟨src, -, ha⟩ := ha
    cases hd : s.cardDef? src with
    | none => simp [hd] at ha
    | some d =>
      simp only [hd, List.mem_flatMap, List.mem_map, List.mem_filter] at ha
      obtain ⟨idx, ⟨-, hr⟩, pay, ⟨-, hp⟩, chosen, hcost, rfl⟩ := ha
      exact ⟨src, idx, pay, chosen, rfl, by simp [manaOk, hr, hp, hcost]⟩
  · rintro ⟨src, idx, pay, chosen, rfl, hok⟩
    unfold manaOk at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨hr, hp⟩, hc⟩ := hok
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
    · obtain ⟨d, _grant, ab, hd, ha⟩ := manaReady_ability hr
      simp only [hd, List.mem_flatMap, List.mem_map, List.mem_filter]
      exact ⟨idx, ⟨List.mem_range.mpr (List.getElem?_eq_some_iff.mp ha).1, hr⟩, pay,
        ⟨mem_manaPays hp, hp⟩, chosen, List.contains_iff_mem.mp hc, rfl⟩

end Riftbound

end
