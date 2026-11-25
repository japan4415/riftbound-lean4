module

public import Riftbound.Rules.Effects

/-!
# Activated abilities and Reactions

A player with priority can use an activated ability of an object they control (CR 361, 363): the
costs are paid, and the ability goes on the Chain as an object of its own (design.md §5.2). The
Chain holds Spells and abilities in the order they were put there (CR 337, 340). While it holds
an item, the players can answer it with a Reaction: a Spell with Reaction (CR 813), or an activated
ability with the speed Reaction, and the Basic Rune abilities (CR 164.2, 430).

The costs this model can pay are the exhaustion of the object and Energy with Power. An ability
with any other cost cannot be used yet.
-/

@[expose] public section

namespace Riftbound

/-- The number of cards to discard as a cost and the filters they must satisfy. -/
def AbilityCost.discardSpec : AbilityCost → Option (Nat × FilterList)
  | .discard n => some (n, .nil)
  | .discardMatching n fs => some (n, fs)
  | _ => none

/-- The discard cost of the ability, if any. -/
def discardCost (costs : List AbilityCost) : Option (Nat × FilterList) :=
  costs.findSome? AbilityCost.discardSpec

/-- The cards in the player's own hand that can pay the discard cost. -/
def GameState.discardCandidates (s : GameState) (p : PlayerId) (src : ObjId)
    (fs : FilterList) : List ObjId :=
  let env : Env := { passMight := s.mightTable }
  ((s.zone (.player p .hand)).filter (fun id => fs.holds s src env id == some true)).eraseDups

/-- Which ordered subset of the hand pays the discard cost exactly (CR 423.3). -/
def GameState.discardCostOk (s : GameState) (p : PlayerId) (src : ObjId)
    (costs : List AbilityCost) (discards : List ObjId) : Bool :=
  match discardCost costs with
  | none => discards.isEmpty
  | some (n, fs) => discards.length == n &&
      decide (discards.Sublist (s.discardCandidates p src fs))

/-- Each legal payment of the discard cost. Cards picked together follow the order of the hand. -/
def GameState.discardPayments (s : GameState) (p : PlayerId) (src : ObjId)
    (costs : List AbilityCost) : List (List ObjId) :=
  match discardCost costs with
  | none => [[]]
  | some (n, fs) => (subseqsUpTo n (s.discardCandidates p src fs)).filter (·.length == n)

/-- Enumeration and legality agree on which cards can pay the discard cost. -/
theorem GameState.mem_discardPayments (s : GameState) (p : PlayerId) (src : ObjId)
    (costs : List AbilityCost) (discards : List ObjId) :
    discards ∈ s.discardPayments p src costs ↔ s.discardCostOk p src costs discards = true := by
  cases h : discardCost costs with
  | none => simp [discardPayments, discardCostOk, h, List.isEmpty_iff]
  | some spec =>
    obtain ⟨n, fs⟩ := spec
    simp [discardPayments, discardCostOk, h, mem_subseqsUpTo, and_comm]
    intro he _
    omega

/-- The costs of an ability the model can pay: whether to exhaust the object, and the Energy and
Power to pay. `none` for unsupported costs or multiple clauses of the same payment kind. -/
def costPlan : List AbilityCost → Option (Bool × Option Cost)
  | [] => some (false, none)
  | .exhaustSelf :: cs =>
    match costPlan cs with
    | some (false, c) => some (true, c)
    | _ => none
  | .pay c :: cs =>
    match costPlan cs with
    | some (e, none) => some (e, some c)
    | _ => none
  | .fromHand :: cs => costPlan cs
  | .fromHidden :: cs => costPlan cs
  | .fromChampionZone :: cs => costPlan cs
  | .fromTrash :: cs => costPlan cs
  | .killFriendly _ _ :: cs => costPlan cs
  | .discard _ :: cs | .discardMatching _ _ :: cs =>
    if (discardCost cs).isNone then costPlan cs else none
  | .disempowerSelf :: cs => costPlan cs
  | .energyDiscount _ _ :: cs => costPlan cs
  | _ :: _ => none

/-- The Energy in the declared cost of an activation (CR 204.1.b, 206.1).
The engine also uses this path to implement other actions such as Hide or playing the
Chosen Champion. Those actions do not play activated abilities. -/
def baseActivationEnergy (costs : List AbilityCost) : Option Nat :=
  if costs.contains .fromHand || costs.contains .fromHidden || costs.contains .fromChampionZone then
    none
  else some ((((costPlan costs).bind Prod.snd).map Cost.energy).getD 0)

/-- Gear activations exclude the internal abilities used to implement hiding and card plays. -/
def isGearActivation (d : CardDef) (costs : List AbilityCost) : Bool :=
  d.hasType .gear && !costs.contains .fromHand && !costs.contains .fromHidden &&
    !costs.contains .fromChampionZone && !costs.contains .fromTrash

/-- Each player's first Gear activation counts even if it is free or will be countered. -/
def GameState.noteGearAbility (s : GameState) (p : PlayerId) (d : CardDef)
    (costs : List AbilityCost) : GameState :=
  if isGearActivation d costs && !(s.fxOf p).contains .usedGearAbility then
    s.addTurnFx p .usedGearAbility
  else s

theorem GameState.noteGearAbility_safe (s : GameState) (p : PlayerId) (d : CardDef)
    (costs : List AbilityCost) : Safe s (s.noteGearAbility p d costs) := by
  unfold noteGearAbility
  split
  · exact addTurnFx_safe _ _ _
  · exact Safe.refl _

theorem GameState.noteGearAbility_zone (s : GameState) (p : PlayerId) (d : CardDef)
    (costs : List AbilityCost) (z : Zone) : (s.noteGearAbility p d costs).zone z = s.zone z := by
  unfold noteGearAbility
  split <;> rfl

/-- Energy reductions for the player's first Gear activation at Battlefields they control. -/
def GameState.firstGearAbilityCut (s : GameState) (p : PlayerId) (d : CardDef)
    (costs : List AbilityCost) : Nat :=
  if isGearActivation d costs && !(s.fxOf p).contains .usedGearAbility then
    ((s.zone .battlefieldZone).flatMap (fun bf =>
      if (s.obj? bf).any (·.control == some p) then
        (s.activeMods bf).filterMap (fun
          | .firstGearAbilityLess n => some n
          | _ => none)
      else [])).sum
  else 0

/-- Flexible reductions to the Empower cost of a Unit at a Battlefield its player controls
(CR 190.6.d, 356.4.c, 827). -/
def GameState.empowerHereCut (s : GameState) (p : PlayerId) (src : ObjId) (d : CardDef)
    (idx : Nat) : Nat :=
  if d.hasType .unit && ((s.activationList src d)[idx]?).any (·.2.isEmpower) then
    match (s.obj? src).bind (·.loc) with
    | some bf =>
      if (s.obj? bf).any (·.control == some p) then
        ((s.activeMods bf).filterMap (fun
          | .empowerHereLess n => some n
          | _ => none)).sum
      else 0
    | none => 0
  else 0

/-- The costs after applying the discounts for this activated ability (CR 356, 357). -/
def GameState.activationPlan (s : GameState) (p : PlayerId) (src : ObjId)
    (d : CardDef) (idx : Nat) (costs : List AbilityCost) (targets : List ObjId) :
    Option (Bool × List Cost) :=
  (costPlan costs).map (fun (ex, base) =>
    let discount := costs.foldl (fun total c =>
      match c with
      | .energyDiscount cond amount =>
        if cond.eval s p src {} == some true then
          total + (amount.evalS s p src {}).getD 0
        else total
      | _ => total) 0
    let tax := if costs.contains .fromHidden then
      let cut := s.playPowerCut p src targets
      let deflect := if cut != 0 then s.deflectCost p targets (some src) else 0
      s.showdownReactionTax + deflect - cut
      else 0
    let gearCut := s.firstGearAbilityCut p d costs
    let options := (base.getD Cost.zero).cutOptions (s.empowerHereCut p src d idx)
    (ex, options.map (fun c =>
      { c.lessEnergy (discount + gearCut) with power := c.power ++ List.replicate tax .any })))

/-- Whether the costs kill a friendly unit: the last object chosen is the one. -/
def costKills (costs : List AbilityCost) : Bool :=
  costs.any (fun c => match c with | .killFriendly _ _ => true | _ => false)

/-- Pay the cost of killing a friendly unit (CR 361): the last object chosen dies. -/
def payKill (s : GameState) (p : PlayerId) (costs : List AbilityCost) (ts : List ObjId) :
    GameState × List Event :=
  match costKills costs, ts.getLast? with
  | true, some v =>
    if (s.zone (.player p .base)).contains v || (s.zone .battlefieldZone).contains v then
      killObj s v
    else (s, [])
  | _, _ => (s, [])

/-- Paying the cost of killing is a safe change. -/
theorem payKill_safe (s : GameState) (p : PlayerId) (costs : List AbilityCost) (ts : List ObjId) :
    Safe s (payKill s p costs ts).1 := by
  unfold payKill
  split
  · split
    · exact killObj_safe s _
    · exact Safe.refl s
  · exact Safe.refl s

/-- Paying the cost of killing leaves the hands and the Chain as they were. -/
theorem payKill_zones {s : GameState} (hwf : s.WF) (p : PlayerId) (costs : List AbilityCost)
    (ts : List ObjId) :
    (∀ q, (payKill s p costs ts).1.zone (.player q .hand) = s.zone (.player q .hand)) ∧
      (payKill s p costs ts).1.zone .chain = s.zone .chain := by
  unfold payKill
  split
  · rename_i v _ _
    split
    · rename_i hc
      have hz : ∃ z0, v ∈ s.zone z0 ∧ (z0 = Zone.player p .base ∨ z0 = Zone.battlefieldZone) := by
        simp only [Bool.or_eq_true, List.contains_iff_mem] at hc
        rcases hc with h | h
        · exact ⟨_, h, Or.inl rfl⟩
        · exact ⟨_, h, Or.inr rfl⟩
      obtain ⟨z0, hu, hz0⟩ := hz
      refine ⟨fun q => ?_, ?_⟩
      · refine killObj_zone_other hwf hu ?_ ?_
        · rcases hz0 with rfl | rfl <;> intro h <;> cases h
        · intro q' k hk h
          cases h
          rcases hk with h' | h' <;> cases h'
      · refine killObj_zone_other hwf hu ?_ ?_
        · rcases hz0 with rfl | rfl <;> intro h <;> cases h
        · intro q' k hk h
          cases h
    · exact ⟨fun _ => rfl, rfl⟩
  · exact ⟨fun _ => rfl, rfl⟩

/-- A direct discard from hand leaves the Chain unchanged. -/
theorem discardObj_chain {s : GameState} (hwf : s.WF) {p : PlayerId} {id : ObjId}
    (hc : id ∈ s.zone (.player p .hand)) : (discardObj s id).1.zone .chain = s.zone .chain := by
  have hsend : (sendObj .trash s id).1.zone .chain = s.zone .chain := by
    unfold sendObj
    split
    · rename_i o _
      split
      · rename_i r hm
        exact moveObj_zone_unchanged hwf hc hm (by simp) (fun _ _ => by simp [Zone.normalize, Zone.isBoard])
      · rfl
    · rfl
  unfold discardObj
  split
  · dsimp only
    split <;> exact hsend
  · exact hsend

/-- Discarding a cost preserves the Chain. -/
theorem payDiscards_chain (p : PlayerId) :
    ∀ (ds : List ObjId) (s : GameState), s.WF → (payDiscards p s ds).1.zone .chain = s.zone .chain
  | [], _, _ => rfl
  | id :: ids, s, hwf => by
    simp only [payDiscards]
    split
    · rename_i hc
      exact (payDiscards_chain p ids _ ((discardObj_safe s id).wf hwf)).trans
        (discardObj_chain hwf (List.contains_iff_mem.mp hc))
    · exact payDiscards_chain p ids s hwf

/-- Pay the selected non-mana costs, and spend any restricted Power spent on a Gear first. -/
def preCost (s : GameState) (p : PlayerId) (costs : List AbilityCost) (ts : List ObjId)
    (gear : Bool) (pool : RunePool) (discards : List ObjId := []) : GameState × List Event :=
  let k := payKill s p costs ts
  let d := payDiscards p k.1 discards
  let next := if gear then
    let spent := (s.poolOf p).any - pool.any
    { d.1 with turnFx := dropGearFx s.turn p spent d.1.turnFx }
  else d.1
  (next, k.2 ++ d.2)

/-- Paying the costs is a safe change. -/
theorem preCost_safe (s : GameState) (p : PlayerId) (costs : List AbilityCost) (ts : List ObjId)
    (gear : Bool) (pool : RunePool) (discards : List ObjId) :
    Safe s (preCost s p costs ts gear pool discards).1 := by
  have h := (payKill_safe s p costs ts).trans (payDiscards_safe p discards _)
  unfold preCost
  split
  · exact h.trans ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
      fun _ hown => hown.congr rfl rfl, rfl⟩
  · exact h

/-- Paying the costs, without discards, leaves the hands and the Chain as they were. -/
theorem preCost_zones {s : GameState} (hwf : s.WF) (p : PlayerId) (costs : List AbilityCost)
    (ts : List ObjId) (gear : Bool) (pool : RunePool) :
    (∀ q, (preCost s p costs ts gear pool).1.zone (.player q .hand) = s.zone (.player q .hand)) ∧
      (preCost s p costs ts gear pool).1.zone .chain = s.zone .chain := by
  have h := payKill_zones hwf p costs ts
  unfold preCost
  split <;> exact h

/-- Paying the costs, including discards, preserves the Chain. -/
theorem preCost_chain {s : GameState} (hwf : s.WF) (p : PlayerId) (costs : List AbilityCost)
    (ts : List ObjId) (gear : Bool) (pool : RunePool) (discards : List ObjId) :
    (preCost s p costs ts gear pool discards).1.zone .chain = s.zone .chain := by
  have h := (payDiscards_chain p discards _ ((payKill_safe s p costs ts).wf hwf)).trans
    (payKill_zones hwf p costs ts).2
  unfold preCost
  split <;> exact h

/-- Whether the costs exhaust the object. -/
def costExhausts (costs : List AbilityCost) : Bool :=
  match costPlan costs with
  | some (e, _) => e
  | none => false

/-- The object is one a player can use abilities of: they control it, and it is on their Base, on
their Legend Zone, or on the Battlefield Zone. -/
def GameState.usesAbilitiesOf (s : GameState) (p : PlayerId) (src : ObjId) : Bool :=
  (s.zone (.player p .base)).contains src || (s.zone (.player p .legendZone)).contains src ||
    (s.zone .battlefieldZone).contains src

/-- A card hidden at a Battlefield cannot be revealed by its owner `p` while a Unit of an opponent
there has the passive ability that forbids it (CR 811). -/
def GameState.hiddenBlocked (s : GameState) (p : PlayerId) (src : ObjId) : Bool :=
  match (s.obj? src).bind (·.hiddenAt) with
  | some bf =>
    (s.zone .battlefieldZone).any (fun u =>
      (s.obj? u).any (fun o => o.loc == some bf && o.controller != p) &&
        (s.activeMods u).contains .noHiddenReveal)
  | none => false

/-- The cost an ability pays when it resolves ("Recycle 3 from your trash: ...") is written as the
first part of the effect, guarded by a condition: the ability cannot be used while the condition is
false, as an ability whose cost cannot be paid cannot be used. A condition about the chosen objects
cannot be answered yet, and does not stop the use. An ability that only plays a card to a
Battlefield cannot be used while the opponents of its player play Units only to their Base (the
play by a triggered ability goes to the Base instead). A hidden card that cannot be revealed
stops its ability, too. -/
def guardOk (s : GameState) (p : PlayerId) (src : ObjId) (body : EffectDef) : Bool :=
  (match body.body with
    | .ifThen c _ .nop => c.eval s p src {} != some false
    | _ => true) && !s.hiddenBlocked p src &&
    -- the opponents of a Warden play Units only to their Base
    (match body.body with
      | .prim (.playTo _ _) => !s.oppHas p .oppsPlayToBaseOnly
      | .ifThen _ (.prim (.playTo _ _)) .nop => !s.oppHas p .oppsPlayToBaseOnly
      | _ => true)

/-- Where the object that has the ability is, for the ability at place `idx`: an ability that can be
used from the hand (Hide) or from hiding (CR 811) is used there, from the turn after the card was
hidden; the others, where the player uses abilities of objects. An ability with a guard is used
only while the guard holds. -/
def GameState.abilityZoneOk (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) : Bool :=
  match s.activationAt src idx with
  | some (_, .activated costs _ body _) =>
    (guardOk s p src body && (!costs.contains .disempowerSelf ||
      (s.obj? src).any (fun o => 0 < o.empowerCount))) &&
      (if costs.contains .fromHand then
        -- an ability that plays the card to a Battlefield is a play: "can't play" stops it
        (s.zone (.player p .hand)).contains src &&
          !((match body.body with
              | .prim (.playTo _ _) => true
              | .ifThen _ (.prim (.playTo _ _)) .nop => true
              | _ => false) && s.cantPlay p)
      else if costs.contains .fromHidden then
        (s.zone (.player p .hidden)).contains src &&
          (((s.obj? src).bind (·.hiddenTurn)).any (fun t => decide (t < s.turn)) &&
            !(s.cardDef? src).any (s.blocksNamedPlay p))
      else if costs.contains .fromTrash then
        (s.zone (.player p .trash)).contains src && !s.cantPlay p
      else if costs.contains .fromChampionZone then
        (s.zone (.player p .championZone)).contains src && !s.cantPlay p
      else s.usesAbilitiesOf p src)
  | _ => s.usesAbilitiesOf p src

/-- Where abilities are used from: the places of the board, the hand, the hidden cards and the
Champion Zone. -/
def GameState.abilityZones (s : GameState) (p : PlayerId) : List ObjId :=
  s.zone (.player p .base) ++ s.zone (.player p .legendZone) ++ s.zone .battlefieldZone ++
    s.zone (.player p .hand) ++ s.zone (.player p .hidden) ++ s.zone (.player p .championZone) ++
    s.zone (.player p .trash)

/-- An object the player uses abilities of is in one of these places. -/
theorem GameState.usesAbilitiesOf_mem {s : GameState} {p : PlayerId} {src : ObjId}
    (h : s.usesAbilitiesOf p src = true) : src ∈ s.abilityZones p := by
  simp only [GameState.usesAbilitiesOf, Bool.or_eq_true, List.contains_iff_mem] at h
  unfold GameState.abilityZones
  simp only [List.mem_append]
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))

/-- A usable ability is of an object in one of these places. -/
theorem GameState.abilityZoneOk_mem {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    (h : s.abilityZoneOk p src idx = true) : src ∈ s.abilityZones p := by
  unfold GameState.abilityZoneOk at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    split at h
    · unfold GameState.abilityZones
      simp only [List.mem_append]
      simp only [Bool.and_eq_true] at h
      exact Or.inl (Or.inl (Or.inl (Or.inr (by simpa [List.contains_iff_mem] using h.1))))
    · split at h
      · simp only [Bool.and_eq_true, List.contains_iff_mem] at h
        unfold GameState.abilityZones
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr h.1))
      · split at h
        · simp only [Bool.and_eq_true] at h
          unfold GameState.abilityZones
          simp only [List.mem_append]
          exact Or.inr (by simpa [List.contains_iff_mem] using h.1)
        · split at h
          · simp only [Bool.and_eq_true] at h
            unfold GameState.abilityZones
            simp only [List.mem_append]
            exact Or.inl (Or.inr (by simpa [List.contains_iff_mem] using h.1))
          · exact GameState.usesAbilitiesOf_mem h
  · exact GameState.usesAbilitiesOf_mem h

/-- The change an object goes through when an ability is used: it is exhausted if the cost says
so, and the use is noted (CR 371, 386). -/
def useOf (idx : Nat) (ex : Bool) (o : Object) : Object :=
  { o with exhausted := o.exhausted || ex, used := o.used ++ [idx] }

/-- The object an ability becomes on the Chain: it belongs to the player who used it (CR 337). -/
def abilityItem (card : CardId) (idx : Nat) (src : ObjId) (p : PlayerId) (ts : List ObjId)
    (eventAmount : Option Nat := none) : Object :=
  { kind := .chainAbility card idx src, owner := p, controller := p, timestamp := ⟨0⟩,
    targets := ts, eventAmount := eventAmount }

/-- What an Add ability adds. -/
inductive ManaKind where
  /-- Energy. -/
  | energy (n : Nat)
  /-- Energy that pays only for Units and activated abilities of Units. -/
  | unitEnergy (n : Nat)
  /-- Power of a domain. -/
  | power (d : Domain) (n : Nat)
  /-- Power of any domain. -/
  | any (n : Nat)
  /-- Power of any domain that only pays for Gear this turn (Fire Below the Mountain). -/
  | gear (n : Nat)
  /-- Pay any amount of Power, to add that much Energy (Hextech Anomaly): the payment is chosen. -/
  | powerToEnergy
  /-- Pay any amount of Energy, to add that much Power of any domain (Ancient Henge). -/
  | energyToPower
deriving DecidableEq, Repr

/-- The Pool after adding. -/
def ManaKind.add : ManaKind → RunePool → RunePool.Payment → RunePool
  | .energy n, p, _ => p.addEnergy n
  | .unitEnergy n, p, _ => p.addUnitEnergy n
  | .power d n, p, _ => p.addPower d n
  | .any n, p, _ => p.addAny n
  | .gear n, p, _ => p.addAny n
  | .powerToEnergy, p, payment => p.addEnergy payment.power.length
  | .energyToPower, p, payment => p.addAny payment.energy

/-- The resource effect an Add ability resolves immediately (CR 430.2). -/
def manaKind (body : EffectDef) : Option ManaKind :=
  match body.choices, body.body with
  | [], .prim (.addEnergy .you (.const n) none) => some (.energy n)
  | [], .prim (.addUnitEnergy .you (.const n)) => some (.unitEnergy n)
  | [], .prim (.addPower .you (.const n) (some d) none) => some (.power d n)
  | [], .prim (.addPower .you (.const n) none none) => some (.any n)
  -- the Power of Fire Below the Mountain: it pays only for Gear
  | [], .seq (.cons (.prim (.addPower .you (.const n) none none))
      (.cons (.prim (.turnEffect .gearMana)) .nil)) => some (.gear n)
  -- an Add that works only while a condition holds: it is used only then (`guardOk`)
  | [], .ifThen _ (.prim (.addEnergy .you (.const n) none)) .nop => some (.energy n)
  | [], .ifThen _ (.prim (.addPower .you (.const n) (some d) none)) .nop => some (.power d n)
  | [], .ifThen _ (.prim (.addPower .you (.const n) none none)) .nop => some (.any n)
  -- "pay any amount of Power to add that much Energy", and the other way round
  | [], e =>
    if e == payAny ⟨0, [.any]⟩ (.prim (.addEnergy .you (.notes .unitPaid) none)) then
      some .powerToEnergy
    else if e == payAny ⟨1, []⟩ (.prim (.addPower .you (.notes .unitPaid) none none)) then
      some .energyToPower
    else none
  | _, _ => none

/-- Unit-only Energy pays for the Unit's activated abilities and its play. The internal Hide
activation is a discretionary action (CR 811.1.c). -/
def GameState.unitActivationPayment (s : GameState) (src : ObjId) (idx : Nat) : Bool :=
  (s.cardDef? src).any (fun d =>
    d.hasType .unit && ((s.activationList src d)[idx]?).any (fun (_, ability) =>
      match ability with
      | .activated costs _ body _ =>
        !costs.contains .fromHand || (match body.body with
          | .prim (.playTo ..) | .ifThen _ (.prim (.playTo ..)) .nop => true
          | _ => false)
      | _ => false))

/-- The player can use the activated ability at place `idx` of the object `src`, with the payment
and the targets, in the Main Phase (CR 361, 363, 355-357). `open_` is whether the Chain is empty:
an ability that is not a Reaction can be used only then (CR 312, 813). -/
def activatable (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (pay : RunePool.Payment)
    (ts : List ObjId) (open_ : Bool) (discards : List ObjId := []) (targetPlayer : Option PlayerId := none) : Bool :=
  s.phase == .main &&
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      -- a Battlefield is used by the player who controls it
      (if d.hasType .battlefield then o.control == some p else o.controller == p) &&
        s.abilityZoneOk p src idx &&
        match (s.activationList src d)[idx]? with
        | some (_, .activated costs speed body limit) =>
          match s.activationPlan p src d idx costs ts with
          | some (ex, pc) =>
            if (manaKind body).isSome then false
            else
              (open_ || speed == .reaction) && (!ex || !o.exhausted) &&
                pc.any (fun c => c.paidBy d.domains pay) &&
                (s.spendFor p (d.hasType .gear) pay (s.unitActivationPayment src idx)).any (fun pool =>
                  (costs.contains .fromHidden && s.playPowerCut p src ts != 0) ||
                    s.deflectOk p pool ts) &&
                (match limit with
                  | .unlimited => true
                  | .perTurn n => decide (o.used.count idx < n)) &&
                targetsOk s p src s.mightTable body.choices ts &&
                (s.discardCostOk p src costs discards &&
                  (s.playerTargetOptions p body.playerTarget).contains targetPlayer)
          | none => false
        | _ => false
    | _, _ => false

/-- Record the use and pay costs that change the source before putting the ability on the Chain. -/
def useAtCost (s : GameState) (idx : Nat) (costs : List AbilityCost) (ts : List ObjId)
    (o : Object) : Object :=
  let used := (useOf idx (costExhausts costs) o).noteChose s.turn ts
  { used with empowerCount := o.empowerCount - if costs.contains .disempowerSelf then 1 else 0 }

/-- Use an activated ability (CR 361, 363): pay, exhaust the object if the cost says so, and put
the ability on the Chain with the objects chosen. -/
def applyActivate (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat)
    (pay : RunePool.Payment) (ts : List ObjId) (discards : List ObjId := []) (targetPlayer : Option PlayerId := none) :
    Option (GameState × List Event) :=
  match s.cardDef? src, (s.poolOf p).spend pay (s.unitActivationPayment src idx) with
  | some d, some pool =>
    match (s.activationList src d)[idx]? with
    | some (grant, .activated costs _ _ _) =>
      let paid := preCost s p costs ts (d.hasType .gear) pool discards
      let noted := paid.1.noteGearAbility p d costs
      (addObject ((noted.modObj src (useAtCost s idx costs ts)).setPool p pool)
        { abilityItem d.id idx src p ts with activationGrant := grant, targetPlayer } .chain).map
        (fun r => (r.1, paid.2 ++ [Event.activated p src idx (baseActivationEnergy costs)]))
    | _ => none
  | _, _ => none

/-- The shape of an ability being used. -/
theorem applyActivate_cases {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {es : List Event}
    (h : applyActivate s p src idx pay ts discards targetPlayer = some (s', es)) :
    ∃ s0 d costs f pool item id',
      s0 = (preCost s p costs ts (d.hasType .gear) pool discards).1.noteGearAbility p d costs ∧
        Safe s s0 ∧
      (∀ o, (f o).kind = o.kind ∧ (f o).owner = o.owner) ∧
      (s.poolOf p).spend pay (s.unitActivationPayment src idx) = some pool ∧
        item.kind.phys? = none ∧ item.owner = p ∧
        addObject ((s0.modObj src f).setPool p pool) item .chain = some (s', id') ∧
          ∃ ke, es = ke ++ [Event.activated p src idx (baseActivationEnergy costs)] := by
  unfold applyActivate at h
  cases hd : s.cardDef? src with
  | none => simp [hd] at h
  | some d =>
    cases hs : (s.poolOf p).spend pay (s.unitActivationPayment src idx) with
    | none => simp [hd, hs] at h
    | some pool =>
      cases ha : (s.activationList src d)[idx]? with
      | none => simp [hd, hs, ha] at h
      | some entry =>
        obtain ⟨grant, ab⟩ := entry
        cases ab with
        | activated costs sp body lim =>
          simp only [hd, hs, ha, Option.map_eq_some_iff] at h
          obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          let paid := (preCost s p costs ts (d.hasType .gear) pool discards).1
          exact ⟨paid.noteGearAbility p d costs, d, costs, useAtCost s idx costs ts,
            pool, { abilityItem d.id idx src p ts with activationGrant := grant, targetPlayer }, id', rfl,
            (preCost_safe s p costs ts _ pool discards).trans (paid.noteGearAbility_safe p d costs),
            fun o => ⟨rfl, rfl⟩, rfl, rfl, rfl, hm, _, rfl⟩
        | passive _ _ => simp [hd, hs, ha] at h
        | replacement _ _ _ => simp [hd, hs, ha] at h
        | triggered _ _ _ => simp [hd, hs, ha] at h

/-- Using an ability keeps the game well formed. -/
theorem applyActivate_wf {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {es : List Event} (hwf : s.WF)
    (h : applyActivate s p src idx pay ts discards targetPlayer = some (s', es)) : s'.WF := by
  obtain ⟨s0, -, -, f, pool, item, id', -, hS, hf, -, -, -, hm, -⟩ := applyActivate_cases h
  have h1 : ((s0.modObj src f).setPool p pool).WF :=
    (GameState.wf_modObj (hS.wf hwf) src f).congr rfl rfl rfl rfl
  exact addObject_wf h1 hm

/-- Using an ability keeps the physical cards. -/
theorem applyActivate_physIds {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {es : List Event} (hwf : s.WF)
    (h : applyActivate s p src idx pay ts discards targetPlayer = some (s', es)) : s'.physIds.Perm s.physIds := by
  obtain ⟨s0, -, -, f, pool, item, id', -, hS, hf, -, hk, -, hm, -⟩ := applyActivate_cases h
  have h1 : ((s0.modObj src f).setPool p pool).WF :=
    (GameState.wf_modObj (hS.wf hwf) src f).congr rfl rfl rfl rfl
  have hp := addObject_physIds h1 hm hk
  have h2 : ((s0.modObj src f).setPool p pool).physIds = (s0.modObj src f).physIds := rfl
  rw [h2, GameState.physIds_modObj s0 src (fun o => (hf o).1)] at hp
  exact hp.trans (hS.phys hwf)

/-- Using an ability keeps `OwnerOk`. -/
theorem applyActivate_ownerOk {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : applyActivate s p src idx pay ts discards targetPlayer = some (s', es)) : s'.OwnerOk := by
  obtain ⟨s0, -, -, f, pool, item, id', -, hS, hf, -, -, -, hm, -⟩ := applyActivate_cases h
  have h1 : ((s0.modObj src f).setPool p pool).WF :=
    (GameState.wf_modObj (hS.wf hwf) src f).congr rfl rfl rfl rfl
  have h2 : ((s0.modObj src f).setPool p pool).OwnerOk :=
    (GameState.ownerOk_modObj (hS.own hwf hown) src (fun o => (hf o).2)).congr rfl rfl
  exact addObject_ownerOk h1 h2 hm

/-- Using an ability changes nothing of the stack, the turn order, the phase, the result, the rules
or the cards. -/
theorem applyActivate_meta {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {es : List Event}
    (h : applyActivate s p src idx pay ts discards targetPlayer = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending ∧ s'.cards = s.cards := by
  obtain ⟨s0, -, -, f, pool, item, id', -, hS, hf, -, -, -, hm, -⟩ := applyActivate_cases h
  have hs1 := addObject_sameMeta hm
  have hs2 := GameState.sameMeta_modObj s0 src f
  have hs3 := hS.same
  have c3 : s0.cards = s.cards := by
    have := congrArg GameState.cards hs3
    exact this
  have c1 : s'.cards = (s0.modObj src f).cards := by
    have := congrArg GameState.cards hs1
    exact this
  have c2 : (s0.modObj src f).cards = s0.cards := by
    have := congrArg GameState.cards hs2
    exact this
  exact ⟨hs1.config.trans (hs2.config.trans hs3.config),
    hs1.turnOrder.trans (hs2.turnOrder.trans hs3.turnOrder),
    hs1.phase.trans (hs2.phase.trans hs3.phase), hs1.result.trans (hs2.result.trans hs3.result),
    hs1.pending.trans (hs2.pending.trans hs3.pending),
    c1.trans (c2.trans c3)⟩

/-- Activating without discards leaves the hands as they were. -/
theorem applyActivate_hand {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {targetPlayer : Option PlayerId} {es : List Event} (hwf : s.WF)
    (h : applyActivate s p src idx pay ts [] targetPlayer = some (s', es)) (q : PlayerId) :
    s'.zone (.player q .hand) = s.zone (.player q .hand) := by
  obtain ⟨s0, d, costs, f, pool, item, id', hs0, hS, hf, -, -, -, hm, -⟩ := applyActivate_cases h
  rw [addObject_zone_other hm (by simp)]
  show (s0.modObj src f).zone _ = _
  rw [GameState.zone_modObj s0 src f _, hs0, GameState.noteGearAbility_zone]
  exact (preCost_zones hwf p costs ts (d.hasType .gear) pool).1 q

/-- A usable ability can be used. -/
theorem applyActivate_isSome {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {open_ : Bool}
    (h : activatable s p src idx pay ts open_ discards targetPlayer = true) :
    ∃ r, applyActivate s p src idx pay ts discards targetPlayer = some r := by
  unfold activatable at h
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
      cases ha : (s.activationList src d)[idx]? with
      | none => simp [ha] at h
      | some entry =>
        obtain ⟨grant, ab⟩ := entry
        cases ab with
        | activated costs sp body lim =>
          simp only [ha] at h
          cases hp : s.activationPlan p src d idx costs ts with
          | none => simp [hp] at h
          | some pe =>
            obtain ⟨ex, pc⟩ := pe
            simp only [hp] at h
            by_cases hm : (manaKind body).isSome = true
            · simp [hm] at h
            simp only [hm, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h
            have hpool := h.1.1.1.2
            cases hsf : s.spendFor p (d.hasType .gear) pay (s.unitActivationPayment src idx) with
            | none => rw [hsf] at hpool; simp at hpool
            | some pool =>
              have hs := GameState.spendFor_eq_some hsf
              unfold applyActivate
              simp only [hd, hs, ha]
              have hv : (Zone.chain).Valid s.playerCount ∧ Zone.chain.fits
                  (abilityItem d.id idx src p ts).owner = true :=
                ⟨Zone.valid_chain _, by simp [Zone.fits]⟩
              unfold addObject
              simp only [hv]
              exact ⟨_, rfl⟩
        | passive _ _ => simp [ha] at h
        | replacement _ _ _ => simp [ha] at h
        | triggered _ _ _ => simp [ha] at h

/-- What a usable ability is: an activated ability of an object the player controls, in the Main
Phase, with a payment that pays the cost and the Pool covers, and a legal pick of targets. -/
theorem activatable_spec {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {open_ : Bool}
    (h : activatable s p src idx pay ts open_ discards targetPlayer = true) :
    ∃ d costs sp body lim pc grant, s.phase = .main ∧ s.abilityZoneOk p src idx = true ∧
      s.cardDef? src = some d ∧
        (s.activationList src d)[idx]? = some (grant, .activated costs sp body lim) ∧
        s.activationPlan p src d idx costs ts = some (costExhausts costs, pc) ∧
          pc.any (fun c => c.paidBy d.domains pay) = true ∧
            targetsOk s p src s.mightTable body.choices ts = true ∧
            s.discardCostOk p src costs discards = true ∧
            targetPlayer ∈ s.playerTargetOptions p body.playerTarget ∧ ∃ o, s.obj? src = some o ∧
              (o.controller = p ∨ o.control = some p) := by
  unfold activatable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hph, h⟩ := h
  cases ho : s.obj? src with
  | none => simp [ho] at h
  | some o =>
    cases hd : s.cardDef? src with
    | none => simp [ho, hd] at h
    | some d =>
      simp only [ho, hd, Bool.and_eq_true] at h
      obtain ⟨⟨hctl0, huse⟩, h⟩ := h
      have hctl : o.controller = p ∨ o.control = some p := by
        by_cases hb : d.hasType .battlefield = true
        · simp only [hb, ite_true, beq_iff_eq] at hctl0
          exact Or.inr hctl0
        · simp only [Bool.not_eq_true] at hb
          simp only [hb, Bool.false_eq_true, ite_false, beq_iff_eq] at hctl0
          exact Or.inl hctl0
      cases ha : (s.activationList src d)[idx]? with
      | none => simp [ha] at h
      | some entry =>
        obtain ⟨grant, ab⟩ := entry
        cases ab with
        | activated costs sp body lim =>
          simp only [ha] at h
          cases hp : s.activationPlan p src d idx costs ts with
          | none => simp [hp] at h
          | some pe =>
            obtain ⟨ex, pc⟩ := pe
            simp only [hp] at h
            by_cases hm : (manaKind body).isSome = true
            · simp [hm] at h
            simp only [hm, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h
            have hex : costExhausts costs = ex := by
              cases hc : costPlan costs with
              | none => simp [GameState.activationPlan, hc] at hp
              | some base =>
                have he := congrArg (Option.map Prod.fst) hp
                simpa [GameState.activationPlan, costExhausts, hc] using he
            exact ⟨d, costs, sp, body, lim, pc, grant, hph, huse, rfl, ha, by rw [hex]; exact hp,
              h.1.1.1.1.2, h.1.2, h.2.1, List.contains_iff_mem.mp h.2.2, o, rfl, hctl⟩
        | passive _ _ => simp [ha] at h
        | replacement _ _ _ => simp [ha] at h
        | triggered _ _ _ => simp [ha] at h

/-- The Unit has Ambush and the pick names a Battlefield where its player has Units (CR 822): it can
be played there as a Reaction. -/
def ambushPick (s : GameState) (c : ObjId) (ts : List ObjId) : Bool :=
  (s.cardDef? c).any (·.hasKeyword .ambush) &&
    match s.bfPick ts with
    | some b => FilterList.holds s c Env.empty b (FilterList.ofList [.myUnitsHere]) == some true
    | none => false

/-- The card is a Reaction (CR 813): a Gear with Quick-Draw has Reaction (CR 819). -/
def reactSpell (s : GameState) (c : ObjId) : Bool :=
  s.cardHasReaction c

/-- The card of the hand can answer an item of the Chain: a Spell, a Unit or a Gear with Reaction
(CR 813). A Unit or a Gear is played at once. -/
def reactable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (ts : List ObjId) (flow : Option Cost := none) (pick : SpellPick := .plain) : Bool :=
  ((castable s p c pay ts flow pick ||
      (flow.isNone && pick == .plain && ts.isEmpty && s.extraOk p c ts && playable s p c pay none ts) ||
      (flow.isNone && bfPlayOk s p c pay ts pick)) &&
    reactSpell s c) || ((flow.isNone && bfPlayOk s p c pay ts pick) && ambushPick s c ts)

/-- Every way the player can use an activated ability: each object they use abilities of, each
ability, each payment that pays its cost, and each pick of targets, that the Pool covers. -/
def legalActivates (s : GameState) (p : PlayerId) (open_ : Bool) : List Action :=
  (s.abilityZones p).flatMap
    (fun src =>
      match s.cardDef? src with
      | some d =>
        (List.range (s.activationList src d).length).flatMap (fun (idx : Nat) =>
          match (s.activationList src d)[idx]? with
          | some (_, .activated costs _ body _) =>
            ([] :: (targetTuples s p src s.mightTable body.choices).filter
                (fun ts => decide (ts ≠ []))).flatMap (fun ts =>
              (match s.activationPlan p src d idx costs ts with
                | some (_, cs) => (cs.flatMap (Cost.payments d.domains)).eraseDups
                | none => []).flatMap (fun pay =>
                  (s.playerTargetOptions p body.playerTarget).flatMap (fun targetPlayer =>
                    ((s.discardPayments p src costs).filter
                      (fun ds => activatable s p src idx pay ts open_ ds targetPlayer)).map
                      (fun ds => ⟨.player p, .activate src idx pay ts ds targetPlayer⟩))))
          | _ => [])
      | none => [])

/-- Every way the player can answer the Chain with a Reaction. -/
def legalReactions (s : GameState) (p : PlayerId) : List Action :=
  (legalPlays s p).filter (fun a =>
    match a.kind with
    | .playCard c pay ts flow _ pick => reactable s p c pay ts flow pick
    | _ => false)

/-- The card is a Spell with Action (CR 806): it can be played in a Showdown. -/
def actionSpell (s : GameState) (c : ObjId) : Bool :=
  (s.cardDef? c).any (fun d => d.hasKeyword .action)

/-- The card can be played in a Showdown (CR 347-348, 806, 813): a Spell with Action, or
a card that can answer the Chain (Reaction). -/
def showdownable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (ts : List ObjId) (flow : Option Cost := none) (pick : SpellPick := .plain) : Bool :=
  reactable s p c pay ts flow pick || (castable s p c pay ts flow pick && actionSpell s c)

/-- Every way the player can play a card in a Showdown. -/
def legalShowdownPlays (s : GameState) (p : PlayerId) : List Action :=
  (legalPlays s p).filter (fun a =>
    match a.kind with
    | .playCard c pay ts flow _ pick => showdownable s p c pay ts flow pick
    | _ => false)

/-- The ability at place `idx` of the object has Action or Reaction speed (CR 806, 813): it can be
used in a Showdown. -/
def showdownSpeed (s : GameState) (src : ObjId) (idx : Nat) : Bool :=
  match s.activationAt src idx with
  | some (_, .activated _ sp _ _) => decide (sp ≠ Speed.normal)
  | _ => false

/-- The player can use the activated ability in a Showdown (CR 347-348): the Chain is empty, and the
ability has Action or Reaction speed. -/
def activatableSD (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat)
    (pay : RunePool.Payment) (ts : List ObjId) (discards : List ObjId := []) (targetPlayer : Option PlayerId := none) : Bool :=
  activatable s p src idx pay ts true discards targetPlayer && showdownSpeed s src idx

/-- Every way the player can use an activated ability in a Showdown. -/
def legalShowdownActivates (s : GameState) (p : PlayerId) : List Action :=
  (legalActivates s p true).filter (fun a =>
    match a.kind with
    | .activate src idx _ _ _ _ => showdownSpeed s src idx
    | _ => false)

/-- The abilities listed are exactly the ones that can be used. -/
theorem mem_legalActivates (s : GameState) (p : PlayerId) (open_ : Bool) (a : Action) :
    a ∈ legalActivates s p open_ ↔ ∃ src idx pay ts discards targetPlayer,
      a = ⟨.player p, .activate src idx pay ts discards targetPlayer⟩ ∧
        activatable s p src idx pay ts open_ discards targetPlayer = true := by
  constructor
  · intro ha
    unfold legalActivates at ha
    simp only [List.mem_flatMap] at ha
    obtain ⟨src, -, ha⟩ := ha
    cases hd : s.cardDef? src with
    | none => simp [hd] at ha
    | some d =>
      simp only [hd, List.mem_flatMap, List.mem_range] at ha
      obtain ⟨idx, hidx, ha⟩ := ha
      cases hab : (s.activationList src d)[idx]? with
      | none => simp [hab] at ha
      | some entry =>
        obtain ⟨grant, ab⟩ := entry
        cases ab with
        | activated costs sp body lim =>
          simp only [hab, List.mem_flatMap, List.mem_map, List.mem_filter] at ha
          obtain ⟨ts, -, pay, -, targetPlayer, -, ds, ⟨-, hact⟩, rfl⟩ := ha
          exact ⟨src, idx, pay, ts, ds, targetPlayer, rfl, hact⟩
        | passive _ _ => simp [hab] at ha
        | replacement _ _ _ => simp [hab] at ha
        | triggered _ _ _ => simp [hab] at ha
  · rintro ⟨src, idx, pay, ts, discards, targetPlayer, rfl, hact⟩
    obtain ⟨d, costs, sp, body, lim, pc, grant, hph, huse, hd, hab, hplan, hpay, hts, hds, hplayer, o, ho, hctl⟩ :=
      activatable_spec hact
    unfold legalActivates
    simp only [List.mem_flatMap]
    refine ⟨src, ?_, ?_⟩
    · exact GameState.abilityZoneOk_mem huse
    · simp only [hd, List.mem_flatMap, List.mem_range]
      refine ⟨idx, (List.getElem?_eq_some_iff.mp hab).1, ?_⟩
      simp only [hab, List.mem_flatMap, List.mem_map, List.mem_filter]
      refine ⟨ts, ?_, pay, ?_, targetPlayer, hplayer, discards,
        ⟨(s.mem_discardPayments p src costs discards).mpr hds, hact⟩, rfl⟩
      · by_cases hn : ts = []
        · subst hn
          exact List.mem_cons_self
        · refine List.mem_cons_of_mem _ ?_
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨(mem_targetTuples s p src s.mightTable body.choices ts).mpr hts, hn⟩
      · rw [hplan]
        simpa only [List.mem_eraseDups, List.mem_flatMap, Cost.mem_payments, List.any_eq_true]
          using hpay

/-- A Spell that can be cast in answer to an item of the Chain: it can be cast, and has Reaction. -/
theorem reactable_spec {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} {flow : Option Cost} {pick : SpellPick} : reactable s p c pay ts flow pick = true ↔
      (((castable s p c pay ts flow pick = true ∨
        (flow = none ∧ pick = .plain ∧ ts = [] ∧ s.extraOk p c ts = true ∧ playable s p c pay none ts = true)) ∨
        (flow = none ∧ bfPlayOk s p c pay ts pick = true)) ∧
        reactSpell s c = true) ∨
        ((flow = none ∧ bfPlayOk s p c pay ts pick = true) ∧ ambushPick s c ts = true) := by
  simp [reactable, List.isEmpty_iff, and_assoc]

/-- The Reactions listed are exactly the Spells that can be cast in answer. -/
theorem mem_legalReactions (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalReactions s p ↔ ∃ c pay ts flow discard pick,
      a = ⟨.player p, .playCard c pay ts flow discard pick⟩ ∧
      c ∈ s.playSources p ∧ reactable s p c pay ts flow pick = true ∧
        s.playDiscardOk p c discard = true := by
  unfold legalReactions
  simp only [List.mem_filter, mem_legalPlays]
  constructor
  · rintro ⟨⟨c, pay, ts, flow, discard, pick, rfl, hc, -, hd⟩, hr⟩
    exact ⟨c, pay, ts, flow, discard, pick, rfl, hc, hr, hd⟩
  · rintro ⟨c, pay, ts, flow, discard, pick, rfl, hc, hr, hd⟩
    refine ⟨⟨c, pay, ts, flow, discard, pick, rfl, hc, ?_, hd⟩, hr⟩
    rcases reactable_spec.mp hr with ⟨(h | h) | h, -⟩ | ⟨h, -⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨h.2.2.2.1, h.2.2.2.2, h.1, h.2.1⟩
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)

/-- A card that can be played in a Showdown is a Spell that can be cast, or can be played as a card
of the hand. -/
theorem showdownable_spec {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} {flow : Option Cost} {pick : SpellPick} (h : showdownable s p c pay ts flow pick = true) :
    castable s p c pay ts flow pick = true ∨ ∃ dest ts' pick', playable s p c pay dest ts' pick' = true := by
  simp only [showdownable, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | h
  · rcases reactable_spec.mp h with ⟨(h | h) | h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨none, ts, .plain, h.2.2.2.2⟩
    · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h.2
      exact Or.inr ⟨some b, ts, pick, hb⟩
    · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h.2
      exact Or.inr ⟨some b, ts, pick, hb⟩
  · exact Or.inl h.1

/-- The plays listed are exactly the cards that can be played in a Showdown. -/
theorem mem_legalShowdownPlays (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalShowdownPlays s p ↔ ∃ c pay ts flow discard pick,
      a = ⟨.player p, .playCard c pay ts flow discard pick⟩ ∧
      c ∈ s.playSources p ∧ showdownable s p c pay ts flow pick = true ∧
        s.playDiscardOk p c discard = true := by
  unfold legalShowdownPlays
  simp only [List.mem_filter, mem_legalPlays]
  constructor
  · rintro ⟨⟨c, pay, ts, flow, discard, pick, rfl, hc, -, hd⟩, hr⟩
    exact ⟨c, pay, ts, flow, discard, pick, rfl, hc, hr, hd⟩
  · rintro ⟨c, pay, ts, flow, discard, pick, rfl, hc, hr, hd⟩
    refine ⟨⟨c, pay, ts, flow, discard, pick, rfl, hc, ?_, hd⟩, hr⟩
    simp only [showdownable, Bool.or_eq_true, Bool.and_eq_true] at hr
    rcases hr with hr | hr
    · rcases reactable_spec.mp hr with ⟨(h | h) | h, -⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨h.2.2.2.1, h.2.2.2.2, h.1, h.2.1⟩
      · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl hr.1)

/-- The abilities listed are exactly the ones that can be used in a Showdown. -/
theorem mem_legalShowdownActivates (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalShowdownActivates s p ↔ ∃ src idx pay ts discards targetPlayer,
      a = ⟨.player p, .activate src idx pay ts discards targetPlayer⟩ ∧ activatableSD s p src idx pay ts discards targetPlayer = true := by
  unfold legalShowdownActivates
  simp only [List.mem_filter, mem_legalActivates]
  constructor
  · rintro ⟨⟨src, idx, pay, ts, discards, targetPlayer, rfl, hact⟩, hsp⟩
    exact ⟨src, idx, pay, ts, discards, targetPlayer, rfl, by simpa [activatableSD, hact] using hsp⟩
  · rintro ⟨src, idx, pay, ts, discards, targetPlayer, rfl, hact⟩
    simp only [activatableSD, Bool.and_eq_true] at hact
    exact ⟨⟨src, idx, pay, ts, discards, targetPlayer, rfl, hact.1⟩, hact.2⟩

/-- Use an ability, and put `new` on the stack in place of the frame that was answered. -/
def activateStep (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (pay : RunePool.Payment)
    (ts : List ObjId) (new : List Frame) (discards : List ObjId := []) (targetPlayer : Option PlayerId := none) :
    Option (GameState × List Event) :=
  (applyActivate s p src idx pay ts discards targetPlayer).map (fun r => ({ r.1 with pending := new }, r.2))

/-- Cast a Spell in answer to the Chain, and put `new` on the stack in place of the frame that was
answered. -/
def castStep (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (ts : List ObjId) (new : List Frame) (flow : Option Cost := none)
    (pick : SpellPick := .plain) : Option (GameState × List Event) :=
  (applyCast s p c pay ts flow pick).map (fun r =>
    let r' := castPay s c ts r
    ({ r'.1 with pending := new }, r'.2))

/-- What using an ability with a new stack does. -/
theorem activateStep_cases {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {new : List Frame} {es : List Event}
    (h : activateStep s p src idx pay ts new discards targetPlayer = some (s', es)) :
    ∃ s2 es2, applyActivate s p src idx pay ts discards targetPlayer = some (s2, es2) ∧
      s' = { s2 with pending := new } := by
  unfold activateStep at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
  simp only [Prod.mk.injEq] at hr
  exact ⟨s2, es2, hm, hr.1.symm⟩

/-- Using an ability keeps the game well formed. -/
theorem activateStep_wf {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {new : List Frame} {es : List Event}
    (hwf : s.WF) (h : activateStep s p src idx pay ts new discards targetPlayer = some (s', es)) : s'.WF := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  exact (applyActivate_wf hwf hm).congr rfl rfl rfl rfl

/-- Using an ability keeps the physical cards. -/
theorem activateStep_physIds {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {new : List Frame} {es : List Event}
    (hwf : s.WF) (h : activateStep s p src idx pay ts new discards targetPlayer = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  have h2 := applyActivate_physIds hwf hm
  exact h2

/-- Using an ability keeps `OwnerOk`. -/
theorem activateStep_ownerOk {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {new : List Frame} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (h : activateStep s p src idx pay ts new discards targetPlayer = some (s', es)) :
    s'.OwnerOk := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  exact (applyActivate_ownerOk hwf hown hm).congr rfl rfl

/-- Using an ability changes nothing of the turn order, the phase, the result, the rules or the
cards; the stack is `new`. -/
theorem activateStep_meta {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {new : List Frame} {es : List Event}
    (h : activateStep s p src idx pay ts new discards targetPlayer = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.cards = s.cards ∧ s'.pending = new := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := applyActivate_meta hm
  exact ⟨h1, h2, h3, h4, h6, rfl⟩

/-- Using an ability without discards leaves the hands as they were. -/
theorem activateStep_hand {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {targetPlayer : Option PlayerId} {new : List Frame} {es : List Event}
    (hwf : s.WF) (h : activateStep s p src idx pay ts new [] targetPlayer = some (s', es)) (q : PlayerId) :
    s'.zone (.player q .hand) = s.zone (.player q .hand) := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  exact applyActivate_hand hwf hm q

/-- A usable ability can be used, with any new stack. -/
theorem activateStep_isSome {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {open_ : Bool} {new : List Frame}
    (h : activatable s p src idx pay ts open_ discards targetPlayer = true) :
    ∃ r, activateStep s p src idx pay ts new discards targetPlayer = some r := by
  obtain ⟨r, hr⟩ := applyActivate_isSome h
  exact ⟨_, by unfold activateStep; rw [hr]; rfl⟩

/-- What casting a Spell with a new stack does. -/
theorem castStep_cases {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : castStep s p c pay ts new flow pick = some (s', es)) :
    ∃ s2 es2, applyCast s p c pay ts flow pick = some (s2, es2) ∧
      s' = { (castPay s c ts (s2, es2)).1 with pending := new } := by
  unfold castStep at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
  simp only [Prod.mk.injEq] at hr
  exact ⟨s2, es2, hm, hr.1.symm⟩

/-- Casting a Spell keeps the game well formed. -/
theorem castStep_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event} (hwf : s.WF)
    (h : castStep s p c pay ts new flow pick = some (s', es)) : s'.WF := by
  obtain ⟨s2, es2, hm, rfl⟩ := castStep_cases h
  exact ((castPay_safe s c ts (s2, es2)).wf (applyCast_wf hwf hm)).congr rfl rfl rfl rfl

/-- Casting a Spell keeps the physical cards. -/
theorem castStep_physIds {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event} (hwf : s.WF)
    (h : castStep s p c pay ts new flow pick = some (s', es)) : s'.physIds.Perm s.physIds := by
  obtain ⟨s2, es2, hm, rfl⟩ := castStep_cases h
  have h2 := applyCast_physIds hwf hm
  exact ((castPay_safe s c ts (s2, es2)).phys (applyCast_wf hwf hm)).trans h2

/-- Casting a Spell keeps `OwnerOk`. -/
theorem castStep_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : castStep s p c pay ts new flow pick = some (s', es)) : s'.OwnerOk := by
  obtain ⟨s2, es2, hm, rfl⟩ := castStep_cases h
  exact ((castPay_safe s c ts (s2, es2)).own (applyCast_wf hwf hm)
    (applyCast_ownerOk hwf hown hm)).congr rfl rfl

/-- Casting a Spell changes nothing of the turn order, the phase, the result, the rules or the
cards; the stack is `new`. -/
theorem castStep_meta {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : castStep s p c pay ts new flow pick = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.cards = s.cards ∧ s'.pending = new := by
  obtain ⟨s2, es2, hm, rfl⟩ := castStep_cases h
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := applyCast_meta hm
  have hs := (castPay_safe s c ts (s2, es2)).same
  exact ⟨hs.config.trans h1, hs.turnOrder.trans h2, hs.phase.trans h3, hs.result.trans h4,
    (congrArg GameState.cards hs).trans h6, rfl⟩

/-- A castable Spell from a permitted zone can be cast, with any new stack. -/
theorem castStep_isSome {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} (hwf : s.WF) (hc : c ∈ s.playSources p)
    (h : castable s p c pay ts flow pick = true) :
    ∃ r, castStep s p c pay ts new flow pick = some r := by
  obtain ⟨r, hr⟩ := applyCast_isSome hwf hc h
  exact ⟨_, by unfold castStep; rw [hr]; rfl⟩

/-- Answer the Chain with a card of the hand that has Reaction: cast a Spell, or play a Unit or a
Gear at once (it goes to the Base, and what it sets off goes on the Chain). `new` is put on the
stack in place of the frame that was answered. -/
def reactStep (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (ts : List ObjId) (new : List Frame) (flow : Option Cost := none)
    (pick : SpellPick := .plain) : Option (GameState × List Event) :=
  if castable s p c pay ts flow pick = true then castStep s p c pay ts new flow pick
  else ((applyPlay s p c pay pick).bind (fun r => payExtra s c ts r)).map
    (fun r => ({ r.1 with pending := new }, r.2))

/-- What answering with a card does. -/
theorem reactStep_cases {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : reactStep s p c pay ts new flow pick = some (s', es)) :
    (∃ s2 es2, applyCast s p c pay ts flow pick = some (s2, es2) ∧
      s' = { (castPay s c ts (s2, es2)).1 with pending := new }) ∨
    (∃ s1 es1 s2 es2, applyPlay s p c pay pick = some (s1, es1) ∧
      payExtra s c ts (s1, es1) = some (s2, es2) ∧ s' = { s2 with pending := new }) := by
  unfold reactStep at h
  split at h
  · exact Or.inl (castStep_cases h)
  · simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, ⟨r, hr, h2⟩, hr2⟩ := h
    simp only [Prod.mk.injEq] at hr2
    exact Or.inr ⟨r.1, r.2, s2, es2, hr, h2, hr2.1.symm⟩

/-- Answering the Chain keeps the game well formed. -/
theorem reactStep_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event} (hwf : s.WF)
    (h : reactStep s p c pay ts new flow pick = some (s', es)) : s'.WF := by
  rcases reactStep_cases h with ⟨s2, es2, hm, rfl⟩ | ⟨s1, es1, s2, es2, hm, hx, rfl⟩
  · exact ((castPay_safe s c ts (s2, es2)).wf (applyCast_wf hwf hm)).congr rfl rfl rfl rfl
  · exact ((payExtra_safe hx).wf (applyPlay_wf hwf hm)).congr rfl rfl rfl rfl

/-- Answering the Chain keeps the physical cards. -/
theorem reactStep_physIds {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event} (hwf : s.WF)
    (h : reactStep s p c pay ts new flow pick = some (s', es)) : s'.physIds.Perm s.physIds := by
  rcases reactStep_cases h with ⟨s2, es2, hm, rfl⟩ | ⟨s1, es1, s2, es2, hm, hx, rfl⟩
  · have h2 := applyCast_physIds hwf hm
    exact ((castPay_safe s c ts (s2, es2)).phys (applyCast_wf hwf hm)).trans h2
  · have h2 := applyPlay_physIds hwf hm
    exact ((payExtra_safe hx).phys (applyPlay_wf hwf hm)).trans h2

/-- Answering the Chain keeps `OwnerOk`. -/
theorem reactStep_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : reactStep s p c pay ts new flow pick = some (s', es)) : s'.OwnerOk := by
  rcases reactStep_cases h with ⟨s2, es2, hm, rfl⟩ | ⟨s1, es1, s2, es2, hm, hx, rfl⟩
  · exact ((castPay_safe s c ts (s2, es2)).own (applyCast_wf hwf hm)
      (applyCast_ownerOk hwf hown hm)).congr rfl rfl
  · exact ((payExtra_safe hx).own (applyPlay_wf hwf hm) (applyPlay_ownerOk hwf hown hm)).congr rfl
      rfl

/-- Answering the Chain changes nothing of the turn order, the phase, the result, the rules or the
cards; the stack is `new`. -/
theorem reactStep_meta {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : reactStep s p c pay ts new flow pick = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.cards = s.cards ∧ s'.pending = new := by
  rcases reactStep_cases h with ⟨s2, es2, hm, rfl⟩ | ⟨s1, es1, s2, es2, hm, hx, rfl⟩
  · obtain ⟨h1, h2, h3, h4, -, h6⟩ := applyCast_meta hm
    have hs := (castPay_safe s c ts (s2, es2)).same
    exact ⟨hs.config.trans h1, hs.turnOrder.trans h2, hs.phase.trans h3, hs.result.trans h4,
      (congrArg GameState.cards hs).trans h6, rfl⟩
  · obtain ⟨h1, h2, h3, h4, -, h6⟩ := applyPlay_meta hm
    have hs := (payExtra_safe hx).same
    exact ⟨hs.config.trans h1, hs.turnOrder.trans h2, hs.phase.trans h3, hs.result.trans h4,
      (congrArg GameState.cards hs).trans h6, rfl⟩

/-- An optional discard preserves the rules and the stack produced by a Main Phase play. -/
theorem applyPlayCard_discard_meta {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {rest : List Frame}
    {discard : Option ObjId} {es : List Event}
    (h : (applyPlayCard s p c pay ts rest flow pick).map (payPlayDiscard p c discard) = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.cards = s.cards ∧
      (s'.pending = s.pending ∨ s'.pending = .chainPass p 0 :: .priority p :: rest) := by
  obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hcfg, hto, hph, hres, hcards, hp⟩ := applyPlayCard_meta hr
  have hf := (payPlayDiscard_safe p c discard r).same
  rw [he] at hf
  change SameMeta r.1 s' at hf
  exact ⟨hf.config.trans hcfg, hf.turnOrder.trans hto, hf.phase.trans hph, hf.result.trans hres,
    (congrArg GameState.cards hf).trans hcards, hp.imp (hf.pending.trans) (hf.pending.trans)⟩

/-- An optional discard preserves the rules and the stack produced by answering the Chain. -/
theorem reactStep_discard_meta {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame}
    {discard : Option ObjId} {es : List Event}
    (h : (reactStep s p c pay ts new flow pick).map (payPlayDiscard p c discard) = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.cards = s.cards ∧ s'.pending = new := by
  obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hcfg, hto, hph, hres, hcards, hp⟩ := reactStep_meta hr
  have hf := (payPlayDiscard_safe p c discard r).same
  rw [he] at hf
  change SameMeta r.1 s' at hf
  exact ⟨hf.config.trans hcfg, hf.turnOrder.trans hto, hf.phase.trans hph, hf.result.trans hres,
    (congrArg GameState.cards hf).trans hcards, hf.pending.trans hp⟩

/-- A card from a permitted zone can answer the Chain, with any new stack. -/
theorem reactStep_isSome {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} (hwf : s.WF) (hc : c ∈ s.playSources p)
    (h : castable s p c pay ts flow pick = true ∨ ∃ dest ts' pick', playable s p c pay dest ts' pick' = true) :
    ∃ r, reactStep s p c pay ts new flow pick = some r := by
  unfold reactStep
  split
  · rename_i hk
    exact castStep_isSome hwf hc hk
  · rename_i hk
    rcases h with h | ⟨dest, ts', _, h⟩
    · exact absurd h hk
    · obtain ⟨r, hr⟩ := applyPlay_isSome hwf (playable_mem_hand hc h) h (applied := pick)
      obtain ⟨r', hr'⟩ := payExtra_isSome s c ts r
      refine ⟨({ r'.1 with pending := new }, r'.2), ?_⟩
      simp [hr, hr']

/-! ### I9: the Chain is last in, first out (CR 340.1) -/

/-- **An ability goes on top of the Chain**: the new item is the head of the Chain zone, and the
items that were there are below it, in the same order. -/
theorem applyActivate_chain {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {es : List Event} (hwf : s.WF)
    (h : applyActivate s p src idx pay ts discards targetPlayer = some (s', es)) :
    ∃ id', s'.zone .chain = id' :: s.zone .chain := by
  obtain ⟨s0, d, costs, f, pool, item, id', hs0, hS, hf, -, -, -, hm, -⟩ := applyActivate_cases h
  obtain ⟨hz, hid, hs'⟩ := addObject_spec hm
  refine ⟨id', ?_⟩
  rw [hs', hid]
  show ((((s0.modObj src f).setPool p pool).setZone .chain
    (Pos.top.insert ⟨_⟩ (((s0.modObj src f).setPool p pool).zone .chain)))).zone .chain = _
  rw [GameState.zone_setZone_self]
  have : ((s0.modObj src f).setPool p pool).zone .chain = s.zone .chain := by
    rw [show ((s0.modObj src f).setPool p pool).zone .chain = (s0.modObj src f).zone .chain from rfl,
      GameState.zone_modObj s0 src f _, hs0, GameState.noteGearAbility_zone]
    exact preCost_chain hwf p costs ts (d.hasType .gear) pool discards
  rw [this]
  rfl

/-- **A Spell goes on top of the Chain**: the new item is the head of the Chain zone, and the
items that were there are below it, in the same order. -/
theorem applyCast_chain {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {es : List Event} (h : applyCast s p c pay ts flow pick = some (s', es)) :
    ∃ id', s'.zone .chain = id' :: s.zone .chain := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  obtain ⟨src, dd, hs, o', ho', hdd⟩ := moveObj_spec_dst hm
  have hd2 : dd = .chain := by rw [hdd]; simp [Zone.normalize]
  have h2 := hs.zone_dst
  rw [hd2] at h2
  refine ⟨id', ?_⟩
  show (s2.zone .chain) = _
  rw [h2]
  rfl

/-- **The item that resolves is the one on top** (CR 340.1): the frames that resolve the Chain
finish the head of the Chain zone, whichever kind of item it is. -/
theorem resolveFrames_top {s : GameState} {item : ObjId} {more : List ObjId}
    (hc : s.zone .chain = item :: more) (rest : List Frame) :
    Frame.finishSpell item ∈ resolveFrames s rest := by
  unfold resolveFrames
  rw [hc]
  cases ho : s.obj? item with
  | none => simp [ho]
  | some o =>
    cases hd : s.cardDef? item with
    | some d => simp [ho, hd]
    | none =>
      simp only [ho, hd, itemFrames]
      split <;> simp

/-- **An item that has resolved leaves the Chain**: what is left is the Chain without it. If the
item could not be finished, nothing changes. -/
theorem finishItem_chain {s : GameState} (hwf : s.WF) (item : ObjId) :
    (finishItem s item).1.zone .chain = (s.zone .chain).erase item ∨
      (finishItem s item).1 = s := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, hc, hm, h⟩ | ⟨o, s2, -, hc, -, hr, h⟩
  · exact Or.inr h
  · left
    rw [h]
    obtain ⟨src, dd, hs⟩ := moveObj_spec hm
    have hsrc : src = .chain :=
      Option.some.inj (hs.locate.symm.trans
        (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hc) hc))
    have := hs.zone_src
    rw [hsrc] at this
    exact this
  · left
    rw [h]
    obtain ⟨z, hz, hid, hs'⟩ := removeObj_spec hr
    have hzc : z = .chain :=
      GameState.zone_unique hwf (GameState.zone_valid_of_mem hwf hc) hz hc hid
    rw [hs']
    subst hzc
    exact GameState.zone_setZone_self s _ _

/-- **Last in, first out** (CR 340.1): with the Chain `item :: more`, an item that resolves is
`item`, and what is left is `more`. -/
theorem finishItem_top_chain {s : GameState} (hwf : s.WF) {item : ObjId} {more : List ObjId}
    (hc : s.zone .chain = item :: more) :
    (finishItem s item).1.zone .chain = more ∨ (finishItem s item).1 = s := by
  have hnd : (item :: more).Nodup := hc ▸ GameState.zone_nodup_any hwf .chain
  rcases finishItem_chain hwf item with h | h
  · left
    rw [h, hc]
    simp
  · exact Or.inr h

end Riftbound

end
