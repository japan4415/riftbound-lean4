module

public import Riftbound.Rules.Resources
public import Riftbound.Rules.Pay
public import Riftbound.Rules.Select
public import Riftbound.Rules.Passive
public import Riftbound.Rules.Deflect

/-!
# Playing a card

A player with priority in their Main Phase can play a Unit or a Gear from their hand: the cost is
paid from the Rune Pool, and the card goes to the Base (CR 349-359). A Unit enters exhausted
(CR 359). Units and Gear resolve at once when they are finalized (CR 337.2), so for them the Chain
holds the card for no time at all and nothing can be played in answer; the Chain itself comes with
Spells (milestone M4).

The definition of the card is read from `GameState.cards`. The game's cards are fixed, so the
engine does not know any card by name (design.md §3, P3).
-/

@[expose] public section

namespace Riftbound

/-- The additional costs a card may pay when it is played, one at a time (CR 357.2): a Unit with
Accelerate may pay 1 Energy and a Power of its domain, to enter ready (CR 805); a Spell with Repeat
may pay the cost the keyword names, to repeat its effect (CR 820). -/
def CardDef.extraCosts (d : CardDef) : List Cost :=
  d.additionalCost.toList ++ d.keywords.filterMap (fun i =>
    match i.keyword, i.arg with
    | .accelerate, _ => if d.hasType .unit then some ⟨1, [.own]⟩ else none
    | .repeat_, .cost c => if d.hasType .spell then some c else none
    | _, _ => none)

/-- The costs a card may be played for: its cost, or its cost with one additional cost. -/
def CardDef.playCosts (d : CardDef) (cost : Cost) : List Cost :=
  cost :: d.extraCosts.map cost.plus

/-- The payment pays the cost of the card, or the cost with an additional cost. -/
def CardDef.paysFor (d : CardDef) (cost : Cost) (pay : RunePool.Payment) : Bool :=
  (d.playCosts cost).any (fun c => c.paidBy d.domains pay)

/-- Every payment that pays the cost of the card, with or without an additional cost. -/
def CardDef.playPayments (d : CardDef) (cost : Cost) : List RunePool.Payment :=
  (d.playCosts cost).flatMap (fun c => c.payments d.domains)

/-- The payments listed are exactly the payments that pay. -/
theorem CardDef.mem_playPayments (d : CardDef) (cost : Cost) (pay : RunePool.Payment) :
    pay ∈ d.playPayments cost ↔ d.paysFor cost pay = true := by
  simp only [playPayments, paysFor, List.mem_flatMap, List.any_eq_true, Cost.mem_payments]

/-- A payment that pays takes out as much as one of the costs it can pay. -/
theorem CardDef.paysFor_total {d : CardDef} {cost : Cost} {pay : RunePool.Payment}
    (h : d.paysFor cost pay = true) :
    ∃ c ∈ d.playCosts cost, pay.energy + pay.power.length = c.total := by
  unfold paysFor at h
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, hp⟩ := h
  exact ⟨c, hc, Cost.total_of_paidBy hp⟩

/-- The player has played a card in the turn that is going on, Legion (CR 812). -/
def GameState.playedBefore (s : GameState) (p : PlayerId) : Bool :=
  s.objects.toList.any (fun (_, o) => o.owner == p && o.playedTurn == some s.turn)

/-- Whether the card `c` is one of the objects the selector of a passive ability of `src`, which
the player `p` controls, stands for, as a cost change reads it (the card is not in play): the card
itself, or a card on a side (seen by `p`) with the properties. -/
def GameState.costSelects (s : GameState) (p : PlayerId) (src c : ObjId) : Selector → Bool
  | .self => src == c
  | .pick .all side _ fs =>
    (s.obj? c).any (fun o => side.admits p o) && (fs.holds s src {} c == some true)
  | _ => false

/-- The card `c` enters ready: by itself, by a passive ability of its own whose condition holds,
by the passive ability of an object the player controls, or by an effect of the turn. -/
def GameState.readyNow (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) : Bool :=
  d.entersReady || s.readyByFx p ||
    (d.fullAbilities.any (fun ab =>
      match ab with
      | Ability.passive cond mods =>
        mods.contains (.entersReady .self) && cond.eval s p c {} == some true
      | _ => false)) ||
    (s.passiveSources.any (fun src =>
      match s.obj? src, s.cardDef? src with
      | some o, some d2 =>
        d2.fullAbilities.any (fun ab =>
          match ab with
          | Ability.passive cond mods =>
            cond.eval s o.controller src {} == some true &&
              mods.any (fun m => match m with
                | .entersReady sel => src != c && s.costSelects o.controller src c sel
                | _ => false)
          | _ => false)
      | _, _ => false))

/-- The player a passive ability of the object speaks for: its controller, and for a Battlefield the
player who controls it (none while nobody does). -/
def GameState.sourceOwner (s : GameState) (src : ObjId) : Option Object :=
  match s.obj? src with
  | some o =>
    if (s.cardDef? src).any (·.hasType .battlefield) then
      o.control.map (fun q => { o with controller := q })
    else some o
  | none => none

/-- The cuts of the Energy cost of the card `c` of the player: each is an amount and the floor the
cost does not go below (CR 356). They come from the passive abilities of the objects in play and of
the card itself, whose condition holds: Legion is the player having played a card (CR 812). -/
def GameState.costCuts (s : GameState) (p : PlayerId) (c : ObjId) : List (Nat × Nat) :=
  (s.passiveSources ++ [c]).flatMap (fun src =>
    match s.sourceOwner src, s.cardDef? src with
    | some o, some d =>
      d.fullAbilities.flatMap (fun ab =>
        match ab with
        | Ability.passive cond mods =>
          let holds := match cond with
            | .legion =>
              -- another card of the player was played this turn, not the card itself
              some (s.objects.toList.any (fun (k, x) =>
                x.owner == p && x.playedTurn == some s.turn && k != c.n))
            | k => k.eval s o.controller src {}
          if holds == some true then
            mods.filterMap (fun m =>
              match m with
              | .costMinus sel a =>
                if s.costSelects o.controller src c sel then
                  some ((a.evalS s o.controller src (Env.empty.withMight s.mightTable)).getD 0, 0)
                  else none
              | .costMinusMin sel a fl =>
                if s.costSelects o.controller src c sel then
                  some ((a.evalS s o.controller src (Env.empty.withMight s.mightTable)).getD 0, fl)
                  else none
              | _ => none)
          else []
        | _ => [])
    | _, _ => []) ++
  (if (s.cardDef? c).any (·.hasType .spell) then (s.spellCutFx p).map (fun n => (n, 0)) else []) ++
  -- the Gear played from the hand, with a cost within the limit, costs no Energy (Jayce)
  (if (s.cardDef? c).any (·.hasType .gear) && (s.zone (.player p .hand)).contains c then
    (if (s.gearFreeFx p).any (fun n =>
        decide ((((s.cardDef? c).bind (·.cost)).map (·.energy)).getD 0 ≤ n))
      then [(1000, 0)] else [])
  else [])

/-- The Energy that the passive abilities add to the cost of the card `c` of the player (CR 356):
the cost of the spells of the opponents of Vex, Cheerless goes up. -/
def GameState.costRaise (s : GameState) (c : ObjId) : Nat :=
  -- the units of the player cost more this turn, by an effect (Vaults of Helia)
  ((match s.obj? c, s.cardDef? c with
    | some o, some d =>
      if d.hasType .unit then
        (s.turnFx.filter (fun f => f.turn == s.turn && f.who == o.owner)).foldl (fun a f =>
          match f.kind with | .unitsCostMore n => a + n | _ => a) 0
      else 0
    | _, _ => 0) +
  (s.passiveSources ++ [c]).foldl (fun acc src =>
    match s.sourceOwner src, s.cardDef? src with
    | some o, some d =>
      d.fullAbilities.foldl (fun acc ab =>
        match ab with
        | Ability.passive cond mods =>
          if cond.eval s o.controller src {} == some true then
            mods.foldl (fun acc m =>
              match m with
              | .costPlus sel a =>
                if s.costSelects o.controller src c sel then
                  acc + ((a.evalS s o.controller src (Env.empty.withMight s.mightTable)).getD 0)
                else acc
              | _ => acc) acc
          else acc
        | _ => acc) acc
    | _, _ => acc) 0)

/-- Take away one Power symbol: of the domain if one is named, else the first. -/
def removeSym (dom : Option Domain) : List PowerSym → List PowerSym
  | [] => []
  | x :: xs =>
    match dom with
    | none => xs
    | some d => if x == .domain d then xs else x :: removeSym dom xs

/-- A card has Reaction by printing, grant or the Quick-Draw keyword (CR 813, 819.1.b).
Ambush and Hidden grant it only for particular plays (CR 811, 822). -/
def GameState.cardHasReaction (s : GameState) (c : ObjId) : Bool :=
  s.hasKw c .reaction || s.hasKw c .quickDraw

/-- Additional Power due from Reaction cards at the ongoing Showdown (CR 341, 356.3). -/
def GameState.showdownReactionTax (s : GameState) : Nat :=
  let battlefield := s.pending.findSome? (fun
    | .showdown bf _ _ => some bf
    | _ => none)
  (battlefield.toList.flatMap (fun bf => (s.activeMods bf).filterMap (fun
    | .showdownReactionTax n => some n
    | _ => none))).sum

/-- The Power symbols of the cost of the card `c`, more or less by the passive abilities (Vex,
Needlessly Large Yordle): more first, then less. -/
def GameState.adjustPower (s : GameState) (c : ObjId) (power : List PowerSym) : List PowerSym :=
  let changes : List (Nat × Option Domain × Bool) :=
    (s.passiveSources ++ [c]).flatMap (fun src =>
      match s.sourceOwner src, s.cardDef? src with
      | some o, some d =>
        d.fullAbilities.flatMap (fun ab =>
          match ab with
          | Ability.passive cond mods =>
            if cond.eval s o.controller src {} == some true then
              mods.filterMap (fun m =>
                match m with
                | .costPower sel a dom more =>
                  if s.costSelects o.controller src c sel then
                    some (((a.evalS s o.controller src (Env.empty.withMight s.mightTable)).getD 0),
                      dom, more)
                  else none
                | _ => none)
            else []
          | _ => [])
      | _, _ => [])
  let tax := s.showdownReactionTax
  let taxed := if tax != 0 && s.cardHasReaction c then power ++ List.replicate tax .any else power
  let up := changes.foldl (fun l ch => if ch.2.2 then l ++ List.replicate ch.1 .any else l) taxed
  changes.foldl (fun l ch =>
    if ch.2.2 then l else (List.range ch.1).foldl (fun l _ => removeSym ch.2.1 l) l) up

/-- Adjust a starting cost for passive cost increases and reductions (CR 356). -/
def GameState.adjustCost (s : GameState) (p : PlayerId) (c : ObjId) (base : Cost) : Cost :=
  let energy := (s.costCuts p c).foldl
    (fun e (cut : Nat × Nat) => if e ≤ cut.2 then e else Nat.max cut.2 (e - cut.1))
    (base.energy + s.costRaise c)
  { energy, power := s.adjustPower c base.power }

/-- A card's own play restriction applies in every zone it could be played from (CR 002, 349). -/
def GameState.blocksOwnPlay (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) : Bool :=
  d.fullAbilities.any (fun
    | .passive cond mods =>
      mods.contains (.cant .self .play) && cond.eval s p c {} == some true
    | _ => false)

/-- The cost of playing an eligible card for its base cost (CR 356). -/
def GameState.effCost (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) : Option Cost :=
  if s.blocksOwnPlay p c d then none else d.cost.map (s.adjustCost p c)

/-- The distinct resource costs granted by the printed and temporary instances of Flow (CR 829). -/
def GameState.flowCosts (s : GameState) (c : ObjId) (d : CardDef) : List Cost :=
  if d.types == [.spell] then
    let temporary := (((s.obj? c).map (·.tempKws)).getD []).map (·.1)
    ((d.keywords ++ temporary).filterMap KeywordInst.flowCost?).eraseDups
  else []

/-- All cards in a zone that permits a direct play: hand cards and Flow Spells in the Trash. -/
def GameState.playSources (s : GameState) (p : PlayerId) : List ObjId :=
  s.zone (.player p .hand) ++ (s.zone (.player p .trash)).filter (fun c =>
    (s.cardDef? c).any (fun d => !(s.flowCosts c d).isEmpty))

/-- Whether a direct play of the card uses Flow in the player's Trash. -/
def GameState.flowPlaying (s : GameState) (p : PlayerId) (c : ObjId) : Bool :=
  !(s.zone (.player p .hand)).contains c && (s.zone (.player p .trash)).contains c

/-- Base-cost choices and the resulting costs after play-time adjustments (CR 356, 829).
When several raw Flow costs are available, the action names one even if the payments coincide. -/
def GameState.directOptions (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) :
    List (Option Cost × Cost) :=
  if s.flowPlaying p c then
    if s.blocksOwnPlay p c d then []
    else
      match s.flowCosts c d with
      | [base] => [(none, s.adjustCost p c base)]
      | costs => costs.map (fun base => (some base, s.adjustCost p c base))
  else (s.effCost p c d).toList.map (none, ·)

/-- The cost selected for this play, after applying the normal adjustments. -/
def GameState.directCost (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (flow : Option Cost := none) : Option Cost :=
  ((s.directOptions p c d).find? (fun option => option.1 == flow)).map Prod.snd

/-- The cost less `k`: the Energy first, then the Power symbols. -/
def Cost.less (c : Cost) (k : Nat) : Cost :=
  { energy := c.energy - k, power := c.power.drop (k - c.energy) }

/-- The cost with `k` less Energy (never Power). -/
def Cost.lessEnergy (c : Cost) (k : Nat) : Cost := { c with energy := c.energy - k }

/-- How much less the optional additional costs of the player cost (the passive abilities of their
objects: Ezreal, Prodigy), and how much less their Repeat costs (Marai Spire). -/
def GameState.extraCuts (s : GameState) (p : PlayerId) : Nat × Nat :=
  s.passiveSources.foldl (fun acc g =>
    match s.sourceOwner g with
    | some o =>
      if o.controller == p then
        (s.activeMods g).foldl (fun acc m =>
          match m with
          | .extraCostLess n => (acc.1 + n, acc.2)
          | .repeatCostLess n => (acc.1, acc.2 + n)
          | _ => acc) acc
      else acc
    | none => acc) (0, 0)

/-- The cost with `k` less Power symbols. -/
def Cost.lessPower (c : Cost) (k : Nat) : Cost := { c with power := c.power.drop k }

/-- The optional additional costs the card may pay when the player plays it now, as they are
printed: those it prints (Accelerate, Repeat, an extra cost), and the Repeat that an effect of the
turn gives the next Spell, for its cost (Temporal Portal). A Repeat is marked: it can be cut in
Energy by a passive ability (Marai Spire). -/
def GameState.extrasRaw (s : GameState) (p : PlayerId) (_c : ObjId) (d : CardDef) :
    List (Cost × Bool) :=
  d.additionalCost.toList.map (fun k => (k, false)) ++ d.keywords.filterMap (fun i =>
    match i.keyword, i.arg with
    | .accelerate, _ => if d.hasType .unit then some (⟨1, [.own]⟩, false) else none
    | .repeat_, .cost k => if d.hasType .spell then some (k, true) else none
    | _, _ => none) ++
  -- the Repeat that a passive ability of an object of the player gives their Spells (Syndra)
  (if d.hasType .spell then
    s.passiveSources.flatMap (fun g =>
      match s.sourceOwner g, s.cardDef? g with
      | some o, some dg =>
        if o.controller == p then
          dg.fullAbilities.flatMap (fun ab =>
            match ab with
            | Ability.passive cond mods =>
              if cond.eval s p g {} == some true then
                mods.filterMap (fun m => match m with | .grantRepeat k => some (k, true) | _ => none)
              else []
            | _ => [])
        else []
      | _, _ => [])
  else []) ++
  -- each effect of the turn that gives Repeat gives one more Repeat
  (if d.hasType .spell then
    ((s.fxOf p).filter (· == .nextSpellRepeat)).map (fun _ =>
      (d.cost.getD Cost.zero, true))
  else [])

/-- The ways to pay each optional additional cost of the card, less what the passive abilities cut
(Ezreal, Prodigy: 1 Energy or 1 Power less): the Energy is cut first (what is left over cuts
the Power), or only the Power is cut. -/
def GameState.extraAlts (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) :
    List (List Cost) :=
  let cuts := s.extraCuts p
  (s.extrasRaw p c d).map (fun x =>
    let fin (k : Cost) : Cost := if x.2 then k.lessEnergy cuts.2 else k
    let a := fin (x.1.less cuts.1)
    let b := fin (x.1.lessPower cuts.1)
    if a == b then [a] else [a, b])

/-- The optional additional costs the card may pay when the player plays it now: those it prints
(Accelerate, Repeat, an extra cost), less what the passive abilities cut, and the Repeat that an
effect of the turn gives the next Spell, for its cost (Temporal Portal). -/
def GameState.extrasFor (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) : List Cost :=
  let cuts := s.extraCuts p
  (s.extrasRaw p c d).map (fun x =>
    let k := x.1.less cuts.1
    if x.2 then k.lessEnergy cuts.2 else k)

/-- One way to pay each of the costs. -/
def waysToPay : List (List Cost) → List (List Cost)
  | [] => [[]]
  | a :: rest => a.flatMap (fun x => (waysToPay rest).map (x :: ·))

/-- The costs the card may be played for now, with how many additional costs each pays: its cost,
with any of its additional costs paid (each one is optional, and paid at most once) (CR 820). -/
def GameState.playCostsOfK (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (cost : Cost) : List (Cost × Nat) :=
  let es := s.extraAlts p c d
  (subseqsUpTo es.length es).flatMap (fun t =>
    (waysToPay t).map (fun cs => (cs.foldl (fun k e => k.plus e) cost, cs.length)))

/-- The costs the card may be played for now: its cost, with any of its additional costs paid. -/
def GameState.playCostsOf (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) (cost : Cost) :
    List Cost :=
  (s.playCostsOfK p c d cost).map (·.1)

/-- The payment pays the cost of the card, or the cost with an additional cost. -/
def GameState.paysForX (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) (cost : Cost)
    (pay : RunePool.Payment) : Bool :=
  (s.playCostsOf p c d cost).any (fun k => k.paidBy d.domains pay)

/-- Every payment that pays the cost of the card, with or without an additional cost. -/
def GameState.playPaymentsOf (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (cost : Cost) : List RunePool.Payment :=
  (s.playCostsOf p c d cost).flatMap (fun k => k.payments d.domains)

/-- The payments listed are exactly the payments that pay. -/
theorem GameState.mem_playPaymentsOf (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (cost : Cost) (pay : RunePool.Payment) :
    pay ∈ s.playPaymentsOf p c d cost ↔ s.paysForX p c d cost pay = true := by
  simp only [playPaymentsOf, paysForX, List.mem_flatMap, List.any_eq_true, Cost.mem_payments]

/-- A payment that pays takes out as much as one of the costs it can pay. -/
theorem GameState.paysForX_total {s : GameState} {p : PlayerId} {c : ObjId} {d : CardDef}
    {cost : Cost} {pay : RunePool.Payment} (h : s.paysForX p c d cost pay = true) :
    ∃ k ∈ s.playCostsOf p c d cost, pay.energy + pay.power.length = k.total := by
  unfold paysForX at h
  rw [List.any_eq_true] at h
  obtain ⟨k, hk, hp⟩ := h
  exact ⟨k, hk, Cost.total_of_paidBy hp⟩

/-- The Power symbols in a fixed order, so that the same symbols in another order are one cost. -/
def canonPower (l : List PowerSym) : List PowerSym :=
  l.mergeSort (fun a b => decide (toString (repr a) ≤ toString (repr b)))

/-- The Power symbols, with one of them left out, each way. -/
def dropEach : List PowerSym → List (List PowerSym)
  | [] => []
  | x :: xs => xs :: (dropEach xs).map (x :: ·)

/-- The Power symbols with `k` of them left out, whichever the player chooses (all of them, when
there are fewer). -/
def dropPowers : Nat → List PowerSym → List (List PowerSym)
  | 0, l => [l]
  | k + 1, l => if l.isEmpty then [l] else (dropEach l).flatMap (dropPowers k)

/-- The costs a Spell may have, by how much less (1 Energy or 1 Power each time) the objects it
chooses make it cost (at most `k`). -/
def Cost.cutOptions (c : Cost) (k : Nat) (floor : Nat := 0) : List Cost :=
  -- the cut is not optional: with something to cut, the whole cost is not one of the costs
  if k = 0 then [c]
  else
    -- the Energy does not go below the floor that the cost already has (Vex)
    let es := (List.range (k + 1)).filter (fun a => a == 0 || floor + a ≤ c.energy)
    let all := es.flatMap (fun a => (List.range (k + 1 - a)).flatMap (fun b =>
      (dropPowers b c.power).map (fun pw => { c.lessEnergy a with power := pw })))
    -- the same symbols in another order are one cost: keep the first
    let key (x : Cost) : Cost := ⟨x.energy, canonPower x.power⟩
    let l := (all.foldl (fun (acc : List Cost) x =>
      if acc.any (fun y => key y == key x) then acc else acc ++ [x]) []).filter
        (fun x => key x != key c)
    if l.isEmpty then [c] else l

/-- With nothing cut, the cost itself is the one cost. -/
theorem Cost.mem_cutOptions_zero (c : Cost) : c ∈ c.cutOptions 0 := by
  simp [Cost.cutOptions]

/-- The object can be the object of the additional cost of the kind: a gear of the player in play,
or their Legend, ready. -/
def GameState.extraTarget (s : GameState) (p : PlayerId) (k : PlayExtra) (t : ObjId) : Bool :=
  match k with
  | .returnGear | .killGear =>
    decide (t ∈ s.inPlay) && (s.obj? t).any (·.controller == p) &&
      (s.cardDef? t).any (·.hasType .gear)
  | .exhaustLegend =>
    decide (t ∈ s.zone (.player p .legendZone)) && (s.obj? t).any (fun o => !o.exhausted)
  | .killPet =>
    decide (t ∈ s.inPlay) && (s.obj? t).any (·.controller == p) &&
      (s.cardDef? t).any (fun d => d.hasType .unit &&
        (d.tags.any (fun g => g.name == "Bird" || g.name == "Cat" || g.name == "Dog" ||
          g.name == "Poro")))
  | .killUnit =>
    decide (t ∈ s.inPlay) && (s.obj? t).any (·.controller == p) &&
      (s.cardDef? t).any (·.hasType .unit)
  | .spendXP n =>
    decide (t ∈ s.zone (.player p .legendZone)) && decide (n ≤ s.xpOf p)
  | .spendXPOver _ _ => false

/-- The objects an additional cost of the kind can be done to. -/
def GameState.extraCandidates (s : GameState) (p : PlayerId) (k : PlayExtra) : List ObjId :=
  (s.inPlay ++ s.zone (.player p .legendZone)).filter (fun t => s.extraTarget p k t)

/-- How much less the Spell `c` of the player costs because of the objects it chooses (Irelia). -/
def GameState.chooseCut (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId) : Nat :=
  if (s.cardDef? c).any (·.hasType .spell) then
    ts.eraseDups.foldl (fun acc t =>
      if (s.obj? t).any (·.controller == p) then
        (s.activeMods t).foldl (fun acc m =>
          match m with | .chosenSpellsCostLess n => acc + n | _ => acc) acc
      else acc) 0
  else 0

/-- Ambush grants Reaction when a Unit is played to a Battlefield where its player has a Unit
(CR 822.1.b). -/
def GameState.ambushAt (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId) : Bool :=
  s.hasKw c .ambush && (match ts with
    | [bf] => (s.cardDef? bf).any (·.hasType .battlefield) &&
        (s.zone .battlefieldZone).any (fun u =>
          (s.cardDef? u).any (·.hasType .unit) &&
            (s.obj? u).any (fun o => o.controller == p && o.loc == some bf))
    | _ => false)

/-- The lowest Energy the cost of the card `c` can be cut to: the greatest floor of the cuts. -/
def GameState.cutFloor (s : GameState) (p : PlayerId) (c : ObjId) : Nat :=
  (s.costCuts p c).foldl (fun m cut => Nat.max m cut.2) 0

/-- How much the additional cost the picks name takes off the cost of the card (Poppy, Atakhan):
the Energy and the Power symbols. `none` if the card has no such cost, or the picks are not its
object. -/
def GameState.extraCutOf (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId) :
    Option (Nat × Nat) :=
  match (s.cardDef? c).bind (·.playExtra), (s.cardDef? c).bind (·.paidCut), ts with
  | some (k, _), some cut, [t] =>
    if s.extraTarget p k t then
      match cut with
      | .energy n => some (n, 0)
      | .killed =>
        some ((((s.cardDef? t).bind (·.cost)).map (·.energy)).getD 0,
          (((s.cardDef? t).bind (·.cost)).map (·.power.length)).getD 0)
    else none
  | _, _, _ => none

/-- The costs the card may have, with what the objects it chooses take off (Irelia), or what the
additional cost it is played with takes off (Poppy, Atakhan). -/
def GameState.cutOptionsOf (s : GameState) (p : PlayerId) (c : ObjId) (cost : Cost)
    (ts : List ObjId) : List Cost :=
  match s.extraCutOf p c ts with
  | some (e, w) => [(cost.lessEnergy e).lessPower w]
  | none => cost.cutOptions (s.chooseCut p c ts) (s.cutFloor p c)

/-- The possible Power adjustments that depend on targets or the Ambush destination (CR 356).
Target discounts apply to the total, including optional costs (CR 356.4.c-356.4.f). -/
def GameState.targetPowerOptions (s : GameState) (p : PlayerId) (c : ObjId)
    (ts : List ObjId) (cost : Cost) : List Cost :=
  let tax := s.showdownReactionTax
  let power := if tax != 0 && s.ambushAt p c ts && !s.cardHasReaction c then
    cost.power ++ List.replicate tax .any else cost.power
  let cut := s.choosePowerCut p c ts
  if cut = 0 then [{ cost with power := power }]
  else
    let total := power ++ List.replicate (s.deflectCost p ts (some c)) .any
    ((dropPowers cut total).eraseDups).map (fun adjusted => { cost with power := adjusted })

/-- The totals for a base cost and a set of targets, with the number of optional costs paid. -/
def GameState.targetCosts (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (cost : Cost) (ts : List ObjId) : List (Cost × Nat) :=
  (s.playCostsOfK p c d cost).flatMap (fun (total, extras) =>
    (s.targetPowerOptions p c ts total).map (·, extras))

/-- The payment pays the cost of the card, less what the objects it chooses take off, or the cost
with an additional cost. -/
def GameState.paysForXT (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) (cost : Cost)
    (ts : List ObjId) (pay : RunePool.Payment) : Bool :=
  (s.cutOptionsOf p c cost ts).any (fun b =>
    (s.targetCosts p c d b ts).any (fun x => x.1.paidBy d.domains pay))

/-- The payments that pay the cost of the card, with what the objects it chooses take off. -/
def GameState.playPaymentsOfT (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (cost : Cost) (ts : List ObjId) : List RunePool.Payment :=
  (s.cutOptionsOf p c cost ts).flatMap (fun b =>
    (s.targetCosts p c d b ts).flatMap (fun x => x.1.payments d.domains))

/-- The payments listed are exactly the payments that pay. -/
theorem GameState.mem_playPaymentsOfT (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (cost : Cost) (ts : List ObjId) (pay : RunePool.Payment) :
    pay ∈ s.playPaymentsOfT p c d cost ts ↔ s.paysForXT p c d cost ts pay = true := by
  simp only [playPaymentsOfT, paysForXT, List.mem_flatMap, List.any_eq_true, Cost.mem_payments]

/-- A payment that pays takes out as much as one of the costs it can pay. -/
theorem GameState.paysForXT_total {s : GameState} {p : PlayerId} {c : ObjId} {d : CardDef}
    {cost : Cost} {ts : List ObjId} {pay : RunePool.Payment}
    (h : s.paysForXT p c d cost ts pay = true) :
    ∃ b ∈ s.cutOptionsOf p c cost ts, ∃ k ∈ s.targetCosts p c d b ts,
      pay.energy + pay.power.length = k.1.total := by
  unfold paysForXT at h
  rw [List.any_eq_true] at h
  obtain ⟨b, hb, hp⟩ := h
  obtain ⟨k, hk, ht⟩ := List.any_eq_true.mp hp
  exact ⟨b, hb, k, hk, Cost.total_of_paidBy ht⟩

/-- The costs the card may be played for when its additional cost takes something off the cost
(Poppy, Atakhan), one for each object the additional cost can be done to. -/
def GameState.extraAltCosts (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) (cost : Cost) :
    List Cost :=
  match d.playExtra, d.paidCut with
  | some (k, _), some _ =>
    (s.extraCandidates p k).filterMap (fun t =>
      (s.extraCutOf p c [t]).map (fun x => (cost.lessEnergy x.1).lessPower x.2))
  | _, _ => []

/-- The payment pays more than the cost of the card: an additional cost is paid. A payment that
pays the cost less what the additional cost takes off pays no more than the cost. -/
def GameState.paidExtra (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (pay : RunePool.Payment) : Bool :=
  match s.effCost p c d with
  -- an additional cost that costs nothing is always paid
  | some cost =>
    (!(cost.paidBy d.domains pay) &&
      !((s.extraAltCosts p c d cost).any (fun b => b.paidBy d.domains pay))) ||
      (s.extrasFor p c d).any (·.total == 0)
  | none => false

/-- The Battlefields the Unit `c` of the player may be played to instead of the Base: those its
own ability names (Rengar, Perched Grimwyrm, Dauntless Vanguard), and the open ones, while an object
of the player says so (Origins: units can be played to open Battlefields). -/
def GameState.playBfOptions (s : GameState) (p : PlayerId) (c : ObjId) : List ObjId :=
  match s.cardDef? c with
  | some d =>
    if d.hasType .unit && !d.hasType .spell then
      let own : List FilterList := d.abilities.flatMap (fun ab =>
        match ab with
        | Ability.passive _ mods =>
          mods.filterMap (fun m =>
            match m with | .playToBf fs => some (FilterList.ofList fs) | _ => none)
        | _ => [])
      -- the units of the player can be played to the Battlefields another object of theirs names
      let granted : List FilterList := s.inPlay.flatMap (fun g =>
        if (s.obj? g).any (·.controller == p) then
          ((s.cardDef? g).map (fun dg => dg.abilities.flatMap (fun ab =>
            match ab with
            | Ability.passive .always mods =>
              mods.filterMap (fun m =>
                match m with | .playToBfAll fs => some (FilterList.ofList fs) | _ => none)
            | _ => []))).getD []
        else [])
      let permit := (s.inPlay ++ s.zone (.player p .legendZone)).any (fun g =>
        (s.obj? g).any (·.controller == p) &&
          FilterList.holds s c Env.empty g (FilterList.ofList [.permitsOpenPlay]) == some true)
      let open_ : List FilterList := if permit then [FilterList.ofList [.openBf]] else []
      -- Ambush: to a Battlefield where the player has Units
      let ambush : List FilterList :=
        if d.hasKeyword .ambush then [FilterList.ofList [.myUnitsHere]] else []
      (s.zone .battlefieldZone).filter (fun b =>
        (s.cardDef? b).any (·.hasType .battlefield) &&
          !s.oppHas p .oppsPlayToBaseOnly && !s.cantActHere p .play b &&
          FilterList.holds s c Env.empty b
            (FilterList.ofList [.ofType .battlefield, .unitsPlayable]) == some true &&
          (own ++ open_ ++ ambush ++ granted).any (fun fs => FilterList.holds s c Env.empty b fs == some true))
    else []
  | none => []

/-- A Battlefield a card can be played to means the card is a Unit and no Spell. -/
theorem playBfOptions_unit {s : GameState} {p : PlayerId} {c b : ObjId}
    (h : b ∈ s.playBfOptions p c) :
    ∃ d, s.cardDef? c = some d ∧ d.hasType .spell = false := by
  unfold GameState.playBfOptions at h
  cases hd : s.cardDef? c with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h
    refine ⟨d, rfl, ?_⟩
    by_cases hc : (d.hasType .unit && !d.hasType .spell) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact hc.2
    · simp only [hc] at h
      simp at h

/-- The Battlefield the picks name, if the first and only pick is one of them. -/
def GameState.bfPick (s : GameState) (ts : List ObjId) : Option ObjId :=
  match ts with
  | [b] => if (s.cardDef? b).any (·.hasType .battlefield) then some b else none
  | _ => none

/-- The player can play the object with the payment: it is the player's card, a Unit or a Gear, in
the Main Phase, and the payment pays its cost and the Rune Pool holds it (CR 349, 356, 357). The
card must also be in the hand, which `Legal` states apart. It is played to the Base, or to the
Battlefield `dest` if it can be played there. -/
def playable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (dest : Option ObjId := none) (ts : List ObjId := []) : Bool :=
  s.phase == .main && !s.cantPlay p &&
    match s.obj? c, s.cardDef? c with
    | some o, some d =>
      o.owner == p && (d.hasType .unit || d.hasType .gear) &&
        (match s.effCost p c d with
          | some cost => s.paysForXT p c d cost ts pay
          | none => false) &&
        (s.spendFor p (d.hasType .gear) pay).isSome &&
        (match dest with
          | none =>
            -- a card that is played only to a Battlefield is not played to the Base
            !(d.abilities.any (fun ab =>
              match ab with | Ability.passive _ mods => mods.contains .noPlayToBase | _ => false))
          | some b => (s.playBfOptions p c).contains b)
    | _, _ => false

/-- The Unit can be played to the Battlefield the picks name, with the payment. -/
def bfPlayOk (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) : Bool :=
  match s.bfPick targets with
  | some b => playable s p c pay (some b) targets
  | none => false

/-- What is true when a card is played: whether an additional cost was paid, whether another card
had been played in the turn (Legion), and the turn. -/
structure PlayMark where
  /-- An additional cost was paid. -/
  paid : Bool
  /-- How many additional costs were paid. -/
  extraPaid : Nat := 0
  /-- Another card of the player had been played in the turn. -/
  legion : Bool
  /-- The turn. -/
  turn : Nat
  /-- The timestamp counter. -/
  stamp : Nat
  /-- The Energy paid. -/
  energy : Nat
  /-- The Unit is buffed as it is played, by an effect of the turn. -/
  buff : Bool := false
  /-- The card is played from its owner's hand. -/
  fromHand : Bool := true
  /-- The spell is being played from the Trash for Flow. -/
  flowed : Bool := false

/-- The object after it is played: the objects chosen (for a Spell on the Chain), and the facts of
the play. -/
def Object.withPlay (ts : List ObjId) (m : PlayMark) (o : Object) : Object :=
  let o1 : Object :=
    { o with targets := ts, paid := m.paid, discardPaid := false, extraPaid := m.extraPaid,
             legion := m.legion, playedTurn := some m.turn,
             buffed := o.buffed || m.buff, playedFromHand := m.fromHand, flowed := m.flowed }
  { o1 with playedStamp := some m.stamp, energyPaid := m.energy }

/-- The greatest number of optional costs that this payment covers at the selected base cost. -/
def GameState.extraPaidAt (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) (cost : Cost)
    (ts : List ObjId) (pay : RunePool.Payment) : Nat :=
  ((s.cutOptionsOf p c cost ts).flatMap (fun b =>
    ((s.targetCosts p c d b ts).filter (fun x => x.1.paidBy d.domains pay)).map (·.2))).foldl
    Nat.max 0

/-- The facts of playing the card now with the payment. -/
def GameState.playMark (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (ts : List ObjId := []) (directCast : Bool := false) (flow : Option Cost := none) : PlayMark :=
  let costOf := if directCast then (fun d => s.directCost p c d flow) else s.effCost p c
  { paid := (s.cardDef? c).any (fun d =>
      match costOf d with
      | some cost =>
        (s.cutOptionsOf p c cost ts).all (fun b =>
          (s.targetPowerOptions p c ts b).all (fun x => !x.paidBy d.domains pay)) ||
          (s.extrasFor p c d).any (·.total == 0)
      | none => false),
    extraPaid := (s.cardDef? c).elim 0 (fun d =>
      match costOf d with
      | some cost => s.extraPaidAt p c d cost ts pay
      | none => 0),
    legion := s.playedBefore p,
    turn := s.turn, stamp := s.nextTimestamp, energy := pay.energy,
    buff := (s.cardDef? c).any (·.hasType .unit) && (s.fxOf p).any (fun k => k == .unitsBuffed || k == .nextUnitBuffed),
    fromHand := (s.obj? c).any (fun o => (s.zone (.player o.owner .hand)).contains c),
    flowed := directCast && s.flowPlaying p c }

/-- Play a card (CR 349-359): pay, and put it on the Base, exhausted if it is a Unit (CR 359),
unless it enters ready or the cost of Accelerate was paid (CR 805). -/
def applyPlay (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment) :
    Option (GameState × List Event) :=
  match s.cardDef? c, (s.poolOf p).spend pay with
  | some d, some pool =>
    (moveObj s c (.player p .base)).map (fun r =>
      let s1 := (r.1.modObj r.2 (Object.withPlay [] (s.playMark p c pay))).setPool p pool
      ((if (d.hasType .unit && !s.readyNow p c d &&
            !(d.hasKeyword .accelerate && s.paidExtra p c d pay)) || d.entersExhausted
          then s1.exhaustObj r.2
        else s1),
        [Event.moved c r.2 (.player p .base)]))
  | _, _ => none

/-- The objects chosen are a legal pick for the additional cost of the card to play it: none if it
has none (or may be left out), or the one object it is done to. -/
def GameState.extraOk (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId) : Bool :=
  match (s.cardDef? c).bind (·.playExtra) with
  | none => ts.isEmpty
  | some (k, mandatory) =>
    match ts with
    | [] => !mandatory
    | [t] => s.extraTarget p k t && !((s.cardDef? c).any (·.hasType .spell))
    | _ => false

/-- Do the additional cost of the kind to the object. -/
def applyExtra (s : GameState) (k : PlayExtra) (t : ObjId) :
    Option (GameState × List Event) :=
  match k with
  | .exhaustLegend => some (s.exhaustObj t, [])
  | .killPet | .killUnit =>
    (s.obj? t).bind (fun o => (moveObj s t (.player o.owner .trash)).map (fun r =>
      (r.1, [Event.moved t r.2 (.player o.owner .trash), Event.died r.2 o.controller])))
  | .spendXP n => some (s.modObj t (fun o => { o with xp := o.xp - n }), [])
  | .spendXPOver _ _ => some (s, [])
  | .returnGear =>
    (s.obj? t).bind (fun o => (moveObj s t (.player o.owner .hand)).map (fun r =>
      (r.1, [Event.moved t r.2 (.player o.owner .hand)])))
  | .killGear =>
    (s.obj? t).bind (fun o => (moveObj s t (.player o.owner .trash)).map (fun r =>
      (r.1, [Event.moved t r.2 (.player o.owner .trash)])))

/-- The card that was played remembers that its additional cost was paid. -/
def markPaid (s : GameState) (id : Option ObjId) (discarded : Bool := false) : GameState :=
  match id with
  | none => s
  | some n => s.modObj n (fun o => { o with paid := true, discardPaid := o.discardPaid || discarded })

/-- Remembering that the additional cost was paid is a safe change. -/
theorem markPaid_safe (s : GameState) (o : Option ObjId) (discarded : Bool := false) :
    Safe s (markPaid s o discarded) := by
  cases o with
  | none => exact Safe.refl s
  | some n => exact Safe.modObj s n (fun _ => rfl) (fun _ => rfl)

/-- The Battlefield is Contested by the player if the player does not control it (CR 190.3). A
Battlefield that is Contested already keeps the player who made it so: the rule that a Unit cannot
be moved to a Battlefield with a Combat in progress (CR 449.2.a) is not written yet. -/
def contestFor (p : PlayerId) (bf : ObjId) (s : GameState) : GameState :=
  if (s.obj? bf).bind (·.control) = some p ∨ ((s.obj? bf).bind (·.contested)).isSome then s
  else s.modObj bf (fun b => { b with contested := some p })

/-- Contesting is a safe change. -/
theorem contestFor_safe (p : PlayerId) (bf : ObjId) (s : GameState) :
    Safe s (contestFor p bf s) := by
  unfold contestFor
  split
  · exact Safe.refl s
  · exact Safe.modObj s bf (fun _ => rfl) (fun _ => rfl)

/-- Move a Unit to a Battlefield by an effect (CR 447): it is not exhausted, and it stays where it
is if it is there already. Its controller contests the Battlefield. -/
def sendToBf (bf : ObjId) (s : GameState) (u : ObjId) : GameState × List Event :=
  match s.obj? u with
  | some o =>
    if o.loc = some bf then (s, [])
    else if u ∈ s.zone .battlefieldZone then
      (contestFor o.controller bf
        (s.modObj u (fun x => ({ x with loc := some bf } : Object).countMove s.turn x.loc)),
        [Event.standardMoved u (some bf)])
    else
      match moveObj s u .battlefieldZone with
      | some r =>
        (contestFor o.controller bf
          (r.1.modObj r.2 (fun x => ({ x with loc := some bf } : Object).countMove s.turn x.loc)),
          [Event.standardMoved r.2 (some bf)])
      | none => (s, [])
  | none => (s, [])

/-- Moving to a Battlefield is a safe change. -/
theorem sendToBf_safe (bf : ObjId) (s : GameState) (u : ObjId) : Safe s (sendToBf bf s u).1 := by
  unfold sendToBf
  split
  · split
    · exact Safe.refl s
    · split
      · rename_i o ho hl hz
        have h1 : Safe s
            (s.modObj u
              (fun x => ({ x with loc := some bf } : Object).countMove s.turn x.loc)) :=
          Safe.modObj s u (fun _ => rfl) (fun _ => rfl)
        exact h1.trans (contestFor_safe _ _ _)
      · split
        · rename_i o ho hl hz r hm
          have h1 : Safe r.1
              (r.1.modObj r.2
                (fun x => ({ x with loc := some bf } : Object).countMove s.turn x.loc)) :=
            Safe.modObj r.1 r.2 (fun _ => rfl) (fun _ => rfl)
          exact ((Safe.moveObj hm).trans h1).trans (contestFor_safe _ _ _)
        · exact Safe.refl s
  · exact Safe.refl s

/-- A Unit or a Gear has been played (`r`, from `s`): the additional cost is done, if it was chosen,
and the card remembers that it was paid. -/
def payExtra0 (s : GameState) (c : ObjId) (ts : List ObjId)
    (r : GameState × List Event) : Option (GameState × List Event) :=
  match (s.cardDef? c).bind (·.playExtra), ts with
  | some (k, _), [t] =>
    -- the pick was legal, so the cost can be done; if it cannot, the card is played all the same
    match applyExtra r.1 k t with
    | some x =>
      some (markPaid x.1 (r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none)),
        r.2 ++ x.2)
    | none => some r
  | _, _ => some r

/-- Paying the additional cost of a card that was played always gives a state. -/
theorem payExtra0_isSome (s : GameState) (c : ObjId) (ts : List ObjId)
    (r : GameState × List Event) : ∃ r', payExtra0 s c ts r = some r' := by
  unfold payExtra0
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Doing an additional cost is a safe change. -/
theorem applyExtra_safe {s s' : GameState} {k : PlayExtra} {t : ObjId}
    {es : List Event} (h : applyExtra s k t = some (s', es)) : Safe s s' := by
  unfold applyExtra at h
  cases k with
  | exhaustLegend =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨fun hwf => GameState.wf_exhaustObj hwf t,
      fun _ => (GameState.physIds_exhaustObj s t) ▸ List.Perm.refl _,
      fun _ hown => GameState.ownerOk_exhaustObj hown t, GameState.sameMeta_exhaustObj s t⟩
  | returnGear =>
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨o, -, ⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact Safe.moveObj hm
  | killGear =>
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨o, -, ⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact Safe.moveObj hm
  | killPet =>
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨o, -, ⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact Safe.moveObj hm
  | killUnit =>
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨o, -, ⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact Safe.moveObj hm
  | spendXP n =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Safe.modObj s t (fun _ => rfl) (fun _ => rfl)
  | spendXPOver n cap =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Safe.refl s

/-- Paying the additional cost of a card that was played is a safe change. -/
theorem payExtra0_safe {s : GameState} {c : ObjId} {ts : List ObjId}
    {r r' : GameState × List Event} (h : payExtra0 s c ts r = some r') : Safe r.1 r'.1 := by
  unfold payExtra0 at h
  split at h
  · rename_i k b t hk
    split at h
    · rename_i x hx
      simp only [Option.some.injEq] at h
      subst h
      have h1 := applyExtra_safe (k := k) (t := t) (s := r.1) (s' := x.1) (es := x.2) hx
      exact h1.trans (markPaid_safe _ _)
    · simp only [Option.some.injEq] at h
      subst h
      exact Safe.refl _
  · simp only [Option.some.injEq] at h
    subst h
    exact Safe.refl _

/-- The player spends XP: it goes down, to 0 at the least. -/
def spendLegendXP (n : Nat) (s : GameState) (p : PlayerId) : GameState :=
  match s.zone (.player p .legendZone) with
  | l :: _ => s.modObj l (fun o => { o with xp := o.xp - n })
  | [] => s

/-- Spending XP is a safe change. -/
theorem spendLegendXP_safe (n : Nat) (s : GameState) (p : PlayerId) :
    Safe s (spendLegendXP n s p) := by
  unfold spendLegendXP
  split
  · exact Safe.modObj s _ (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- A Spell has been cast (`r`, from `s`): the additional cost is done, as it is cast. The object it
is done to is the first object the Spell chooses (the card's first choice names it); the Spell on
the Chain then has the object the cost made of it (a killed Unit is in the Trash) in its place. -/
def castPay (s : GameState) (c : ObjId) (ts : List ObjId) (r : GameState × List Event) :
    GameState × List Event :=
  match (s.cardDef? c).bind (·.playExtra), ts,
      r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none) with
  | some (.spendXPOver n cap, _), t :: _, some _ =>
    -- the XP is spent only for an object with more Might than the cap
    match s.obj? c with
    | some o =>
      if decide (((cap : Nat) : Int) < (s.mightNow t).getD 0) then (spendLegendXP n r.1 o.owner, r.2)
      else r
    | none => r
  | some (k, _), t :: rest, some n =>
    match applyExtra r.1 k t with
    | some x =>
      let t' := (x.2.findSome? (fun e => match e with | .moved _ m _ => some m | _ => none)).getD t
      (x.1.modObj n (fun o => { o with targets := t' :: rest }), r.2 ++ x.2)
    | none => r
  | _, _, _ => r

/-- Paying the additional cost of a Spell that was cast is a safe change. -/
theorem castPay_safe (s : GameState) (c : ObjId) (ts : List ObjId) (r : GameState × List Event) :
    Safe r.1 (castPay s c ts r).1 := by
  unfold castPay
  split
  · split
    · split
      · exact spendLegendXP_safe _ _ _
      · exact Safe.refl _
    · exact Safe.refl _
  · split
    · rename_i x hx
      exact (applyExtra_safe hx).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl))
    · exact Safe.refl _
  · exact Safe.refl _

/-- Power of Any domain that was spent on a Gear is no longer noted as Power that only pays for
Gear (the Power that only pays for Gear is spent first). -/
def gearSpent (s : GameState) (c : ObjId) (r : GameState × List Event) : GameState × List Event :=
  match s.obj? c with
  | some o =>
    if (s.cardDef? c).any (·.hasType .gear) then
      let spent := (s.poolOf o.owner).any - (r.1.poolOf o.owner).any
      ({ r.1 with turnFx := dropGearFx s.turn o.owner spent r.1.turnFx }, r.2)
    else r
  | none => r

/-- Noting the Power spent on a Gear is a safe change. -/
theorem gearSpent_safe (s : GameState) (c : ObjId) (r : GameState × List Event) :
    Safe r.1 (gearSpent s c r).1 := by
  unfold gearSpent
  split
  · split
    · exact ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
        fun _ hown => hown.congr rfl rfl, rfl⟩
    · exact Safe.refl _
  · exact Safe.refl _

/-- A Unit that was played to a Battlefield (the pick names it) is there: it does not move, so
nothing that waits for a move fires, and no move is counted (CR 447). -/
def placeAtBf (s : GameState) (ts : List ObjId) (r : GameState × List Event) :
    GameState × List Event :=
  match s.bfPick ts, r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none) with
  | some b, some n =>
    (((sendToBf b r.1 n).1.modObj n (fun x => { x with moves := 0, movesTurn := none })), r.2)
  | _, _ => r

/-- Placing a Unit at the Battlefield it was played to is a safe change. -/
theorem placeAtBf_safe (s : GameState) (ts : List ObjId) (r : GameState × List Event) :
    Safe r.1 (placeAtBf s ts r).1 := by
  unfold placeAtBf
  split
  · exact (sendToBf_safe _ _ _).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl))
  · exact Safe.refl _

/-- A Unit or a Gear has been played (`r`, from `s`): the Power spent on a Gear is noted, a Unit
played to a Battlefield is put there, the additional cost is done, if it was chosen, and the card
remembers that it was paid. -/
def payExtra (s : GameState) (c : ObjId) (ts : List ObjId)
    (r : GameState × List Event) : Option (GameState × List Event) :=
  payExtra0 s c ts (placeAtBf s ts (gearSpent s c r))

/-- Paying the additional cost of a card that was played always gives a state. -/
theorem payExtra_isSome (s : GameState) (c : ObjId) (ts : List ObjId)
    (r : GameState × List Event) : ∃ r', payExtra s c ts r = some r' :=
  payExtra0_isSome s c ts _

/-- Paying the additional cost of a card that was played is a safe change. -/
theorem payExtra_safe {s : GameState} {c : ObjId} {ts : List ObjId}
    {r r' : GameState × List Event} (h : payExtra s c ts r = some r') : Safe r.1 r'.1 :=
  ((gearSpent_safe s c r).trans (placeAtBf_safe s ts _)).trans (payExtra0_safe h)

/-- The player can cast the object with the payment and the targets: it is the player's Spell, the
objects chosen are a legal pick for its choices, and the payment pays its cost and the Pool covers
it, in the Main Phase (CR 349, 355, 356, 357). The card must also be in a zone in
`playSources`, which `Legal` states separately. -/
def castable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) (flow : Option Cost := none) : Bool :=
  s.phase == .main && !s.cantPlay p && !s.noSpells p &&
    match s.obj? c, s.cardDef? c with
    | some o, some d =>
      o.owner == p && d.hasType .spell &&
        (match d.spellEffect with
          | some e => targetsOk s p c s.mightTable e.choices targets
          | none => false) &&
        (match s.directCost p c d flow with
          | some cost => s.paysForXT p c d cost targets pay &&
              (!d.repeatChooses || decide (targets.length ≤ 1) ||
                decide (0 < s.extraPaidAt p c d cost targets pay))
          | none => false) &&
        (s.spendFor p false pay).any (fun pool =>
          s.choosePowerCut p c targets != 0 || s.deflectOk p pool targets (some c))
    | _, _ => false

/-- Cast a Spell (CR 354, 357): pay, and put it on the Chain with the objects chosen. -/
def applyCast (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) (flow : Option Cost := none) : Option (GameState × List Event) :=
  match (s.poolOf p).spend pay with
  | some pool =>
    (moveObj s c .chain).map (fun r =>
      (((r.1.setPool p pool).modObj r.2 (Object.withPlay targets (s.playMark p c pay targets true flow))),
        [Event.moved c r.2 .chain]))
  | none => none

/-- What a playable card is: the game is in the Main Phase, and the card is the player's, a Unit or
a Gear, with a cost that the payment pays and the Pool covers (CR 349, 356, 357). -/
theorem playable_spec {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {dest : Option ObjId} {ts : List ObjId} (h : playable s p c pay dest ts = true) :
    ∃ o d cost pool, s.phase = .main ∧ s.obj? c = some o ∧ s.cardDef? c = some d ∧
      o.owner = p ∧ (d.hasType .unit = true ∨ d.hasType .gear = true) ∧
        s.effCost p c d = some cost ∧
      s.paysForXT p c d cost ts pay = true ∧ (s.poolOf p).spend pay = some pool := by
  unfold playable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hph, -⟩, hrest⟩ := h
  cases ho : s.obj? c with
  | none => rw [ho] at hrest; simp at hrest
  | some o =>
    cases hd : s.cardDef? c with
    | none => rw [ho, hd] at hrest; simp at hrest
    | some d =>
      rw [ho, hd] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hrest
      obtain ⟨⟨⟨⟨howner, hty⟩, hcost⟩, hspend⟩, -⟩ := hrest
      cases hc : s.effCost p c d with
      | none => rw [hc] at hcost; simp at hcost
      | some cost =>
        simp only [hc] at hcost
        obtain ⟨pool, hpool⟩ := Option.isSome_iff_exists.mp hspend
        exact ⟨o, d, cost, pool, hph, rfl, rfl, howner, hty, hc, hcost,
          GameState.spendFor_eq_some hpool⟩

/-- A card that is playable to a Battlefield can be played there. -/
theorem playable_dest {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {b : ObjId} {ts : List ObjId} (h : playable s p c pay (some b) ts = true) :
    b ∈ s.playBfOptions p c := by
  unfold playable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨-, hrest⟩ := h
  cases ho : s.obj? c with
  | none => rw [ho] at hrest; simp at hrest
  | some o =>
    cases hd : s.cardDef? c with
    | none => rw [ho, hd] at hrest; simp at hrest
    | some d =>
      rw [ho, hd] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hrest
      simpa using hrest.2

/-- A Unit that can be played to a Battlefield with some picks is played to the one they name. -/
theorem bfPlayOk_spec {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} (h : bfPlayOk s p c pay ts = true) :
    ∃ b, ts = [b] ∧ playable s p c pay (some b) ts = true := by
  unfold bfPlayOk at h
  cases hpk : s.bfPick ts with
  | none => rw [hpk] at h; simp at h
  | some b =>
    rw [hpk] at h
    refine ⟨b, ?_, h⟩
    unfold GameState.bfPick at hpk
    split at hpk
    · split at hpk
      · simp only [Option.some.injEq] at hpk
        subst hpk
        rfl
      · simp at hpk
    · simp at hpk

/-- The shape of a card being played: its definition, the Pool after paying, and the move to the
Base. -/
theorem applyPlay_cases {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    ∃ d pool s2 id' m, s.cardDef? c = some d ∧ (s.poolOf p).spend pay = some pool ∧
      moveObj s c (.player p .base) = some (s2, id') ∧
      s' = (if ((d.hasType .unit && !s.readyNow p c d &&
          !(d.hasKeyword .accelerate && s.paidExtra p c d pay)) || d.entersExhausted) = true
        then ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).exhaustObj id'
        else (s2.modObj id' (Object.withPlay [] m)).setPool p pool) := by
  unfold applyPlay at h
  cases hd : s.cardDef? c with
  | none => simp [hd] at h
  | some d =>
    cases hs : (s.poolOf p).spend pay with
    | none => simp [hd, hs] at h
    | some pool =>
      simp only [hd, hs, Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      exact ⟨d, pool, s2, id', _, rfl, rfl, hm, hr.1.symm⟩

/-- Playing a card keeps the game well formed. -/
theorem applyPlay_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (h : applyPlay s p c pay = some (s', es)) : s'.WF := by
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
  have h2 : ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).WF :=
    (GameState.wf_modObj (moveObj_wf hwf hm) id' _).congr rfl rfl rfl rfl
  split
  · exact GameState.wf_exhaustObj h2 id'
  · exact h2

/-- Playing a card keeps the physical cards. -/
theorem applyPlay_physIds {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (h : applyPlay s p c pay = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
  have hp0 := moveObj_physIds hwf hm
  have hp : ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).physIds.Perm s.physIds := by
    have e : (s2.modObj id' (Object.withPlay [] m)).physIds = s2.physIds :=
      GameState.physIds_modObj s2 id' (f := Object.withPlay [] m) (fun _ => rfl)
    exact e ▸ hp0
  split
  · rw [GameState.physIds_exhaustObj]
    exact hp
  · exact hp

/-- Playing a card keeps `OwnerOk`. -/
theorem applyPlay_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (hown : s.OwnerOk) (h : applyPlay s p c pay = some (s', es)) :
    s'.OwnerOk := by
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
  have h2 : ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).OwnerOk :=
    (GameState.ownerOk_modObj (moveObj_ownerOk hwf hown hm) id'
      (f := Object.withPlay [] m) (fun _ => rfl)).congr rfl rfl
  split
  · exact GameState.ownerOk_exhaustObj h2 id'
  · exact h2

/-- Playing a card changes nothing of the stack, the turn order, the phase, the result, the rules
or the cards. -/
theorem applyPlay_meta {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending ∧ s'.cards = s.cards := by
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have hc := hs.other.config
  have ht := hs.other.turnOrder
  have hph := hs.other.phase
  have hr := hs.other.result
  have hpe := hs.other.pending
  have hcd : s2.cards = s.cards := by
    have := congrArg GameState.cards hs.other
    exact this
  split
  · exact ⟨hc, ht, hph, hr, hpe, hcd⟩
  · exact ⟨hc, ht, hph, hr, hpe, hcd⟩

/-- A playable card of the hand can be played. -/
theorem applyPlay_isSome {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {dest : Option ObjId} (hwf : s.WF) (hc : c ∈ s.zone (.player p .hand))
    {ts : List ObjId} (hp : playable s p c pay dest ts = true) :
    ∃ r, applyPlay s p c pay = some r := by
  obtain ⟨o, d, cost, pool, -, ho, hd, howner, -, -, -, hpool⟩ := playable_spec hp
  have hpn : p.n < s.playerCount :=
    Zone.lt_of_valid_player (GameState.zone_valid_of_mem hwf hc)
  obtain ⟨r, hr⟩ := moveObj_isSome hwf hc (.player p .base) .top (fun o' ho' => by
    have : o' = o := Option.some.inj (ho'.symm.trans ho)
    subst this
    rw [howner]
    simp only [Zone.normalize, Zone.isBoard, ite_true]
    exact ⟨Zone.valid_player hpn _, by simp⟩)
  unfold applyPlay
  rw [hd, hpool]
  simp only [hr, Option.map_some]
  exact ⟨_, rfl⟩

/-- **Playing a card takes exactly the payment out of the Pool** (I8) (CR 357, 445): the player's
Pool is what the Pool is left with after paying, and no other Pool changes. -/
theorem applyPlay_pool {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    ∃ pool, (s.poolOf p).spend pay = some pool ∧ s'.poolOf p = pool ∧
      ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  obtain ⟨d, pool, s2, id', m, -, hspend, hm, rfl⟩ := applyPlay_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have hpools : (s2.modObj id' (Object.withPlay [] m)).pools = s.pools := hs.pools
  refine ⟨pool, hspend, ?_, fun q hq => ?_⟩
  · split
    · exact GameState.poolOf_setPool_self (s2.modObj id' (Object.withPlay [] m)) p pool
    · exact GameState.poolOf_setPool_self (s2.modObj id' (Object.withPlay [] m)) p pool
  · split
    · rw [show (((s2.modObj id' (Object.withPlay [] m)).setPool p pool).exhaustObj id').poolOf q =
          ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).poolOf q from rfl,
        GameState.poolOf_setPool_ne _ hq]
      simp [GameState.poolOf, hpools]
    · rw [GameState.poolOf_setPool_ne _ hq]
      simp [GameState.poolOf, hpools]

/-- **Playing a card moves it from the hand to the Base** (CR 359): the hand is one card shorter,
the Base one card longer. -/
theorem applyPlay_zones {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (hc : c ∈ s.zone (.player p .hand))
    (hp : playable s p c pay = true) (h : applyPlay s p c pay = some (s', es)) :
    (s'.zone (.player p .hand)).length + 1 = (s.zone (.player p .hand)).length ∧
      (s'.zone (.player p .base)).length = (s.zone (.player p .base)).length + 1 := by
  obtain ⟨o, d0, cost, pool0, -, ho, -, howner, -, -, -, -⟩ := playable_spec hp
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
  obtain ⟨src, dd, hs, o', ho', hdd⟩ := moveObj_spec_dst hm
  have hsrc : src = .player p .hand :=
    Option.some.inj (hs.locate.symm.trans
      (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hc) hc))
  have hoo : o' = o := Option.some.inj (ho'.symm.trans ho)
  have hd2 : dd = .player p .base := by
    rw [hdd, hoo, howner]
    simp [Zone.normalize, Zone.isBoard]
  have h1 := hs.zone_src
  have h2 := hs.zone_dst
  rw [hsrc] at h1
  rw [hd2] at h2
  have hne : (Zone.player p .hand) ≠ .player p .base := by simp
  have hlen1 : (s2.zone (.player p .hand)).length + 1 = (s.zone (.player p .hand)).length := by
    rw [h1, List.length_erase_of_mem hc]
    have : 0 < (s.zone (.player p .hand)).length := List.length_pos_of_mem hc
    omega
  have hlen2 : (s2.zone (.player p .base)).length = (s.zone (.player p .base)).length + 1 := by
    rw [h2, (Pos.insert_perm _ _ _).length_eq]
    simp
  split
  · exact ⟨hlen1, hlen2⟩
  · exact ⟨hlen1, hlen2⟩

/-- Playing a card tells that it moved to the Base, under its new identifier. -/
theorem applyPlay_events {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    ∃ id', es = [Event.moved c id' (.player p .base)] ∧
      ∀ d, s.cardDef? c = some d → d.hasType .unit = true → s.readyNow p c d = false →
        s.paidExtra p c d pay = false → ∀ o, s'.obj? id' = some o → o.exhausted = true := by
  unfold applyPlay at h
  cases hd : s.cardDef? c with
  | none => simp [hd] at h
  | some d =>
    cases hs : (s.poolOf p).spend pay with
    | none => simp [hd, hs] at h
    | some pool =>
      simp only [hd, hs, Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨hs', hes⟩ := hr
      refine ⟨id', hes.symm, fun d' hd' hu hr hx0 o ho => ?_⟩
      cases hd'
      rw [← hs'] at ho
      simp only [hu, hr, hx0, Bool.and_false, Bool.not_false, Bool.and_self, Bool.true_or, ite_true,
        GameState.obj?_exhaustObj] at ho
      cases hx : ((s2.modObj id' (Object.withPlay [] (s.playMark p c pay))).setPool p pool).obj?
          id' with
      | none => rw [hx] at ho; simp at ho
      | some o0 =>
        rw [hx] at ho
        simp only [Option.map_some, Option.some.injEq] at ho
        subst ho
        rfl

/-- What a castable Spell is: the game is in the Main Phase, and the card is the player's Spell,
with an effect that asks for no choice, and a cost that the payment pays and the Pool covers. -/
theorem castable_spec {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} (h : castable s p c pay targets flow = true) :
    ∃ o d cost pool, s.phase = .main ∧ s.obj? c = some o ∧ s.cardDef? c = some d ∧
      o.owner = p ∧ d.hasType .spell = true ∧ s.directCost p c d flow = some cost ∧
      s.paysForXT p c d cost targets pay = true ∧ (s.poolOf p).spend pay = some pool := by
  unfold castable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hph, -⟩, -⟩, hrest⟩ := h
  cases ho : s.obj? c with
  | none => rw [ho] at hrest; simp at hrest
  | some o =>
    cases hd : s.cardDef? c with
    | none => rw [ho, hd] at hrest; simp at hrest
    | some d =>
      rw [ho, hd] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨⟨⟨⟨howner, hty⟩, -⟩, hcost⟩, hspend⟩ := hrest
      cases hc : s.directCost p c d flow with
      | none => rw [hc] at hcost; simp at hcost
      | some cost =>
        simp only [hc, Bool.and_eq_true] at hcost
        obtain ⟨pool, hpool⟩ : ∃ pool, (s.poolOf p).spend pay = some pool := by
          cases hs : s.spendFor p false pay with
          | none => rw [hs] at hspend; simp at hspend
          | some pool => exact ⟨pool, GameState.spendFor_eq_some hs⟩
        exact ⟨o, d, cost, pool, hph, rfl, rfl, howner, hty, hc, hcost.1, hpool⟩

/-- A castable card is a Spell whose effect the targets are a legal pick for. -/
theorem castable_targets {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} (h : castable s p c pay targets flow = true) :
    ∃ d e, s.cardDef? c = some d ∧ d.spellEffect = some e ∧
      targetsOk s p c s.mightTable e.choices targets = true := by
  unfold castable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨-, hrest⟩ := h
  cases ho : s.obj? c with
  | none => rw [ho] at hrest; simp at hrest
  | some o =>
    cases hd : s.cardDef? c with
    | none => rw [ho, hd] at hrest; simp at hrest
    | some d =>
      rw [ho, hd] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨⟨⟨⟨-, -⟩, htg⟩, -⟩, -⟩ := hrest
      cases he : d.spellEffect with
      | none => rw [he] at htg; simp at htg
      | some e =>
        rw [he] at htg
        exact ⟨d, e, rfl, he, htg⟩

/-- The shape of a Spell being cast: the Pool after paying, and the move to the Chain. -/
theorem applyCast_cases {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} {es : List Event} (h : applyCast s p c pay targets flow = some (s', es)) :
    ∃ pool s2 id' rep, (s.poolOf p).spend pay = some pool ∧
      moveObj s c .chain = some (s2, id') ∧
      s' = (s2.setPool p pool).modObj id' (Object.withPlay targets rep) ∧
        es = [Event.moved c id' .chain] := by
  unfold applyCast at h
  cases hs : (s.poolOf p).spend pay with
  | none => simp [hs] at h
  | some pool =>
    simp only [hs, Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    exact ⟨pool, s2, id', _, rfl, hm, hr.1.symm, hr.2.symm⟩

/-- Casting a Spell keeps the game well formed. -/
theorem applyCast_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} {es : List Event} (hwf : s.WF)
    (h : applyCast s p c pay targets flow = some (s', es)) : s'.WF := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  have h2 : (s2.setPool p pool).WF := (moveObj_wf hwf hm).congr rfl rfl rfl rfl
  exact GameState.wf_modObj h2 _ _

/-- Casting a Spell keeps the physical cards. -/
theorem applyCast_physIds {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} {es : List Event} (hwf : s.WF)
    (h : applyCast s p c pay targets flow = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  have hp := moveObj_physIds hwf hm
  have h2 : (s2.setPool p pool).physIds = s2.physIds := rfl
  rw [GameState.physIds_modObj _ id' (f := Object.withPlay targets rep) (fun _ => rfl), h2]
  exact hp

/-- Casting a Spell keeps `OwnerOk`. -/
theorem applyCast_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : applyCast s p c pay targets flow = some (s', es)) :
    s'.OwnerOk := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  have h2 : (s2.setPool p pool).OwnerOk := (moveObj_ownerOk hwf hown hm).congr rfl rfl
  exact GameState.ownerOk_modObj h2 _ (fun _ => rfl)

/-- Casting a Spell changes nothing of the stack, the turn order, the phase, the result, the rules
or the cards. -/
theorem applyCast_meta {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} {es : List Event} (h : applyCast s p c pay targets flow = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending ∧ s'.cards = s.cards := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have hcd : s2.cards = s.cards := by
    have := congrArg GameState.cards hs.other
    exact this
  exact ⟨hs.other.config, hs.other.turnOrder, hs.other.phase, hs.other.result, hs.other.pending,
    hcd⟩

/-- A direct play starts in the player's hand or Trash. -/
theorem GameState.playSource_zone {s : GameState} {p : PlayerId} {c : ObjId}
    (h : c ∈ s.playSources p) : c ∈ s.zone (.player p .hand) ∨ c ∈ s.zone (.player p .trash) := by
  simp only [GameState.playSources, List.mem_append, List.mem_filter] at h
  exact h.imp id And.left

/-- A card played as a permanent from one of the direct-play zones comes from the hand. -/
theorem playable_mem_hand {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {dest : Option ObjId} {ts : List ObjId} (hc : c ∈ s.playSources p)
    (hp : playable s p c pay dest ts = true) : c ∈ s.zone (.player p .hand) := by
  simp only [GameState.playSources, List.mem_append, List.mem_filter] at hc
  rcases hc with hc | ⟨_, hflow⟩
  · exact hc
  · obtain ⟨_, d, _, _, _, _, hd, _, hty, _, _, _⟩ := playable_spec hp
    rw [hd] at hflow
    by_cases ht : d.types = [.spell]
    · simp [CardDef.hasType, ht] at hty
    · simp [GameState.flowCosts, ht] at hflow

/-- Flow never replaces the base cost for a card in the hand. -/
theorem GameState.directOptions_of_hand {s : GameState} {p : PlayerId} {c : ObjId}
    (h : c ∈ s.zone (.player p .hand)) (d : CardDef) :
    s.directOptions p c d = (s.effCost p c d).toList.map (none, ·) := by
  simp [GameState.directOptions, GameState.flowPlaying, h]

/-- A cost returned by direct-cost lookup corresponds to an actual choice in the list. -/
theorem GameState.directCost_mem {s : GameState} {p : PlayerId} {c : ObjId} {d : CardDef}
    {flow : Option Cost} {cost : Cost} (h : s.directCost p c d flow = some cost) :
    (flow, cost) ∈ s.directOptions p c d := by
  unfold directCost at h
  obtain ⟨⟨choice, base⟩, hfind, rfl⟩ := Option.map_eq_some_iff.mp h
  have hf : choice = flow := beq_iff_eq.mp (List.find?_some (p := fun x : Option Cost × Cost => x.1 == flow) hfind)
  exact hf ▸ List.mem_of_find?_eq_some (p := fun x : Option Cost × Cost => x.1 == flow) hfind

/-- A castable Spell from a direct-play zone can be cast. -/
theorem applyCast_isSome {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} (hwf : s.WF) (hc : c ∈ s.playSources p)
    (hp : castable s p c pay targets flow = true) :
    ∃ r, applyCast s p c pay targets flow = some r := by
  obtain ⟨_, _, _, pool, _, _, _, _, _, _, _, hpool⟩ := castable_spec hp
  have hz : ∃ z, c ∈ s.zone z ∧ z ≠ .chain := by
    rcases GameState.playSource_zone hc with hm | hm
    · exact ⟨.player p .hand, hm, by simp⟩
    · exact ⟨.player p .trash, hm, by simp⟩
  obtain ⟨z, hm, hn⟩ := hz
  obtain ⟨r, hr⟩ := moveObj_isSome hwf hm .chain .top (fun _ _ =>
    ⟨Zone.valid_chain _, hn⟩)
  unfold applyCast
  rw [hpool]
  simp only [hr, Option.map_some]
  exact ⟨_, rfl⟩

/-- **Casting a Spell takes exactly the payment out of the Pool** (I8) (CR 357, 445). -/
theorem applyCast_pool {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} {es : List Event} (h : applyCast s p c pay targets flow = some (s', es)) :
    ∃ pool, (s.poolOf p).spend pay = some pool ∧ s'.poolOf p = pool ∧
      ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  obtain ⟨pool, s2, id', rep, hspend, hm, rfl, -⟩ := applyCast_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have hpools : s2.pools = s.pools := hs.pools
  refine ⟨pool, hspend, GameState.poolOf_setPool_self s2 p pool, fun q hq => ?_⟩
  show (s2.setPool p pool).poolOf q = _
  rw [GameState.poolOf_setPool_ne _ hq]
  simp [GameState.poolOf, hpools]

/-- **Casting a Spell moves it from the hand to the Chain** (CR 354). -/
theorem applyCast_zones {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} {es : List Event} (hwf : s.WF) (hc : c ∈ s.zone (.player p .hand))
    (h : applyCast s p c pay targets flow = some (s', es)) :
    (s'.zone (.player p .hand)).length + 1 = (s.zone (.player p .hand)).length ∧
      (s'.zone .chain).length = (s.zone .chain).length + 1 := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  obtain ⟨src, dd, hs, o', ho', hdd⟩ := moveObj_spec_dst hm
  have hsrc : src = .player p .hand :=
    Option.some.inj (hs.locate.symm.trans
      (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hc) hc))
  have hd2 : dd = .chain := by rw [hdd]; simp [Zone.normalize]
  have h1 := hs.zone_src
  have h2 := hs.zone_dst
  rw [hsrc] at h1
  rw [hd2] at h2
  refine ⟨?_, ?_⟩
  · show (s2.zone (.player p .hand)).length + 1 = _
    rw [h1, List.length_erase_of_mem hc]
    have : 0 < (s.zone (.player p .hand)).length := List.length_pos_of_mem hc
    omega
  · show (s2.zone .chain).length = _
    rw [h2, (Pos.insert_perm _ _ _).length_eq]
    simp

/-- A card of the hand can be played with the payment and the targets: a Unit or a Gear with no
targets, or a Spell with a legal pick of targets (CR 349-359). -/
def PlayOk (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) (flow : Option Cost := none) : Prop :=
  (s.extraOk p c targets = true ∧ playable s p c pay none targets = true ∧ flow = none) ∨
    castable s p c pay targets flow = true ∨
    (bfPlayOk s p c pay targets = true ∧ flow = none)

instance PlayOk.decidable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) (flow : Option Cost) : Decidable (PlayOk s p c pay targets flow) := by
  unfold PlayOk
  infer_instance

/-- The picks of targets worth trying for a card: none, every legal pick of its Spell effect, and
each object its additional cost can be done to. -/
def playTargets (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) : List (List ObjId) :=
  [] :: ((match d.spellEffect with
    | some e => (targetTuples s p c s.mightTable e.choices).filter (fun ts => decide (ts ≠ []))
    | none => []) ++
    ((match d.playExtra with
      | some (k, _) => (s.extraCandidates p k).map (fun t => [t])
      | none => []) ++
    -- the Battlefields a Unit can be played to
    (s.playBfOptions p c).map (fun b => [b])))

/-- The picks listed are no target, or a legal pick of the Spell effect, or the object of the
additional cost. -/
theorem mem_playTargets (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (ts : List ObjId) : ts ∈ playTargets s p c d ↔
      ts = [] ∨ (∃ e, d.spellEffect = some e ∧ targetsOk s p c s.mightTable e.choices ts = true) ∨
        (∃ k b t, d.playExtra = some (k, b) ∧ ts = [t] ∧ s.extraTarget p k t = true) ∨
        (∃ b, ts = [b] ∧ b ∈ s.playBfOptions p c) := by
  unfold playTargets
  rw [List.mem_cons, List.mem_append, List.mem_append]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · right; left
      cases hs : d.spellEffect with
      | none => rw [hs] at h; simp at h
      | some e =>
        rw [hs] at h
        simp only [List.mem_filter, decide_eq_true_eq] at h
        exact ⟨e, rfl, (mem_targetTuples s p c s.mightTable e.choices ts).mp h.1⟩
    · right; right; left
      cases hx : d.playExtra with
      | none => rw [hx] at h; simp at h
      | some kb =>
        rw [hx] at h
        simp only [List.mem_map, GameState.extraCandidates, List.mem_filter] at h
        obtain ⟨t, ⟨-, ht⟩, rfl⟩ := h
        exact ⟨kb.1, kb.2, t, rfl, rfl, ht⟩
    · right; right; right
      simp only [List.mem_map] at h
      obtain ⟨b, hb, rfl⟩ := h
      exact ⟨b, rfl, hb⟩
  · rintro (h | ⟨e, he, hok⟩ | ⟨k, b, t, hx, rfl, ht⟩ | ⟨b, rfl, hb⟩)
    · exact Or.inl h
    · by_cases hne : ts = []
      · exact Or.inl hne
      · right; left
        rw [he]
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨(mem_targetTuples s p c s.mightTable e.choices ts).mpr hok, hne⟩
    · right; right; left
      rw [hx]
      simp only [List.mem_map, GameState.extraCandidates, List.mem_filter]
      refine ⟨t, ⟨?_, ht⟩, rfl⟩
      cases k
      all_goals
        simp only [GameState.extraTarget, Bool.and_eq_true, decide_eq_true_eq] at ht
      · exact List.mem_append.mpr (Or.inl ht.1.1)
      · exact List.mem_append.mpr (Or.inl ht.1.1)
      · exact List.mem_append.mpr (Or.inr ht.1)
      · exact List.mem_append.mpr (Or.inl ht.1.1)
      · exact List.mem_append.mpr (Or.inl ht.1.1)
      · exact List.mem_append.mpr (Or.inr ht.1)
      · simp at ht
    · right; right; right
      exact List.mem_map.mpr ⟨b, hb, rfl⟩

/-- A card that is played with a legal pick for its additional cost takes nothing off its cost for
the objects it chooses. -/
theorem chooseCut_of_extraOk {s : GameState} {p : PlayerId} {c : ObjId} {ts : List ObjId}
    (h : s.extraOk p c ts = true) : s.chooseCut p c ts = 0 := by
  unfold GameState.chooseCut
  by_cases hsp : (s.cardDef? c).any (·.hasType .spell) = true
  · -- a Spell has no additional cost to play it: the only pick is none
    have : ts = [] := by
      unfold GameState.extraOk at h
      cases hx : (s.cardDef? c).bind (·.playExtra) with
      | none => rw [hx] at h; simpa [List.isEmpty_iff] using h
      | some kb =>
        rw [hx] at h
        cases ts with
        | nil => rfl
        | cons t tl =>
          cases tl with
          | nil =>
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
            rw [hsp] at h
            exact absurd h.2 (by simp)
          | cons _ _ => simp at h
    subst this
    simp [hsp]
  · simp [hsp]

/-- A legal pick for the additional cost of a card is one of the picks worth trying. -/
theorem extraOk_mem_playTargets {s : GameState} {p : PlayerId} {c : ObjId} {d : CardDef}
    {ts : List ObjId} (hd : s.cardDef? c = some d) (h : s.extraOk p c ts = true) :
    ts ∈ playTargets s p c d := by
  rw [mem_playTargets]
  unfold GameState.extraOk at h
  rw [hd] at h
  simp only [Option.bind_some] at h
  cases hx : d.playExtra with
  | none =>
    rw [hx] at h
    simp only [List.isEmpty_iff] at h
    exact Or.inl h
  | some kb =>
    rw [hx] at h
    obtain ⟨k, b⟩ := kb
    cases ts with
    | nil => exact Or.inl rfl
    | cons t tl =>
      cases tl with
      | nil =>
        simp only [Bool.and_eq_true] at h
        exact Or.inr (Or.inr (Or.inl ⟨k, b, t, rfl, rfl, h.1⟩))
      | cons _ _ => simp at h

/-- A card can be discarded as a play cost only from the player's hand. The card being played
has already left its previous zone for the Chain (CR 353, 357.2, 423.1). -/
def GameState.playDiscardOk (s : GameState) (p : PlayerId) (c : ObjId) : Option ObjId → Bool
  | none => true
  | some id =>
    (s.cardDef? c).any (·.discardToPlay) && id != c && (s.zone (.player p .hand)).contains id

/-- Leave the optional discard unpaid, or select one of the hand cards that can pay it. -/
def GameState.playDiscards (s : GameState) (p : PlayerId) (c : ObjId) : List (Option ObjId) :=
  none :: (if (s.cardDef? c).any (·.discardToPlay) then
    ((s.zone (.player p .hand)).filter (· != c)).map some else [])

/-- All and only the legal discard choices are listed. -/
theorem GameState.mem_playDiscards (s : GameState) (p : PlayerId) (c : ObjId) (o : Option ObjId) :
    o ∈ s.playDiscards p c ↔ s.playDiscardOk p c o = true := by
  cases o with
  | none => simp [playDiscards, playDiscardOk]
  | some id =>
    by_cases h : (s.cardDef? c).any (·.discardToPlay) = true
    · simp [playDiscards, playDiscardOk, h, and_comm]
    · simp [playDiscards, playDiscardOk, h]

/-- Every way the player can play a card from a permitted zone: each card with each payment that pays its
cost, and each pick of targets, that the Pool covers. -/
def legalPlays (s : GameState) (p : PlayerId) : List Action :=
  (s.playSources p).flatMap (fun c =>
    match s.cardDef? c with
    | some d =>
      (s.directOptions p c d).flatMap (fun (flow, cost) =>
        (playTargets s p c d).flatMap (fun ts =>
          ((s.playPaymentsOfT p c d cost ts).filter
            (fun pay => decide (PlayOk s p c pay ts flow))).flatMap
            (fun pay => (s.playDiscards p c).map
              (fun discard => ⟨.player p, .playCard c pay ts flow discard⟩))))
    | none => [])

/-- The plays listed are exactly the card, payment, targets and base-cost choice that can be played. -/
theorem mem_legalPlays (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalPlays s p ↔ ∃ c pay ts flow discard,
      a = ⟨.player p, .playCard c pay ts flow discard⟩ ∧
      c ∈ s.playSources p ∧ PlayOk s p c pay ts flow ∧ s.playDiscardOk p c discard = true := by
  unfold legalPlays
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, ha⟩
    cases hd : s.cardDef? c with
    | none => simp [hd] at ha
    | some d =>
      simp only [hd, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at ha
      obtain ⟨⟨flow, cost⟩, -, ts, -, pay, ⟨-, hok⟩, discard, hdiscard, rfl⟩ := ha
      exact ⟨c, pay, ts, flow, discard, rfl, hc, hok, (s.mem_playDiscards p c discard).mp hdiscard⟩
  · rintro ⟨c, pay, ts, flow, discard, rfl, hc, hok, hdiscard⟩
    have hdc : ∃ d cost, s.cardDef? c = some d ∧ (flow, cost) ∈ s.directOptions p c d ∧
        s.paysForXT p c d cost ts pay = true ∧ ts ∈ playTargets s p c d := by
      rcases hok with ⟨hts, h, rfl⟩ | h | ⟨hb, rfl⟩
      · obtain ⟨o, d, cost, pool, -, -, hd, -, -, hcost, hpaid, -⟩ := playable_spec h
        refine ⟨d, cost, hd, ?_, hpaid, extraOk_mem_playTargets hd hts⟩
        simp [GameState.directOptions_of_hand (playable_mem_hand hc h), hcost]
      · obtain ⟨o, d, cost, pool, -, -, hd, -, -, hcost, hpaid, -⟩ := castable_spec h
        obtain ⟨d', e, hd', he, hok⟩ := castable_targets h
        have : d' = d := Option.some.inj (hd'.symm.trans hd)
        subst this
        exact ⟨d', cost, hd, GameState.directCost_mem hcost, hpaid,
          (mem_playTargets s p c d' ts).mpr (Or.inr (Or.inl ⟨e, he, hok⟩))⟩
      · obtain ⟨b, hts, hb'⟩ := bfPlayOk_spec hb
        obtain ⟨o, d, cost, pool, -, -, hd, -, -, hcost, hpaid, -⟩ := playable_spec hb'
        refine ⟨d, cost, hd, ?_, hpaid, (mem_playTargets s p c d ts).mpr
          (Or.inr (Or.inr (Or.inr ⟨b, hts, playable_dest hb'⟩)))⟩
        simp [GameState.directOptions_of_hand (playable_mem_hand hc hb'), hcost]
    obtain ⟨d, cost, hd, hcost, hpaid, hts⟩ := hdc
    refine ⟨c, hc, ?_⟩
    simp only [hd, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨(flow, cost), hcost, ts, hts, pay,
      ⟨(GameState.mem_playPaymentsOfT _ _ _ _ _ _ _).mpr hpaid, hok⟩,
      discard, (s.mem_playDiscards p c discard).mpr hdiscard, rfl⟩

/-- Play a card with the payment and the targets: a Spell is cast, and goes to the
Chain with the players to pass (CR 354, 311-313); a Unit or a Gear is played at once. `rest` is the
stack below the `priority` frame. -/
def applyPlayCard (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) (rest : List Frame) (flow : Option Cost := none) : Option (GameState × List Event) :=
  if castable s p c pay targets flow = true then
    (applyCast s p c pay targets flow).map
      (fun r =>
        let r' := castPay s c targets r
        ({ r'.1 with pending := .chainPass p 0 :: .priority p :: rest }, r'.2))
  else (applyPlay s p c pay).bind (fun r => payExtra s c targets r)

/-- Playing a card keeps the game well formed. -/
theorem applyPlayCard_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} {rest : List Frame} {es : List Event} (hwf : s.WF)
    (h : applyPlayCard s p c pay targets rest flow = some (s', es)) : s'.WF := by
  unfold applyPlayCard at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact ((castPay_safe s c targets (s2, es2)).wf (applyCast_wf hwf hm)).congr rfl rfl rfl rfl
  · obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (payExtra_safe h2).wf (applyPlay_wf hwf hr)

/-- Playing a card keeps the physical cards. -/
theorem applyPlayCard_physIds {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {flow : Option Cost} {targets : List ObjId} {rest : List Frame} {es : List Event}
    (hwf : s.WF) (h : applyPlayCard s p c pay targets rest flow = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  unfold applyPlayCard at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hp := applyCast_physIds hwf hm
    exact ((castPay_safe s c targets (s2, es2)).phys (applyCast_wf hwf hm)).trans hp
  · obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.mp h
    exact ((payExtra_safe h2).phys (applyPlay_wf hwf hr)).trans (applyPlay_physIds hwf hr)

/-- Playing a card keeps `OwnerOk`. -/
theorem applyPlayCard_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {flow : Option Cost} {targets : List ObjId} {rest : List Frame} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (h : applyPlayCard s p c pay targets rest flow = some (s', es)) :
    s'.OwnerOk := by
  unfold applyPlayCard at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact ((castPay_safe s c targets (s2, es2)).own (applyCast_wf hwf hm)
      (applyCast_ownerOk hwf hown hm)).congr rfl rfl
  · obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (payExtra_safe h2).own (applyPlay_wf hwf hr) (applyPlay_ownerOk hwf hown hr)

/-- Playing a card changes nothing of the turn order, the phase, the result, the rules or the
cards; the stack is the same, or the Spell's players have to pass above the `priority` frame. -/
theorem applyPlayCard_meta {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {flow : Option Cost} {targets : List ObjId} {rest : List Frame} {es : List Event}
    (h : applyPlayCard s p c pay targets rest flow = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.cards = s.cards ∧
      (s'.pending = s.pending ∨ s'.pending = .chainPass p 0 :: .priority p :: rest) := by
  unfold applyPlayCard at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨h1, h2, h3, h4, -, h6⟩ := applyCast_meta hm
    have hs := (castPay_safe s c targets (s2, es2)).same
    exact ⟨hs.config.trans h1, hs.turnOrder.trans h2, hs.phase.trans h3, hs.result.trans h4,
      (congrArg GameState.cards hs).trans h6, Or.inr rfl⟩
  · obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨h1, h2', h3, h4, h5, h6⟩ := applyPlay_meta hr
    have hs := (payExtra_safe h2).same
    exact ⟨hs.config.trans h1, hs.turnOrder.trans h2', hs.phase.trans h3, hs.result.trans h4,
      (congrArg GameState.cards hs).trans h6, Or.inl (hs.pending.trans h5)⟩

/-- A card that can be played or cast is played in the Main Phase. -/
theorem playOk_main {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} (h : PlayOk s p c pay targets flow) : s.phase = .main := by
  rcases h with ⟨-, h, -⟩ | h | ⟨h, -⟩
  · obtain ⟨-, -, -, -, hm, -⟩ := playable_spec h
    exact hm
  · obtain ⟨-, -, -, -, hm, -⟩ := castable_spec h
    exact hm
  · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h
    obtain ⟨-, -, -, -, hm, -⟩ := playable_spec hb
    exact hm

/-- A playable or castable card from a permitted zone can be played. -/
theorem applyPlayCard_isSome {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {targets : List ObjId} {rest : List Frame} (hwf : s.WF)
    (hc : c ∈ s.playSources p) (hp : PlayOk s p c pay targets flow) :
    ∃ r, applyPlayCard s p c pay targets rest flow = some r := by
  unfold applyPlayCard
  by_cases hcast : castable s p c pay targets flow = true
  · obtain ⟨r, hr⟩ := applyCast_isSome hwf hc hcast
    simp only [hcast, ite_true, hr, Option.map_some]
    exact ⟨_, rfl⟩
  · simp only [hcast]
    rcases hp with ⟨-, h, -⟩ | h | ⟨h, -⟩
    · obtain ⟨r, hr⟩ := applyPlay_isSome hwf (playable_mem_hand hc h) h
      obtain ⟨r', hr'⟩ := payExtra_isSome s c targets r
      exact ⟨r', by simp [hr, hr']⟩
    · exact absurd h hcast
    · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h
      obtain ⟨r, hr⟩ := applyPlay_isSome hwf (playable_mem_hand hc hb) hb
      obtain ⟨r', hr'⟩ := payExtra_isSome s c targets r
      exact ⟨r', by simp [hr, hr']⟩

end Riftbound

end
