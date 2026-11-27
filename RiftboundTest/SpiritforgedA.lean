module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests: Spiritforged (scenario tests of single cards)

Each test puts the cards it needs in the lab (the Main Phase of the first turn), plays the card
for exactly its cost, lets the Chain resolve, and reads what happened (as `OriginsA.lean` does).
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- The card of the player in their Base that has the identifier. -/
meta def _root_.Riftbound.GameState.inBase (s : GameState) (p : PlayerId) (code : String) :
    Option ObjId :=
  (s.zone (.player p .base)).find? (fun o => (s.cardDef? o).any (·.id.code == code))

/-- Run a scenario in the lab; it must say `true`. -/
meta def tsf (f : GameState → Option Bool) : Bool :=
  match lab with
  | some s => (f s).getD false
  | none => false

/-- A neutral main-phase fixture with all four seats available. -/
private meta def teamMain (labState : GameState) : GameState :=
  let game := GameState.empty { mode := .teamDuel, ruleSet := .coreOnly } labState.cards
  { game with
    phase := .main
    turn := 3
    active := some ⟨0⟩
    pending := [.priority ⟨0⟩]
    turnOrder := Mode.teamTurnOrder true }

-- Against the Odds can target a teammate's Unit and counts only enemy Units at that Battlefield.
#guard tsf fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let foe : PlayerId := ⟨2⟩
  let (s, field) ← putBf (teamMain labState) p "OGN-275"
  let (s, other) ← putBf s foe "OGN-276"
  let (s, ally) ← putAt s mate "OGN-051" field
  let (s, _) ← putAt s p "OGN-051" field
  let (s, _) ← putAt s foe "OGN-116" field
  let (s, _) ← putAt s foe "OGN-116" other
  let (s, spell) ← put s p "SFD-001" .hand
  let finished ← play s p spell [ally]
  return finished.mightNow ally == (s.mightNow ally).map (· + 2)

-- Bushwhack applies to friendly Units, including those played by a teammate as tokens.
#guard tsf fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let foe : PlayerId := ⟨2⟩
  let (s, spell) ← put (teamMain labState) p "SFD-004" .hand
  let casted ← play s p spell
  let ready (q : PlayerId) : Option Bool := do
    let card ← casted.tokenCard "Mech"
    let (next, _) := playInstructedTokens casted q card none 1 false
    let token ← next.firstOf q .base card.id.code
    next.tired token
  let gold ← casted.firstOf p .base "SFD-T03"
  return ready p == some false && ready mate == some false &&
    ready foe == some true && casted.tired gold == some true &&
    !({ casted with turn := casted.turn + 1 }).friendlyUnitsReady mate

-- Bushwhack can be played from Hidden on a later turn without paying its printed cost.
#guard tsf fun s => do
  let p := s.me
  let field := s.bf0
  let (s, _) ← putAt s p "OGN-051" field
  let (s, card) ← put (s.control p field) p "SFD-004" .hidden
  let hiddenOn (turn : Nat) :=
    s.modObj card (fun o => { o with hiddenAt := some field, hiddenTurn := some turn })
  let older := { (hiddenOn 0).fund p 0 with turn := 1 }
  let sameTurn := { (hiddenOn 1).fund p 0 with turn := 1 }
  let reveal (state : GameState) := legalFrameActions state |>.find? (fun a =>
    match a.kind with | .activate source .. => source == card | _ => false)
  let answer ← reveal older
  let (casting, _) ← (step 100 older answer).toOption
  let resolved := settleChain {} 12 casting
  let gold ← resolved.firstOf p .base "SFD-T03"
  return (reveal sameTurn).isNone && resolved.friendlyUnitsReady p &&
    resolved.tired gold == some true && (resolved.poolOf p).total == 0

-- Eager Drakehound needs no Accelerate payment to enter ready.
#guard tsf fun s => do
  let p := s.me
  let (s, card) ← put s p "SFD-006" .hand
  let resolved ← cast (s.fund p 3 (fury := 1)) p card ⟨3, [.fury]⟩
  let entered ← resolved.firstOf p .base "SFD-006"
  return resolved.tired entered == some false && (resolved.poolOf p).total == 0

-- Blast Corps Cadet chooses a Unit at a Battlefield only if the additional cost was paid.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let (s, card) ← put s p "SFD-013" .hand
  let (s, victim) ← putAt s q "OGN-116" s.bf0
  let (s, outside) ← put s q "OGN-116" .base
  let plain ← cast (s.rich p) p card ⟨2, []⟩
  let paid ← cast (s.rich p) p card ⟨3, [.fury]⟩ [] { pick := (· == [victim]) }
  return (plain.obj? victim).any (·.damage == 0) &&
    (paid.obj? victim).any (·.damage == 2) && (paid.obj? outside).any (·.damage == 0)

-- Ferrous Forerunner creates two exhausted 3-Might Mechs at its controller's Base.
#guard tsf fun s => do
  let p := s.me
  let (s, card) ← put s p "SFD-021" .hand
  let resolved ← play s p card
  let source ← resolved.firstOf p .base "SFD-021"
  let (dead, events) := killObj resolved source
  let finished ← fire dead events
  let mechs := (finished.zone (.player p .base)).filter
    (fun id => (finished.cardDef? id).any (·.name == "Mech"))
  return mechs.length == 2 &&
    mechs.all (fun id => finished.tired id == some true && finished.mightNow id == some 3) &&
    finished.countIn p .trash "SFD-021" == 1

-- Production Surge's discount requires a Mech controlled by the caster.
#guard tsf fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let (s, spell) ← put (teamMain labState) p "SFD-076" .hand
  let (s, _) ← put s mate "SFD-062" .base
  let (both, _) ← put s p "SFD-062" .base
  return s.energyCost? p spell == some 4 && both.energyCost? p spell == some 2

-- Vex treats her teammate's spells as friendly for both Energy and Power in Combat.
#guard tsf fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let foe : PlayerId := ⟨2⟩
  let (s, field) ← putBf (teamMain labState) p "OGN-275"
  let (s, _) ← putAt s p "SFD-146" field
  let (s, _) ← putAt s foe "OGN-051" field
  let (s, friendly) ← put s mate "OGN-024" .hand
  let (s, enemy) ← put s foe "OGN-024" .hand
  let fight := s.inShowdownAt field p
  let cost (state : GameState) (q : PlayerId) (card : ObjId) :=
    ((state.cardDef? card).bind (state.effCost q card)).map (fun c => (c.energy, c.power.length))
  return cost s mate friendly == some (3, 1) && cost s foe enemy == some (3, 1) &&
    cost fight mate friendly == some (2, 0) && cost fight foe enemy == some (4, 2)

-- Serrated Dirk's Assault follows the holder, with its printed Equip payment.
#guard tsf fun s => do
  let p := s.me
  let (s, dirk) ← put s p "SFD-009" .base
  let (s, first) ← put s p "OGN-051" .base
  let (s, second) ← put s p "OGN-051" .base
  let (s, angleShot) ← put s p "SFD-011" .hand
  let pay : RunePool.Payment := ⟨0, [.fury]⟩
  let equipped ← activate s p dirk 0 [first] pay
  let transferred ← play equipped p angleShot [second, dirk] { fromEnd := some 1 }
  return (activate equipped p dirk 0 [second] pay).isNone &&
    s.kwAmount first .assault == 0 && equipped.kwAmount first .assault == 2 &&
    equipped.kwAmount second .assault == 0 && transferred.kwAmount first .assault == 0 &&
    transferred.kwAmount second .assault == 2

-- Hidden Sudden Storm selects a Unit at the Battlefield where it was hidden.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, _) ← putAt (s.control p field) p "OGN-051" field
  let (s, beside) ← putAt s q "OGN-116" field
  let (s, other) ← putBf s q "OGN-276"
  let (s, away) ← putAt s q "OGN-116" other
  let (s, hidden) ← put s p "SFD-017" .hidden
  let s := s.modObj hidden (fun o => { o with hiddenAt := some field, hiddenTurn := some 0 })
  let waiting := { (s.fund p 0) with turn := 1 }
  let reveal (targets : List ObjId) := legalFrameActions waiting |>.find? (fun a =>
    match a.kind with | .activate source _ _ picked .. => source == hidden && picked == targets | _ => false)
  let answer ← reveal [beside]
  let (casting, _) ← (step 100 waiting answer).toOption
  let finished := settleChain {} 12 casting
  return (finished.obj? beside).any (·.damage == 2) && (reveal [away]).isNone

-- Rengar can join an attack as a Reaction with another item already on the Chain.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s q "OGN-275"
  let (s, attacker) ← put s p "OGN-051" .base
  let (s, _) ← putAt (s.control q field) q "OGN-116" field
  let (s, rengar) ← put s p "SFD-025" .hand
  let s := s.modObj attacker (fun o => { o with exhausted := false })
  let (showdown, _) ← (step 100 s ⟨.player p, .standardMove attacker (.battlefield field)⟩).toOption
  let (closed, spell) ← onChain showdown q "OGN-004"
  let ready := { (closed.fund p 3 (fury := 1)) with pending := .chainPass p 0 :: showdown.pending }
  let (answered, _) ← (step 100 ready ⟨.player p, .playCard rengar ⟨3, [.fury]⟩ [field]⟩).toOption
  let joined ← (answered.unitsAt field).find? (fun id =>
    (answered.cardDef? id).any (fun d => d.id == cid "SFD-025"))
  return answered.kwAmount joined .assault == 2 && (answered.zone .chain).contains spell

-- Quick-Draw (Sterak's Gage, SFD-056): played, it attaches itself to a unit its player controls
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-056" .hand
  let (s2, u) ← put s1 s.me "OGN-001" .base
  let s3 ← play s2 s.me g
  let gear := s3.inBase s.me "SFD-056"
  return gear.any (fun o => (s3.obj? o).any (·.attached == some u))
-- ... and not to a unit of the opponent
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-056" .hand
  let (s2, _) ← put s1 s.you "OGN-001" .base
  let s3 ← play s2 s.me g
  let gear := s3.inBase s.me "SFD-056"
  return gear.any (fun o => (s3.obj? o).any (·.attached == none))

-- Weaponmaster (Combat Chef, SFD-092) discounts [A]. Brutalizer still requires Calm Power.
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-042" .base
  let s3 ← play s2 s.me chef
  let unfunded ← cast (s2.fund s.me 5) s.me chef (payOf s2 chef)
  let chef' := s3.inBase s.me "SFD-092"
  return chef'.any (fun c => (s3.obj? gear).any (·.attached == some c)) &&
    (s3.poolOf s.me).calm == 11 && (s3.poolOf s.me).energy == 7 &&
    (unfunded.obj? gear).any (·.attached.isNone)
-- Skyfall of Areion retains both its Energy and Fury cost.
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-030" .base
  let s3 ← play s2 s.me chef
  let chef' := s3.inBase s.me "SFD-092"
  return chef'.any (fun c => (s3.obj? gear).any (·.attached == some c)) &&
    (s3.poolOf s.me).fury == 11 && (s3.poolOf s.me).energy == 6
-- ... and if the Energy is not there, the Equipment stays where it is
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-030" .base
  let s3 ← cast (s2.fund s.me 5 (fury := 1)) s.me chef (payOf s2 chef)
  return (s3.obj? gear).any (·.attached == none)
-- "even if it's already attached": the Equipment of another unit moves to the new one
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-042" .base
  let (s3, other) ← put s2 s.me "OGN-001" .base
  let s4 := s3.modObj gear (fun o => { o with attached := some other })
  let s5 ← play s4 s.me chef
  let chef' := s5.inBase s.me "SFD-092"
  return chef'.any (fun c => (s5.obj? gear).any (·.attached == some c))
-- the Equipment of the opponent is not one of "your Equipment"
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.you "SFD-042" .base
  let s3 ← play s2 s.me chef
  return (s3.obj? gear).any (·.attached == none)
-- no Equipment: the unit is simply played
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let s2 ← play s1 s.me chef
  return s2.countIn s.me .base "SFD-092" == 1

private meta def weaponmasterPlay (code : String) : Bool :=
  tsf fun s => do
    let p := s.me
    let (s, card) ← put s p code .hand
    let (s, original) ← put s p "OGN-135" .base
    let (s, cape) ← put s p "SFD-190" .base
    let s := s.modObj cape (fun o => { o with attached := some original })
    let payment := payOf s card
    let (first, _) ← (step 100 (s.rich p) ⟨.player p, .playCard card payment []⟩).toOption
    let actions := legalFrameActions first
    let take ← actions.find? (fun a => match a.kind with
      | .putTrigger _ [target] (.pay ..) => target == cape
      | _ => false)
    let skip ← actions.find? (fun a => match a.kind with
      | .putTrigger _ [] .skip => true
      | _ => false)
    let (accepted, _) ← (step 100 first take).toOption
    let (declined, _) ← (step 100 first skip).toOption
    let done := settleChain {} 12 accepted
    let new ← done.firstOf p .base code
    return (done.obj? cape).any (·.attached == some new) &&
      (declined.obj? cape).any (·.attached == some original) &&
      done.poolOf p == declined.poolOf p

-- Each printed Weaponmaster can move Equipment already attached and can decline without paying.
#guard weaponmasterPlay "SFD-002"
#guard weaponmasterPlay "SFD-008"
#guard weaponmasterPlay "SFD-092"
#guard weaponmasterPlay "SFD-099"
#guard weaponmasterPlay "SFD-127"

-- Armed Assailant can buy Accelerate in the same play as its Weaponmaster trigger.
#guard tsf fun s => do
  let p := s.me
  let (s, card) ← put s p "SFD-002" .hand
  let (s, cape) ← put s p "SFD-190" .base
  let payment := payOf s card
  let rich := s.rich p
  let accelerated ← cast rich p card ⟨payment.energy + 1, payment.power ++ [.fury]⟩
  let normal ← cast rich p card payment
  let a ← accelerated.firstOf p .base "SFD-002"
  let n ← normal.firstOf p .base "SFD-002"
  return accelerated.tired a == some false && normal.tired n == some true &&
    (accelerated.obj? cape).any (·.attached == some a) && (normal.obj? cape).any (·.attached == some n)

-- Quick-Draw with several friendly units: the player picks the unit
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-056" .hand
  let (s2, u) ← put s1 s.me "OGN-001" .base
  let (s3, v) ← put s2 s.me "OGN-051" .base
  let s4 ← play s3 s.me g [] { pick := fun ts => ts == [v] }
  let s5 ← play s3 s.me g [] { pick := fun ts => ts == [u] }
  let gear4 := s4.inBase s.me "SFD-056"
  let gear5 := s5.inBase s.me "SFD-056"
  return gear4.any (fun o => (s4.obj? o).any (·.attached == some v)) &&
    gear5.any (fun o => (s5.obj? o).any (·.attached == some u))
-- Weaponmaster can be declined before choosing an Equipment or putting the ability on the Chain.
#guard tsf fun s => do
  let p := s.me
  let (s1, chef) ← put s p "SFD-092" .hand
  let (s2, gear) ← put s1 p "SFD-042" .base
  let (waiting, _) ← (step 100 (s2.rich p) ⟨.player p, .playCard chef (payOf s2 chef) []⟩).toOption
  let actions := legalFrameActions waiting
  let skip ← actions.find? (fun action => match action.kind with
    | .putTrigger _ [] .skip => true
    | _ => false)
  let (declined, events) ← (step 100 waiting skip).toOption
  return actions.any (fun action => match action.kind with
      | .putTrigger _ [target] (.pay ..) => target == gear
      | _ => false) && (declined.zone .chain).isEmpty &&
    !events.any (fun | .chosenByAbility _ target => target == gear | _ => false) &&
    (declined.obj? gear).any (·.attached.isNone) && (declined.poolOf p).calm == 12
-- ... one of several Equipment, as the player picks
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, g1) ← put s1 s.me "SFD-042" .base
  let (s3, g2) ← put s2 s.me "SFD-051" .base
  let s4 ← play s3 s.me chef [] { pick := fun ts => ts == [g2] }
  return (s4.obj? g1).any (·.attached == none) && (s4.obj? g2).any (·.attached.isSome)
-- an Equip cost of one Power of any domain (Forgefire Cape) is paid in full by the discount
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-190" .base
  let s3 ← play s2 s.me chef
  return (s3.obj? gear).any (·.attached.isSome) && (s3.poolOf s.me).energy == 7
-- the unit may have left play before the ability resolves: nothing is attached, nothing is paid
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .trash
  let (s2, gear) ← put s1 s.me "SFD-030" .base
  let r ← applyAttachPaying (s2.rich s.me) s.me chef { slots := [.obj gear] } (.slot 0) .self 1
  return (r.1.obj? gear).any (·.attached == none) &&
    (r.1.poolOf s.me).energy == ((s2.rich s.me).poolOf s.me).energy
-- (the same with the unit in play: it is attached, and the Energy is paid)
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .base
  let (s2, gear) ← put s1 s.me "SFD-030" .base
  let r ← applyAttachPaying (s2.rich s.me) s.me chef { slots := [.obj gear] } (.slot 0) .self 1
  return (r.1.obj? gear).any (·.attached == some chef) &&
    (r.1.poolOf s.me).energy + 1 == ((s2.rich s.me).poolOf s.me).energy &&
    (r.1.poolOf s.me).fury + 1 == ((s2.rich s.me).poolOf s.me).fury

/-- The damage on the object. -/
meta def _root_.Riftbound.GameState.dmg (s : GameState) (u : ObjId) : Option Nat :=
  (s.obj? u).map (·.damage)

-- Against the Odds (SFD-001): +2 Might for each enemy unit at the battlefield
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-001" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, _) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, _) ← putAt s3 s.you "OGN-001" s.bf0
  let s5 ← play s4 s.me c [u]
  return s5.mightNow u == (s4.mightNow u).map (· + 4)
-- no enemy there: no bonus; and an enemy unit is not a friendly target
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-001" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, e) ← put s2 s.you "OGN-001" .base
  let s4 ← play s3 s.me c [u]
  return s4.mightNow u == s3.mightNow u && (play s3 s.me c [e]).isNone

-- Blood Rush (SFD-003): a unit has Assault 2 this turn, only that unit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-003" .hand
  let (s2, v) ← put s1 s.me "OGN-136" .base
  let (s3, w) ← put s2 s.me "OGN-136" .base
  let s4 ← play s3 s.me c [v]
  return s4.kwAmount v .assault == 2 && s4.kwAmount w .assault == 0

-- Bushwhack (SFD-004): a Gold token, and the units played this turn enter ready
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-004" .hand
  let (s2, v) ← put s1 s.me "OGN-051" .hand
  let (s2b, w) ← put s2 s.me "OGN-136" .hand
  let s3 ← play s2b s.me c
  let s4 ← play s3 s.me v
  let s5 ← play s4 s.me w
  let (t1, v2) ← put s s.me "OGN-051" .hand
  let t3 ← play t1 s.me v2
  return s3.countIn s.me .base "SFD-T03" == 1 &&
    (s5.firstOf s.me .base "OGN-051").bind s5.tired == some false &&
    (s5.firstOf s.me .base "OGN-136").bind s5.tired == some false &&
    (t3.firstOf s.me .base "OGN-051").bind t3.tired == some true

-- Detonate (SFD-005): kill a gear; its controller draws 2
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-005" .hand
  let (s2, g) ← put s1 s.me "SFD-030" .base
  let s3 ← play s2 s.me c [g]
  return s3.countIn s.me .trash "SFD-030" == 1 && s3.handN s.me == s2.handN s.me + 1 &&
    s3.handN s.you == s2.handN s.you
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-005" .hand
  let (s2, g) ← put s1 s.you "SFD-030" .base
  let s3 ← play s2 s.me c [g]
  return s3.countIn s.you .trash "SFD-030" == 1 && s3.handN s.you == s2.handN s.you + 2 &&
    s3.handN s.me == s2.handN s.me - 1

-- Gem Jammer (SFD-007): the unit the player picks has Ganking this turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-007" .hand
  let (s2, v) ← put s1 s.you "OGN-051" .base
  let (s3, w) ← put s2 s.me "OGN-051" .base
  let s4 ← play s3 s.me c [] { pick := fun ts => ts == [v] }
  return s4.hasKw v .ganking && !s4.hasKw w .ganking

-- Battering Ram (SFD-012): 1 less for each card played this turn, never below 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-012" .hand
  let (s2, a) ← put s1 s.me "OGN-051" .hand
  let (s3, b) ← put s2 s.me "OGN-051" .hand
  let s4 ← play s3 s.me a
  let s5 ← play s4 s.me b
  let (s6, d) ← put s5 s.me "OGN-051" .hand
  let (s7, e) ← put s6 s.me "OGN-051" .hand
  let (s8, f) ← put s7 s.me "OGN-051" .hand
  let (s9, g) ← put s8 s.me "OGN-051" .hand
  let t1 ← play s9 s.me d
  let t2 ← play t1 s.me e
  let t3 ← play t2 s.me f
  let t4 ← play t3 s.me g
  return s1.energyCost? s.me c == some 5 && s4.energyCost? s.me c == some 4 &&
    s5.energyCost? s.me c == some 3 && t3.energyCost? s.me c == some 1 &&
    t4.energyCost? s.me c == some 1

-- Sudden Storm (SFD-017): 2 damage to a unit at a battlefield, 4 if it is attacking
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-017" .hand
  let (s2, u) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, _) ← putAt s2 s.you "OGN-051" s.bf0
  let a ← play s3 s.me c [u]
  let b ← play (s3.inShowdownAt s.bf0 s.me) s.me c [u]
  return a.dmg u == some 2 && b.dmg u == some 4
-- not a unit at a base
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-017" .hand
  let (s2, u) ← put s1 s.you "OGN-001" .base
  return (play s2 s.me c [u]).isNone

-- Piercing Light (SFD-023): 2 to a unit at a battlefield, then 2 to up to one other unit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-023" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, v) ← put s2 s.you "OGN-001" .base
  let s4 ← play s3 s.me c [u, v]
  let s5 ← play s3 s.me c [u]
  return s4.dmg u == some 2 && s4.dmg v == some 2 && s5.dmg u == some 2 && s5.dmg v == some 0 &&
    (play s3 s.me c [u, u]).isNone && (play s3 s.me c []).isNone
-- ... with no other unit, only the first is hit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-023" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let s3 ← play s2 s.me c [u]
  return s3.dmg u == some 2

-- When Flash moves the first target away, Piercing Light still deals its second hit.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let (s, first) ← putAt (s.control q s.bf0) q "OGN-001" s.bf0
  let (s, second) ← put s q "OGN-001" .base
  let (s, spell) ← put s p "SFD-023" .hand
  let (s, flash) ← put s q "OGS-011" .hand
  let (chain, _) ← (step 100 (s.rich p)
    ⟨.player p, .playCard spell ⟨2, [.fury]⟩ [first, second]⟩).toOption
  let (response, _) ← (step 100 chain ⟨.player p, .pass⟩).toOption
  let settled ← play response q flash [first]
  return settled.where? first == some (.player q .base) && settled.dmg first == some 0 &&
    settled.dmg second == some 2

/-- The player has `n` points. -/
meta def _root_.Riftbound.GameState.setPoints (s : GameState) (p : PlayerId) (n : Nat) :
    GameState :=
  { s with points := s.points.insert p.n n }

/-- The player keeps the card `c` and the first `n` other cards of their hand. -/
meta def _root_.Riftbound.GameState.keepHand (s : GameState) (p : PlayerId) (c : ObjId) (n : Nat) :
    GameState :=
  let l := s.zone (.player p .hand)
  s.setZone (.player p .hand) (l.filter (· == c) ++ (l.filter (· != c)).take n)

-- Dunebreaker (SFD-027): enters ready with two or fewer cards in hand
#guard tsf fun s => do
  let (s1, d) ← put s s.me "SFD-027" .hand
  let a ← play (s1.keepHand s.me d 1) s.me d
  let a2 ← play (s1.keepHand s.me d 2) s.me d
  let b ← play (s1.keepHand s.me d 3) s.me d
  return (a.firstOf s.me .base "SFD-027").bind a.tired == some false &&
    (a2.firstOf s.me .base "SFD-027").bind a2.tired == some false &&
    (b.firstOf s.me .base "SFD-027").bind b.tired == some true
-- ... and draws 2 when it holds
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, _) ← putAt s1 s.me "SFD-027" bf
  let r ← fire s2 [.scored s.me bf false]
  return r.handN s.me == s2.handN s.me + 2

-- Disarming Rake (SFD-032): when played, the player may kill a gear
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-032" .hand
  let (s2, g) ← put s1 s.you "SFD-030" .base
  let a ← play s2 s.me c
  let b ← play s2 s.me c [] { yes := false }
  return a.countIn s.you .trash "SFD-030" == 1 && b.countIn s.you .base "SFD-030" == 1 &&
    (a.obj? g).isNone
-- (with no gear, the unit is simply played)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-032" .hand
  let a ← play s1 s.me c
  return a.countIn s.me .base "SFD-032" == 1

-- Guardian of the Passage (SFD-035): when it holds, a unit or gear (not a spell) from the Trash
-- may be targeted upon finalization or the player can decline the trigger.
#guard tsf fun s => do
  let p := s.me
  let (s, bf) ← putBf s p "OGN-280"
  let (s, _) ← putAt s p "SFD-035" bf
  let (s, spell) ← put s p "OGN-004" .trash
  let (s, unit) ← put s p "OGN-051" .trash
  let (s, gear) ← put s p "SFD-056" .trash
  let (s, opposing) ← put s s.you "SFD-056" .trash
  let holds := [Event.scored p bf false]
  let picks ← firePicks s holds
  let a ← fire s holds { pick := (· == [gear]) }
  let b ← fire s holds { yes := false }
  return picks.contains gear && picks.contains unit && !picks.contains spell && !picks.contains opposing &&
    a.countIn p .hand "SFD-056" == s.countIn p .hand "SFD-056" + 1 &&
    b.zone (.player p .trash) == s.zone (.player p .trash)

-- Aspiring Engineer chooses a Gear while the ability is put on the Chain.
#guard tsf fun s => do
  let p := s.me
  let (s, engineer) ← put s p "SFD-061" .hand
  let (s, gear) ← put s p "SFD-056" .trash
  let (s, unit) ← put s p "OGN-051" .trash
  let (s, rivalGear) ← put s s.you "SFD-056" .trash
  let deciding ← castStop s p engineer
  let action ← (legalFrameActions deciding).find? (fun act => match act.kind with
    | .putTrigger _ [id] (.pay ..) => id == gear
    | _ => false)
  let (queued, _) ← (step 100 deciding action).toOption
  let (removed, _) ← moveObj queued gear (.player p .mainDeck)
  let found := settleChain {} 12 queued
  let lost := settleChain {} 12 removed
  return !(legalFrameActions deciding).any (fun act => match act.kind with
      | .putTrigger _ [id] (.pay ..) => id == unit || id == rivalGear
      | _ => false) &&
    found.countIn p .hand "SFD-056" == s.countIn p .hand "SFD-056" + 1 &&
    lost.countIn p .hand "SFD-056" == s.countIn p .hand "SFD-056"

-- Ribbon Dancer (SFD-038): when it moves to a battlefield, another friendly unit has +1 Might
#guard tsf fun s => do
  let (s1, d) ← putAt s s.me "SFD-038" s.bf0
  let (s2, v) ← put s1 s.me "OGN-051" .base
  let (s3, e) ← put s2 s.me "SFD-038" .base
  let picks ← firePicks s2 [.standardMoved d (some s.bf0)]
  let a ← fire s2 [.standardMoved d (some s.bf0)] { pick := fun ts => ts == [v] }
  let b ← fire s3 [.standardMoved e none] { pick := fun ts => ts == [v] }
  return picks.contains v && !picks.contains d && a.mightNow v == (s2.mightNow v).map (· + 1) &&
    b.mightNow v == s3.mightNow v

-- Thwonk! (SFD-040): stun an attacking unit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-040" .hand
  let (s2, u) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, _) ← putAt s2 s.you "OGN-051" s.bf0
  let r ← play (s3.inShowdownAt s.bf0 s.me) s.me c [u]
  return (r.obj? u).map (·.stunned) == some true && (play s3 s.me c [u]).isNone

-- Emperor's Divide (SFD-043): any number of friendly units at a battlefield move to their base
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-043" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, v) ← putAt s2 s.me "OGN-001" s.bf0
  let (s4, e) ← putAt s3 s.you "OGN-051" s.bf0
  let (s5, w) ← put s4 s.me "OGN-051" .base
  let atBf (x : GameState) (o : ObjId) : Bool := (x.obj? o).any (·.loc == some s.bf0)
  let (lo, hi) := if u.n < v.n then (u, v) else (v, u)
  let none_ ← play s5 s.me c [s.bf0]
  let one ← play s5 s.me c [s.bf0, lo]
  let both ← play s5 s.me c [s.bf0, lo, hi]
  return atBf none_ u && atBf none_ v && !atBf one lo && atBf one hi &&
    !atBf both u && !atBf both v && atBf both e &&
    (play s5 s.me c [s.bf0, hi, lo]).isNone && (play s5 s.me c [s.bf0, e]).isNone &&
    (play s5 s.me c [s.bf0, w]).isNone && (play s5 s.me c [s.bf0, lo, lo]).isNone &&
    (play s5 s.me c []).isNone

-- Simian Ancestor readies when its controller buffs it, even in a team game.
#guard tsf fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let foe : PlayerId := ⟨2⟩
  let (s, unit) ← put (teamMain labState) p "SFD-047" .base
  let exhausted := s.tire unit
  let buff (giver : PlayerId) := applyPrim exhausted giver unit {} (.buff .self)
  let (own, ownEvents) ← buff p
  let (ally, allyEvents) ← buff mate
  let (enemy, enemyEvents) ← buff foe
  let ownDone ← fire own ownEvents
  let allyDone ← fire ally allyEvents
  let enemyDone ← fire enemy enemyEvents
  let (twice, repeated) ← applyPrim ownDone p unit {} (.buff .self)
  return ownEvents == [.buffedBy unit p] && allyEvents == [.buffedBy unit mate] &&
    enemyEvents == [.buffedBy unit foe] && ownDone.tired unit == some false &&
    allyDone.tired unit == some true && enemyDone.tired unit == some true &&
    (allyDone.obj? unit).any (·.buffed) && (enemyDone.obj? unit).any (·.buffed) &&
    repeated.isEmpty && (twice.obj? unit).any (·.buffed)

-- Janna, Savior (SFD-053), at a battlefield when played: heal my units here, and move an enemy
-- unit from here to its base
#guard tsf fun s => do
  let (s1, j) ← putAt s s.me "SFD-053" s.bf0
  let (s2, a) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let s4 := s3.modObj a (fun o => { o with damage := 3 })
  let r ← fire s4 [.played s.me j] { pick := (· == [e]) }
  return r.dmg a == some 0 && (r.obj? e).any (·.loc.isNone) &&
    (r.obj? j).any (·.loc == some s.bf0)

-- The target is chosen on the Chain. Moving it away does not let Janna select a replacement
-- and does not stop her from healing every damaged Unit she still controls there.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, janna) ← putAt (s.control p field) p "SFD-053" field
  let (s, first) ← putAt s p "OGN-001" field
  let (s, second) ← putAt s p "OGN-001" field
  let (s, atBase) ← put s p "OGN-001" .base
  let (s, foe) ← putAt s q "OGN-001" field
  let (s, another) ← putAt s q "OGN-001" field
  let s := (setBaseMight 130 s first).1
  let s := (s.markDamage first 105 (some q)).markDamage second 2 (some q)
  let s := (s.markDamage atBase 2 (some q)).markDamage another 1 (some p)
  let pending := insertTriggers (s.detect [.played p janna]) (below s.pending)
  let (window, _) ← (advance 100 { s with pending } []).toOption
  let withTarget : Action := ⟨.player p, .putTrigger 0 [foe] (.pay [])⟩
  let withoutTarget : Action := ⟨.player p, .putTrigger 0 [] (.pay [])⟩
  let (chain, chose) ← (step 100 window withTarget).toOption
  let (emptyChoice, _) ← (step 100 window withoutTarget).toOption
  let noMove := settleChain {} 12 emptyChoice
  let fromBase := settleChain {} 12 (moveHome chain janna).1
  let noSource := settleChain {} 12 (sendObj .trash chain janna).1
  let fled := (moveHome chain foe).1
  let .chainPass firstSeat _ :: _ := fled.pending | none
  let (passed, _) ← (step 100 fled ⟨.player firstSeat, .pass⟩).toOption
  let .chainPass lastSeat _ :: _ := passed.pending | none
  let (result, events) ← (step 100 passed ⟨.player lastSeat, .pass⟩).toOption
  let heals := events.filter (fun | .healed .. => true | _ => false)
  return (legalFrameActions window).contains withTarget &&
    (legalFrameActions window).contains withoutTarget && chose.contains (.chosenByAbility p foe) &&
    noMove.dmg first == some 0 && (noMove.obj? foe).any (·.loc == some field) &&
    fromBase.dmg atBase == some 0 && fromBase.dmg first == some 105 &&
    (fromBase.obj? foe).any (·.loc == some field) &&
    noSource.dmg first == some 105 && (noSource.obj? foe).any (·.loc == some field) &&
    heals.length == 2 && heals.contains (.healed first 105) && heals.contains (.healed second 2) &&
    result.dmg first == some 0 && result.dmg second == some 0 &&
    result.damageMarks[first.n]?.isNone && result.damageMarks[second.n]?.isNone &&
    result.dmg atBase == some 2 && result.dmg another == some 1 &&
    (result.obj? another).any (·.loc == some field)

-- Bubble Bot (SFD-062): when played, ready another friendly Mech (not itself, not a non-Mech)
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-062" .hand
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, o) ← put s2 s.me "OGN-051" .base
  let s4 := (s3.tire m).tire o
  let r ← play s4 s.me b [] { pick := fun ts => ts == [m] }
  let picks ← firePicks (s4.rich s.me) [.played s.me b]
  return r.tired m == some false && r.tired o == some true && !picks.contains o

-- Breakneck Mech (SFD-071): friendly Mechs have Deflect and Ganking; it enters ready if there is
-- another Mech
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-071" .base
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, o) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "SFD-062" .base
  return s4.hasKw m .deflect && s4.hasKw m .ganking && !s4.hasKw o .deflect &&
    !s4.hasKw e .ganking && b != m
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-071" .hand
  let (s2, _) ← put s1 s.me "SFD-062" .base
  let (t1, c) ← put s s.me "SFD-071" .hand
  let a ← play s2 s.me b
  let r ← play t1 s.me c
  return (a.firstOf s.me .base "SFD-071").bind a.tired == some false &&
    (r.firstOf s.me .base "SFD-071").bind r.tired == some true

-- Dropboarder (SFD-072): when played with two or more gear, it readies itself
#guard tsf fun s => do
  let (s1, d) ← put s s.me "SFD-072" .hand
  let (s2, _) ← put s1 s.me "SFD-030" .base
  let (s3, _) ← put s2 s.me "SFD-030" .base
  let a ← play s3 s.me d
  let (t1, c) ← put s s.me "SFD-072" .hand
  let (t2, _) ← put t1 s.me "SFD-030" .base
  let r ← play t2 s.me c
  return (a.firstOf s.me .base "SFD-072").bind a.tired == some false &&
    (r.firstOf s.me .base "SFD-072").bind r.tired == some true

-- Production Surge (SFD-076): costs 2 less with a Mech; a Mech token, and draw 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-076" .hand
  let (s2, _) ← put s1 s.me "SFD-062" .base
  let r ← play s2 s.me c
  return s1.energyCost? s.me c == some 4 && s2.energyCost? s.me c == some 2 &&
    r.countNamed s.me .base "Mech" == 1 && r.handN s.me == s2.handN s.me

-- Rumble, Scrapper (SFD-089): friendly Mechs have +1 Might; a Mech token when it holds
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, e) ← put s2 s.you "SFD-062" .base
  let (s4, _) ← putAt s3 s.me "SFD-089" bf
  let r ← fire s4 [.scored s.me bf false]
  return s4.mightNow m == (s3.mightNow m).map (· + 1) && s4.mightNow e == s3.mightNow e &&
    r.countNamed s.me .base "Mech" == 1

-- Buhru Captain (SFD-091): when played, the player may draw 1 or buff it
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-091" .hand
  let d ← play s1 s.me c [] { fromEnd := some 1 }
  let b ← play s1 s.me c [] { fromEnd := some 2 }
  let n ← play s1 s.me c [] { yes := false }
  let buffed (x : GameState) :=
    (x.firstOf s.me .base "SFD-091").bind (fun o => (x.obj? o).map (·.buffed))
  return buffed d == some false && buffed b == some true && buffed n == some false &&
    d.handN s.me == b.handN s.me + 1 && d.handN s.me == n.handN s.me + 1

-- Direwing (SFD-094): enters ready if the player controls another Dragon
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-094" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let a ← play s2 s.me c
  let (t1, c2) ← put s s.me "SFD-094" .hand
  let r ← play t1 s.me c2
  return (a.firstOf s.me .base "SFD-094").bind a.tired == some false &&
    (r.firstOf s.me .base "SFD-094").bind r.tired == some true

-- Laurent Bladekeeper (SFD-096) has Ganking
#guard match RiftboundCards.db.find? ⟨"SFD-096"⟩ with
  | some c => c.hasKeyword .ganking && c.runs
  | none => false

-- Yordle Explorer (SFD-100): draw 1 when the player plays a card with two or more Power
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-100" .base
  let (s2, hi) ← put s1 s.me "OGN-029" .trash
  let (s3, lo) ← put s2 s.me "OGN-051" .trash
  let a ← fire s3 [.spellResolved s.me hi]
  let b ← fire s3 [.played s.me lo]
  let c ← fire s3 [.spellResolved s.you hi]
  return a.handN s.me == s3.handN s.me + 1 && b.handN s.me == s3.handN s.me &&
    c.handN s.me == s3.handN s.me

-- Petricite Monument (SFD-104): friendly units have Deflect
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-104" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, e) ← put s2 s.you "OGN-051" .base
  return s3.hasKw u .deflect && !s3.hasKw e .deflect

-- Show of Strength (SFD-106): draw 1 for each friendly Mighty unit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-106" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let (s3, _) ← put s2 s.me "OGN-001" .base
  let (s4, _) ← put s3 s.me "OGN-051" .base
  let (s5, _) ← put s4 s.you "OGN-001" .base
  let r ← play s5 s.me c
  return r.handN s.me == s5.handN s.me - 1 + 2

-- Show of Strength reads the Might the passive abilities give: Draven (3 Might, +1 for each point
-- of his player) with a buff has 5 Might with one point (Mighty), but 4 with none
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-106" .hand
  let (s2, d) ← put s1 s.me "OGN-028" .base
  let none_ := (s2.buff d).setPoints s.me 0
  let one := (s2.buff d).setPoints s.me 1
  let a ← play one s.me c
  let b ← play none_ s.me c
  return one.mightNow d == some 5 && none_.mightNow d == some 4 &&
    a.handN s.me == one.handN s.me - 1 + 1 && b.handN s.me == none_.handN s.me - 1

-- Ownership and the shared team side do not determine who draws or satisfies "you control".
#guard tsf fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) initial).toOption
  let p := s.me
  let mate ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← s.players.find? (fun q => !config.mode.sameSide p q)
  let (s, detonate) ← put s p "SFD-005" .hand
  let (s, gear) ← put s enemy "SFD-030" .base
  let (s, ownGear) ← put s p "SFD-030" .base
  let s := s.modObj gear (fun o => { o with controller := mate })
  let sent ← play s p detonate [gear]
  let (s, dropboarder) ← put s p "SFD-072" .hand
  let pitched ← play s p dropboarder
  let (more, _) ← put s p "SFD-030" .base
  let twoGear ← play more p dropboarder
  let (s, direwing) ← put s p "SFD-094" .hand
  let (s, _) ← put s mate "OGN-001" .base
  let otherDragon ← play s p direwing
  let (s, ownDragon) ← put s p "OGN-001" .base
  let ready ← play s p direwing
  let (s, strength) ← put s p "SFD-106" .hand
  let drawn ← play s p strength
  return sent.handN mate == s.handN mate + 2 && sent.handN enemy == s.handN enemy &&
    sent.countIn enemy .trash "SFD-030" == 1 && (sent.obj? ownGear).isSome &&
    (pitched.inBase p "SFD-072").bind pitched.tired == some true &&
    (twoGear.inBase p "SFD-072").bind twoGear.tired == some false &&
    (otherDragon.inBase p "SFD-094").bind otherDragon.tired == some true &&
    (ready.inBase p "SFD-094").bind ready.tired == some false &&
    drawn.handN p == s.handN p && (drawn.obj? ownDragon).isSome

-- Jaull-Fish (SFD-103) counts a unit that is Mighty by a passive ability (Draven with a point)
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-103" .hand
  let (s2, d) ← put s1 s.me "OGN-028" .base
  let base := (s2.buff d).setPoints s.me 0
  let mighty := (s2.buff d).setPoints s.me 1
  let cost (x : GameState) : Option Nat := ((x.cardDef? j).bind (x.effCost s.me j)).map (·.energy)
  return (cost mighty).map (· + 2) == cost base && cost base == some 7

-- The filters read the Might the passive abilities give, with their floors: Leona, Zealot (OGN-079)
-- takes 8 Might from a stunned enemy unit here, to a minimum of 1
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "OGN-079" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, f) ← putAt s2 s.you "OGN-001" s.bf0
  let st := s3.modObj e (fun o => { o with stunned := true })
  let env : Env := Env.empty.withMight st.mightTable
  let small (x : GameState) (id : ObjId) : Bool :=
    Filter.holds x id env id (.might .le (.const 3)) == some true
  let lethal (x : GameState) (id : ObjId) : Bool :=
    Filter.holds x id env id .lethal == some true
  let hurt := st.modObj e (fun o => { o with damage := 1 })
  let env2 : Env := Env.empty.withMight hurt.mightTable
  return st.mightNow e == some 1 && st.mightNow f == s3.mightNow f && small st e && !small st f &&
    Filter.holds hurt e env2 e .lethal == some true &&
    Filter.holds hurt f env2 f .lethal == some false && !lethal st e

-- Marching Orders (SFD-114): a friendly unit and an enemy unit at a battlefield deal damage
-- equal to their Might to each other
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-114" .hand
  let (s2, f) ← put s1 s.me "OGN-001" .base
  let (s3, e) ← putAt s2 s.you "OGN-051" s.bf0
  let r ← play s3 s.me c [f, e]
  return r.dmg f == some 2 && (r.obj? e).isNone && (play s3 s.me c [e, f]).isNone

-- Danger Zone (SFD-182): friendly Mechs have +1 Might this turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-182" .hand
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, o) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "SFD-062" .base
  let r ← play s4 s.me c
  return r.mightNow m == (s4.mightNow m).map (· + 1) && r.mightNow o == s4.mightNow o &&
    r.mightNow e == s4.mightNow e

-- (review) Detonate: if the gear is gone when the spell resolves, nobody draws
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-005" .hand
  let (s2, g) ← put s1 s.me "SFD-030" .base
  let s3 ← match step 100 (s2.rich s.me) ⟨.player s.me, .playCard c (payOf s2 c) [g]⟩ with
    | .ok (x, _) => some x
    | .error _ => none
  let s4 := (killObj s3 g).1
  let s5 := settleChain {} 12 s4
  return s5.handN s.me == s3.handN s.me && s5.handN s.you == s3.handN s.you
-- (review) Against the Odds and Emperor's Divide look at the one battlefield only
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-001" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, b2) ← putBf s2 s.you "SFD-216"
  let (s4, _) ← putAt s3 s.you "OGN-001" b2
  let (s5, _) ← put s4 s.you "OGN-001" .base
  let r ← play s5 s.me c [u]
  return r.mightNow u == s5.mightNow u
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-043" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, b2) ← putBf s2 s.me "SFD-216"
  let (s4, w) ← putAt s3 s.me "OGN-051" b2
  let r ← play s4 s.me c [s.bf0, u]
  return (r.obj? u).any (·.loc.isNone) && (r.obj? w).any (·.loc == some b2) &&
    (play s4 s.me c [s.bf0, w]).isNone
-- (review) Yordle Explorer: a card with exactly one Power does not draw
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-100" .base
  let (s2, one) ← put s1 s.me "SFD-004" .trash
  let a ← fire s2 [.played s.me one]
  return a.handN s.me == s2.handN s.me
-- (review) Production Surge: an enemy Mech does not lower the cost
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-076" .hand
  let (s2, _) ← put s1 s.you "SFD-062" .base
  return s2.energyCost? s.me c == some 4
-- (review) Bushwhack: the Gold token is exhausted, and a Mech token enters ready
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-004" .hand
  let (s2, p) ← put s1 s.me "SFD-076" .hand
  let s3 ← play s2 s.me c
  let s4 ← play s3 s.me p
  let gold := s4.firstOf s.me .base "SFD-T03"
  let mech := (s4.zone (.player s.me .base)).find? (fun o =>
    (s4.cardDef? o).any (·.name == "Mech"))
  return gold.bind s4.tired == some true && mech.bind s4.tired == some false
-- (review) Piercing Light with Repeat paid: the effect is done twice
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-023" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let pay := payOf s2 c
  let pick : SpellPick := .withCosts (.thenRepeat .plain 1 .plain) false 1
  let r ← cast (s2.rich s.me) s.me c ⟨pay.energy + 2, pay.power ++ [.fury]⟩ [u, u] (pick := pick)
  return r.dmg u == some 4
-- (review) Blood Rush with Repeat paid: Assault 2 is given twice
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-003" .hand
  let (s2, v) ← put s1 s.me "OGN-136" .base
  let (s2, rival) ← put s2 s.you "OGN-136" .base
  let pay := payOf s2 c
  let pick : SpellPick := .withCosts (.thenRepeat .plain 1 .plain) false 1
  let rich := s2.rich s.me
  let both ← cast rich s.me c ⟨pay.energy + 1, pay.power⟩ [v, v] (pick := pick)
  let split ← cast rich s.me c ⟨pay.energy + 1, pay.power⟩ [v, rival] (pick := pick)
  let single ← cast rich s.me c pay [v]
  return both.kwAmount v .assault == 4 && single.kwAmount v .assault == 2 &&
    split.kwAmount v .assault == 2 && split.kwAmount rival .assault == 2 &&
    (both.mapObjects endTurnObj).kwAmount v .assault == 0
-- (review) Marching Orders: each unit takes damage equal to the Might of the other
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-114" .hand
  let (s2, f) ← put s1 s.me "OGN-051" .base
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let r ← play s3 s.me c [f, e]
  return r.dmg e == some 2 && (r.obj? f).isNone
-- (review) Simian Ancestor: buffing another unit does not ready it
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-047" .base
  let (s2, o) ← put s1 s.me "OGN-051" .base
  let s3 := s2.tire u
  let r ← fire s3 [.buffedBy o s.me]
  return r.tired u == some true
-- (review) Piercing Light: with no other unit, the first unit is not hit twice
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-023" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let r ← play s2 s.me c [u]
  return r.dmg u == some 2
-- Trinity Force (SFD-115): the unit it is attached to scores 1 point when it holds
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, u) ← putAt s1 s.me "OGN-051" bf
  let (s3, g) ← put s2 s.me "SFD-115" .base
  let s4 := s3.modObj g (fun o => { o with attached := some u })
  let a ← fire s4 [.scored s.me bf false]
  let b ← fire s3 [.scored s.me bf false]
  return a.pointsOf s.me == s4.pointsOf s.me + 1 && b.pointsOf s.me == s3.pointsOf s.me

-- Forgefire Cape (SFD-190): when its unit attacks or defends, 2 damage to all enemy units here
#guard tsf fun s => do
  let (s1, u) ← putAt s s.me "OGN-001" s.bf0
  let (s2, g) ← put s1 s.me "SFD-190" .base
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, f) ← put s3 s.you "OGN-001" .base
  let s5 := s4.modObj g (fun o => { o with attached := some u })
  let a ← fire s5 [.combatStarted s.bf0 s.me]
  let b ← fire s5 [.combatStarted s.bf0 s.you]
  return a.dmg e == some 2 && a.dmg f == some 0 && a.dmg u == some 0 && b.dmg e == some 2

-- Emperor's Dais (SFD-207): conquer here, pay 1 and return a unit here to its hand: a Sand Soldier
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-207"
  let (s2, u) ← putAt s1 s.me "OGN-051" bf
  let a ← fire (s2.rich s.me) [.scored s.me bf true]
  let b ← fire (s2.rich s.me) [.scored s.me bf true] { yes := false }
  let c ← fire (s2.rich s.me) [.scored s.me bf false]
  return a.countIn s.me .hand "OGN-051" == s2.countIn s.me .hand "OGN-051" + 1 &&
    (a.zone .battlefieldZone).any (fun o => (a.cardDef? o).any (·.name == "Sand Soldier")) &&
    (b.obj? u).isSome && c.countIn s.me .hand "OGN-051" == s2.countIn s.me .hand "OGN-051"

-- Both parts of the cost are paid before the ability can be countered. The returned Unit need
-- only be controlled by the payer, and goes to its owner's hand.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf (s.fund p 1) p "SFD-207"
  let (s, unit) ← putAt s q "OGN-051" field
  let (s, other) ← put s p "OGN-001" .base
  let s := s.modObj unit (fun o => { o with controller := p })
  let offer (state : GameState) :=
    let pending := insertTriggers (state.detect [.scored p field true]) state.pending
    (advance 100 { state with pending } []).toOption
  let (waiting, _) ← offer s
  let (unfunded, _) ← offer (s.fund p 0)
  let pay : Action := ⟨.player p, .putTrigger 0 [] (.pay [unit])⟩
  let offsite : Action := ⟨.player p, .putTrigger 0 [] (.pay [other])⟩
  let skip : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (chain, _) ← (step 100 waiting pay).toOption
  let (skipped, _) ← (step 100 waiting skip).toOption
  let item ← (chain.zone .chain).head?
  let resolved := settleChain {} 12 chain
  let countered := settleChain {} 12 (counterObj chain item).1
  let soldier (state : GameState) :=
    (state.unitsAtOf field p).find? (fun id => (state.cardDef? id).any (·.name == "Sand Soldier"))
  return (legalFrameActions waiting).contains pay && !(step 100 waiting offsite).isOk &&
    !(step 100 unfunded pay).isOk &&
    (skipped.poolOf p).energy == 1 && (skipped.obj? unit).isSome &&
    (chain.poolOf p).energy == 0 && (chain.obj? unit).isNone &&
    chain.countIn q .hand "OGN-051" == s.countIn q .hand "OGN-051" + 1 &&
    (soldier chain).isNone && (soldier resolved).bind resolved.tired == some true &&
    (soldier countered).isNone && (countered.poolOf p).energy == 0 &&
    countered.countIn q .hand "OGN-051" == chain.countIn q .hand "OGN-051"

-- Minefield (SFD-212): when its player conquers here, the top 2 cards of their Main Deck go to
-- the Trash
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-212"
  let a ← fire s1 [.scored s.me bf true]
  let b ← fire s1 [.scored s.me bf false]
  let trash (x : GameState) := (x.zone (.player s.me .trash)).length
  let deck (x : GameState) := (x.zone (.player s.me .mainDeck)).length
  return trash a == trash s1 + 2 && deck a + 2 == deck s1 && trash b == trash s1

-- Power Nexus (SFD-214): when its player holds here, they may pay 4 Power to score 1 point
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-214"
  let rich := s1.rich s.me
  let a ← fire rich [.scored s.me bf false]
  let b ← fire rich [.scored s.me bf false] { yes := false }
  let c ← fire (s1.fund s.me 0 3) [.scored s.me bf false]
  let d ← fire rich [.scored s.me bf true]
  return a.pointsOf s.me == rich.pointsOf s.me + 1 && b.pointsOf s.me == rich.pointsOf s.me &&
    c.pointsOf s.me == s1.pointsOf s.me && d.pointsOf s.me == rich.pointsOf s.me

-- Seat of Power (SFD-217): when its player conquers here, they draw 1 for each other battlefield
-- they control
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-217"
  let (s2, b2) ← putBf s1 s.me "SFD-216"
  let (s3, b3) ← putBf s2 s.you "SFD-216"
  let s4 := ((s3.control s.me bf).control s.me b2).control s.you b3
  let a ← fire s4 [.scored s.me bf true]
  return a.handN s.me == s4.handN s.me + 1
-- (not for one the opponent controls, not when the player holds)
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-217"
  let (s2, b2) ← putBf s1 s.you "SFD-216"
  let s3 := (s2.control s.me bf).control s.you b2
  let a ← fire s3 [.scored s.me bf true]
  return a.handN s.me == s3.handN s.me

-- Sunken Temple (SFD-218): conquer here with a Mighty unit, pay 1: draw 1
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-218"
  let (s2, mighty) ← putAt s1 s.me "OGN-001" bf
  let (t2, _) ← putAt s1 s.me "OGN-051" bf
  let a ← fire (s2.rich s.me) [.scored s.me bf true]
  let b ← fire (t2.rich s.me) [.scored s.me bf true]
  let c ← fire (s2.fund s.me 0) [.scored s.me bf true]
  let funded := s2.fund s.me 1
  let es := [Event.scored s.me bf true]
  let (waiting, _) ← (advance 100
    { funded with pending := insertTriggers (funded.detect es) funded.pending } []).toOption
  let (paid, _) ← (step 100 waiting ⟨.player s.me, .putTrigger 0 [] (.pay [])⟩).toOption
  let weakened := (setBaseMight 1 paid mighty).1
  let resolved := settleChain {} 12 weakened
  return a.handN s.me == s2.handN s.me + 1 && (a.poolOf s.me).energy + 1 == 12 &&
    b.handN s.me == t2.handN s.me && c.handN s.me == s2.handN s.me &&
    (paid.poolOf s.me).energy == 0 && paid.handN s.me == funded.handN s.me &&
    (paid.zone .chain).length == 1 && resolved.handN s.me == funded.handN s.me + 1

-- The Papertree (SFD-219): when its player holds here, each player channels 1 rune exhausted
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-219"
  let a ← fire s1 [.scored s.me bf false]
  let b ← fire s1 [.scored s.me bf true]
  let runes (x : GameState) (p : PlayerId) := (x.zone (.player p .runeDeck)).length
  return runes a s.me + 1 == runes s1 s.me && runes a s.you + 1 == runes s1 s.you &&
    runes b s.me == runes s1 s.me

-- Treasure Hoard (SFD-220): conquer here, pay 1: a Gold token
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-220"
  let a ← fire (s1.rich s.me) [.scored s.me bf true]
  let b ← fire (s1.rich s.me) [.scored s.me bf true] { yes := false }
  let c ← fire (s1.fund s.me 0) [.scored s.me bf true]
  return a.countIn s.me .base "SFD-T03" == 1 && b.countIn s.me .base "SFD-T03" == 0 &&
    c.countIn s.me .base "SFD-T03" == 0

-- Gold (SFD-T03): kill it, exhaust it: 1 Power of any domain
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-T03" .base
  let runs := (RiftboundCards.db.find? ⟨"SFD-T03"⟩).any (·.runs)
  return runs && manaReady s1 s.me g 0

-- A sole remaining side wins. Recalling attackers during Combat Cleanup leaves it without a result.
#guard tsf fun s => do
  let (s1, a) ← putAt s s.me "OGN-001" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-051" s.bf0
  let (recalled, events) := combatCleanup s2 s.bf0 s.me
  let attackerOnly := s2.modObj e (fun o => { o with loc := none })
  let defenderOnly := s2.modObj a (fun o => { o with loc := none })
  let neither := attackerOnly.modObj a (fun o => { o with loc := none })
  return events.contains (.recalled a) && (combatResultEvents recalled s.bf0 true).isEmpty &&
    combatResultEvents attackerOnly s.bf0 false == [.combatWon s.bf0 s.me] &&
    combatResultEvents defenderOnly s.bf0 false == [.combatWon s.bf0 s.you] &&
    (combatResultEvents neither s.bf0 false).isEmpty

-- Draven, Vanquisher (SFD-020): when it wins a combat, a Gold token; when it attacks or defends,
-- the player may pay 1 Fury for +2 Might
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-020" s.bf0
  let a ← fire s1 [.combatWon s.bf0 s.me]
  let b ← fire s1 [.combatWon s.bf0 s.you]
  let gold := a.firstOf s.me .base "SFD-T03"
  return a.countIn s.me .base "SFD-T03" == 1 && b.countIn s.me .base "SFD-T03" == 0 &&
    gold.bind a.tired == some true
#guard tsf fun s => do
  let (s1, d) ← putAt s s.me "SFD-020" s.bf0
  let (s2, _) ← putAt s1 s.you "OGN-051" s.bf0
  let a ← fire (s2.rich s.me) [.combatStarted s.bf0 s.me]
  let b ← fire (s2.rich s.me) [.combatStarted s.bf0 s.you]
  let c ← fire (s2.rich s.me) [.combatStarted s.bf0 s.me] { yes := false }
  let e ← fire (s2.fund s.me 5) [.combatStarted s.bf0 s.me]
  return a.mightNow d == (s2.mightNow d).map (· + 2) && (a.poolOf s.me).fury == 11 &&
    b.mightNow d == (s2.mightNow d).map (· + 2) && c.mightNow d == s2.mightNow d &&
    e.mightNow d == s2.mightNow d

-- The Vendetta errata makes Fury a base cost of the attack or defend trigger. It is already
-- spent while the ability can still be countered.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, draven) ← putAt (s.fund p 0 1) p "SFD-020" bf
  let (s, _) ← putAt s q "OGN-049" bf
  let offer (state : GameState) (attacker : PlayerId) :=
    let pending := insertTriggers (state.detect [.combatStarted bf attacker]) state.pending
    (advance 100 { state with pending } []).toOption
  let (attacking, _) ← offer s p
  let (defending, _) ← offer s q
  let (short, _) ← offer (s.fund p 1 0 1) p
  let pay : Action := ⟨.player p, .putTrigger 0 [] (.pay [])⟩
  let skip : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (chain, _) ← (step 100 attacking pay).toOption
  let (skipped, _) ← (step 100 defending skip).toOption
  let item ← (chain.zone .chain).head?
  let resolved := settleChain {} 12 chain
  let countered := settleChain {} 12 (counterObj chain item).1
  return (legalFrameActions attacking).contains pay && (legalFrameActions defending).contains pay &&
    !(step 100 short pay).isOk && (chain.poolOf p).fury == 0 && (skipped.poolOf p).fury == 1 &&
    chain.mightNow draven == some 4 && resolved.mightNow draven == some 6 &&
    (countered.poolOf p).fury == 0 && countered.mightNow draven == some 4

-- Corrupt Enforcer (SFD-123): discard 1 when it moves to a battlefield; draw 1 when it wins
#guard tsf fun s => do
  let (s1, u) ← putAt s s.me "SFD-123" s.bf0
  let (s2, v) ← put s1 s.me "SFD-123" .base
  let a ← fire s2 [.standardMoved u (some s.bf0)]
  let b ← fire s2 [.standardMoved v none]
  let c ← fire s2 [.combatWon s.bf0 s.me]
  return a.handN s.me + 1 == s2.handN s.me && b.handN s.me == s2.handN s.me &&
    c.handN s.me == s2.handN s.me + 1

-- Glorious Executioner (SFD-185), a Legend: draw 1 when its player wins a combat
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-185" .legendZone
  let a ← fire s1 [.combatWon s.bf0 s.me]
  let b ← fire s1 [.combatWon s.bf0 s.you]
  return a.handN s.me == s1.handN s.me + 1 && b.handN s.me == s1.handN s.me

-- Mechanized Menace (SFD-181), a Legend: the Mechs of its player have Shield
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-181" .legendZone
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, o) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "SFD-062" .base
  return s4.hasKw m .shield && !s4.hasKw o .shield && !s4.hasKw e .shield

-- (review) Mechanized Menace: Shield is +1 Might in the damage of a defending Mech
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-181" .legendZone
  let (s2, m) ← putAt s1 s.me "SFD-062" s.bf0
  let (s3, o) ← putAt s2 s.me "OGN-051" s.bf0
  return s3.combatMight m false == s3.combatMight m true + 1 &&
    s3.combatMight o false == s3.combatMight o true

-- Draven creates Gold if its side wins. A Combat that ends with a Recall has no winner.
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-020" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-051" s.bf0
  let dead := s2.modObj e (fun o => { o with loc := none })
  let combat := (s2.observeCombat [.showdown s.bf0 s.me 0]).1
  let finish (x : GameState) : Option GameState := do
    let pending := .combatResolve s.bf0 s.me :: combatSteps s.bf0
    let (waiting, _) ← (advance 100 { x with combat := combat, pending := pending } []).toOption
    return settleChain {} 12 waiting
  let won ← finish dead
  let noResult ← finish s2
  return won.countIn s.me .base "SFD-T03" == 1 && noResult.countIn s.me .base "SFD-T03" == 0

-- (review) The Papertree: the runes channelled are exhausted
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-219"
  let a ← fire s1 [.scored s.me bf false]
  let fresh (x : GameState) (p : PlayerId) :=
    (x.zone (.player p .base)).filter (fun r => (x.cardDef? r).any (·.hasType .rune) &&
      (s1.zone (.player p .base)).all (· != r))
  return (fresh a s.me).length == 1 && (fresh a s.me).all (fun r => a.tired r == some true) &&
    (fresh a s.you).all (fun r => a.tired r == some true)

-- Papertree channels for all four seats; shared scoring does not merge their Rune Decks.
#guard tsf fun base => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let opening ← GameState.initial base.cards config (List.replicate 4 goodDeck)
  let start ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) opening).toOption
  let p := start.me
  let (s, bf) ← putBf start p "SFD-219"
  let (scored, _, events) := scoreBf (s.control p bf) p bf false
  let after ← fire scored events
  return s.players.all (fun seat =>
    let runes := Zone.player seat .runeDeck
    let base := Zone.player seat .base
    let newRunes := (after.zone base).filter (fun r => !(s.zone base).contains r)
    (after.zone runes).length + 1 == (s.zone runes).length &&
      newRunes.length == 1 && newRunes.all (fun r => after.tired r == some true))

-- (review) Treasure Hoard and Draven's Gold token are exhausted; the cost is exactly 1
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-220"
  let a ← fire (s1.fund s.me 1) [.scored s.me bf true]
  let g := a.firstOf s.me .base "SFD-T03"
  return g.bind a.tired == some true && (a.poolOf s.me).energy == 0

-- (review) Power Nexus: exactly 4 Power pays; the Power is gone afterwards
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-214"
  let a ← fire (s1.fund s.me 0 4) [.scored s.me bf false]
  return a.pointsOf s.me == s1.pointsOf s.me + 1 && (a.poolOf s.me).fury == 0

-- (review) Emperor's Dais: no Energy, no return and no token; with 1 Energy, one cost
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-207"
  let (s2, _) ← putAt s1 s.me "OGN-051" bf
  let a ← fire (s2.fund s.me 0) [.scored s.me bf true]
  let b ← fire (s2.fund s.me 1) [.scored s.me bf true]
  return a.countIn s.me .hand "OGN-051" == s2.countIn s.me .hand "OGN-051" &&
    b.countIn s.me .hand "OGN-051" == s2.countIn s.me .hand "OGN-051" + 1 &&
    (b.poolOf s.me).energy == 0

-- (review) Sunken Temple: no draw when the player declines, or when they hold
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-218"
  let (s2, _) ← putAt s1 s.me "OGN-001" bf
  let a ← fire (s2.rich s.me) [.scored s.me bf true] { yes := false }
  let b ← fire (s2.rich s.me) [.scored s.me bf false]
  return a.handN s.me == s2.handN s.me && b.handN s.me == s2.handN s.me

-- (review) Corrupt Enforcer: the opponent's win does not draw for the player
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-123" s.bf0
  let a ← fire s1 [.combatWon s.bf0 s.you]
  return a.handN s.me == s1.handN s.me

-- Chemtech Cask (SFD-063): when its player plays a spell on an opponent's turn, they may exhaust it
-- to play a Gold token (exhausted)
#guard tsf fun s => do
  let (s1, k) ← put s s.me "SFD-063" .base
  let (s2, sp) ← put s1 s.me "OGN-004" .trash
  let theirs := { s2 with active := some s.you }
  let a ← fire theirs [.spellResolved s.me sp]
  let b ← fire s2 [.spellResolved s.me sp]
  let c ← fire theirs [.spellResolved s.me sp] { yes := false }
  let d ← fire (theirs.tire k) [.spellResolved s.me sp]
  let e ← fire theirs [.spellResolved s.you sp]
  let gold (x : GameState) := x.countIn s.me .base "SFD-T03"
  return gold a == 1 && a.tired k == some true &&
    (a.firstOf s.me .base "SFD-T03").bind a.tired == some true &&
    gold b == 0 && gold c == 0 && gold d == 0 && gold e == 0

-- An ally's cast and an ally's turn are distinct from the Cask controller's cast on an enemy turn.
#guard tsf fun base => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let start ← GameState.initial base.cards config (List.replicate 4 goodDeck)
  let s ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) start).toOption
  let p := s.me
  let ally ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← s.players.find? (fun q => !config.mode.sameSide p q)
  let (s, cask) ← put s p "SFD-063" .base
  let (s, mine) ← put s p "OGN-004" .trash
  let (s, theirs) ← put s ally "OGN-004" .trash
  let allyTurn ← fire { s with active := some ally } [.spellResolved p mine]
  let allySpell ← fire { s with active := some enemy } [.spellResolved ally theirs]
  let payForMine ← fire { s with active := some enemy } [.spellResolved p mine]
  return allyTurn.tired cask == some false && allySpell.tired cask == some false &&
    payForMine.tired cask == some true && payForMine.countIn p .base "SFD-T03" == 1

-- Pickpocket (SFD-074): kill a gear with Energy cost 1 or less, then a Gold token
#guard tsf fun s => do
  let (s1, p) ← put s s.me "SFD-074" .hand
  let (s2, g) ← put s1 s.you "SFD-009" .base
  let (s3, big) ← put s2 s.you "SFD-042" .base
  let a ← play s3 s.me p [] { pick := fun ts => ts == [g] }
  let b ← play s3 s.me p [] { yes := false }
  let st ← castStop s3 s.me p
  return (a.obj? g).isNone && a.countIn s.me .base "SFD-T03" == 1 && (a.obj? big).isSome &&
    (b.obj? g).isSome && b.countIn s.me .base "SFD-T03" == 0 &&
    st.trigPicks.contains g && !st.trigPicks.contains big

-- Beast Below (SFD-132): when played, return another friendly unit and an enemy unit to hands
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-132" .hand
  let (s2, f) ← put s1 s.me "OGN-051" .base
  let (s3, e) ← put s2 s.you "OGN-001" .base
  let r ← play s3 s.me b [] { pick := fun ts => ts == [f, e] }
  let st ← castStop s3 s.me b
  let beast := st.firstOf s.me .base "SFD-132"
  return r.countIn s.me .hand "OGN-051" == 1 && r.countIn s.you .hand "OGN-001" == 1 &&
    r.countIn s.me .base "SFD-132" == 1 && beast.any (fun x => !st.trigPicks.contains x)
-- (with no enemy unit the friendly one is returned alone; with no other friendly unit nothing is)
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-132" .hand
  let (s2, _) ← put s1 s.me "OGN-051" .base
  let r ← play s2 s.me b
  let (t1, b2) ← put s s.me "SFD-132" .hand
  let (t2, _) ← put t1 s.you "OGN-001" .base
  let r2 ← play t2 s.me b2
  return r.countIn s.me .hand "OGN-051" == 1 && r.countIn s.me .base "SFD-132" == 1 &&
    r2.countIn s.you .hand "OGN-001" == 0 && r2.countIn s.me .base "SFD-132" == 1

-- Factory Recall (SFD-135): return a gear to its owner's hand (not a unit)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-135" .hand
  let (s2, g) ← put s1 s.you "SFD-030" .base
  let (s3, u) ← put s2 s.you "OGN-051" .base
  let attached := (attachTo u s3 g).1
  let r ← play attached s.me c [g]
  return r.countIn s.you .hand "SFD-030" == 1 && r.countIn s.me .hand "SFD-030" == 0 &&
    r.mightNow u == s3.mightNow u && (play s3 s.me c [u]).isNone

-- Windsinger (SFD-138): Hidden; when played, may return another unit at a battlefield with 3 Might
-- or less
#guard match RiftboundCards.db.find? ⟨"SFD-138"⟩ with
  | some c => c.hasKeyword .hidden && c.runs
  | none => false
#guard tsf fun s => do
  let (s1, w) ← put s s.me "SFD-138" .hand
  let (s2, small) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, big) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, base) ← put s3 s.you "OGN-051" .base
  let r ← play s4 s.me w
  let r2 ← play s4 s.me w [] { yes := false }
  let st ← castStop s4 s.me w
  return r.countIn s.you .hand "OGN-051" == 1 && (r.obj? small).isNone &&
    (r.obj? big).isSome && (r.obj? base).isSome && r2.countIn s.you .hand "OGN-051" == 0 &&
    st.trigPicks == [small]

-- Downwell (SFD-147): return all units and gear to their owners' hands
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-147" .hand
  let (s2, _) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, _) ← put s3 s.you "SFD-030" .base
  let r ← play s4 s.me c
  return r.countIn s.me .hand "OGN-051" == 1 && r.countIn s.you .hand "OGN-001" == 1 &&
    r.countIn s.you .hand "SFD-030" == 1 && (r.zone .battlefieldZone).length ==
      (s4.zone .battlefieldZone).length - 1 && (r.zone (.player s.me .base)).all (fun o =>
        (r.cardDef? o).any (fun d => d.hasType .rune))

-- Bonds of Strength (SFD-151): two different friendly units each have +1 Might
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-151" .hand
  let (s2, a) ← put s1 s.me "OGN-051" .base
  let (s3, b) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-051" .base
  let r ← play s4 s.me c [a, b]
  return r.mightNow a == (s4.mightNow a).map (· + 1) &&
    r.mightNow b == (s4.mightNow b).map (· + 1) &&
    (play s4 s.me c [a, a]).isNone && (play s4 s.me c [a, e]).isNone

-- Guards! (SFD-154): a Sand Soldier token; the player may pay 1 Order Power to ready it
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-154" .hand
  let (s2, _) ← putAt s1 s.me "OGN-001" s.bf0
  let soldier (x : GameState) :=
    (x.zone (.player s.me .base)).find? (fun o => (x.cardDef? o).any (·.name == "Sand Soldier"))
  let a ← cast (s2.fund s.me 5 0 0 0 0 0 1) s.me c (payOf s2 c) [] { fromEnd := some 1 }
  let b ← cast (s2.fund s.me 5 0 0 0 0 0 1) s.me c (payOf s2 c) [] { fromEnd := some 2 }
  let n ← cast (s2.fund s.me 5) s.me c (payOf s2 c)
  return (soldier a).bind a.tired == some false && (a.poolOf s.me).order == 0 &&
    (soldier b).bind b.tired == some true && (b.poolOf s.me).order == 1 &&
    (soldier n).bind n.tired == some true

-- Sandshifter (SFD-158): when played, kill an enemy unit with 3 Might or less
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-158" .hand
  let (s2, small) ← put s1 s.you "OGN-051" .base
  let (s3, big) ← put s2 s.you "OGN-001" .base
  let (s4, mine) ← put s3 s.me "OGN-051" .base
  let threshold := s4.buff small
  let r ← play threshold s.me c
  return threshold.mightNow small == some 3 && (r.obj? small).isNone &&
    (r.obj? big).isSome && (r.obj? mine).isSome
-- (nothing to kill: the unit is simply played)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-158" .hand
  let (s2, big) ← put s1 s.you "OGN-001" .base
  let r ← play s2 s.me c
  return (r.obj? big).isSome && r.countIn s.me .base "SFD-158" == 1

-- Trusty Ramhound (SFD-159): +1 Might while another friendly unit is at the same place
#guard tsf fun s => do
  let (s1, r) ← put s s.me "SFD-159" .base
  let (s2, _) ← put s1 s.you "OGN-051" .base
  let (s3, _) ← put s2 s.me "OGN-051" .base
  let (t1, q) ← putAt s s.me "SFD-159" s.bf0
  let (t2, _) ← putAt t1 s.me "OGN-051" s.bf0
  let (t3, _) ← put t2 s.me "OGN-051" .base
  return s2.mightNow r == s1.mightNow r && s3.mightNow r == (s1.mightNow r).map (· + 1) &&
    t2.mightNow q == (t1.mightNow q).map (· + 1) && t1.mightNow q == s1.mightNow r &&
    t3.mightNow q == t2.mightNow q

-- Blood Money (SFD-162): kill a unit at a battlefield with 2 Might or less; 1 Gold if it was an
-- enemy's, 2 if it was a friendly one
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-162" .hand
  let (s2, e) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, f) ← putAt s2 s.me "OGN-051" s.bf0
  let (s4, big) ← putAt s3 s.you "OGN-001" s.bf0
  let a ← play s4 s.me c [e]
  let b ← play s4 s.me c [f]
  return (a.obj? e).isNone && a.countIn s.me .base "SFD-T03" == 1 &&
    (b.obj? f).isNone && b.countIn s.me .base "SFD-T03" == 2 && (play s4 s.me c [big]).isNone
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-162" .hand
  let (s2, e) ← put s1 s.you "OGN-051" .base
  return (play s2 s.me c [e]).isNone

-- Deathgrip (SFD-163): the first target's Might is read before the Kill. An actual death
-- grants Might, and a death replaced by Hourglass or Banish still draws one (Spiritforged FAQ).
#guard tsf fun s => do
  let p := s.me
  let (s, c) ← put s p "SFD-163" .hand
  let (s, victim) ← put s p "OGN-001" .base
  let (s, recipient) ← put s p "OGN-051" .base
  let s := s.buff victim
  let withKill ← play s p c [victim, recipient]
  let (withGear, firstGear) ← put s p "OGN-077" .base
  let (withGear, secondGear) ← put withGear p "OGN-077" .base
  let withFirst ← play withGear p c [victim, recipient] { yes := true }
  let withSecond ← play withGear p c [victim, recipient] { yes := false }
  let withBanish ← play (s.addTurnFxOn s.you victim .banishInstead) p c [victim, recipient]
  let original := s.mightNow recipient
  let might ← s.mightNow victim
  return (withKill.obj? victim).isNone && withKill.mightNow recipient == original.map (· + might) &&
    withKill.countIn p .trash "OGN-001" == 1 &&
    [withFirst, withSecond].all (fun board => (board.obj? victim).any (·.exhausted) &&
      board.countIn p .trash "OGN-077" == 1 && board.mightNow recipient == original) &&
    (withFirst.obj? firstGear).isSome != (withSecond.obj? firstGear).isSome &&
    (withFirst.obj? secondGear).isSome != (withSecond.obj? secondGear).isSome &&
    withBanish.countIn p .banishment "OGN-001" == 1 && withBanish.mightNow recipient == original &&
    [withKill, withFirst, withSecond, withBanish].all (fun board => board.handN p == s.handN p) &&
    (play s p c [victim, victim]).isNone

-- Retreat in response can make either target illegal independently. Deathgrip still draws.
#guard tsf fun s => do
  let p := s.me
  let (s, c) ← put s p "SFD-163" .hand
  let (s, retreat) ← put s p "OGN-104" .hand
  let (s, victim) ← put s p "OGN-001" .base
  let (s, recipient) ← put s p "OGN-051" .base
  let before := s.rich p
  let (declared, _) ← (step 100 before
    ⟨.player p, .playCard c (payOf before c) [victim, recipient]⟩).toOption
  let respond (target : ObjId) : Option GameState :=
    cast declared p retreat (payOf declared retreat) [target]
  let noVictim ← respond victim
  let noRecipient ← respond recipient
  let stolen := settleChain {} 12 (setController s.you declared victim).1
  return declared.inPlay.contains victim && declared.inPlay.contains recipient &&
    stolen.inPlay.contains victim && stolen.mightNow recipient == before.mightNow recipient &&
    stolen.countIn p .trash "SFD-163" == 1 && stolen.handN p == before.handN p &&
    noVictim.countIn p .hand "OGN-001" == 1 && noVictim.countIn p .trash "OGN-001" == 0 &&
    noVictim.mightNow recipient == before.mightNow recipient &&
    noRecipient.countIn p .hand "OGN-051" == 1 && noRecipient.countIn p .trash "OGN-001" == 1 &&
    [noVictim, noRecipient].all (fun board =>
      board.countIn p .trash "SFD-163" == 1 && board.handN p == before.handN p)

-- Janna, Savior (SFD-053) at a base: heals the friendly units there
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-053" .base
  let (s2, a) ← put s1 s.me "OGN-001" .base
  let (s3, b) ← putAt s2 s.me "OGN-001" s.bf0
  let hurt (x : GameState) (u : ObjId) := x.modObj u (fun o => { o with damage := 3 })
  let s4 := hurt (hurt s3 a) b
  let r ← fire s4 [.played s.me j]
  return r.dmg a == some 0 && r.dmg b == some 3

-- (review) Chemtech Cask: a spell played from Hidden is played too; a unit played is not a spell
#guard tsf fun s => do
  let (s1, k) ← put s s.me "SFD-063" .base
  let (s2, h) ← put s1 s.me "SFD-017" .hidden
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let theirs := { s3 with active := some s.you }
  let a ← fire theirs [.spellResolved s.me h]
  let b ← fire theirs [.played s.me u]
  return a.countIn s.me .base "SFD-T03" == 1 && b.countIn s.me .base "SFD-T03" == 0 && k != u
-- (review) the effect of playing a Hidden spell announces that it was played
#guard tsf fun s => do
  let (s1, h) ← put s s.me "SFD-017" .hidden
  let r := applyPrim s1 s.me h {} (.turnEffect .hiddenPlayed)
  return r.any (fun (_, es) => es.contains (.played s.me h))
-- (review) Bonds of Strength: if the second unit is gone when the spell resolves, the first still
-- gets +1 (and the other way round)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-151" .hand
  let (s2, a) ← put s1 s.me "OGN-051" .base
  let (s3, b) ← put s2 s.me "OGN-051" .base
  let s4 ← match step 100 (s3.rich s.me) ⟨.player s.me, .playCard c (payOf s3 c) [a, b]⟩ with
    | .ok (x, _) => some x
    | .error _ => none
  let r1 := settleChain {} 12 (killObj s4 b).1
  let r2 := settleChain {} 12 (killObj s4 a).1
  return r1.mightNow a == (s3.mightNow a).map (· + 1) &&
    r2.mightNow b == (s3.mightNow b).map (· + 1)
-- (review) Windsinger: a unit of its own player is a legal choice too
#guard tsf fun s => do
  let (s1, w) ← put s s.me "SFD-138" .hand
  let (s2, mine) ← putAt s1 s.me "OGN-051" s.bf0
  let r ← play s2 s.me w
  return r.countIn s.me .hand "OGN-051" == 1 && (r.obj? mine).isNone
-- (review) Ramhound: an enemy at the same battlefield does not count
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-159" s.bf0
  let (s2, _) ← putAt s1 s.you "OGN-051" s.bf0
  return s2.mightNow r == s1.mightNow r
-- (review) Pickpocket: if the gear is gone when the ability resolves, no Gold
#guard tsf fun s => do
  let (s1, p) ← put s s.me "SFD-074" .hand
  let (s2, g) ← put s1 s.you "SFD-009" .base
  let s3 ← match step 100 (s2.rich s.me) ⟨.player s.me, .playCard p (payOf s2 p) []⟩ with
    | .ok (x, _) => some x
    | .error _ => none
  let s4 := settleChain { pick := fun ts => ts == [g] } 1 s3
  let s5 := (killObj s4 g).1
  let r := settleChain {} 12 s5
  return r.countIn s.me .base "SFD-T03" == 0
/-- How many Sand Soldier tokens the player has at their Base, and how many are ready. -/
meta def _root_.Riftbound.GameState.soldiers (s : GameState) (p : PlayerId) : Nat × Nat :=
  let l := (s.zone (.player p .base)).filter (fun o =>
    (s.cardDef? o).any (·.name == "Sand Soldier"))
  (l.length, (l.filter (fun o => s.tired o == some false)).length)

-- Rocket Barrage offers its mode and target even when no Repeat is paid.
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-077" .hand
  let (s2, u) ← put s1 s.you "OGN-001" .base
  let (s3, g) ← put s2 s.you "SFD-030" .base
  let (s4, w) ← putAt s3 s.you "OGN-001" s.bf0
  let castMode (i : Nat) (targets : List ObjId) :=
    cast (s4.rich s.me) s.me c (payOf s4 c) targets (pick := .mode i)
  let a ← castMode 0 [u]
  let b ← castMode 1 [g]
  return a.dmg u == some 4 && (a.obj? g).isSome && a.dmg w == some 0 &&
    (b.obj? g).isNone && b.dmg u == some 0 && (castMode 0 [w]).isNone &&
    (castMode 0 []).isNone && (castMode 1 [u]).isNone && (castMode 0 [g]).isNone

-- Rocket Barrage locks the ordered choices for both the printed and a granted Repeat.
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-077" .hand
  let (s2, u) ← put s1 s.you "OGN-001" .base
  let (s3, g) ← put s2 s.you "SFD-030" .base
  let (s4, h) ← put s3 s.you "SFD-030" .base
  let p := s.me
  let rich := s4.rich p
  let paid : RunePool.Payment := ⟨8, [.mind, .mind]⟩
  let order (i j : Nat) : SpellPick := .withCosts (.thenRepeat (.mode i) 1 (.mode j)) false 1
  let both ← cast rich p c paid [u, g] (pick := order 0 1)
  let reversed ← cast rich p c paid [g, u] (pick := order 1 0)
  let gears ← cast rich p c paid [g, h] (pick := order 1 1)
  let plain ← cast rich p c (payOf rich c) [u] (pick := .mode 0)
  let three : SpellPick := .withCosts
    (.thenRepeat (.mode 1) 1 (.thenRepeat (.mode 0) 1 (.mode 1))) false 2
  let thrice ← cast (rich.addTurnFx p .nextSpellRepeat) p c ⟨12, [.mind, .mind, .mind]⟩
    [g, u, h] (pick := three)
  return both.dmg u == some 4 && (both.obj? g).isNone && (both.obj? h).isSome &&
    reversed.dmg u == some 4 && (reversed.obj? g).isNone &&
    (gears.obj? g).isNone && (gears.obj? h).isNone && gears.dmg u == some 0 &&
    plain.dmg u == some 4 && (plain.obj? g).isSome &&
    thrice.dmg u == some 4 && (thrice.obj? g).isNone && (thrice.obj? h).isNone &&
    (cast rich p c paid [u] (pick := order 0 1)).isNone &&
    (cast rich p c paid [u] (pick := .mode 0)).isNone

-- CR 820.2.a: both Rocket Barrage executions can choose the same Gear before it is killed.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "SFD-077" .hand
  let (s, gear) ← put s q "SFD-030" .base
  let (s, other) ← put s q "SFD-030" .base
  let choices : SpellPick := .withCosts (.thenRepeat (.mode 1) 1 (.mode 1)) false 1
  let (chain, _) ← (step 100 (s.rich p)
    ⟨.player p, .playCard spell ⟨8, [.mind, .mind]⟩ [gear, gear] none none choices⟩).toOption
  let (response, _) ← (step 100 chain ⟨.player p, .pass⟩).toOption
  let (settled, events) ← (step 100 response ⟨.player q, .pass⟩).toOption
  let dead ← settled.firstOf q .trash "SFD-030"
  return events.filter (fun | .died .. => true | _ => false) == [.died dead q] &&
    (settled.obj? other).isSome && settled.countIn q .trash "SFD-030" == 1

-- Jayce (SFD-084): when played, may kill a friendly gear; if so, the player may play a gear (cost 7
-- or less) from the hand this turn for no Energy: it is played later, and only the first one is free
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-084" .hand
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-115" .hand
  let a ← play s3 s.me c [] { pick := fun ts => ts == [g] }
  let b ← play s3 s.me c [] { yes := false }
  let g2 ← a.firstOf s.me .hand "SFD-115"
  let a2 ← play a s.me g2
  let h2 ← b.firstOf s.me .hand "SFD-115"
  let b2 ← play b s.me h2
  return (a.obj? g).isNone && a.countIn s.me .base "SFD-115" == 0 &&
    a2.countIn s.me .base "SFD-115" == 1 && (a2.poolOf s.me).energy == 12 &&
    b2.countIn s.me .base "SFD-115" == 1 && (b2.poolOf s.me).energy < 12 &&
    (b.obj? g).isSome

-- Ornn, Forge God (SFD-085): +1 Might for each friendly gear
#guard tsf fun s => do
  let (s1, o) ← put s s.me "SFD-085" .base
  let (s2, _) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-030" .base
  let (s4, _) ← put s3 s.you "SFD-030" .base
  return s3.mightNow o == (s1.mightNow o).map (· + 2) && s4.mightNow o == s3.mightNow o

-- Fae Porter chooses and pays during finalization. Flash moves the source, while its ability
-- still moves the chosen Unit to the original destination.
#guard tsf fun s => do
  let p := s.me
  let field := s.bf0
  let (s, porter) ← put ((s.control p field).fund p 2 0 0 0 0 1) p "SFD-125" .base
  let (s, unit) ← put s p "OGN-051" .base
  let (s, flash) ← put s p "OGS-011" .hand
  let (offered, _) ← (step 100 s ⟨.player p, .standardMove porter (.battlefield field)⟩).toOption
  let accept : Action := ⟨.player p, .putTrigger 0 [unit] (.pay [])⟩
  let (paid, events) ← (step 100 offered accept).toOption
  let (declined, _) ← (step 100 offered ⟨.player p, .putTrigger 0 [] .skip⟩).toOption
  let returned ← cast paid p flash ⟨2, []⟩ [porter]
  return (legalActions offered).contains accept && events.contains (.chosenByAbility p unit) &&
    (paid.poolOf p).chaos == 0 && paid.where? unit == some (.player p .base) &&
    (declined.poolOf p).chaos == 1 && declined.where? unit == some (.player p .base) &&
    !(step 100 (offered.fund p 2) accept).isOk && returned.countIn p .base "SFD-125" == 1 &&
    (returned.unitsAtOf field p).contains unit

-- Overzealous Fan (SFD-128): when it defends, may kill itself to move an attacker to its base
#guard tsf fun s => do
  let (s1, f) ← putAt s s.me "SFD-128" s.bf0
  let (s2, a) ← putAt s1 s.you "OGN-001" s.bf0
  let s3 := s2.modObj s.bf0 (fun o => { o with contested := some s.you })
  let fight := s3.inShowdownAt s.bf0 s.you
  let r ← fire fight [.combatStarted s.bf0 s.you]
  let n ← fire fight [.combatStarted s.bf0 s.you] { yes := false }
  let o ← fire fight [.combatStarted s.bf0 s.me]
  return (r.obj? f).isNone && (r.obj? a).any (·.loc.isNone) && (n.obj? f).isSome &&
    (n.obj? a).any (·.loc == some s.bf0) && (o.obj? a).any (·.loc == some s.bf0)

-- Temptation (SFD-129): move an enemy unit to where another enemy unit is
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-129" .hand
  let (s2, a) ← put s1 s.you "OGN-051" .base
  let (s3, b) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, m) ← put s3 s.me "OGN-051" .base
  let r ← play s4 s.me c [a, b]
  return (r.obj? a).any (·.loc == some s.bf0) && (play s4 s.me c [a, a]).isNone &&
    (play s4 s.me c [m, b]).isNone

-- Switcheroo (SFD-145): swap the Mights of two units at the same battlefield this turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-145" .hand
  let (s2, a) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, b) ← putAt s2 s.you "OGN-051" s.bf0
  let r ← play s3 s.me c [a, b]
  return r.mightNow a == s3.mightNow b && r.mightNow b == s3.mightNow a &&
    s3.mightNow a == some 5 && s3.mightNow b == some 2
-- (not two units at different battlefields; not a unit at a base)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-145" .hand
  let (s2, a) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, other) ← putBf s2 s.you "SFD-216"
  let (s4, b) ← putAt s3 s.you "OGN-051" other
  let (s5, base) ← put s4 s.you "OGN-051" .base
  return (play s4 s.me c [a, b]).isNone && (play s5 s.me c [a, base]).isNone &&
    (play s5 s.me c [a, a]).isNone

-- Glasc Mixologist (SFD-165): when it dies, may play a unit (cost 3 or less, at most 1 Power) from
-- the Trash for nothing
#guard tsf fun s => do
  let p := s.me
  let (s, mixologist) ← put s p "SFD-165" .base
  let (s, valid) ← put s p "OGN-218" .trash
  let (s, energy) ← put s p "OGN-001" .trash
  let (s, power) ← put s p "OGN-150" .trash
  let (s, spell) ← put s p "UNL-007" .trash
  let (s, enemy) ← put s s.you "OGN-218" .trash
  let (dead, events) := killObj (s.fund p 0) mixologist
  let picks ← firePicks dead events
  let accepted ← fire dead events
  let declined ← fire dead events { yes := false }
  let entered ← accepted.firstOf p .base "OGN-218"
  return picks == [valid] &&
    (accepted.obj? entered).any (fun o => o.energyPaid == 0 && o.exhausted) &&
    (accepted.poolOf p).total == 0 && !(accepted.zone (.player p .trash)).contains valid &&
    [energy, power, spell].all (accepted.zone (.player p .trash)).contains &&
    (accepted.zone (.player s.you .trash)).contains enemy &&
    (declined.zone (.player p .trash)).contains valid && declined.countIn p .base "OGN-218" == 0

-- Xin Zhao, Vigilant (SFD-176): enters ready if two or more other units of the player are at base
#guard tsf fun s => do
  let (s1, x) ← put s s.me "SFD-176" .hand
  let (s2, _) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← put s2 s.me "OGN-051" .base
  let (s4, _) ← putAt s2 s.me "OGN-051" s.bf0
  let (s5, _) ← put s2 s.you "OGN-051" .base
  let a ← play s3 s.me x
  let b ← play s2 s.me x
  let c ← play s4 s.me x
  let d ← play s5 s.me x
  let ready (r : GameState) := (r.firstOf s.me .base "SFD-176").bind r.tired
  return ready a == some false && ready b == some true && ready c == some true &&
    ready d == some true

-- Corina may pay an extra Energy and Order Power to enter ready.
#guard tsf fun s => do
  let p := s.me
  let (s, corina) ← put (s.rich p) p "SFD-179" .hand
  let normal ← cast s p corina ⟨7, [.order]⟩
  let accelerated ← cast s p corina ⟨8, [.order, .order]⟩
  return (normal.firstOf p .base "SFD-179").bind normal.tired == some true &&
    (accelerated.firstOf p .base "SFD-179").bind accelerated.tired == some false

-- Corina checks “here” when her triggered ability resolves (CR 359.3.f.2).
-- Flash can move her back before the Recruit tokens enter. This return does not trigger her.
#guard tsf fun s => do
  let p := s.me
  let field := s.bf0
  let (s, corina) ← put (s.control p field) p "SFD-179" .base
  let (s, flash) ← put s p "OGS-011" .hand
  let (queued, _) ← (step 100 s ⟨.player p, .standardMove corina (.battlefield field)⟩).toOption
  let finished := settleChain {} 12 queued
  let recruits := (finished.unitsAtOf field p).filter (fun id =>
    (finished.cardDef? id).any (·.name == "Recruit"))
  let returned ← play queued p flash [corina]
  return (queued.zone .chain).length == 1 && recruits.length == 3 &&
    recruits.all (fun id => finished.tired id == some true) &&
    (returned.unitsAtOf field p).isEmpty && returned.countIn p .base "SFD-179" == 1 &&
    returned.countNamed p .base "Recruit" == 3

-- Defiant Dance (SFD-196): one unit +2 Might, another -2 Might this turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-196" .hand
  let (s2, a) ← put s1 s.me "OGN-001" .base
  let (s3, b) ← put s2 s.you "OGN-001" .base
  let r ← play s3 s.me c [a, b]
  return r.mightNow a == (s3.mightNow a).map (· + 2) &&
    r.mightNow b == (s3.mightNow b).map (· - 2) && (play s3 s.me c [a, a]).isNone

-- Arise! (SFD-198): a Sand Soldier for each Equipment the player controls, and two of them ready
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-198" .hand
  let (s2, _) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-042" .base
  let (s4, _) ← put s3 s.me "SFD-042" .base
  let (s5, _) ← put s3 s.you "SFD-042" .base
  let a ← play s4 s.me c
  let b ← play s3 s.me c
  let n ← play s1 s.me c
  let e ← play s5 s.me c
  return a.soldiers s.me == (3, 2) && b.soldiers s.me == (2, 2) && n.soldiers s.me == (0, 0) &&
    e.soldiers s.me == (2, 2)

-- On the Hunt (SFD-204): ready the units of the player
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-204" .hand
  let (s2, a) ← put s1 s.me "OGN-051" .base
  let (s3, b) ← put s2 s.you "OGN-051" .base
  let s4 := (s3.tire a).tire b
  let r ← play s4 s.me c
  return r.tired a == some false && r.tired b == some true

-- (review) Jayce: the gear is played ignoring its Energy cost, but its Power cost is paid
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-084" .hand
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-022" .hand
  let a0 ← play s3 s.me c [] { pick := fun ts => ts == [g] }
  let a ← play a0 s.me (← a0.firstOf s.me .hand "SFD-022")
  let n0 ← play (s3.fund s.me 4) s.me c [] { pick := fun ts => ts == [g] }
  let n ← play n0 s.me (← n0.firstOf s.me .hand "SFD-022")
  return a.countIn s.me .base "SFD-022" == 1 && (a.poolOf s.me).fury == 11 &&
    (a.poolOf s.me).energy == 12 && n.countIn s.me .base "SFD-022" == 1
-- (a hand with no Fury: the gear is not played, but the other gear was killed)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-084" .hand
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-022" .hand
  let poor := s3.fund s.me 4
  let r ← cast poor s.me c (payOf s3 c) [] { pick := fun ts => ts == [g] }
  return (r.obj? g).isNone && r.countIn s.me .base "SFD-022" == 0
-- (review) Switcheroo with the first unit weaker, and with equal Might
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-145" .hand
  let (s2, a) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, b) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, e) ← putAt s3 s.you "OGN-051" s.bf0
  let r ← play s4 s.me c [a, b]
  let q ← play s4 s.me c [a, e]
  return r.mightNow a == some 5 && r.mightNow b == some 2 &&
    q.mightNow a == some 2 && q.mightNow e == some 2
-- (review) Temptation: to the place of a unit at a base, the unit goes to its base
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-129" .hand
  let (s2, a) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, b) ← put s2 s.you "OGN-051" .base
  let r ← play s3 s.me c [a, b]
  return (r.obj? a).any (·.loc.isNone) && (r.zone (.player s.you .base)).contains a
-- (review) Arise!: no Equipment, nothing happens; one Equipment, one new soldier ready, and
-- another soldier was already there, exhausted
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-198" .hand
  let (s2, old) ← put s1 s.me "TKN-Sand Soldier" .base
  let s2t := s2.tire old
  let (s3, _) ← put s2t s.me "SFD-042" .base
  let r ← play s3 s.me c
  let n ← play s2t s.me c
  return r.soldiers s.me == (2, 1) && n.soldiers s.me == (1, 0)
-- (review) Fae Porter at a base does not set the ability off; the move away from a battlefield
-- to a base does not either
#guard tsf fun s => do
  let (s1, p) ← put s s.me "SFD-125" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let a ← fire (s2.fund s.me 0 0 0 0 0 1) [.standardMoved p none]
  return (a.obj? u).any (·.loc.isNone) && (a.poolOf s.me).chaos == 1
-- (review) Defiant Dance: the changes end with the turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-196" .hand
  let (s2, a) ← put s1 s.me "OGN-001" .base
  let (s3, b) ← put s2 s.you "OGN-001" .base
  let r ← play s3 s.me c [a, b]
  let t := r.mapObjects endTurnObj
  return t.mightNow a == s3.mightNow a && t.mightNow b == s3.mightNow b

-- Angle Shot (SFD-011): attach an Equipment to a unit, or detach it (same controller), then draw 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-011" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let a ← play s3 s.me c [u, g] { fromEnd := some 1 }
  let hooked := s3.modObj g (fun o => { o with attached := some u })
  let d ← play hooked s.me c [u, g] { fromEnd := some 2 }
  return (a.obj? g).any (·.attached == some u) && a.handN s.me == s3.handN s.me &&
    (d.obj? g).any (·.attached == none) && d.handN s.me == s3.handN s.me
-- (a unit of the player and an Equipment of the opponent: they cannot be chosen together)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-011" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.you "SFD-042" .base
  return (play s3 s.me c [u, g]).isNone
-- (the enemy's own: the Equipment may be attached to the enemy's unit)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-011" .hand
  let (s2, u) ← put s1 s.you "OGN-051" .base
  let (s3, g) ← put s2 s.you "SFD-042" .base
  let a ← play s3 s.me c [u, g]
  return (a.obj? g).any (·.attached == some u)

-- Strike Down (SFD-107): an equipped friendly unit deals damage equal to its Might to an enemy
-- unit, then an Equipment is detached from it
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-107" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let (s4, e) ← put s3 s.you "OGN-001" .base
  let (s5, free) ← put s4 s.me "OGN-051" .base
  let s6 := s5.modObj g (fun o => { o with attached := some u })
  let r ← play s6 s.me c [u, e]
  return r.dmg e == (s6.mightNow u).map Int.toNat && (r.obj? g).any (·.attached == none) &&
    (play s6 s.me c [free, e]).isNone && (play s6 s.me c [u, free]).isNone

-- (the Equipment of another unit stays attached, whichever of the two was put first)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-107" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, v) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-001" .base
  let (a1, g) ← put s4 s.me "SFD-042" .base
  let (a2, g2) ← put a1 s.me "SFD-051" .base
  let (b1, h2) ← put s4 s.me "SFD-051" .base
  let (b2, h) ← put b1 s.me "SFD-042" .base
  let sa := (a2.modObj g (fun o => { o with attached := some u })).modObj g2
    (fun o => { o with attached := some v })
  let sb := (b2.modObj h (fun o => { o with attached := some u })).modObj h2
    (fun o => { o with attached := some v })
  let ra ← play sa s.me c [u, e]
  let rb ← play sb s.me c [u, e]
  return (ra.obj? g).any (·.attached == none) && (ra.obj? g2).any (·.attached == some v) &&
    (rb.obj? h).any (·.attached == none) && (rb.obj? h2).any (·.attached == some v)

-- Veiled Temple (SFD-221): conquer here, ready a friendly gear; an Equipment may be detached
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-221"
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let s4 := (s3.modObj g (fun o => { o with attached := some u })).tire g
  let a ← fire s4 [.scored s.me bf true] { pick := fun ts => ts == [g] }
  let b ← fire s4 [.scored s.me bf true] { pick := fun ts => ts == [g], yes := false }
  let c ← fire s4 [.scored s.me bf false] { pick := fun ts => ts == [g] }
  return a.tired g == some false && (a.obj? g).any (·.attached == none) &&
    b.tired g == some true && (b.obj? g).any (·.attached == some u) &&
    c.tired g == some true

-- Jae Medarda (SFD-142): draw 1 when its player chooses it with a spell
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, jae) ← put s1 s.me "SFD-142" .base
  let (s3, other) ← put s2 s.me "OGN-051" .base
  let a ← play s3 s.me c [jae]
  let b ← play s3 s.me c [other]
  let e ← fire s3 [.chosenBySpell s.you jae]
  return a.handN s.me == s3.handN s.me && b.handN s.me + 1 == s3.handN s.me &&
    e.handN s.me == s3.handN s.me

-- Irelia, Fervent (SFD-057): +1 Might this turn when she is chosen or readied
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, i) ← put s1 s.me "SFD-057" .base
  let a ← play s2 s.me c [i]
  let b ← fire s2 [.readied i]
  let n ← fire s2 [.chosenBySpell s.you i]
  return a.mightNow i == (s2.mightNow i).map (· + 1) &&
    b.mightNow i == (s2.mightNow i).map (· + 1) && n.mightNow i == s2.mightNow i

-- Spirit Wheel (SFD-144): when its player chooses a friendly unit, pay 1 and exhaust it to draw 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, w) ← put s1 s.me "SFD-144" .base
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-051" .base
  let a ← play s4 s.me c [u]
  let b ← play s4 s.me c [e]
  let n ← play s4 s.me c [u] { yes := false }
  let t ← play (s4.tire w) s.me c [u]
  let p ← cast (s4.fund s.me 1) s.me c (payOf s4 c) [u]
  return a.handN s.me == s4.handN s.me && a.tired w == some true &&
    b.handN s.me + 1 == s4.handN s.me && n.handN s.me + 1 == s4.handN s.me &&
    t.handN s.me + 1 == s4.handN s.me && p.tired w == some false

-- The caster's Spirit Wheel may pay for choosing its teammate's Unit. Its teammate's Wheel
-- does not fire, and the payment happens while Cleave and the draw are still on the Chain.
#guard tsf fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) initial).toOption
  let p := s.me
  let mate ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← s.players.find? (fun q => !config.mode.sameSide p q)
  let (s, wheel) ← put (s.fund p 2) p "SFD-144" .base
  let (s, other) ← put s mate "SFD-144" .base
  let (s, friend) ← put s mate "OGN-051" .base
  let (s, foe) ← put s enemy "OGN-051" .base
  let (s, cleave) ← put s p "OGN-004" .hand
  let castAt (target : ObjId) : Action := ⟨.player p, .playCard cleave ⟨1, []⟩ [target]⟩
  let (offered, _) ← (step 100 s (castAt friend)).toOption
  let (enemyCast, _) ← (step 100 s (castAt foe)).toOption
  let accept : Action := ⟨.player p, .putTrigger 0 [] (.pay [])⟩
  let (paid, _) ← (step 100 offered accept).toOption
  let done := settleChain {} 20 paid
  return (legalActions offered).contains accept && !(legalActions enemyCast).contains accept &&
    paid.tired wheel == some true && paid.tired other == some false && (paid.poolOf p).energy == 0 &&
    paid.handN p + 1 == s.handN p && done.handN p == s.handN p &&
    paid.kwAmount friend .assault == 0 && done.kwAmount friend .assault == 3

-- Blade Dancer (SFD-195), a Legend: when its player chooses a friendly unit, exhaust it and pay 1
-- Power to ready the unit; when they conquer, pay 1 Energy to ready it
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, l) ← put s1 s.me "SFD-195" .legendZone
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let tired := s3.tire u
  let a ← play tired s.me c [u]
  let b ← play (s3.tire l) s.me c [u]
  let (s4, bf) ← putBf s3 s.me "SFD-216"
  let k ← fire ((s4.tire l).rich s.me) [.scored s.me bf true]
  let m ← fire ((s4.tire l).fund s.me 0) [.scored s.me bf true]
  return a.tired u == some false && a.tired l == some true && b.tired u == some false &&
    k.tired l == some false && m.tired l == some true

-- Azir, Sovereign (SFD-177): when it attacks, the player may move their token units there
#guard tsf fun s => do
  let (s1, a) ← putAt s s.me "SFD-177" s.bf0
  let (s2, _) ← applyCreate s1 s.me a {} "Sand Soldier" (.const 1) .atBase false
  let (s3, plain) ← put s2 s.me "OGN-051" .base
  let tok := (s3.zone (.player s.me .base)).find? (fun o =>
    (s3.cardDef? o).any (·.name == "Sand Soldier"))
  let t ← tok
  let r ← fire s3 [.combatStarted s.bf0 s.me] { pick := (· == [t]) }
  let n ← fire s3 [.combatStarted s.bf0 s.me] { yes := false }
  let d ← fire s3 [.combatStarted s.bf0 s.you]
  return (r.obj? t).any (·.loc == some s.bf0) && (r.obj? plain).any (·.loc.isNone) &&
    (n.obj? t).any (·.loc.isNone) && (d.obj? t).any (·.loc.isNone)

-- Renata Glasc, Industrialist (SFD-171): the player's tokens enter ready
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-076" .hand
  let (s2, _) ← put s1 s.me "SFD-171" .base
  let (s3, c2) ← put s1 s.me "SFD-076" .hand
  let a ← play s2 s.me c
  let b ← play s3 s.me c2
  let mech (x : GameState) :=
    (x.zone (.player s.me .base)).find? (fun o => (x.cardDef? o).any (·.name == "Mech"))
  return (mech a).bind a.tired == some false && (mech b).bind b.tired == some true

-- (review) Angle Shot: "detach from that unit": an Equipment attached to another unit stays
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-011" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, v) ← put s2 s.me "OGN-051" .base
  let (s4, g) ← put s3 s.me "SFD-042" .base
  let hooked := s4.modObj g (fun o => { o with attached := some v })
  -- "detach" cannot be chosen for an Equipment attached to another unit: only "attach" is left
  let d ← play hooked s.me c [u, g] { fromEnd := some 1 }
  let e ← play hooked s.me c [u, g] { fromEnd := some 2 }
  return (d.obj? g).any (·.attached == some u) && d.handN s.me == hooked.handN s.me &&
    (e.obj? g).any (·.attached == some v)

-- (review) Blade Dancer: an enemy unit, a refusal, and no Power change nothing
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, l) ← put s1 s.me "SFD-195" .legendZone
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-051" .base
  let t := (s4.tire u).tire e
  let a ← play t s.me c [e]
  let n ← play t s.me c [u] { yes := false }
  let p ← cast (t.fund s.me 1) s.me c (payOf t c) [u]
  let ok ← play t s.me c [u]
  return a.tired e == some true && a.tired l == some false && n.tired u == some true &&
    n.tired l == some false && p.tired u == some true && p.tired l == some false &&
    ok.tired u == some false && ok.tired l == some true && (ok.poolOf s.me).fury == 11

-- (review) Renata: the opponent's Renata does not help; Gold stays exhausted; a unit card is played
-- exhausted as usual
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-076" .hand
  let (s2, _) ← put s1 s.you "SFD-171" .base
  let (t1, _) ← put s s.me "SFD-171" .base
  let (t2, bw) ← put t1 s.me "SFD-004" .hand
  let (t3, v) ← put t2 s.me "OGN-051" .hand
  let a ← play s2 s.me c
  let b ← play t3 s.me bw
  let u ← play t3 s.me v
  let mech (x : GameState) :=
    (x.zone (.player s.me .base)).find? (fun o => (x.cardDef? o).any (·.name == "Mech"))
  return (mech a).bind a.tired == some true &&
    (b.firstOf s.me .base "SFD-T03").bind b.tired == some true &&
    (u.firstOf s.me .base "OGN-051").bind u.tired == some true

-- (review) Veiled Temple: a gear that is not an Equipment is only readied; an enemy gear is no
-- choice
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-221"
  let (s2, g) ← put s1 s.me "OGN-098" .base
  let (s3, e) ← put s2 s.you "OGN-098" .base
  let t := (s3.tire g).tire e
  let a ← fire t [.scored s.me bf true] { pick := fun ts => ts == [g] }
  let picks ← firePicks t [.scored s.me bf true]
  return a.tired g == some false && picks.contains g && !picks.contains e
-- (ready it, but do not detach)
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-221"
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let t := (s3.modObj g (fun o => { o with attached := some u })).tire g
  let a ← fire t [.scored s.me bf true] { pick := fun ts => ts == [g], fromEnd := some 1 }
  return a.tired g == some false

-- (review) Azir: tokens at another battlefield come too; the opponent's tokens do not
#guard tsf fun s => do
  let other ← s.battlefields.find? (· != s.bf0)
  let (s1, a) ← putAt s s.me "SFD-177" s.bf0
  let (s2, _) ← applyCreate s1 s.me a {} "Sand Soldier" (.const 2) .atBase false
  let offsite ← s2.firstOf s.me .base "TKN-Sand Soldier"
  let spread := (moveByEffect s.me (some other) s2 offsite).1
  let (s3, _) ← applyCreate spread s.you a {} "Sand Soldier" (.const 1) .atBase false
  let mine (x : GameState) := (x.zone .battlefieldZone).filter (fun o =>
    (x.cardDef? o).any (·.name == "Sand Soldier") &&
      (x.obj? o).any (fun ob => ob.loc == some s.bf0 && ob.controller == s.me))
  let r ← fire s3 [.combatStarted s.bf0 s.me] { pick := fun ids => ids.length == 2 }
  return (spread.obj? offsite).any (·.loc == some other) &&
    (mine r).length == 2 && (r.zone (.player s.you .base)).length ==
    (s3.zone (.player s.you .base)).length
/-- Put the cards on top of the player's Main Deck, the first of the list on top; their ids. -/
meta def _root_.Riftbound.GameState.stackTop (s : GameState) (p : PlayerId) (cards : List String) :
    Option (GameState × List ObjId) :=
  let r := cards.foldlM (fun (acc : GameState × List ObjId) c => do
    let (s1, o) ← put acc.1 p c .mainDeck
    pure (s1, acc.2 ++ [o])) (s, [])
  r.map (fun (s1, ids) =>
    (s1.setZone (.player p .mainDeck)
      (ids ++ (s1.zone (.player p .mainDeck)).filter (fun o => !ids.contains o)), ids))

/-- The top card of the player's Main Deck. -/
meta def _root_.Riftbound.GameState.topCard (s : GameState) (p : PlayerId) : Option ObjId :=
  (s.zone (.player p .mainDeck)).head?

/-- The last card of the player's Main Deck, the bottom one. -/
meta def _root_.Riftbound.GameState.bottomCards (s : GameState) (p : PlayerId) (n : Nat) :
    List ObjId :=
  ((s.zone (.player p .mainDeck)).reverse.take n).reverse

/-- The cards of the bottom `n` places of the Main Deck of the player are the card. -/
meta def _root_.Riftbound.GameState.bottomIs (s : GameState) (p : PlayerId) (n : Nat)
    (code : String) : Bool :=
  (s.bottomCards p n).length == n &&
    (s.bottomCards p n).all (fun o => (s.cardDef? o).any (·.id.code == code))

/-- The number of cards in the Main Deck of the player. -/
meta def _root_.Riftbound.GameState.deckN (s : GameState) (p : PlayerId) : Nat :=
  (s.zone (.player p .mainDeck)).length

/-- The object is a card with the identifier. -/
meta def _root_.Riftbound.GameState.isCard (s : GameState) (code : String) (o : ObjId) : Bool :=
  (s.cardDef? o).any (·.id.code == code)

-- Apprentice Smith (SFD-041): when it moves, reveal the top card: a gear is drawn, else recycled
#guard tsf fun s => do
  let (s1, a) ← put s s.me "SFD-041" .base
  let (g, _) ← s1.stackTop s.me ["SFD-042"]
  let (u, _) ← s1.stackTop s.me ["OGN-051"]
  let r ← fire g [.standardMoved a none]
  let q ← fire u [.standardMoved a none]
  return r.countIn s.me .hand "SFD-042" == g.countIn s.me .hand "SFD-042" + 1 &&
    r.deckN s.me + 1 == g.deckN s.me &&
    q.countIn s.me .hand "OGN-051" == u.countIn s.me .hand "OGN-051" &&
    q.deckN s.me == u.deckN s.me && q.bottomIs s.me 1 "OGN-051"

-- Stellacorn Herder draws for either direction of movement, including a move by Flash.
#guard tsf fun s => do
  let p := s.me
  let field := s.bf0
  let (s, herder) ← put (s.control p field) p "SFD-048" .base
  let (s, flash) ← put s p "OGS-011" .hand
  let (queued, _) ← (step 100 s ⟨.player p, .standardMove herder (.battlefield field)⟩).toOption
  let arrived := settleChain {} 12 queued
  let returned ← play arrived p flash [herder]
  return arrived.deckN p + 1 == s.deckN p && returned.deckN p + 1 == arrived.deckN p &&
    returned.countIn p .base "SFD-048" == 1 && returned.deckN s.you == s.deckN s.you

-- Treasure Hunter plays a new exhausted Gold each time it moves, even on returning to Base.
#guard tsf fun s => do
  let p := s.me
  let field := s.bf0
  let (s, hunter) ← put (s.control p field) p "SFD-130" .base
  let (s, flash) ← put s p "OGS-011" .hand
  let (queued, _) ← (step 100 s ⟨.player p, .standardMove hunter (.battlefield field)⟩).toOption
  let arrived := settleChain {} 12 queued
  let returned ← play arrived p flash [hunter]
  let gold := (returned.zone (.player p .base)).filter (returned.isCard "SFD-T03")
  return arrived.countIn p .base "SFD-T03" == 1 && gold.length == 2 &&
    gold.all (fun id => returned.tired id == some true) && returned.countIn p .base "SFD-130" == 1

-- Ornn, Blacksmith (SFD-058): when played or when it holds, look at the top 4 cards: a gear among
-- them may be drawn, the rest are recycled
#guard tsf fun s => do
  let (s1, o) ← put s s.me "SFD-058" .base
  let (d, _) ← s1.stackTop s.me ["OGN-051", "SFD-042", "OGN-051", "OGN-051"]
  let a ← fire d [.played s.me o]
  let b ← fire d [.played s.me o] { yes := false }
  let (h1, bf) ← putBf s1 s.me "SFD-216"
  let (h2, _) ← putAt h1 s.me "SFD-058" bf
  let (h3, _) ← h2.stackTop s.me ["OGN-051", "SFD-042", "OGN-051", "OGN-051"]
  let c ← fire h3 [.scored s.me bf false]
  let e ← fire h3 [.scored s.me bf true]
  return a.countIn s.me .hand "SFD-042" == d.countIn s.me .hand "SFD-042" + 1 &&
    a.deckN s.me + 1 == d.deckN s.me && a.bottomIs s.me 3 "OGN-051" &&
    b.countIn s.me .hand "SFD-042" == d.countIn s.me .hand "SFD-042" &&
    b.deckN s.me == d.deckN s.me && b.bottomIs s.me 1 "OGN-051" &&
    c.countIn s.me .hand "SFD-042" == h3.countIn s.me .hand "SFD-042" + 1 &&
    e.deckN s.me == h3.deckN s.me

-- Called Shot (SFD-122): look at the top 2 cards, draw one and recycle the other
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-122" .hand
  let (d, _) ← s1.stackTop s.me ["OGN-051", "SFD-042"]
  let r ← play d s.me c
  return r.deckN s.me + 1 == d.deckN s.me && r.handN s.me == d.handN s.me &&
    (r.countIn s.me .hand "OGN-051" + r.countIn s.me .hand "SFD-042" ==
      d.countIn s.me .hand "OGN-051" + d.countIn s.me .hand "SFD-042" + 1)

-- Ravenbloom Conservatory (SFD-215): when its player defends here, reveal the top card: a spell is
-- put in the hand, anything else is recycled
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-215"
  let (s2, _) ← putAt s1 s.me "OGN-051" bf
  let (s3, _) ← putAt s2 s.you "OGN-051" bf
  let (sp, _) ← s3.stackTop s.me ["OGN-004"]
  let (un, _) ← s3.stackTop s.me ["OGN-051"]
  let a ← fire sp [.combatStarted bf s.you]
  let b ← fire un [.combatStarted bf s.you]
  let c ← fire sp [.combatStarted bf s.me]
  return a.countIn s.me .hand "OGN-004" == sp.countIn s.me .hand "OGN-004" + 1 &&
    b.countIn s.me .hand "OGN-051" == un.countIn s.me .hand "OGN-051" &&
    b.deckN s.me == un.deckN s.me && b.bottomIs s.me 1 "OGN-051" &&
    c.countIn s.me .hand "OGN-004" == sp.countIn s.me .hand "OGN-004"

-- Void Rush (SFD-188): reveal the top 2 cards, play one for 2 less, draw the ones not played
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-188" .hand
  let (d, _) ← s1.stackTop s.me ["OGN-001", "SFD-042"]
  let r ← play d s.me c [] { obj := d.isCard "OGN-001" }
  let n ← play d s.me c [] { yes := false }
  return r.countIn s.me .base "OGN-001" == 1 && r.countIn s.me .hand "SFD-042" ==
      d.countIn s.me .hand "SFD-042" + 1 && (r.poolOf s.me).energy == 12 - 2 - 3 &&
    n.countIn s.me .base "OGN-001" == 0 && n.countIn s.me .hand "OGN-001" ==
      d.countIn s.me .hand "OGN-001" + 1 && n.countIn s.me .hand "SFD-042" ==
      d.countIn s.me .hand "SFD-042" + 1

-- Rek'Sai, Swarm Queen (SFD-170): when it attacks, may reveal the top 2, play one, recycle the rest
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-170" s.bf0
  let (d, _) ← s1.stackTop s.me ["OGN-051", "SFD-042"]
  let a ← fire (d.rich s.me) [.combatStarted s.bf0 s.me] { obj := d.isCard "OGN-051" }
  let n ← fire (d.rich s.me) [.combatStarted s.bf0 s.me] { yes := false }
  -- the Unit is played here, where Rek'Sai attacks
  return (a.zone .battlefieldZone).any (fun o => a.isCard "OGN-051" o &&
      (a.obj? o).any (·.loc == some s.bf0)) && a.countIn s.me .base "OGN-051" == 0 &&
    a.deckN s.me + 1 == d.deckN s.me &&
    a.bottomIs s.me 1 "SFD-042" && n.countIn s.me .base "OGN-051" == 0 &&
    n.deckN s.me == d.deckN s.me && r != s.bf0

-- Void Burrower (SFD-187), a Legend: when its player conquers, it may be exhausted to reveal the
-- top 2 cards, play one and recycle the rest
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-187" .legendZone
  let (bfs, bf) ← putBf s1 s.me "SFD-216"
  let (d, _) ← bfs.stackTop s.me ["OGN-051", "SFD-042"]
  let a ← fire (d.rich s.me) [.scored s.me bf true] { obj := d.isCard "OGN-051" }
  let t ← fire ((d.tire l).rich s.me) [.scored s.me bf true]
  return a.countIn s.me .base "OGN-051" == 1 && a.tired l == some true &&
    t.countIn s.me .base "OGN-051" == 0 && t.deckN s.me == d.deckN s.me

-- Here to Help (SFD-111): play a unit from the hand to a battlefield the player controls, for 3
-- less
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-111" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .hand
  let s3 := s2.control s.me s.bf0
  let r ← play s3 s.me c []
  let n ← play s3 s.me c [] { yes := false }
  let nowhere ← play s2 s.me c []
  let there := (r.zone .battlefieldZone).any (fun o => r.isCard "OGN-001" o &&
    (r.obj? o).any (·.loc == some s.bf0))
  return there && (r.poolOf s.me).energy == 12 - 2 - 2 && n.countIn s.me .hand "OGN-001" == 1 &&
    nowhere.countIn s.me .hand "OGN-001" == 1 && (play s3 s.me c [s.bf0]).isNone

-- Rumble, Hotheaded (SFD-026): when it conquers, may recycle another friendly unit to play a Mech
-- from the Trash, its Energy cost reduced by the Might of the recycled unit; Mechs have Assault
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-026" s.bf0
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← put s2 s.me "SFD-062" .trash
  let (s4, m) ← put s3 s.me "SFD-062" .base
  let a ← fire (s4.rich s.me) [.conquerActivated r] { pick := fun ts => ts == [u] }
  let n ← fire (s4.rich s.me) [.conquerActivated r] { pick := fun ts => ts == [u], yes := false }
  return a.countIn s.me .base "SFD-062" == 2 && (a.obj? u).isNone &&
    (a.poolOf s.me).energy == 12 - 1 && n.countIn s.me .base "SFD-062" == 1 &&
    (n.obj? u).isSome && s4.kwAmount m .assault == 1 && s4.kwAmount u .assault == 0

-- (Fizz: a spell with Energy cost 4 is not a legal choice)
#guard tsf fun s => do
  let (s1, f) ← put s s.me "SFD-140" .hand
  let (s2, sp) ← put s1 s.me "SFD-076" .trash
  let r ← play s2 s.me f
  return r.countIn s.me .trash "SFD-076" == 1 && (r.obj? sp).isSome &&
    r.countNamed s.me .base "Mech" == 0

-- Fizz, Trickster (SFD-140): when played, may play a spell from the Trash (Energy cost 3 or less),
-- ignoring its Energy cost; it is recycled after
#guard tsf fun s => do
  let (s1, f) ← put s s.me "SFD-140" .hand
  let (s2, sp) ← put s1 s.me "SFD-204" .trash
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let (s4, big) ← put s3 s.me "SFD-147" .trash
  let a ← play (s4.tire u) s.me f
  let n ← play (s4.tire u) s.me f [] { yes := false }
  return a.tired u == some false && (a.obj? sp).isNone && a.countIn s.me .trash "SFD-204" == 0 &&
    n.tired u == some true && n.countIn s.me .trash "SFD-204" == 1 &&
    a.countIn s.me .trash "SFD-147" == 1 && (a.poolOf s.me).energy == 12 - 3 - 0 - 0 &&
    (a.obj? big).isSome

private meta def fizzResponse : Nat → GameState → Option (GameState × ObjId)
  | 0, _ => none
  | n + 1, s => do
    if let some item := (s.zone .chain).find? (fun id =>
        (s.obj? id).any (fun o => o.limitedSpellExit == .recycle && o.pendingSpellPlay.isNone)) then
      return (s, item)
    let action ← (legalFrameActions s).find? (fun a => match a.kind with
      | .decide false | .putTrigger _ _ .skip => false
      | _ => true)
    let (next, _) ← (step 100 s action).toOption
    fizzResponse n next

-- A finalized Spell played by Fizz is recycled directly when it resolves or is countered.
-- On the Hunt still requires both Power, and countering it does not ready any Units.
#guard tsf fun s => do
  let p := s.me
  let (s, fizz) ← put s p "SFD-140" .hand
  let (s, _) ← put s p "SFD-204" .trash
  let (s, unit) ← put s p "OGN-051" .base
  let s := s.tire unit
  let castFizz : Action := ⟨.player p, .playCard fizz ⟨3, [.chaos]⟩ []⟩
  let (started, _) ← (step 100 (s.fund p 3 (chaos := 3)) castFizz).toOption
  let (short, _) ← (step 100 (s.fund p 3 (chaos := 2)) castFizz).toOption
  let skip : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (response, item) ← fizzResponse 14 started
  let normal := finishItem response item
  let stopped := counterObj response item
  let resolved := settleChain {} 12 response
  let (selfBanish, ownEvents) ← applyPrim response p item {} (.banish .self)
  let deck := Zone.player p .mainDeck
  let normalCard ← (normal.1.zone deck).getLast?
  let counteredCard ← (stopped.1.zone deck).getLast?
  return (legalFrameActions started).contains skip && (started.zone .chain).isEmpty &&
    (fizzResponse 14 short).isNone && (response.poolOf p).chaos == 0 &&
    normal.2 == [.moved item normalCard deck, .recycled p, .spellResolved p normalCard] &&
    stopped.2 == [.moved item counteredCard deck, .recycled p] &&
    normal.1.isCard "SFD-204" normalCard && stopped.1.isCard "SFD-204" counteredCard &&
    (normal.1.zone deck).dropLast == response.zone deck &&
    (stopped.1.zone deck).dropLast == response.zone deck &&
    stopped.1.tired unit == some true && resolved.tired unit == some false &&
    selfBanish.countIn p .banishment "SFD-204" == 1 && (finishItem selfBanish item).2.isEmpty &&
    !(ownEvents.contains (.recycled p))

-- (review) playing for a reduced cost: the Energy goes down to the floor of 0 and the Power is paid
-- in full; with no Power in the Pool, nothing is paid and the card is not played
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-002" .hand
  let rich := s1.fund s.me 3 1
  let ok := playReducedOne s.me 3 none rich u
  let poor := playReducedOne s.me 3 none (s1.fund s.me 3) u
  let (s2, v) ← put s s.me "OGN-051" .hand
  let floor := playReducedOne s.me 10 none (s2.fund s.me 0) v
  return ok.1.countIn s.me .base "SFD-002" == 1 && (ok.1.poolOf s.me).energy == 0 &&
    (ok.1.poolOf s.me).fury == 0 && poor.1.countIn s.me .base "SFD-002" == 0 &&
    (poor.1.poolOf s.me).energy == 3 && floor.1.countIn s.me .base "OGN-051" == 1

-- (review) Rek'Sai and Void Burrower pay the whole cost of the unit they play
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-170" s.bf0
  let (d, ids) ← s1.stackTop s.me ["OGN-051", "SFD-042"]
  let cost := (d.energyCost? s.me (ids.head?.getD ⟨0⟩)).getD 0
  let a ← fire (d.rich s.me) [.combatStarted s.bf0 s.me] { obj := d.isCard "OGN-051" }
  return (a.zone .battlefieldZone).any (fun o => a.isCard "OGN-051" o) &&
    (a.poolOf s.me).energy + cost == 12 && cost > 0

-- (review) Called Shot: the card not drawn goes to the bottom of the deck
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-122" .hand
  let (d, _) ← s1.stackTop s.me ["OGN-051", "SFD-042"]
  let r ← play d s.me c
  let gainedA := r.countIn s.me .hand "OGN-051" == d.countIn s.me .hand "OGN-051" + 1
  let gainedB := r.countIn s.me .hand "SFD-042" == d.countIn s.me .hand "SFD-042" + 1
  return (gainedA && r.bottomIs s.me 1 "SFD-042") || (gainedB && r.bottomIs s.me 1 "OGN-051")

-- Void Rush plays a spell it reveals: with a legal target the spell is cast (it goes on the Chain,
-- and resolves), for 2 less Energy; with no legal target it is drawn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-188" .hand
  let (s2, _) ← put s1 s.me "OGN-051" .base
  let (d, _) ← s2.stackTop s.me ["OGN-004", "SFD-042"]
  let r ← play d s.me c [] { obj := d.isCard "OGN-004" }
  return r.countIn s.me .trash "OGN-004" == 1 && r.countIn s.me .hand "OGN-004" ==
      d.countIn s.me .hand "OGN-004" && (r.poolOf s.me).energy == 12 - 2 &&
    r.countIn s.me .hand "SFD-042" == d.countIn s.me .hand "SFD-042" + 1

-- Void Rush draws both revealed Spells when neither has a legal target.
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-188" .hand
  let (d, _) ← s1.stackTop s.me ["OGN-004", "OGN-004"]
  let r ← play d s.me c [] { obj := d.isCard "OGN-004" }
  return r.countIn s.me .hand "OGN-004" == d.countIn s.me .hand "OGN-004" + 2

-- (review) Rumble: if the unit chosen is gone when the ability resolves, no Mech is played
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-026" s.bf0
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← put s2 s.me "SFD-062" .trash
  let s4 := s3.rich s.me
  let s5 := { s4 with pending := insertTriggers (s4.detect [.conquerActivated r]) s4.pending }
  let r1 ← match advance 100 s5 [] with
    | .ok (x, _) => some x
    | .error _ => none
  let r2 := settleChain { pick := fun ts => ts == [u] } 1 r1
  let r3 := (killObj r2 u).1
  let r4 := settleChain {} 12 r3
  return r4.countIn s.me .base "SFD-062" == 0 && r4.countIn s.me .trash "SFD-062" == 1
-- Assembly Rig recycles an eligible Unit during payment, then plays a Mech when it resolves.
#guard tsf fun s => do
  let p := s.me
  let (s, rig) ← put s p "SFD-019" .base
  let (s, unit) ← put s p "OGN-051" .trash
  let (s, spell) ← put s p "OGN-004" .trash
  let (s, other) ← put s s.you "OGN-051" .trash
  let act : Action := ⟨.player p, .activate rig 0 ⟨1, [.fury]⟩ []⟩
  let funded := s.fund p 1 1
  let (paying, _) ← (step 100 funded act).toOption
  let pick (id : ObjId) : Action := ⟨.player p, .choose id⟩
  let (paid, events) ← (step 100 paying (pick unit)).toOption
  let done := settleChain {} 12 paid
  let mech ← (done.zone (.player p .base)).find?
    (fun id => (done.cardDef? id).any (·.name == "Mech"))
  return (legalFrameActions paying).contains (pick unit) &&
    !(step 100 paying (pick spell)).isOk && !(step 100 paying (pick other)).isOk &&
    paid.zone (.player p .trash) == [spell] && events.contains (.recycled p) &&
    paid.countNamed p .base "Mech" == 0 && paid.tired rig == some true &&
    paid.deckN p == s.deckN p + 1 && done.mightNow mech == some 3 && done.tired mech == some true &&
    (done.poolOf p).energy == 0 && (done.poolOf p).fury == 0

-- Poro Snax (SFD-046): draw 1 when played; pay 1 Calm, exhaust, kill it: draw 1
#guard tsf fun s => do
  let p := s.me
  let (s, card) ← put s p "SFD-046" .hand
  let played ← play s p card
  let gear ← played.firstOf p .base "SFD-046"
  let funded := played.fund p 1 (calm := 1)
  let useGear (pay : RunePool.Payment) : Action := ⟨.player p, .activate gear 1 pay []⟩
  let answer := useGear ⟨1, [.calm]⟩
  let (queued, events) ← (step 100 funded answer).toOption
  let resolved := settleChain {} 12 queued
  return played.handN p == s.handN p && played.deckN p + 1 == s.deckN p &&
    queued.handN p == funded.handN p && queued.countIn p .trash "SFD-046" == 1 &&
    (queued.obj? gear).isNone && queued.tired gear == none && !(queued.zone .chain).isEmpty &&
    (queued.poolOf p).total == 0 && events.any (fun
      | .died _ who => who == p
      | _ => false) &&
    resolved.countIn p .trash "SFD-046" == 1 && resolved.handN p == funded.handN p + 1 &&
    !(step 100 funded (useGear ⟨1, []⟩)).isOk && !(step 100 (funded.tire gear) answer).isOk

-- Premonition answers an opposing Spell on the Chain and draws only for its caster.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let (s, opposing) ← put s p "SFD-087" .hand
  let (s, answer) ← put s q "SFD-087" .hand
  let declared ← castStop s p opposing
  let (reaction, _) ← (step 100 declared ⟨.player p, .pass⟩).toOption
  let pay := payOf reaction answer
  let kind : ActionKind := .playCard answer pay []
  let funded := reaction.rich q
  let (both, _) ← (step 100 funded ⟨.player q, kind⟩).toOption
  let once := settleChain {} 2 both
  let done := settleChain {} 12 both
  return (both.zone .chain).length == 2 &&
    once.deckN q + 3 == both.deckN q && once.deckN p == both.deckN p &&
    done.deckN q + 3 == both.deckN q && done.deckN p + 3 == both.deckN p

-- Punch First can strengthen an enemy Unit and loses exactly its bonus at turn end.
#guard tsf fun s => do
  let (s, card) ← put s s.me "SFD-097" .hand
  let (s, unit) ← put s s.you "OGN-051" .base
  let (s, gear) ← put s s.me "SFD-064" .base
  let resolved ← play s s.me card [unit]
  return resolved.mightNow unit == (s.mightNow unit).map (· + 5) &&
    (resolved.mapObjects endTurnObj).mightNow unit == s.mightNow unit &&
    (play s s.me card [gear]).isNone

-- Feral Strength and Frigid Touch support separate targets and stacking for paid Repeat.
#guard tsf fun s => do
  let p := s.me
  let (s, ally) ← put s p "SFD-158" .base
  let (s, foe) ← put s s.you "SFD-158" .base
  let (s, strength) ← put s p "SFD-034" .hand
  let (s, frigid) ← put s p "SFD-066" .hand
  let pick : SpellPick := .withCosts (.thenRepeat .plain 1 .plain) false 1
  let rich := s.rich p
  let boosted ← cast rich p strength ⟨4, []⟩ [foe, ally] (pick := pick)
  let weakened ← cast rich p frigid ⟨4, []⟩ [foe, foe] (pick := pick)
  let single ← cast rich p frigid ⟨2, []⟩ [ally]
  return boosted.mightNow foe == some 8 && boosted.mightNow ally == some 8 &&
    weakened.mightNow foe == some 2 && weakened.mightNow ally == some 6 &&
    single.mightNow ally == some 4 && single.mightNow foe == some 6 &&
    (weakened.mapObjects endTurnObj).mightNow foe == some 6 &&
    (boosted.mapObjects endTurnObj).mightNow ally == some 6 &&
    (cast rich p frigid ⟨3, []⟩ [foe, foe] (pick := pick)).isNone

-- Honest Broker's Deathknell plays an exhausted Gold only after it dies.
#guard tsf fun s => do
  let p := s.me
  let (s, unit) ← put s p "SFD-155" .base
  let goldBefore := s.countNamed p .base "Gold"
  let (dying, events) := killObj s unit
  let resolved ← fire dying events
  let gold ← resolved.firstOf p .base "SFD-T03"
  let (left, leave) ← moveObj s unit (.player p .hand)
  return resolved.countNamed p .base "Gold" == goldBefore + 1 &&
    resolved.tired gold == some true && (left.detect [.moved unit leave (.player p .hand)]).isEmpty

-- Renata Glasc, Mastermind (SFD-088): at a battlefield only: pay 1 Mind to draw 1; pay 4 Mind and
-- exhaust to score 1 point (an ability with a guard cannot be used while the guard is false)
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-088" s.bf0
  let (s2, q) ← put s s.me "SFD-088" .base
  let a ← activate s1 s.me r 0 [] ⟨1, [.mind]⟩
  let b ← activate s1 s.me r 1 [] ⟨4, [.mind, .mind, .mind, .mind]⟩
  return a.handN s.me == s1.handN s.me + 1 && b.pointsOf s.me == s1.pointsOf s.me + 1 &&
    b.tired r == some true && (activate s2 s.me q 0 [] ⟨1, [.mind]⟩).isNone &&
    (activate s2 s.me q 1 [] ⟨4, [.mind, .mind, .mind, .mind]⟩).isNone

-- Azir, Ascendant (SFD-050): pay 1 Calm: swap places with a friendly unit; may take its Equipment;
-- once per turn
#guard tsf fun s => do
  let (s1, az) ← put s s.me "SFD-050" .base
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let hooked := s3.modObj g (fun o => { o with attached := some u })
  let r ← activate hooked s.me az 0 [u, g] ⟨0, [.calm]⟩
  let n ← activate hooked s.me az 0 [u] ⟨0, [.calm]⟩
  return (r.obj? az).any (·.loc == some s.bf0) && (r.obj? u).any (·.loc.isNone) &&
    (r.obj? g).any (·.attached == some az) && (n.obj? g).any (·.attached == some u) &&
    (n.obj? az).any (·.loc == some s.bf0) && (activate r s.me az 0 [u] ⟨0, [.calm]⟩).isNone &&
    (r.obj? az).any (·.used.length == 1) &&
    (activate hooked s.me az 0 [u, az] ⟨0, [.calm]⟩).isNone

-- Grandmaster at Arms (SFD-193), a Legend: attach a detached Equipment to a unit (pay 1, exhaust);
-- move an attached Equipment to another unit (exhaust)
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-193" .legendZone
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, v) ← put s2 s.me "OGN-051" .base
  let (s4, g) ← put s3 s.me "SFD-042" .base
  let a ← activate s4 s.me l 0 [g, u] ⟨1, []⟩
  let hooked := s4.modObj g (fun o => { o with attached := some u })
  let b ← activate hooked s.me l 1 [g, v]
  return (a.obj? g).any (·.attached == some u) && a.tired l == some true &&
    (b.obj? g).any (·.attached == some v) && b.tired l == some true &&
    (activate hooked s.me l 0 [g, v] ⟨1, []⟩).isNone && (activate s4 s.me l 1 [g, v]).isNone

-- Purifier (SFD-183), a Legend: the units with an Equipment have Assault
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-183" .legendZone
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, w) ← put s2 s.me "OGN-051" .base
  let (s4, g) ← put s3 s.me "SFD-042" .base
  let (s5, e) ← put s4 s.you "OGN-051" .base
  let (s6, h) ← put s5 s.you "SFD-042" .base
  let s7 := (s6.modObj g (fun o => { o with attached := some u })).modObj h
    (fun o => { o with attached := some e })
  let (s8, g2) ← put s7 s.me "SFD-042" .base
  let s9 := s8.modObj g2 (fun o => { o with attached := some u })
  return s7.kwAmount u .assault == 1 && s7.kwAmount w .assault == 0 && s7.kwAmount e .assault == 0 &&
    s9.kwAmount u .assault == 2

-- Lonely Poro (SFD-036): when it dies alone, draw 1 (a real death by `killObj`)
#guard tsf fun s => do
  let (s1, x) ← putAt s s.me "SFD-036" s.bf0
  let (b1, y) ← put s s.me "SFD-036" .base
  let (s2, _) ← put b1 s.me "OGN-051" .base
  let (s3, _) ← putAt s1 s.me "OGN-051" s.bf0
  let (s4, _) ← putAt s1 s.me "OGN-051" s.bf0
  let (s5, _) ← putAt s1 s.you "OGN-051" s.bf0
  let (s6, _) ← put s1 s.me "OGN-051" .base
  let die (st : GameState) (u : ObjId) : Option GameState :=
    let (st1, evs) := killObj st u
    fire st1 evs
  let _ := s4
  let alone ← die s1 x
  let company ← die s3 x
  let elsewhere ← die s6 x
  let enemy ← die s5 x
  let atBase ← die b1 y
  let baseCompany ← die s2 y
  return alone.handN s.me == s1.handN s.me + 1 && company.handN s.me == s3.handN s.me &&
    elsewhere.handN s.me == s6.handN s.me + 1 && enemy.handN s.me == s5.handN s.me + 1 &&
    atBase.handN s.me == b1.handN s.me + 1 && baseCompany.handN s.me == s2.handN s.me

-- Unsung Hero (SFD-167): when it dies and was Mighty (a real death), draw 2
#guard tsf fun s => do
  let (s1, x) ← put s s.me "SFD-167" .base
  let big := s1.modObj x (fun o => { o with mightMods := [{ amount := 3, ends := .never }] })
  let die (st : GameState) : Option GameState :=
    let (st1, evs) := killObj st x
    fire st1 evs
  let a ← die big
  let b ← die s1
  return a.handN s.me == big.handN s.me + 2 && b.handN s.me == s1.handN s.me

-- Zaun Punk (SFD-160): when played, may kill a friendly gear; if so, kill a gear
#guard tsf fun s => do
  let (s1, z) ← put s s.me "SFD-160" .hand
  let (s2, mine) ← put s1 s.me "SFD-042" .base
  let (s3, theirs) ← put s2 s.you "SFD-042" .base
  let a ← play s3 s.me z [mine] { obj := fun o => o == theirs }
  let n ← play s3 s.me z []
  let none_ ← play s1 s.me z
  return (a.obj? mine).isNone && (a.obj? theirs).isNone && (n.obj? mine).isSome &&
    (n.obj? theirs).isSome && none_.countIn s.me .base "SFD-160" == 1 &&
    -- a gear of the opponent cannot pay the cost
    (play s3 s.me z [theirs]).isNone

-- Card Sharp (SFD-081): the player and each opponent may play a Gold; for each opponent who did,
-- the player plays another
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-081" .hand
  let a ← play s1 s.me c
  let n ← play s1 s.me c [] { yes := false }
  return a.countIn s.me .base "SFD-T03" == 2 && a.countIn s.you .base "SFD-T03" == 1 &&
    n.countIn s.me .base "SFD-T03" == 0 && n.countIn s.you .base "SFD-T03" == 0

-- Assembly Rig cannot be activated when its Trash lacks an eligible Unit.
#guard tsf fun s => do
  let (s1, rig) ← put s s.me "SFD-019" .base
  let (s2, _) ← put s1 s.me "OGN-004" .trash
  return (activate s1 s.me rig 0 [] ⟨1, [.fury]⟩).isNone &&
    (activate s2 s.me rig 0 [] ⟨1, [.fury]⟩).isNone

-- (review) Zaun Punk: with only an enemy gear, nothing is killed (the cost is a friendly gear)
#guard tsf fun s => do
  let (s1, z) ← put s s.me "SFD-160" .hand
  let (s2, theirs) ← put s1 s.you "SFD-042" .base
  let r ← play s2 s.me z
  return (r.obj? theirs).isSome && r.countIn s.me .base "SFD-160" == 1 &&
    (play s2 s.me z [theirs]).isNone

-- (review) Azir, Ascendant cannot choose itself; Grandmaster at Arms moves only its player's
-- Equipment; Lonely Poro's enemies at the same place do not count (above)
#guard tsf fun s => do
  let (s1, az) ← put s s.me "SFD-050" .base
  return (activate s1 s.me az 0 [az] ⟨0, [.calm]⟩).isNone
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-193" .legendZone
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.you "SFD-042" .base
  return (activate s3 s.me l 0 [g, u] ⟨1, []⟩).isNone

-- (review) Azir, Ascendant: if it left play before the ability resolves, nothing is swapped
#guard tsf fun s => do
  let (s1, az) ← put s s.me "SFD-050" .base
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let act : Action := ⟨.player s.me, .activate az 0 ⟨0, [.calm]⟩ [u]⟩
  let s3 ← match step 100 (s2.rich s.me) act with
    | .ok (x, _) => some x
    | .error _ => none
  let s4 := (killObj s3 az).1
  let r := settleChain {} 12 s4
  return (r.obj? u).any (·.loc == some s.bf0)

/-- Run the effect of the object `src` of the player, with the objects chosen in `slots`, and let
the questions it asks be answered. -/
meta def runBody (s : GameState) (p : PlayerId) (src : ObjId) (slots : List ObjId) (body : Effect)
    (says : Says := {}) : Option GameState :=
  let env : Env := { slots := slots.map Value.obj }
  let s0 := { s with pending := Frame.run p src env (EffectList.cons body EffectList.nil) ::
    s.pending }
  match advance 100 s0 [] with
  | .ok (s1, _) => some (settleChain says 12 s1)
  | .error _ => none

/-- The effect of the card. -/
meta def effectOf (code : String) : Option EffectDef :=
  (RiftboundCards.db.find? ⟨code⟩).bind (·.spellEffect)

-- Jaull-Fish (SFD-103): costs 2 Energy less for each of its player's Mighty units
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-103" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let (s3, _) ← put s2 s.me "OGN-001" .base
  let (s4, _) ← put s3 s.you "OGN-001" .base
  let (s5, _) ← put s4 s.me "OGN-051" .base
  return s1.energyCost? s.me j == some 7 && s2.energyCost? s.me j == some 5 &&
    s5.energyCost? s.me j == some 3

-- Hard Bargain (SFD-136): counter a spell unless its controller pays 2 Energy
#guard tsf fun s => do
  let (s1, sp) ← onChain s s.you "OGN-004"
  let (s2, hb) ← put s1 s.me "SFD-136" .hand
  let body := ((effectOf "SFD-136").map (·.body)).getD .nop
  let poor ← runBody (s2.fund s.you 1) s.me hb [sp] body
  let rich ← runBody (s2.fund s.you 2) s.me hb [sp] body
  let refuse ← runBody (s2.fund s.you 2) s.me hb [sp] body { fromEnd := some 2 }
  return (poor.zone .chain).isEmpty && (poor.poolOf s.you).energy == 1 &&
    (rich.zone .chain).length == 1 && (rich.poolOf s.you).energy == 0 &&
    (refuse.zone .chain).isEmpty && (refuse.poolOf s.you).energy == 2 &&
    (s2.zone .chain).length == 1

-- Not So Fast (SFD-045): counter an enemy spell that chooses a unit or gear of its player
#guard tsf fun s => do
  let (s1, mine) ← put s s.me "OGN-051" .base
  let (s2, sp) ← onChain s1 s.you "OGN-004"
  let (s3, nsf) ← put s2 s.me "SFD-045" .hand
  let (s4, other) ← put s3 s.you "OGN-051" .base
  let on (st : GameState) (sp' : ObjId) (t : ObjId) :=
    let st' := st.modObj sp' (fun o => { o with targets := [t] })
    match effectOf "SFD-045" with
    | some e => targetsOk st' s.me nsf st'.mightTable e.choices [sp']
    | none => false
  return on s4 sp mine && !on s4 sp other

-- Riposte (SFD-206): counter a spell and give a friendly unit +Might equal to its Energy cost
#guard tsf fun s => do
  let (s1, u) ← put s s.me "OGN-051" .base
  let (s2, sp) ← onChain s1 s.you "OGN-004"
  let (s3, rip) ← put s2 s.me "SFD-206" .hand
  let body := ((effectOf "SFD-206").map (·.body)).getD .nop
  let r ← runBody s3 s.me rip [u, sp] body
  return (r.zone .chain).isEmpty && r.mightNow u == (s3.mightNow u).map (· + 1)

-- Dauntless Vanguard (SFD-093): may be played to a battlefield where an enemy unit is
#guard tsf fun s => do
  let (s1, v) ← put s s.me "SFD-093" .hand
  let (s2, _) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, bf2) ← putBf s2 s.me "SFD-216"
  let r ← play s3 s.me v [s.bf0]
  return (r.zone .battlefieldZone).any (fun o => r.isCard "SFD-093" o &&
      (r.obj? o).any (·.loc == some s.bf0)) &&
    (play s3 s.me v [bf2]).isNone

-- Lucian, Gunslinger (SFD-028): when it attacks, damage equal to its Assault to an enemy unit here
#guard tsf fun s => do
  let (s1, l) ← putAt s s.me "SFD-028" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-001" s.bf0
  let boosted := s2.modObj l (fun o => { o with tempKws := [(⟨.assault, .amount 2⟩, .turn)] })
  let a ← fire s2 [.combatStarted s.bf0 s.me]
  let b ← fire boosted [.combatStarted s.bf0 s.me]
  let d ← fire s2 [.combatStarted s.bf0 s.you]
  return a.dmg e == some 1 && b.dmg e == some 3 && d.dmg e == some 0

-- Drag Under (SFD-164): kill a unit at a battlefield
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-164" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, v) ← put s2 s.you "OGN-001" .base
  let r ← play s3 s.me c [u]
  return (r.obj? u).isNone && (play s3 s.me c [v]).isNone

-- (review) Hard Bargain: the opponent's spell only (not one's own); a Repeat does not ask again
-- once the spell is gone; a spell that left the Chain is not asked about
#guard tsf fun s => do
  let (s1, sp) ← onChain s s.you "OGN-004"
  let (s2, mine) ← onChain s1 s.me "OGN-004"
  let (s3, hb) ← put s2 s.me "SFD-136" .hand
  let e ← effectOf "SFD-136"
  let body := e.body
  let twice : Effect := .seq (.cons body (.cons body .nil))
  let r ← runBody (s3.fund s.you 5) s.me hb [sp] twice { fromEnd := some 2 }
  let after : Effect := .seq (.cons (.prim (.counter (.slot 0))) (.cons body .nil))
  let gone ← runBody (s3.fund s.you 5) s.me hb [sp] after
  return (r.poolOf s.you).energy == 5 && (r.zone .chain).length == 1 &&
    (gone.poolOf s.you).energy == 5 && targetsOk s3 s.me hb s3.mightTable e.choices [sp] &&
    !targetsOk s3 s.me hb s3.mightTable e.choices [mine]

-- (review) Not So Fast counters the spell; one that chooses nothing of the player is left alone
#guard tsf fun s => do
  let (s1, mine) ← put s s.me "OGN-051" .base
  let (s2, sp) ← onChain s1 s.you "OGN-004"
  let (s3, nsf) ← put s2 s.me "SFD-045" .hand
  let (s4, gear) ← put s3 s.me "SFD-042" .base
  let e ← effectOf "SFD-045"
  let aimed := s4.modObj sp (fun o => { o with targets := [mine] })
  let aimedAtGear := s4.modObj sp (fun o => { o with targets := [gear] })
  let r ← runBody aimed s.me nsf [sp] e.body
  return (r.zone .chain).isEmpty && targetsOk aimedAtGear s.me nsf aimedAtGear.mightTable e.choices [sp] &&
    !targetsOk s4 s.me nsf s4.mightTable e.choices [sp]

-- (review) Jaull-Fish: never below 0; Drag Under can kill a friendly unit; Lucian hits one enemy
-- unit here, and nothing at a base or at another battlefield
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-103" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let (s3, _) ← put s2 s.me "OGN-001" .base
  let (s4, _) ← put s3 s.me "OGN-001" .base
  let (s5, _) ← put s4 s.me "OGN-001" .base
  return s5.energyCost? s.me j == some 0
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-164" .hand
  let (s2, u) ← putAt s1 s.me "OGN-001" s.bf0
  let r ← play s2 s.me c [u]
  return (r.obj? u).isNone
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-028" s.bf0
  let (s2, near) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, base) ← put s2 s.you "OGN-001" .base
  let (s4, mine) ← putAt s3 s.me "OGN-001" s.bf0
  let r ← fire s4 [.combatStarted s.bf0 s.me]
  return r.dmg near == some 1 && r.dmg base == some 0 && r.dmg mine == some 0
-- Lucian, Merciless (SFD-113): the first time it conquers each turn, ready it
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, l) ← putAt s1 s.me "SFD-113" bf
  let t := s2.tire l
  let a ← fire t [.scored s.me bf true]
  let b ← fire (a.tire l) [.scored s.me bf true]
  let c ← fire t [.scored s.me bf false]
  let next := { (beginTurnStep b []) with pending := b.pending }
  let later ← fire next [.scored s.me bf true]
  return a.tired l == some false && b.tired l == some true && c.tired l == some true &&
    next.turn == b.turn + 1 && next.tired l == some true && later.tired l == some false &&
    later.hasKw l .weaponmaster

-- Draven, Audacious (SFD-148): the first time it wins a combat each turn, score 1 point; when it
-- dies in a combat, the opponent scores 1 point
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-148" s.bf0
  let a ← fire s1 [.combatWon s.bf0 s.me]
  let b ← fire a [.combatWon s.bf0 s.me]
  let (s2, x) ← putAt s s.me "SFD-148" s.bf0
  let (s3, _) ← putAt s2 s.me "OGN-051" s.bf0
  let (s4, _) ← putAt s3 s.you "OGN-051" s.bf0
  let fight := s4.inShowdownAt s.bf0 s.me
  let kc := killObj fight x
  let ke := killObj s4 x
  let c ← fire kc.1 kc.2
  let e ← fire ke.1 ke.2
  return a.pointsOf s.me == s1.pointsOf s.me + 1 && b.pointsOf s.me == a.pointsOf s.me &&
    c.pointsOf s.you == fight.pointsOf s.you + 1 && e.pointsOf s.you == s4.pointsOf s.you &&
    s1.pointsOf s.you == a.pointsOf s.you

-- Black Market Broker (SFD-121): when its player plays a card from face down, a Gold token
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-121" .base
  let a ← fire s1 [.hiddenPlayed s.me]
  let b ← fire s1 [.hiddenPlayed s.you]
  return a.countIn s.me .base "SFD-T03" == 1 && b.countIn s.me .base "SFD-T03" == 0

-- Hiding alone and casting the same spell out of hand create no Gold. Casting it
-- from Hidden creates exactly one Exhausted Gold.
#guard tsf fun s => do
  let p := s.me
  let field := s.bf0
  let (s, _) ← put s p "SFD-121" .base
  let (s, spell) ← put (s.control p field) p "OGN-094" .hand
  let hand ← play s p spell
  let hidden ← activate s p spell 0 [field] ⟨0, [.fury]⟩
  let hiddenSpell ← hidden.firstOf p .hidden "OGN-094"
  let finished ← activate { hidden with turn := hidden.turn + 1 } p hiddenSpell 1
  let gold ← finished.firstOf p .base "SFD-T03"
  return hand.countIn p .base "SFD-T03" == 0 && hidden.countIn p .base "SFD-T03" == 0 &&
    finished.countIn p .base "SFD-T03" == 1 && finished.tired gold == some true

-- Harpoon Squad (SFD-137): when it moves from a battlefield, +2 Might this turn
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-137" .base
  let left := s1.modObj u (fun o => { o with prevLoc := some s.bf0 })
  let a ← fire left [.standardMoved u none]
  let b ← fire s1 [.standardMoved u none]
  return a.mightNow u == (left.mightNow u).map (· + 2) && b.mightNow u == s1.mightNow u

-- Prize of Progress (SFD-075): when its player uses an activated ability of a gear, +1 Might
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-075" .base
  let (s2, g) ← put s1 s.me "SFD-046" .base
  let (s3, h) ← put s2 s.you "SFD-046" .base
  let a ← fire s3 [.activated s.me g 1]
  let b ← fire s3 [.activated s.me u 0]
  let c ← fire s3 [.activated s.you h 1]
  return a.mightNow u == (s3.mightNow u).map (· + 1) && b.mightNow u == s3.mightNow u &&
    c.mightNow u == s3.mightNow u

-- Legion Quartermaster (SFD-044): a friendly gear returns to its owner's hand when it is played
#guard tsf fun s => do
  let (s1, q) ← put s s.me "SFD-044" .hand
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, h) ← put s2 s.you "SFD-042" .base
  let a ← play s3 s.me q [g]
  return a.countIn s.me .hand "SFD-042" == 1 && (a.obj? h).isSome && (a.obj? g).isNone &&
    -- the cost is not optional, and an enemy gear cannot pay it; with no friendly gear it
    -- cannot be played at all
    (play s3 s.me q []).isNone && (play s3 s.me q [h]).isNone && (play s1 s.me q []).isNone &&
    a.countIn s.me .base "SFD-044" == 1

-- In 2v2 a teammate's Gear can pay a friendly return cost. It goes to its owner even
-- if the teammate controlled and wore it, and the host stays on the Board.
#guard tsf fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) initial).toOption
  let p := s.me
  let mate ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← s.players.find? (fun q => !config.mode.sameSide p q)
  let (s, quartermaster) ← put s p "SFD-044" .hand
  let (s, forge) ← put s p "RAD-066" .hand
  let (s, squadron) ← put s p "RAD-075" .hand
  let (s, host) ← put s mate "OGN-001" .base
  let (s, borrowed) ← put s enemy "SFD-042" .base
  let (s, rival) ← put s enemy "SFD-056" .base
  let s := (attachTo host (setController mate s borrowed).1 borrowed).1
  let pay : RunePool.Payment := ⟨3, []⟩
  let action (gear : ObjId) : Action :=
    ⟨.player p, .playCard quartermaster pay [gear] none none .plain⟩
  let funded := s.fund p 3
  let (paid, events) ← (step 100 funded (action borrowed)).toOption
  let forgePaid ← play s p forge [borrowed]
  let squadronPaid ← cast funded p squadron pay [borrowed]
  let forged ← forgePaid.firstOf p .base "RAD-066"
  return (legalActions funded).contains (action borrowed) &&
    !(legalActions funded).contains (action rival) && !(step 100 funded (action rival)).isOk &&
    paid.countIn p .base "SFD-044" == 1 && paid.countIn enemy .hand "SFD-042" == 1 &&
    paid.countIn mate .hand "SFD-042" == 0 && paid.inPlay.contains host &&
    events.any (fun | .moved id _ (.player owner .hand) => id == borrowed && owner == enemy | _ => false) &&
    !events.any (fun | .chosenBySpell .. | .chosenByAbility .. => true | _ => false) &&
    forgePaid.mightNow forged == some 6 && forgePaid.tired forged == some false &&
    squadronPaid.countIn p .base "RAD-075" == 1 && squadronPaid.countIn enemy .hand "SFD-042" == 1

/-- The first Legend of the player (the lab has one for each player). -/
meta def _root_.Riftbound.GameState.legendOf (s : GameState) (p : PlayerId) : Option ObjId :=
  (s.zone (.player p .legendZone)).head?

-- Royal Entourage (SFD-039): ready or exhaust a legend
#guard tsf fun s => do
  let (s1, e) ← put s s.me "SFD-039" .hand
  let l ← s1.legendOf s.me
  let tired := s1.tire l
  let a ← play tired s.me e [] { fromEnd := some 1 }
  let b ← play s1 s.me e [] { fromEnd := some 2 }
  return a.tired l == some false && b.tired l == some true
-- (a legend of the opponent too)
#guard tsf fun s => do
  let (s1, e) ← put s s.me "SFD-039" .hand
  let l ← s1.legendOf s.you
  let mine ← s1.legendOf s.me
  let b ← play (s1.tire mine) s.me e [] { fromEnd := some 2 }
  let c ← play (s1.tire mine) s.me e [] { fromEnd := some 2, obj := fun o => o == l }
  return b.tired l == some false && c.tired l == some true

-- Hall of Legends (SFD-210): when its player conquers here, pay 1 Energy to ready their legend
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-210"
  let l ← s1.legendOf s.me
  let other ← s1.legendOf s.you
  let t := (s1.tire l).tire other
  let a ← fire (t.rich s.me) [.scored s.me bf true]
  let b ← fire (t.rich s.me) [.scored s.me bf true] { yes := false }
  let c ← fire (t.fund s.me 0) [.scored s.me bf true]
  let d ← fire (t.rich s.me) [.scored s.me bf false]
  let e ← fire (t.rich s.me) [.scored s.me bf true] { obj := fun o => o == other }
  return a.tired l == some false && a.tired other == some true && (a.poolOf s.me).energy == 11 &&
    b.tired l == some true && c.tired l == some true && d.tired l == some true &&
    e.tired other == some true

-- Bard, Mercurial (SFD-079): when played, the player may exhaust their legend to move any number
-- of their units to an open battlefield
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-079" .hand
  let l ← s1.legendOf s.me
  let (s3, u) ← put s1 s.me "OGN-051" .base
  let a ← play s3 s.me b [l]
  let n ← play s3 s.me b []
  -- an exhausted legend cannot pay the cost
  return a.tired l == some true && (a.obj? u).any (·.loc == some s.bf0) &&
    (n.obj? u).any (·.loc.isNone) && n.tired l == some false &&
    (play (s3.tire l) s.me b [l]).isNone

/-- Let a Combat run to its end: the first card is assigned damage, the assignment is done, the
players pass, the questions are answered with yes. -/
meta def playOut : Nat → GameState → GameState
  | 0, s => s
  | n + 1, s =>
    let acts := legalFrameActions s
    let pick := acts.find? (fun a => match a.kind with | .assignPick _ => true | _ => false)
    let done := acts.find? (fun a => match a.kind with | .assignDone => true | _ => false)
    let other := acts.find? (fun a => match a.kind with
      | .pass | .decide _ | .choose _ | .putTrigger _ _ _ => true | _ => false)
    match pick <|> done <|> other with
    | some a =>
      match step 100 s a with
      | .ok (s', _) => playOut n s'
      | .error _ => s
    | none => s

-- (review) Draven, Audacious dies in a real Combat: the opponent scores 1 point (the ability waits
-- for the Combat Damage Cleanup, so the condition is on the trigger, not on its effect)
#guard tsf fun s => do
  let (s1, d) ← putAt s s.me "SFD-148" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-001" s.bf0
  let s3 := s2.modObj d (fun o => { o with damage := 5 })
  let r ← startCombatNow s3 s.bf0 s.me
  let end_ := playOut 40 r
  return (end_.obj? d).isNone && end_.pointsOf s.you > s3.pointsOf s.you && e != d

-- (review) Prize of Progress: not for a gear in the hand or hidden, only for one in play (Equip
-- too)
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-075" .base
  let (s2, inHand) ← put s1 s.me "SFD-042" .hand
  let (s3, hidden) ← put s2 s.me "SFD-139" .hidden
  let (s4, board) ← put s3 s.me "SFD-042" .base
  let a ← fire s4 [.activated s.me inHand 0]
  let b ← fire s4 [.activated s.me hidden 0]
  let c ← fire s4 [.activated s.me board 0]
  return a.mightNow u == s4.mightNow u && b.mightNow u == s4.mightNow u &&
    c.mightNow u == (s4.mightNow u).map (· + 1)

/-- Attach the Equipment to the unit now. -/
meta def _root_.Riftbound.GameState.hook (s : GameState) (g u : ObjId) : GameState :=
  (attachTo u s g).1

-- Rabadon's Deathcrown (SFD-191): the spells and abilities of the unit's player deal 3 more damage
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-017" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-191" .base
  let (s4, e) ← putAt s3 s.you "SFD-132" s.bf0
  let plain ← play s4 s.me c [e]
  let armed ← play (s4.hook g u) s.me c [e]
  let (t1, h) ← put s3 s.you "SFD-191" .base
  let (t2, f) ← put t1 s.you "OGN-051" .base
  let (t3, e2) ← putAt t2 s.you "SFD-132" s.bf0
  let theirs ← play (t3.hook h f) s.me c [e2]
  return plain.dmg e == some 2 && armed.dmg e == some 5 && theirs.dmg e2 == some 2

-- Shurelya's Requiem (SFD-192): when played, ready the player's units; the units of the player at
-- the place of its unit have Ganking
#guard tsf fun s => do
  let (s1, r) ← put s s.me "SFD-192" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let a ← play (s2.tire u) s.me r
  let (t1, host) ← putAt s s.me "OGN-051" s.bf0
  let (t2, g) ← put t1 s.me "SFD-192" .base
  let (t3, near) ← putAt t2 s.me "OGN-136" s.bf0
  let (t4, far) ← put t3 s.me "OGN-136" .base
  let (t5, foe) ← putAt t4 s.you "OGN-136" s.bf0
  let t := t5.hook g host
  return a.tired u == some false && t.hasKw near .ganking && t.hasKw host .ganking &&
    !t.hasKw far .ganking && !t.hasKw foe .ganking && !t5.hasKw near .ganking

-- Experimental Hexplate (SFD-073): the unit it is attached to is a Mech
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-182" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-073" .base
  let (s4, v) ← put s3 s.me "OGN-051" .base
  let t := s4.hook g u
  let r ← play t s.me c
  let (detached, _) ← moveObj t g (.player s.me .hand)
  let after ← play detached s.me c
  return r.mightNow u == (t.mightNow u).map (· + 1) && r.mightNow v == t.mightNow v &&
    after.mightNow u == s4.mightNow u && after.mightNow v == s4.mightNow v

-- Gearhead (SFD-068): each Equipment attached to it gives double its Might bonus
#guard tsf fun s => do
  let (s1, gh) ← put s s.me "SFD-068" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-115" .base
  let (s4, h) ← put s3 s.me "SFD-115" .base
  let a := s4.hook g gh
  let b := s4.hook h u
  return a.mightNow gh == (s4.mightNow gh).map (· + 4) &&
    b.mightNow u == (s4.mightNow u).map (· + 2)

-- Brutalizer (SFD-042): +2 Might more if it was attached this turn
#guard tsf fun s => do
  let (s1, u) ← put s s.me "OGN-051" .base
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let a := s2.hook g u
  let later := { a with turn := a.turn + 1 }
  return a.mightNow u == (s2.mightNow u).map (· + 3) &&
    later.mightNow u == (s2.mightNow u).map (· + 1)

-- Skyfall of Areion (SFD-030): the hold effects of its unit are conquer effects too, and back
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, lucian) ← putAt s1 s.me "SFD-113" bf
  let (s3, dune) ← putAt s2 s.me "SFD-027" bf
  let (s4, g) ← put s3 s.me "SFD-030" .base
  let (s5, h) ← put s4 s.me "SFD-030" .base
  let l := (s5.hook g lucian).tire lucian
  let d := s5.hook h dune
  let a ← fire l [.scored s.me bf false]
  let b ← fire (s5.tire lucian) [.scored s.me bf false]
  let c ← fire d [.scored s.me bf true]
  let e ← fire s5 [.scored s.me bf true]
  return a.tired lucian == some false && b.tired lucian == some true &&
    c.handN s.me == d.handN s.me + 2 && e.handN s.me == s5.handN s.me

-- (review) Annie, Fiery (OGS-001): her player's spells deal 1 Bonus Damage more; with Rabadon's
-- Deathcrown, 3 more
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-017" .hand
  let (s2, _) ← put s1 s.me "OGS-001" .base
  let (s3, e) ← putAt s2 s.you "SFD-132" s.bf0
  let (s4, u) ← put s3 s.me "OGN-051" .base
  let (s5, g) ← put s4 s.me "SFD-191" .base
  let a ← play s3 s.me c [e]
  let b ← play (s5.hook g u) s.me c [e]
  return a.dmg e == some 3 && b.dmg e == some 6

-- (review) Gearhead doubles the printed bonus, not Brutalizer's extra; Brutalizer's extra goes to
-- the unit it was attached to this turn (moved to another unit, the first loses it)
#guard tsf fun s => do
  let (s1, gh) ← put s s.me "SFD-068" .base
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, v) ← put s2 s.me "OGN-051" .base
  let a := s3.hook g gh
  let b := (s3.hook g gh).hook g v
  return a.mightNow gh == (s3.mightNow gh).map (· + 2 + 2) &&
    b.mightNow v == (s3.mightNow v).map (· + 3) && b.mightNow gh == s3.mightNow gh

-- (review) Shurelya's Requiem readies the units of its player only; Hexplate on an enemy unit
-- makes that unit a Mech (for its player)
#guard tsf fun s => do
  let (s1, r) ← put s s.me "SFD-192" .hand
  let (s2, mine) ← put s1 s.me "OGN-051" .base
  let (s3, foe) ← put s2 s.you "OGN-051" .base
  let t := (s3.tire mine).tire foe
  let a ← play t s.me r
  return a.tired mine == some false && a.tired foe == some true
#guard tsf fun s => do
  let (s1, foe) ← put s s.you "OGN-051" .base
  let (s2, g) ← put s1 s.you "SFD-073" .base
  let t := s2.hook g foe
  return t.gainedTags foe == [⟨"Mech"⟩] && (t.zone (.player s.you .base)).contains foe

-- (review) Skyfall: a unit with only a hold ability gets it once on a conquer; the Battlefield's
-- own conquer ability does not fire on a hold
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-220"
  let (s2, dune) ← putAt s1 s.me "SFD-027" bf
  let (s3, g) ← put s2 s.me "SFD-030" .base
  let t := s3.hook g dune
  let c ← fire (t.rich s.me) [.scored s.me bf true]
  let h ← fire (t.rich s.me) [.scored s.me bf false]
  return c.handN s.me == t.handN s.me + 2 && h.countIn s.me .base "SFD-T03" == 0 &&
    c.countIn s.me .base "SFD-T03" == 1
-- Ezreal, Dashing (SFD-082): when it attacks or defends, damage equal to its Might to an enemy unit
-- here; it deals no combat damage; pay 1 Mind (an Action): move it to the base
#guard tsf fun s => do
  let (s1, e) ← putAt s s.me "SFD-082" s.bf0
  let (s2, foe) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, other) ← put s2 s.you "OGN-001" .base
  let a ← fire s3 [.combatStarted s.bf0 s.me]
  let b ← fire s3 [.combatStarted s.bf0 s.you]
  let m ← activate s3 s.me e 3 [] ⟨0, [.mind]⟩
  return a.dmg foe == some 3 && b.dmg foe == some 3 && a.dmg other == some 0 &&
    s3.combatMight e true == 0 && s3.combatMight foe true == 5 &&
    (m.obj? e).any (·.loc.isNone)

-- Fiora, Peerless (SFD-110): attacking or defending one on one, double its Might
#guard tsf fun s => do
  let (s1, f) ← putAt s s.me "SFD-110" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, e2) ← putAt s2 s.you "OGN-051" s.bf0
  let (s4, ally) ← putAt s1 s.me "OGN-051" s.bf0
  let fight (x : GameState) (att : PlayerId) :=
    (x.modObj s.bf0 (fun o => { o with contested := some att })).inShowdownAt s.bf0 att
  let a ← fire (fight s2 s.me) [.combatStarted s.bf0 s.me]
  let b ← fire (fight s3 s.me) [.combatStarted s.bf0 s.me]
  let c ← fire (fight (s4.modObj ally (fun o => o)) s.me) [.combatStarted s.bf0 s.me]
  let (t1, g) ← putAt s s.me "SFD-110" s.bf0
  let (t2, _) ← putAt t1 s.you "OGN-051" s.bf0
  let d ← fire (fight t2 s.you) [.combatStarted s.bf0 s.you]
  let (ended, _) ← (advance 100 { a with pending := [.combatFinish s.bf0] } []).toOption
  return a.mightNow f == (s2.mightNow f).map (· * 2) && b.mightNow f == s3.mightNow f &&
    d.mightNow g == (t2.mightNow g).map (· * 2) && e != e2 && ally != f &&
    c.mightNow f == s4.mightNow f &&
    -- the doubling ends with the combat, not with the turn
    ((combatCleanup a s.bf0 s.me).1.mightNow f == a.mightNow f) &&
    ended.mightNow f == s2.mightNow f &&
    -- a Showdown that is not a Combat ends it too
    ((endShowdown a s.bf0).1.mightNow f == s2.mightNow f) &&
    (a.mightNow f != s2.mightNow f)

-- Jax, Unrelenting (SFD-119): when an Equipment is attached to it, may pay 1 to draw 1
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-119" .base
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, other) ← put s2 s.me "OGN-051" .base
  let (a1, evs) := attachTo j s2 g
  let (b1, evs2) := attachTo other s3 g
  let a ← fire (a1.rich s.me) evs
  let n ← fire (a1.rich s.me) evs { yes := false }
  let p ← fire (a1.fund s.me 0) evs
  let one ← fire (a1.fund s.me 1) evs
  let b ← fire (b1.rich s.me) evs2
  return a.handN s.me == a1.handN s.me + 1 && (a.poolOf s.me).energy == 11 &&
    one.handN s.me == a1.handN s.me + 1 && (one.poolOf s.me).energy == 0 &&
    n.handN s.me == a1.handN s.me && p.handN s.me == a1.handN s.me &&
    b.handN s.me == b1.handN s.me

-- Altar of Memories (SFD-169): when a friendly unit dies, exhaust it to draw 1, then put a card
-- from the hand on top or at the bottom of the deck
#guard tsf fun s => do
  let (s1, altar) ← put s s.me "SFD-169" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← put s2 s.me "OGN-001" .hand
  let (s4, foe) ← put s3 s.you "OGN-051" .base
  let die (st : GameState) (x : ObjId) (says : Says := {}) : Option GameState :=
    let (st1, evs) := killObj st x
    fire st1 evs says
  let pick : Says := { obj := fun o => s4.isCard "OGN-001" o }
  let top ← die s4 u { pick with fromEnd := some 1 }
  let bottom ← die s4 u { pick with fromEnd := some 2 }
  let enemy ← die s4 foe
  let tired ← die (s4.tire altar) u
  let (dead, events) := killObj s4 u
  let (waiting, _) ← (advance 100
    { dead with pending := insertTriggers (dead.detect events) dead.pending } []).toOption
  let pay : Action := ⟨.player s.me, .putTrigger 0 [] (.pay [])⟩
  let decline : Action := ⟨.player s.me, .putTrigger 0 [] .skip⟩
  let (paid, paymentEvents) ← (step 100 waiting pay).toOption
  let (declined, _) ← (step 100 waiting decline).toOption
  return top.tired altar == some true && top.handN s.me == s4.handN s.me &&
    top.deckN s.me == s4.deckN s.me && top.countIn s.me .hand "OGN-001" == 0 &&
    (top.topCard s.me).any (top.isCard "OGN-001") && bottom.bottomIs s.me 1 "OGN-001" &&
    bottom.deckN s.me == s4.deckN s.me && enemy.tired altar == some false &&
    tired.handN s.me == s4.handN s.me &&
    paid.tired altar == some true && paymentEvents.contains (.exhausted altar) &&
    (paid.zone .chain).length == 1 && paid.handN s.me == waiting.handN s.me &&
    declined.tired altar == some false && (declined.zone .chain).isEmpty &&
    declined.handN s.me == waiting.handN s.me

-- A teammate's death triggers Altar, while the draw and the hand choice belong to its controller.
#guard tsf fun base => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let start ← GameState.initial base.cards config (List.replicate 4 goodDeck)
  let s ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) start).toOption
  let p := s.me
  let ally ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← s.players.find? (fun q => !config.mode.sameSide p q)
  let (s, altar) ← put s p "SFD-169" .base
  let (s, watched) ← put s ally "OGN-051" .base
  let (s, excluded) ← put s enemy "OGN-051" .base
  let (s, own) ← put s p "OGN-001" .hand
  let (s, allyCard) ← put s ally "OGN-051" .hand
  let choices : Says := { obj := (· == own), fromEnd := some 1 }
  let (allyDied, events) := killObj s watched
  let (enemyDied, enemyEvents) := killObj s excluded
  let after ← fire allyDied events choices
  let afterEnemy ← fire enemyDied enemyEvents choices
  return after.tired altar == some true && (after.topCard p).any (after.isCard "OGN-001") &&
    (after.zone (.player ally .hand)).contains allyCard && after.handN ally == s.handN ally &&
    afterEnemy.tired altar == some false

-- Fae Dragon (SFD-101): buff up to four friendly units when played; when a buff is spent, a Gold
#guard tsf fun s => do
  let (s1, d) ← put s s.me "SFD-101" .hand
  let (s2, a) ← put s1 s.me "OGN-051" .base
  let (s3, b) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-051" .base
  let r ← play s4 s.me d [] { pick := fun ts => ts == [a, b] || ts == [b, a] }
  let n ← play s4 s.me d [] { pick := fun ts => ts.isEmpty }
  let o ← play s4 s.me d [] { pick := fun ts => ts == [a] }
  return (r.obj? a).any (·.buffed) && (r.obj? b).any (·.buffed) && !(r.obj? e).any (·.buffed) &&
    !(n.obj? a).any (·.buffed) && (o.obj? a).any (·.buffed) && !(o.obj? b).any (·.buffed)
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-101" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (t1, ev) := unbuffObj (s2.buff u) u
  let a ← fire t1 ev
  let b ← fire s2 [.buffSpent s.you]
  return a.countIn s.me .base "SFD-T03" == 1 && b.countIn s.me .base "SFD-T03" == 0

-- Arcane Shift (SFD-200): play a friendly unit again, 3 damage to an enemy unit at a battlefield,
-- banish the spell
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-200" .hand
  let (s2, u) ← put s1 s.me "OGN-003" .base
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let hurt := (s3.buff u).modObj u (fun o => { o with damage := 1 })
  let r ← play s3 s.me c [u, e]
  let r2 ← play hurt s.me c [u, e]
  let again (x : GameState) : Option ObjId :=
    (x.zone (.player s.me .base)).find? (fun o => (x.cardDef? o).any (·.id == cid "OGN-003"))
  let n ← again r2
  return r.dmg e == some 3 && r.countIn s.me .trash "SFD-200" == 0 &&
    r.handN s.me + 2 == s3.handN s.me &&
    -- it is a new object, with nothing of what it had: no buff, no damage, and exhausted
    n != u && (r2.obj? n).any (fun o => !o.buffed && o.damage == 0 && o.exhausted)

-- (review) spending a buff the unit does not have is no event; Fiora with a buff and with company
#guard tsf fun s => do
  let (s1, u) ← put s s.me "OGN-051" .base
  let none_ := (unbuffObj s1 u).2
  let some_ := (unbuffObj (s1.buff u) u).2
  return none_.isEmpty && some_ == [.buffSpent s.me]
#guard tsf fun s => do
  let (s1, f) ← putAt s s.me "SFD-110" s.bf0
  let (s2, _) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, _) ← putAt s2 s.me "OGN-051" s.bf0
  let fight (x : GameState) :=
    (x.modObj s.bf0 (fun o => { o with contested := some s.me })).inShowdownAt s.bf0 s.me
  let alone ← fire (fight (s2.buff f)) [.combatStarted s.bf0 s.me]
  let withAlly ← fire (fight s3) [.combatStarted s.bf0 s.me]
  let twice ← fire alone [.combatStarted s.bf0 s.me]
  return alone.mightNow f == ((s2.buff f).mightNow f).map (· * 2) &&
    withAlly.mightNow f == s3.mightNow f && twice.mightNow f != none
-- (review) Jax gets the event through the real Equip ability, and Ezreal deals his current Might
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-119" .base
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let r ← activate s2 s.me g 0 [j] ⟨0, [.calm]⟩
  return (r.obj? g).any (·.attached == some j) && r.handN s.me == s2.handN s.me + 1
#guard tsf fun s => do
  let (s1, e) ← putAt s s.me "SFD-082" s.bf0
  let (s2, foe) ← putAt s1 s.you "OGN-001" s.bf0
  let boosted := s2.buff e
  let a ← fire boosted [.combatStarted s.bf0 s.me]
  return a.dmg foe == (boosted.mightNow e).map Int.toNat && boosted.mightNow e == some 4
-- Tianna Crownguard (SFD-060): while it is at a battlefield, opponents can't score points; the
-- battlefield is still scored (the abilities fire), and the control still changes
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, bf2) ← putBf s1 s.you "SFD-216"
  let (s3, _) ← putAt s2 s.me "SFD-060" bf
  let held := (s3.control s.you bf2)
  let (s4, _) ← put s2 s.me "SFD-060" .base
  let held2 := (s4.control s.you bf2)
  let blocked := scoreBf held s.you bf2 true
  let mine := scoreBf (s3.control s.me bf) s.me bf true
  let free := scoreBf held2 s.you bf2 true
  let h1 := hold held s.you
  let h2 := hold held2 s.you
  return blocked.1.pointsOf s.you == 0 && blocked.2.2 == [.scored s.you bf2 true] &&
    ((blocked.1.obj? bf2).map (·.scored.contains s.you)) == some true &&
    h1.1.pointsOf s.you == 0 && h1.2 == [.scored s.you bf2 false] &&
    free.1.pointsOf s.you == 1 && h2.1.pointsOf s.you == 1 && mine.1.pointsOf s.me == 1 &&
    -- a hold that scored no point is not a held point
    ((h1.1.obj? bf2).map (·.held.contains s.you)) == some false &&
    ((h2.1.obj? bf2).map (·.held.contains s.you)) == some true

-- Forgotten Monument (SFD-209): players can't score here until their third turn: the first player's
-- turns are 1, 3, 5, the second player's 2, 4, 6
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-209"
  let atT (who : PlayerId) (t : Nat) : GameState := ({ s1 with turn := t }.control who bf)
  let pts (who : PlayerId) (t : Nat) := (scoreBf (atT who t) who bf true).1.pointsOf who
  let hp (who : PlayerId) (t : Nat) := (hold (atT who t) who).1.pointsOf who
  let first := s.turnOrder.getD 0 ⟨0⟩
  let second := s.turnOrder.getD 1 ⟨0⟩
  let (s2, other) ← putBf s1 s.you "SFD-216"
  let elsewhere := (scoreBf ({ s2 with turn := 1 }.control s.me other) s.me other true).1
  return elsewhere.pointsOf s.me == 1 &&
    pts first 3 == 0 && pts first 4 == 0 && pts first 5 == 1 &&
    pts second 4 == 0 && pts second 5 == 0 && pts second 6 == 1 &&
    hp first 4 == 0 && hp first 5 == 1 && hp second 4 == 0 && hp second 6 == 1

-- Last Rites (SFD-150): Equip by paying 1 Chaos and recycling 2 cards from the Trash; when its unit
-- conquers or holds, it may play a unit from the Trash
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-150" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, first) ← put s2 s.me "OGN-004" .trash
  let (s4, second) ← put s3 s.me "OGN-010" .trash
  let ready := s4.rich s.me
  let activation : Action := ⟨.player s.me, .activate g 0 ⟨0, [.chaos]⟩ [u]⟩
  let chooseFirst : Action := ⟨.player s.me, .choose first⟩
  let chooseSecond : Action := ⟨.player s.me, .choose second⟩
  let order : Action := ⟨.chance, .arrange [second, first]⟩
  let (initial, deferred) ← (step 100 ready activation).toOption
  let (choosing, _) ← (step 100 initial chooseFirst).toOption
  let (waiting, _) ← (step 100 choosing chooseSecond).toOption
  let .chanceRecycleTrash _ _ cards :: _ := waiting.pending | none
  let (paid, events) ← (step 100 waiting order).toOption
  let r := settleChain {} 12 paid
  return isPlayDeclaration ready activation && decisionRunAnswerWorkSupported initial chooseFirst &&
    decisionRunAnswerWorkSupported choosing chooseSecond && decisionRunAnswerWorkSupported waiting order &&
    !deferred.contains (.activated s.me g 0 (some 0)) && cards == [first, second] &&
    paid.zone (.player s.me .trash) == [] &&
    (paid.obj? g).any (·.attached == none) &&
    events.contains (.recycled s.me) && events.contains (.activated s.me g 0 (some 0)) &&
    (r.obj? g).any (·.attached == some u) && r.deckN s.me == s4.deckN s.me + 2 &&
    (activate s3 s.me g 0 [u] ⟨0, [.chaos]⟩).isNone
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, u) ← putAt s1 s.me "OGN-051" bf
  let (s3, g) ← put s2 s.me "SFD-150" .base
  let (s4, _) ← put s3 s.me "OGN-051" .trash
  let t := s4.hook g u
  let a ← fire (t.rich s.me) [.scored s.me bf true]
  let b ← fire (t.rich s.me) [.scored s.me bf false]
  let c ← fire (t.rich s.me) [.scored s.me bf true] { yes := false }
  let d ← fire (s4.rich s.me) [.scored s.me bf true]
  return a.countIn s.me .base "OGN-051" == t.countIn s.me .base "OGN-051" + 1 &&
    b.countIn s.me .base "OGN-051" == t.countIn s.me .base "OGN-051" + 1 &&
    c.countIn s.me .base "OGN-051" == t.countIn s.me .base "OGN-051" &&
    d.countIn s.me .base "OGN-051" == s4.countIn s.me .base "OGN-051"

-- Blade of the Ruined King (SFD-178): Equip by paying 1 Order and killing a friendly unit
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-178" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let r ← activate s3 s.me g 0 [u, v] ⟨0, [.order]⟩
  let w ← activate s3 s.me g 0 [v, u] ⟨0, [.order]⟩
  return (r.obj? g).any (·.attached == some u) && (r.obj? u).isSome && (r.obj? v).isNone &&
    (w.obj? v).isSome && (w.obj? u).isNone && (r.obj? g).any (·.attached == some u) &&
    -- the unit to kill is chosen with the ability, and cannot be the unit it is attached to
    (activate s3 s.me g 0 [u, u] ⟨0, [.order]⟩).isNone &&
    (activate s2 s.me g 0 [u] ⟨0, [.order]⟩).isNone

-- (cost) The unit is killed as the ability is used, before the Chain resolves: the Equip is still
-- on the Chain, the Blade is not attached yet, and the unit is already dead
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-178" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  match step 100 (s3.rich s.me) ⟨.player s.me, .activate g 0 ⟨0, [.order]⟩ [u, v]⟩ with
  | .ok (a, _) =>
    return (a.obj? v).isNone && (a.obj? g).any (·.attached == none) && !(a.zone .chain).isEmpty
  | .error _ => return false

-- Edge of Night (SFD-139): when played from face down, attach it to a unit its player controls
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-139" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let hidden := s2.modObj g (fun o => { o with fromHidden := true })
  let a ← fire hidden [.played s.me g]
  let b ← fire s2 [.played s.me g]
  return (a.obj? g).any (·.attached == some u) && (b.obj? g).any (·.attached == none)

-- Ruin Runner (SFD-105): enemy spells and abilities can't choose it; its own player can
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-105" .base
  let (s2, v) ← put s1 s.me "OGN-051" .base
  let ch : Choice := .targetOf .one .any .anywhere [.ofType .unit]
  return !(ch.candidates s2 s.you v).contains u && (ch.candidates s2 s.you v).contains v &&
    (ch.candidates s2 s.me v).contains u && s2.blocksChoice s.you u && !s2.blocksChoice s.me u &&
    !s2.blocksChoice s.you v

-- Loyal Pup (SFD-126): when its player defends at a battlefield, it may move there
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, _) ← putAt s1 s.me "OGN-051" bf
  let (s3, _) ← putAt s2 s.you "OGN-051" bf
  let (s4, pup) ← put s3 s.me "SFD-126" .base
  let a ← fire s4 [.combatStarted bf s.you]
  let b ← fire s4 [.combatStarted bf s.you] { yes := false }
  let c ← fire s4 [.combatStarted bf s.me]
  let (defending, sameField) ← putAt s3 s.me "SFD-126" bf
  return a.hereOf pup == some bf && b.hereOf pup == none && c.hereOf pup == none &&
    (defending.detect [.combatStarted bf s.you]).any (fun t => t.source == sameField)

-- Aphelios, Exalted (SFD-049): when an Equipment is attached to it, choose a mode not yet chosen
-- this turn: ready 2 runes, channel 1 rune exhausted, or buff a friendly unit
#guard tsf fun s => do
  let (s1, aph) ← put s s.me "SFD-049" .base
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let runesOf (x : GameState) :=
    (x.zone (.player s.me .base)).filter (fun r => (x.cardDef? r).any (·.hasType .rune))
  let tired := (runesOf s2).foldl (fun x r => x.tire r) s2
  let ready (x : GameState) := (runesOf x).filter (fun r => x.tired r == some false)
  let a ← fire tired [.attached g aph] { fromEnd := some 2 }
  let b ← fire s2 [.attached g aph] { fromEnd := some 1 }
  let c ← fire s2 [.attached g aph] { fromEnd := some 0 }
  return (ready a).length == min 2 (runesOf tired).length && (ready a).length > 0 &&
    (runesOf b).length == (runesOf s2).length + 1 && !(a.obj? aph).any (·.buffed) &&
    (c.obj? aph).any (·.buffed) && (runesOf c).length == (runesOf s2).length
-- ... and a mode chosen already this turn does nothing the second time
#guard tsf fun s => do
  let (s1, aph) ← put s s.me "SFD-049" .base
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let runesOf (x : GameState) :=
    (x.zone (.player s.me .base)).filter (fun r => (x.cardDef? r).any (·.hasType .rune))
  let a ← fire s2 [.attached g aph] { fromEnd := some 1 }
  let b ← fire a [.attached g aph] { fromEnd := some 1 }
  return (runesOf a).length == (runesOf s2).length + 1 && (runesOf b).length == (runesOf a).length

-- (review) Ruin Runner: an enemy's pick of a target is refused, a choice at resolution skips it
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-105" .base
  let (s2, v) ← put s1 s.me "OGN-051" .base
  let ch : Choice := .targetOf .one .any .anywhere [.ofType .unit]
  let cs := [ch]
  return !targetsOk s2 s.you v s2.mightTable cs [u] && targetsOk s2 s.you v s2.mightTable cs [v] &&
    targetsOk s2 s.me v s2.mightTable cs [u] &&
    ((s2.pickCandidates s.you v {} .any .anywhere (FilterList.ofList [.ofType .unit])).getD []).all
      (· != u) &&
    ((s2.pickCandidates s.me v {} .any .anywhere (FilterList.ofList [.ofType .unit])).getD []).any
      (· == u)

/-- A unit of the card is at the Battlefield. -/
meta def unitAt (s : GameState) (code : String) (bf : ObjId) : Bool :=
  (s.zone .battlefieldZone).any (fun x => (s.cardDef? x).any (·.id == cid code) &&
    (s.obj? x).any (·.loc == some bf))

-- Minotaur Reckoner (SFD-014): units can't move to base (any unit, any battlefield)
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, u) ← putAt s1 s.me "OGN-051" bf
  let (s3, _) ← put s2 s.you "SFD-014" .base
  return moveOk s2 s.me u .base && !moveOk s3 s.me u .base &&
    (moveHome s2 u).1.hereOf u == none && (moveHome s3 u).1.hereOf u == some bf

-- Rockfall Path (SFD-216): units can't be played here (a unit played there goes to the base)
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, u) ← put s1 s.me "OGN-051" .hand
  let (s3, other) ← putBf s2 s.you "OGN-275"
  let a := (playToOrBase s.me bf s3 u).1
  let b := (playToOrBase s.me other s3 u).1
  return !unitAt a "OGN-051" bf && unitAt b "OGN-051" other &&
    (a.zone (.player s.me .base)).any (fun x => (a.cardDef? x).any (·.id == cid "OGN-051"))

-- Perched Grimwyrm (SFD-015): only to a battlefield its player scored this turn, never to the base
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, g) ← put s1 s.me "SFD-015" .hand
  let scored := s2.modObj bf (fun o => { o with scored := [s.me] })
  let a ← play scored s.me g [bf]
  let none_ := play s2 s.me g [bf]
  let (s3, plain) ← put s2 s.me "OGN-051" .hand
  return !playable (s3.rich s.me) s.me g (payOf s3 g) &&
    playable (s3.rich s.me) s.me plain (payOf s3 plain) &&
    unitAt a "SFD-015" bf && none_.isNone

-- Rengar, Pouncing (SFD-025): may be played to a battlefield its player is attacking
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, g) ← put s1 s.me "SFD-025" .hand
  let atk := s2.modObj bf (fun o => { o with contested := some s.me })
  let def_ := s2.modObj bf (fun o => { o with contested := some s.you })
  let a ← play atk s.me g [bf]
  return unitAt a "SFD-025" bf && (play def_ s.me g [bf]).isNone &&
    (play s2 s.me g [bf]).isNone

-- Janna, Savior (SFD-053): may be played to a battlefield its player controls, as a Reaction
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, j) ← put s1 s.me "SFD-053" .hand
  let (s3, foe) ← putAt s2 s.you "OGN-051" bf
  let mine := s3.control s.me bf
  let a ← play mine s.me j [bf] { pick := (· == [foe]) }
  return unitAt a "SFD-053" bf && (a.obj? foe).any (·.loc.isNone) && reactSpell s3 j &&
    (play s3 s.me j [bf]).isNone

-- Vex, Cheerless (SFD-146): in combat, my spells cost 1 less (not below 1), enemy spells 1 more
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "SFD-146" bf
  let (s3, _) ← putAt s2 s.you "OGN-051" bf
  let (s4, mine) ← put s3 s.me "OGN-024" .hand
  let (s5, theirs) ← put s4 s.you "OGN-024" .hand
  let cost (x : GameState) (p : PlayerId) (c : ObjId) : Option Nat :=
    ((x.cardDef? c).bind (x.effCost p c)).map (·.energy)
  let base := cost s5 s.me mine
  let ftl := s5.inShowdownAt bf s.me
  let powers (x : GameState) (p : PlayerId) (c : ObjId) : Option Nat :=
    ((x.cardDef? c).bind (x.effCost p c)).map (·.power.length)
  return base == some 3 && cost ftl s.me mine == some 2 && cost s5 s.me mine == some 3 &&
    cost ftl s.you theirs == some 4 && cost s5 s.you theirs == some 3 &&
    powers ftl s.you theirs == (powers s5 s.you theirs).map (· + 1) &&
    powers ftl s.me mine == (powers s5 s.me mine).map (· - 1)
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "SFD-146" bf
  let (s3, _) ← putAt s2 s.you "OGN-051" bf
  let (s4, cheap) ← put s3 s.me "OGN-004" .hand
  let cost (x : GameState) (c : ObjId) : Option Nat :=
    ((x.cardDef? c).bind (x.effCost s.me c)).map (·.energy)
  return cost s4 cheap == some 1 && cost (s4.inShowdownAt bf s.me) cheap == some 1

-- Void Drone (SFD-010): costs 2 less to play from anywhere other than the hand
#guard tsf fun s => do
  let (s1, inHand) ← put s s.me "SFD-010" .hand
  let (s2, inTrash) ← put s1 s.me "SFD-010" .trash
  let cost (x : GameState) (c : ObjId) : Option Nat :=
    ((x.cardDef? c).bind (x.effCost s.me c)).map (·.energy)
  return cost s2 inHand == some 3 && cost s2 inTrash == some 1

-- (review) Vex only counts while she is in the combat; Grimwyrm cannot go to a Rockfall Path
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "SFD-146" bf
  let (s3, _) ← putAt s2 s.you "OGN-051" bf
  let (s4, other) ← putBf s3 s.me "OGN-276"
  let (s5, _) ← putAt s4 s.me "OGN-051" other
  let (s6, _) ← putAt s5 s.you "OGN-051" other
  let (s7, mine) ← put s6 s.me "OGN-024" .hand
  let cost (x : GameState) : Option Nat :=
    ((x.cardDef? mine).bind (x.effCost s.me mine)).map (·.energy)
  return cost (s7.inShowdownAt bf s.me) == some 2 && cost (s7.inShowdownAt other s.me) == some 3
#guard tsf fun s => do
  let (s1, rock) ← putBf s s.me "SFD-216"
  let (s2, g) ← put s1 s.me "SFD-015" .hand
  let scored := s2.modObj rock (fun o => { o with scored := [s.me] })
  return (activate scored s.me g 3 [rock] (payOf scored g)).isNone
-- Rally the Troops (SFD-166): the units played this turn are buffed; draw 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-166" .hand
  let (s2, v) ← put s1 s.me "OGN-051" .hand
  let (s3, g) ← put s2 s.me "SFD-056" .hand
  let a ← play s3 s.me c
  let b ← play a s.me v
  let d ← play b s.me g
  let (t1, v2) ← put s s.me "OGN-051" .hand
  let t3 ← play t1 s.me v2
  let isBuffed (x : GameState) (code : String) : Option Bool :=
    (x.firstOf s.me .base code).bind (fun o => (x.obj? o).map (·.buffed))
  return a.handN s.me == s3.handN s.me && isBuffed b "OGN-051" == some true &&
    isBuffed t3 "OGN-051" == some false && isBuffed d "SFD-056" != some true

-- Ancient Warmonger (SFD-131): Assault for each enemy Unit here increases its Might as an attacker.
#guard tsf fun s => do
  let (s1, w) ← putAt s s.me "SFD-131" s.bf0
  let (s2, _) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, _) ← putAt s2 s.you "OGN-001" s.bf0
  let atk := (s3.modObj s.bf0 (fun o => { o with contested := some s.me })).inShowdownAt s.bf0 s.me
  return s3.kwAmount w .assault == 2 && s1.kwAmount w .assault == 0 &&
    atk.combatMight w true == 4 + 2 && atk.combatMight w false == 4 &&
    s3.mightNow w == some 4 && atk.mightNow w == some 6

-- Forecaster (SFD-065): my Mechs have Vision: when I play one, look at the top card, may recycle it
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-065" .base
  let (s2, m) ← put s1 s.me "SFD-062" .hand
  let (s3, o) ← put s2 s.me "OGN-051" .hand
  let (s4, e) ← put s3 s.you "SFD-062" .base
  let a ← fire s4 [.played s.me m] { yes := true }
  let b ← fire s4 [.played s.me m] { yes := false }
  let c ← fire s4 [.played s.me o]
  let d ← fire s4 [.played s.you e]
  return a.topCard s.me != s4.topCard s.me && b.topCard s.me == s4.topCard s.me &&
    c.topCard s.me == s4.topCard s.me && d.topCard s.me == s4.topCard s.me &&
    a.deckN s.me == s4.deckN s.me

-- Jax, Unmatched (SFD-054): an Equipment I play is attached to a unit I control
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-054" .base
  let (s2, _) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .hand
  let (s4, other) ← put s3 s.me "OGN-017" .hand
  let a ← play s4 s.me g
  let b ← play s4 s.me other
  let (q1, q) ← put s2 s.me "SFD-064" .hand
  let qd ← play q1 s.me q
  let (q2, q3) ← put s2 s.me "SFD-064" .base
  let (q4, q5) ← put q2 s.me "SFD-042" .base
  let once := (q2.detect [.played s.me q3]).length == 1 && (q4.detect [.played s.me q5]).length == 1
  let (t1, _) ← put s s.me "OGN-051" .base
  let (t2, g2) ← put t1 s.me "SFD-042" .hand
  let t ← play t2 s.me g2
  let att (x : GameState) (code : String) : Option Bool :=
    (x.firstOf s.me .base code).bind (fun o => (x.obj? o).map (·.attached.isSome))
  return att a "SFD-042" == some true && att b "OGN-017" != some true &&
    att t "SFD-042" == some false && att qd "SFD-064" == some true && once

-- Quick-Draw and paid Equip both grant Shield to the Unit that wears the Armor.
-- The Equip ability becomes available again after detaching (CR 818.5.a).
#guard tsf fun s => do
  let p := s.me
  let (s, armor) ← put s p "SFD-064" .hand
  let (s, first) ← put s p "OGN-136" .base
  let (s, second) ← put s p "OGN-136" .base
  let ready ← play s p armor [] { pick := (· == [first]) }
  let gear ← ready.firstOf p .base "SFD-064"
  let loose := (detachObj ready gear).1
  let moved ← activate loose p gear 0 [second] ⟨0, [.mind]⟩
  return ready.kwAmount first .shield == 2 && ready.kwAmount second .shield == 0 &&
    moved.kwAmount first .shield == 0 && moved.kwAmount second .shield == 2 &&
    (activate ready p gear 0 [second] ⟨0, [.mind]⟩).isNone &&
    (activate loose p gear 0 [second]).isNone

-- Kato the Arm (SFD-112): when I move to a battlefield, a friendly unit gets my keywords and my
-- Might this turn
#guard tsf fun s => do
  let (s1, k) ← putAt s s.me "SFD-112" s.bf0
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let a ← fire s2 [.standardMoved k (some s.bf0)] { pick := fun ts => ts == [u] }
  let (t1, kb) ← put s s.me "SFD-112" .base
  let (t2, ub) ← put t1 s.me "OGN-051" .base
  let b ← fire t2 [.standardMoved kb none] { pick := fun ts => ts == [ub] }
  return a.mightNow u == (s2.mightNow u).map (· + 3) && a.hasKw u .deflect &&
    !s2.hasKw u .deflect && b.mightNow ub == t2.mightNow ub && !b.hasKw ub .deflect

-- (audit) Kato gives all the keywords it has, those it was given for the turn too
#guard tsf fun s => do
  let (s1, k) ← putAt s s.me "SFD-112" s.bf0
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let armed := (addTempKw { keyword := .assault } .turn s2 k).1
  let a ← fire armed [.standardMoved k (some s.bf0)] { pick := fun ts => ts == [u] }
  return a.hasKw u .deflect && a.hasKw u .assault && !armed.hasKw u .assault

-- Fiora, Worthy (SFD-180): when a unit I control becomes Mighty (here: by a buff to 5 Might), I may
-- pay Order to ready it
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-180" .base
  let (s2, four) ← put s1 s.me "OGN-012" .base
  let (s3, three) ← put s2 s.me "OGN-006" .base
  let (s4, five) ← put s3 s.me "OGN-049" .base
  let (s5, foe) ← put s4 s.you "OGN-012" .base
  let tired := ((((s5.tire four).tire three).tire five).tire foe).rich s.me
  let up (x : GameState) (u : ObjId) : Option Bool := x.tired u |>.map (!·)
  let a ← fireFrom tired (tired.buff four) [.buffed four]
  let b ← fireFrom tired (tired.buff three) [.buffed three]
  let c ← fireFrom tired (tired.buff five) [.buffed five]
  let d ← fireFrom tired (tired.buff foe) [.buffed foe]
  let e ← fireFrom tired (tired.buff four) [.buffed four] { yes := false }
  return up a four == some true && up b three == some false && up c five == some false &&
    up d foe == some false && up e four == some false 

-- Grand Duelist (SFD-205): when one of my units becomes Mighty, I may exhaust my legend to channel
-- 1 rune exhausted
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-205" .legendZone
  let (s2, four) ← put s1 s.me "OGN-012" .base
  let (s3, three) ← put s2 s.me "OGN-006" .base
  let (s4, foe) ← put s3 s.you "OGN-012" .base
  let runes (x : GameState) := (x.zone (.player s.me .runeDeck)).length
  let a ← fireFrom s4 (s4.buff four) [.buffed four]
  let b ← fireFrom s4 (s4.buff three) [.buffed three]
  let c ← fireFrom s4 (s4.buff foe) [.buffed foe]
  let d ← fireFrom s4 (s4.buff four) [.buffed four] { yes := false }
  let e ← fireFrom s4 ((s4.buff four).tire l) [.buffed four]
  return a.tired l == some true && runes a + 1 == runes s4 && runes b == runes s4 &&
    runes c == runes s4 && runes d == runes s4 && d.tired l == some false &&
    runes e == runes s4

-- Hextech Anomaly (SFD-083) and Ancient Henge (SFD-117): exhaust, pay any amount of one resource:
-- add that much of the other
/-- Use an ability with the player's own pool as it is (`activate` makes the player rich), and let
the Chain resolve with room for many questions. -/
meta def activateAsIs (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat)
    (says : Says := {}) : Option GameState :=
  match step 100 s ⟨.player p, .activate src idx ⟨0, []⟩ []⟩ with
  | .ok (s1, _) => some (settleChain says 60 s1)
  | .error _ => none

-- Hextech Anomaly: an Add (no Chain): pay any amount of Power, the player chooses which, to add that
-- much Energy; it is exhausted
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-083" .base
  let funded := s1.fund s.me 0 0 0 0 3 0 0
  let use (x : GameState) (pay : RunePool.Payment) :=
    step 100 x ⟨.player s.me, .manaAbility g 0 pay⟩
  let some a := (match use funded ⟨0, [.mind, .mind, .mind]⟩ with | .ok (r, _) => some r | _ => none)
    | return false
  let some b := (match use funded ⟨0, [.mind]⟩ with | .ok (r, _) => some r | _ => none)
    | return false
  let none_ := match use funded ⟨0, []⟩ with | .ok _ => false | .error _ => true
  let toomuch := match use funded ⟨0, [.mind, .mind, .mind, .mind]⟩ with
    | .ok _ => false | .error _ => true
  let withEnergy := match use funded ⟨1, [.mind]⟩ with | .ok _ => false | .error _ => true
  let again := match use a ⟨0, [.mind]⟩ with | .ok _ => false | .error _ => true
  return (a.poolOf s.me).energy == (funded.poolOf s.me).energy + 3 && (a.poolOf s.me).mind == 0 &&
    a.tired g == some true && (a.zone .chain).isEmpty &&
    (b.poolOf s.me).energy == (funded.poolOf s.me).energy + 1 && (b.poolOf s.me).mind == 2 &&
    none_ && toomuch && withEnergy && again

-- Ancient Henge: an Add (no Chain): pay any amount of Energy to add that much Power of any domain
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-117" .base
  let funded := s1.fund s.me 4
  let use (x : GameState) (pay : RunePool.Payment) :=
    step 100 x ⟨.player s.me, .manaAbility g 0 pay⟩
  let some a := (match use funded ⟨4, []⟩ with | .ok (r, _) => some r | _ => none) | return false
  let some b := (match use funded ⟨1, []⟩ with | .ok (r, _) => some r | _ => none) | return false
  let none_ := match use funded ⟨0, []⟩ with | .ok _ => false | .error _ => true
  let toomuch := match use funded ⟨5, []⟩ with | .ok _ => false | .error _ => true
  return (a.poolOf s.me).energy == 0 && (a.poolOf s.me).any == 4 && (a.zone .chain).isEmpty &&
    (b.poolOf s.me).energy == 3 && (b.poolOf s.me).any == 1 && none_ && toomuch

-- Fire Below the Mountain (SFD-189): exhaust my legend: add 1 rainbow Power (a mana ability)
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-189" .legendZone
  let r := step 100 s1 ⟨.player s.me, .manaAbility l 0 ⟨0, []⟩⟩
  match r with
  | .ok (a, _) =>
    let again := step 100 a ⟨.player s.me, .manaAbility l 0 ⟨0, []⟩⟩
    return (a.poolOf s.me).any == (s1.poolOf s.me).any + 1 && a.tired l == some true &&
      (match again with | .ok _ => false | .error _ => true)
  | .error _ => return false

-- (review) Fiora when an Equipment makes the unit Mighty: the whole bonus counts (Brutalizer gives
-- 1 and 2 more the turn it is attached), and a buff that was already there does not count again
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-180" .base
  let (s2, three) ← put s1 s.me "OGN-006" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let (s4, five) ← put s3 s.me "OGN-049" .base
  let (s5, g2) ← put s4 s.me "SFD-030" .base
  let t := (s5.rich s.me).tire three |>.tire five
  let up (x : GameState) (u : ObjId) : Option Bool := x.tired u |>.map (!·)
  let a ← fireFrom t (attachTo three t g).1 [.attached g three]
  let b ← fireFrom t (attachTo five t g2).1 [.attached g2 five]
  return up a three == some true && up b five == some false && (a.mightNow three).any (5 ≤ ·)
-- Needlessly Large Yordle (SFD-055): costs 2 Energy less for each point I scored by holding
#guard tsf fun s => do
  let (s1, y) ← put s s.me "SFD-055" .hand
  let (s2, a) ← putBf s1 s.me "OGN-275"
  let (s3, b) ← putBf s2 s.me "OGN-276"
  let held (x : GameState) (bf : ObjId) (p : PlayerId) : GameState :=
    x.modObj bf (fun o => { o with held := [p] })
  let cost (x : GameState) : Option Nat :=
    ((x.cardDef? y).bind (x.effCost s.me y)).map (·.energy)
  let pw (x : GameState) : Option Nat :=
    ((x.cardDef? y).bind (x.effCost s.me y)).map (·.power.length)
  return cost s3 == some 10 && cost (held s3 a s.me) == some 8 &&
    cost (held (held s3 a s.me) b s.me) == some 6 && cost (held s3 a s.you) == some 10 &&
    pw s3 == some 3 && pw (held s3 a s.me) == some 2 &&
    pw (held (held s3 a s.me) b s.me) == some 1 && pw (held s3 a s.you) == some 3

-- Sivir chooses the enemy Unit before resolution and uses the amount from the Conquer.
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "SFD-120" bf
  let (s3, foe) ← putAt s2 s.you "OGN-088" s.bf0
  let combat (attackerExcess : Nat) : GameState :=
    { s3.addTurnFxOn s.me bf (.excessDamage attackerExcess) with
      combat := some { battlefield := bf, attacker := s.me, defender := s.you, units := [] },
      pending := [.combatFinish bf] }
  let five := combat 7
  let four := combat 4
  let events := [Event.scored s.me bf true]
  let (choosing, _) ← (advance 100 (five.withTriggers events) []).toOption
  let accept : Action := ⟨.player s.me, .putTrigger 0 [foe]⟩
  let (waiting, _) ← (step 100 choosing accept).toOption
  let item ← (waiting.zone .chain).head?
  let a := settleChain {} 12 (clearCombatExcess waiting bf)
  let b ← fire four [.scored s.me bf true]
  let c ← fire five [.scored s.me bf true] { yes := false }
  let d ← fire five [.scored s.me bf false]
  return (waiting.obj? item).any (fun o => o.targets == [foe] && o.eventAmount == some 7) &&
    waiting.dmg foe == some 0 && a.dmg foe == some 7 && b.dmg foe == some 0 &&
    c.dmg foe == some 0 && d.dmg foe == some 0

-- (the held mark comes from holding, not from conquering; and it is gone the next turn)
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, other) ← putBf s1 s.me "OGN-276"
  let held := (s2.control s.me bf)
  let a := (hold held s.me).1
  let c := (scoreBf (s2.control s.me other) s.me other true).1
  let isHeld (x : GameState) (b : ObjId) := (x.obj? b).any (·.held.contains s.me)
  return isHeld a bf && !isHeld c other && (a.obj? bf).any (fun o => (clearScored o).held.isEmpty)

-- Counter Strike (SFD-194): the next damage to the chosen unit this turn is prevented; draw 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-194" .hand
  let (s2, u) ← put s1 s.me "OGN-049" .base
  let (s3, v) ← put s2 s.me "OGN-049" .base
  let (s3, rival) ← put s3 s.you "OGN-049" .base
  let a ← play s3 s.me c [u]
  let enemy ← play s3 s.me c [rival]
  let first := (dealObj 3 a u).1
  let second := (dealObj 2 first u).1
  let other := (dealObj 3 a v).1
  let zero := (dealObj 0 a u).1
  let later := (dealObj 3 { a with turn := a.turn + 1 } u).1
  return a.handN s.me == s3.handN s.me && first.dmg u == some 0 && second.dmg u == some 2 &&
    other.dmg v == some 3 && (dealObj 3 zero u).1.dmg u == some 0 && later.dmg u == some 3 &&
    (dealObj 3 enemy rival).1.dmg rival == some 0 && enemy.handN s.me == s3.handN s.me

-- Ornn's Forge (SFD-213): while its player controls it, their first non-token gear each turn costs
-- 1 less
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-213"
  let (s2, g) ← put s1 s.me "SFD-042" .hand
  let (s3, h) ← put s2 s.me "SFD-030" .hand
  let (s4, u) ← put s3 s.me "OGN-051" .hand
  let cost (x : GameState) (c : ObjId) (p : PlayerId := s.me) : Option Nat :=
    ((x.cardDef? c).bind (x.effCost p c)).map (·.energy)
  let mine := s4.control s.me bf
  let theirs := s4.control s.you bf
  let played ← play mine s.me g
  return cost s4 g == (cost mine g).map (· + 1) && cost mine g == (cost theirs g).map (· - 1) &&
    cost mine u == cost s4 u && cost played h == cost s4 h &&
    cost mine h == (cost s4 h).map (· - 1)

-- Hostile Takeover (SFD-202): take control of an enemy unit at a battlefield, ready it; at the end
-- of the turn it goes back and is recalled
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-202" .hand
  let (s2, u) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, _) ← put s2 s.you "OGN-051" .base
  let a ← play (s3.tire u) s.me c [u]
  let b ← fire a [.phaseStarted s.me .ending]
  let isCard (x : GameState) (o : ObjId) : Bool := (x.cardDef? o).any (·.id == cid "OGN-051")
  let theirs (x : GameState) : Nat :=
    ((x.zone (.player s.you .base)).filter (isCard x)).length
  let stolen (x : GameState) : Nat :=
    ((x.zone .battlefieldZone).filter (fun o => isCard x o &&
      (x.obj? o).any (·.controller == s.me))).length
  return (a.obj? u).any (fun o => o.controller == s.me && !o.exhausted) &&
    theirs a == 1 && stolen a == 1 && theirs b == 2 && stolen b == 0 &&
    (b.zone (.player s.you .base)).all (fun o => (b.obj? o).any (·.controller == s.you)) &&
    (fire a [.phaseStarted s.me .main]).any (fun x => stolen x == 1)

-- Yone, Blademaster (SFD-116): when I conquer an open battlefield, deal damage equal to my Might to
-- an enemy unit in a base
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, yone) ← putAt s1 s.me "SFD-116" bf
  let (s3, foe) ← put s2 s.you "OGN-088" .base
  let (s4, other) ← putBf s3 s.me "OGN-276"
  let (s5, _) ← putAt s4 s.me "SFD-116" other
  let (s6, foeAt) ← putAt s5 s.you "OGN-088" other
  let open_ := endShowdown s6 bf
  let a ← fire open_.1 open_.2.2
  -- a battlefield the opponent controlled: no damage
  let busy := (s6.control s.you bf)
  let clash := endShowdown busy bf
  let b ← fire clash.1 clash.2.2
  return a.dmg foe == (s6.mightNow yone).map Int.toNat && a.dmg foe != some 0 &&
    b.dmg foe == some 0 && a.dmg foeAt == some 0

-- (review) Hostile Takeover with another enemy unit there: the battlefield becomes Contested by me
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-202" .hand
  let (s2, bf) ← putBf s1 s.you "OGN-275"
  let (s3, u) ← putAt s2 s.you "OGN-051" bf
  let (s4, _) ← putAt s3 s.you "OGN-136" bf
  let a ← play (s4.control s.you bf) s.me c [u]
  return ((a.obj? bf).bind (·.contested)) == some s.me &&
    ((s4.obj? bf).bind (·.contested)).isNone
-- Guardian Angel (SFD-051): if the unit it is attached to would die, the Angel dies instead; the
-- Unit survives and reports Heal, Exhaust, and Recall in that order.
#guard tsf fun s => do
  let p := s.me
  let bf := s.bf0
  let (s, unit) ← putAt (s.control p bf) p "OGN-006" bf
  let (s, card) ← put s p "SFD-051" .hand
  let played ← play s p card
  let gear ← played.inBase p "SFD-051"
  let suited ← activate played p gear 0 [unit] ⟨0, [.calm]⟩
  let hit := suited.markDamage unit 4 (some s.you)
  let (saved, events) ← (advance 100 { hit with pending := .cleanup :: hit.pending } []).toOption
  let trashed ← saved.firstOf p .trash "SFD-051"
  let replaced := events.filter (fun
    | .died .. | .healed .. | .exhausted .. | .recalled .. | .standardMoved .. => true
    | _ => false)
  return (suited.obj? gear).any (·.attached == some unit) && suited.mightNow unit == some 4 &&
    (saved.obj? unit).any (fun o => o.damage == 0 && o.exhausted && o.loc.isNone) &&
    saved.where? unit == some (.player p .base) && saved.damageMarks[unit.n]?.isNone &&
    replaced == [.died trashed p, .healed unit 4, .exhausted unit, .recalled unit]

-- Soraka uses the same healing and exhaustion at Base, where the Unit already stands.
#guard tsf fun s => do
  let p := s.me
  let (s, _) ← put s p "SFD-173" .base
  let (s, unit) ← put s p "OGN-006" .base
  let hit := s.markDamage unit 3 (some s.you)
  let (saved, events) ← (advance 100 { hit with pending := .cleanup :: hit.pending } []).toOption
  return saved.where? unit == some (.player p .base) && saved.damageMarks[unit.n]?.isNone &&
    (saved.obj? unit).any (fun o => o.damage == 0 && o.exhausted) &&
    events == [.healed unit 3, .exhausted unit]

-- Combat Damage is marked on both sides before Guardian Angel's Cleanup replacement (CR 468.1).
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, defender) ← putAt (s.control p field) p "OGN-006" field
  let (s, gear) ← put s p "SFD-051" .base
  let (s, attacker) ← putAt (attachTo defender s gear).1 q "OGN-001" field
  let contested := s.modObj field (fun o => { o with contested := some q })
  let assigning := { contested with
    active := some q,
    combat := some {
      battlefield := field, attacker := q, defender := p, units := [attacker, defender] },
    pending := [.assign field q p [attacker] [(defender, 5)], .priority q] }
  let (saved, events) ← (step 100 assigning ⟨.player p, .assignDone⟩).toOption
  let dead ← saved.firstOf p .trash "SFD-051"
  return events.filter (fun
      | .damaged .. | .died .. | .healed .. | .exhausted .. | .recalled .. => true | _ => false) ==
        [.damaged defender 5, .damaged attacker 4, .died dead p, .healed defender 5,
          .exhausted defender, .recalled defender] &&
    saved.where? defender == some (.player p .base) &&
    (saved.obj? attacker).any (fun o => o.loc == some field)

-- The Angel also saves the attached Unit from a direct Kill, but stays attached after a nonlethal hit.
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, u) ← putAt s1 s.me "OGN-006" bf
  let (s3, g) ← put s2 s.me "SFD-051" .base
  let held := (attachTo u s3 g).1
  let hit := (dealObj 4 held u).1
  let soft := (dealObj 2 held u).1
  let killed := (killOrSave held u).1
  let bare := (dealObj 3 s3 u).1
  let isIn (x : GameState) (z : Zone) (code : String) : Bool :=
    (x.zone z).any (fun o => (x.cardDef? o).any (·.id == cid code))
  return isIn hit (.player s.me .trash) "SFD-051" && isIn hit (.player s.me .base) "OGN-006" &&
    ((hit.firstOf s.me .base "OGN-006").bind (fun o => hit.obj? o)).any
      (fun o => o.damage == 0 && o.exhausted && o.loc.isNone) &&
    isIn soft .battlefieldZone "OGN-006" && isIn soft (.player s.me .base) "SFD-051" &&
    isIn killed (.player s.me .trash) "SFD-051" && isIn killed (.player s.me .base) "OGN-006" &&
    bare.dmg u == some 3

-- Soraka, Wanderer (SFD-173): another unit of mine here with less Might than her is healed,
-- exhausted and recalled instead of dying
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "SFD-173" bf
  let (s3, weak) ← putAt s2 s.me "OGN-006" bf
  let (s4, strong) ← putAt s3 s.me "OGN-088" bf
  let (s5, foe) ← putAt s4 s.you "OGN-006" bf
  let (s6, home) ← put s5 s.me "OGN-006" .base
  let saved := (dealObj 3 s6 weak).1
  let (s7, other) ← putBf s6 s.me "OGN-276"
  let (s8, apart) ← putAt s7 s.me "OGN-006" other
  let elsewhere := (dealObj 3 s8 apart).1.dmg apart == some 3
  let isIn (x : GameState) (z : Zone) (code : String) : Bool :=
    (x.zone z).any (fun o => (x.cardDef? o).any (·.id == cid code))
  let atBf (x : GameState) : Nat :=
    ((x.zone .battlefieldZone).filter (fun o => (x.cardDef? o).any (·.id == cid "OGN-006") &&
      (x.obj? o).any (·.controller == s.me))).length
  return atBf s6 == 1 && atBf saved == 0 &&
    ((saved.zone (.player s.me .base)).filter (fun o => (saved.cardDef? o).any
      (·.id == cid "OGN-006"))).length == 2 &&
    (dealObj 3 s6 foe).1.dmg foe == some 3 && (dealObj 3 s6 home).1.dmg home == some 3 &&
    (dealObj 2 s6 weak).1.dmg weak == some 2 && (dealObj 8 s6 strong).1.dmg strong == some 8 &&
    elsewhere &&
    !isIn saved (.player s.me .trash) "OGN-006"

-- Rell, Magnetic (SFD-024): when I attack, I may play an Equipment costing 2 or less, free, and
-- attach it to me
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, rell) ← putAt s1 s.me "SFD-024" bf
  let (s3, _) ← putAt s2 s.you "OGN-051" bf
  let (s4, _) ← put s3 s.me "SFD-042" .hand
  let (s5, _) ← put s4 s.me "SFD-030" .hand
  let a ← fire s5 [.combatStarted bf s.me]
  let b ← fire s5 [.combatStarted bf s.me] { yes := false }
  let c ← fire s5 [.combatStarted bf s.you]
  let withRell (x : GameState) (code : String) : Bool :=
    (x.zone (.player s.me .base)).any (fun o => (x.cardDef? o).any (·.id == cid code) &&
      (x.obj? o).any (·.attached == some rell))
  return withRell a "SFD-042" && !withRell a "SFD-030" && a.handN s.me == s5.handN s.me - 1 &&
    !withRell b "SFD-042" && b.handN s.me == s5.handN s.me && !withRell c "SFD-042" &&
    (a.poolOf s.me).energy == (s5.poolOf s.me).energy

-- Sivir, Mercenary (SFD-143): once I have spent 2 or more Power this turn, +2 Might and Ganking
#guard tsf fun s => do
  let (s1, sivir) ← put s s.me "SFD-143" .base
  let pool (n : Nat) : GameState := s1.setPool s.me { spent := n }
  let paid := ((s1.rich s.me).poolOf s.me).spend ⟨0, [.fury, .calm]⟩
  let (s2, other) ← put (pool 0) s.you "SFD-143" .base
  return s1.mightNow sivir == some 4 && !s1.hasKw sivir .ganking &&
    (pool 1).mightNow sivir == some 4 && !(pool 1).hasKw sivir .ganking &&
    (pool 2).mightNow sivir == some 6 && (pool 2).hasKw sivir .ganking &&
    (pool 5).mightNow sivir == some 6 && paid.any (·.spent == 2) &&
    ((s2.setPool s.me { spent := 3 }).mightNow other == some 4)

-- (the Power paid by playing a card is counted)
#guard tsf fun s => do
  let (s1, v) ← put s s.me "SFD-146" .hand
  let a ← play s1 s.me v
  let (t1, c) ← put s s.me "OGN-051" .hand
  let b ← play t1 s.me c
  return (a.poolOf s.me).spent == 1 && (b.poolOf s.me).spent == 0

-- Battle Mistress (SFD-203): when I recycle a rune, I may exhaust my legend to play an exhausted
-- Gold; when enemy units die, ready my legend
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-203" .legendZone
  let rune ← (s1.zone (.player s.me .base)).find? (fun o =>
    (s1.obj? o).any (·.runeDomain.isSome))
  let rec_ ← applyRune s1 s.me rune .recycle
  let a ← fire rec_.1 rec_.2
  let b ← fire rec_.1 rec_.2 { yes := false }
  let c ← fire (rec_.1.tire l) rec_.2
  let exh ← applyRune s1 s.me rune .exhaust
  let d ← fire exh.1 exh.2
  let (t1, dead) ← put s1 s.you "OGN-051" .trash
  let e ← fire (t1.tire l) [.died dead s.you]
  let (t2, mine) ← put s1 s.me "OGN-051" .trash
  let f ← fire (t2.tire l) [.died mine s.me]
  let (t3, other) ← put t1 s.you "OGN-051" .trash
  let both := [Event.died dead s.you, Event.died other s.you]
  return a.countIn s.me .base "SFD-T03" == 1 && a.tired l == some true &&
    (a.firstOf s.me .base "SFD-T03").bind a.tired == some true &&
    b.countIn s.me .base "SFD-T03" == 0 && c.countIn s.me .base "SFD-T03" == 0 &&
    d.countIn s.me .base "SFD-T03" == 0 && e.tired l == some false && f.tired l == some true &&
    ((t3.tire l).detect both).countP (fun triggered => triggered.source == l) == 1

-- (review) Rell plays the Equipment for free: its Power is not paid either
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "SFD-024" bf
  let (s3, _) ← putAt s2 s.you "OGN-051" bf
  let (s4, _) ← put s3 s.me "SFD-022" .hand
  let broke := s4.setPool s.me {}
  let a ← fire broke [.combatStarted bf s.me]
  return ((a.zone (.player s.me .base)).any (fun o => (a.cardDef? o).any (·.id == cid "SFD-022") &&
    (a.obj? o).any (·.attached.isSome))) && (a.poolOf s.me).spent == 0

-- (review) a unit saved by Guardian Angel is also saved from "dies when damaged" effects
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, u) ← putAt s1 s.me "OGN-088" bf
  let (s3, g) ← put s2 s.me "SFD-051" .base
  let held := (attachTo u s3 g).1.addTurnFx s.you .killOnDamage
  let hit := (dealObj 1 held u).1
  let bare := (dealObj 1 (s3.addTurnFx s.you .killOnDamage) u).1
  let inTrash (x : GameState) (code : String) : Bool :=
    (x.zone (.player s.me .trash)).any (fun o => (x.cardDef? o).any (·.id == cid code))
  return inTrash hit "SFD-051" && !inTrash hit "OGN-088" && inTrash bare "OGN-088"
-- Forge of the Fluft (SFD-208): while I control it, my legend can exhaust: attach an Equipment I
-- control to a unit I control
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-208"
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let l ← s3.legendOf s.me
  let mine := s3.control s.me bf
  let a ← activate mine s.me l 0 [g, u]
  let theirs := activate (s3.control s.you bf) s.me l 0 [g, u]
  let none_ := activate s3 s.me l 0 [g, u]
  let tiredLegend := activate (mine.tire l) s.me l 0 [g, u]
  return (a.obj? g).any (·.attached == some u) && a.tired l == some true && theirs.isNone &&
    none_.isNone && tiredLegend.isNone

-- Emperor of the Sands (SFD-197): exhaust, pay 1: a Sand Soldier token, if I played an Equipment
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-197" .legendZone
  let (s2, g) ← put s1 s.me "SFD-042" .hand
  let before := activate (s2.fund s.me 5) s.me l 0 [] ⟨1, []⟩
  let played ← play s2 s.me g
  let a ← activate played s.me l 0 [] ⟨1, []⟩
  return before.isNone && a.countIn s.me .base "SFD-T03" == 0 &&
    ((a.zone (.player s.me .base)).filter (fun o => (a.cardDef? o).any
      (·.name == "Sand Soldier"))).length == 1 && a.tired l == some true

-- Bellows Breath (SFD-080): 1 damage to up to three units at the same location
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-080" .hand
  let (s2, a) ← putAt s1 s.you "OGN-088" s.bf0
  let (s3, b) ← putAt s2 s.you "OGN-088" s.bf0
  let (s4, d) ← putAt s3 s.me "OGN-088" s.bf0
  let (s5, e) ← put s4 s.you "OGN-088" .base
  let r ← play s5 s.me c [a, b, d]
  let one ← play s5 s.me c [a]
  let two ← play s5 s.me c [a, d]
  let empty ← play s5 s.me c []
  return r.dmg a == some 1 && r.dmg b == some 1 && r.dmg d == some 1 && r.dmg e == some 0 &&
    one.dmg a == some 1 && one.dmg b == some 0 && one.dmg d == some 0 &&
    two.dmg a == some 1 && two.dmg b == some 0 && two.dmg d == some 1 &&
    [a, b, d, e].all (fun u => empty.dmg u == some 0) &&
    (play s5 s.me c [a, b, b]).isNone && (play s5 s.me c [a, e]).isNone &&
    (play s5 s.me c [a, a]).isNone

-- The specific Base matters. Flash splits an original group and offers either resulting location.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, a) ← putAt (s.control q field) q "OGN-001" field
  let (s, b) ← putAt s q "OGN-001" field
  let (s, c) ← putAt s q "OGN-001" field
  let (s, home) ← put s p "OGN-001" .base
  let (s, spell) ← put s p "SFD-080" .hand
  let (s, flash) ← put s q "OGS-011" .hand
  let (chain, _) ← (step 100 (s.rich p)
    ⟨.player p, .playCard spell ⟨1, [.mind]⟩ [a, b, c]⟩).toOption
  let (response, _) ← (step 100 chain ⟨.player p, .pass⟩).toOption
  let (withFlash, _) ← (step 100 (response.rich q)
    ⟨.player q, .playCard flash ⟨2, []⟩ [c]⟩).toOption
  let choosing := settleChain {} 4 withFlash
  let atField : Action := ⟨.player p, .choose a⟩
  let atBase : Action := ⟨.player p, .choose c⟩
  let (fieldOnly, _) ← (step 100 choosing atField).toOption
  let (baseOnly, _) ← (step 100 choosing atBase).toOption
  let separated := (moveHome s c).1
  return (play separated p spell [c, home]).isNone && fieldOnly.dmg a == some 1 &&
    fieldOnly.dmg b == some 1 && fieldOnly.dmg c == some 0 && baseOnly.dmg a == some 0 &&
    baseOnly.dmg b == some 0 && baseOnly.dmg c == some 1 && baseOnly.dmg home == some 0

-- Relentless Pursuit (SFD-184): move a friendly unit; this turn it may go home when it conquers
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-184" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, bf) ← putBf s2 s.me "OGN-275"
  let a ← play s3 s.me c [u] { fromEnd := some 0 }
  let atBf := (a.zone .battlefieldZone).any (fun o => (a.cardDef? o).any (·.id == cid "OGN-051") &&
    (a.obj? o).any (·.loc == some bf))
  let home ← fire a [.scored s.me bf true]
  let stay ← fire a [.scored s.me bf true] { yes := false }
  let later := (a.addTurnFx s.me .unitsReady).turn
  return atBf && later == a.turn && ((home.zone (.player s.me .base)).any (fun o =>
    (home.cardDef? o).any (·.id == cid "OGN-051"))) && ((stay.zone .battlefieldZone).any (fun o =>
    (stay.cardDef? o).any (·.id == cid "OGN-051")))

-- Prodigal Explorer (SFD-199): exhaust, Reaction: draw 1, only if I chose enemy objects with
-- two spells this turn
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-199" .legendZone
  let (s2, foe) ← put s1 s.you "OGN-088" .base
  let (s3, mine) ← put s2 s.me "OGN-088" .base
  let (s4, c1) ← put s3 s.me "OGN-050" .hand
  let (s5, c2) ← put s4 s.me "OGN-050" .hand
  let one ← play s5 s.me c1 [foe]
  let two ← play one s.me c2 [foe]
  let own ← play (← play s5 s.me c1 [mine]) s.me c2 [mine]
  let mixed ← play (← play s5 s.me c1 [foe]) s.me c2 [mine]
  let ok := activate two s.me l 0 [] ⟨0, []⟩
  return (activate one s.me l 0 [] ⟨0, []⟩).isNone &&
    (activate own s.me l 0 [] ⟨0, []⟩).isNone &&
    (activate mixed s.me l 0 [] ⟨0, []⟩).isNone &&
    ok.any (fun x => x.handN s.me == two.handN s.me + 1 && x.tired l == some true)

-- Chem-Baroness (SFD-201): when I hold, I may exhaust my legend for an exhausted Gold; with my
-- score within 3 of the Victory Score my Gold adds 1 more Energy
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-201" .legendZone
  let (s2, bf) ← putBf s1 s.me "OGN-275"
  let a ← fire s2 [.scored s.me bf false]
  let b ← fire s2 [.scored s.me bf false] { yes := false }
  let c ← fire s2 [.scored s.me bf true]
  let (s3, gold) ← put s2 s.me "SFD-T03" .base
  let use (x : GameState) := step 100 x ⟨.player s.me, .manaAbility gold 0 ⟨0, []⟩⟩
  let near := s3.gainPoints s.me 6
  let far := s3.gainPoints s.me 4
  let pw (r : Except _ (GameState × List Event)) : Option (Nat × Nat) :=
    match r with | .ok (x, _) => some ((x.poolOf s.me).energy, (x.poolOf s.me).any) | _ => none
  return a.countIn s.me .base "SFD-T03" == 1 && a.tired l == some true &&
    b.countIn s.me .base "SFD-T03" == 0 && c.countIn s.me .base "SFD-T03" == 0 &&
    pw (use near) == some ((s3.poolOf s.me).energy + 1, (s3.poolOf s.me).any + 1) &&
    pw (use far) == some ((s3.poolOf s.me).energy, (s3.poolOf s.me).any + 1) &&
    pw (use s3) == some ((s3.poolOf s.me).energy, (s3.poolOf s.me).any + 1)

-- A teammate's Hold uses each Legend's own controller and pays each optional cost separately.
#guard tsf fun base => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let opening ← GameState.initial base.cards config (List.replicate 4 goodDeck)
  let start ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) opening).toOption
  let p := start.me
  let ally ← start.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← start.players.find? (fun q => !config.mode.sameSide p q)
  let (s, chem) ← put start p "SFD-201" .legendZone
  let (s, gloom) ← put s ally "UNL-193" .legendZone
  let (s, bf) ← putBf s ally "OGN-275"
  let (s, _) ← putAt s ally "UNL-087" bf
  let (s, allyGold) ← put s ally "SFD-T03" .base
  let highScore := s.gainPoints ally (s.victoryScore - 3)
  let (scored, _, events) := scoreBf (s.control ally bf) ally bf false
  let triggers := scored.detect events
  let (waiting, _) ← (advance 100
    { scored with pending := insertTriggers triggers (below scored.pending) } []).toOption
  let hold := settleChain {} 32 waiting
  let skip := settleChain { yes := false } 32 waiting
  let foe ← fire s [.scored enemy bf false]
  let conquest ← fire s [.scored ally bf true]
  let gold (after : GameState) := after.countIn p .base "SFD-T03"
  let spawned ← hold.firstOf p .base "SFD-T03"
  let highHold := hold.gainPoints ally (hold.victoryScore - 3)
  return triggers.countP (fun t => t.source == chem && t.controller == p) == 1 &&
    triggers.countP (fun t => t.source == gloom && t.controller == ally) == 2 &&
    gold hold == 1 && hold.tired chem == some true && hold.tired spawned == some true &&
    hold.tired gloom == some true && hold.handN ally == s.handN ally + 1 &&
    hold.handN p == s.handN p && highHold.manaBonus p spawned == 1 &&
    highScore.manaBonus ally allyGold == 0 &&
    [skip, foe, conquest].all (fun after =>
      gold after == 0 && after.handN ally == s.handN ally && after.tired gloom == some false)

-- Marai Spire (SFD-211) and Ezreal, Prodigy (SFD-149): optional additional costs cost less
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-023" .hand
  let (s2, u) ← put s1 s.me "SFD-029" .hand
  let (s3, bf) ← putBf s2 s.me "SFD-211"
  let dC ← s3.cardDef? c
  let dU ← s3.cardDef? u
  let rep (x : GameState) : List Cost := x.extrasFor s.me c dC
  let acc (x : GameState) : List Cost := x.extrasFor s.me u dU
  let mine := s3.control s.me bf
  let (e1, _) ← put s3 s.me "SFD-149" .base
  let base := rep s3
  return base.length == 1 && (rep mine).map (·.total) == base.map (fun k => k.total - 1) &&
    (rep (s3.control s.you bf)).map (·.total) == base.map (·.total) &&
    (acc s3).map (·.total) == [2] && (acc e1).map (·.total) == [1] &&
    (rep e1).map (·.total) == base.map (fun k => k.total - 1) &&
    (rep (e1.control s.me bf)).map (·.total) == base.map (fun k => k.total - 2)

-- Ezreal, Prodigy: when I play it, discard 1, then draw 2
#guard tsf fun s => do
  let (s1, e) ← put s s.me "SFD-149" .hand
  let a ← fire s1 [.played s.me e]
  return a.handN s.me == s1.handN s.me + 1 && a.deckN s.me + 2 == s1.deckN s.me

-- Temporal Portal (SFD-078): the next spell I play this turn has Repeat for its own cost
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-078" .base
  let (s2, c) ← put s1 s.me "OGN-050" .hand
  let (s3, foe) ← put s2 s.you "OGN-088" .base
  let dC ← s3.cardDef? c
  let funded := s3.fund s.me 12 12 12 12 12 12 12
  let a ← activate funded s.me g 0 [] ⟨0, [.fury]⟩
  let cost ← a.effCost s.me c dC
  let double : RunePool.Payment :=
    ⟨2 * cost.energy, (payOf a c).power ++ (payOf a c).power⟩
  let picks : SpellPick := .withCosts (.thenRepeat .plain 1 .plain) false 1
  let r ← cast a s.me c double [foe, foe] (pick := picks)
  let before := (s3.playCostsOf s.me c dC cost).length
  return (a.playCostsOf s.me c dC cost).length == before + 1 &&
    s3.paysForX s.me c dC cost double == false && a.paysForX s.me c dC cost double &&
    (a.playMark s.me c double).paid && !(a.playMark s.me c (payOf a c)).paid &&
    a.tired g == some true && (r.extrasFor s.me c dC).length == before - 1

-- (review) Marai Spire cuts Energy only: a Repeat that costs Power only keeps its Power; an
-- additional cost cut to nothing counts as paid
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-122" .hand
  let (s2, bf) ← putBf s1 s.me "SFD-211"
  let d ← s2.cardDef? c
  let mine := s2.control s.me bf
  let (s3, y) ← put s2 s.me "SFD-109" .hand
  let dy ← s3.cardDef? y
  let (s4, _) ← put s3 s.me "SFD-149" .base
  let basePay := payOf s4 y
  return (mine.extrasFor s.me c d).all (·.power.length == 1) &&
    (mine.extrasFor s.me c d).length == 1 &&
    !(s4.paidExtra s.me y dy basePay) && (s4.extrasFor s.me y dy).all (·.total == 1) &&
    s2.paidExtra s.me c d (payOf s2 c) == false

-- (review) a spell that chose an enemy unit that is still there counts, one that chose its own
-- unit does not
#guard tsf fun s => do
  let (s2, c) ← put s s.me "OGN-050" .hand
  let (s3, mine) ← put s2 s.me "OGN-088" .base
  let (s4, foe2) ← put s3 s.you "OGN-088" .base
  let a ← play s4 s.me c [foe2]
  let b ← play s4 s.me c [mine]
  let n (x : GameState) : Option Nat := (Amount.spellsChoseEnemy.evalS x s.me c {})
  return n a == some 1 && n b == some 0
-- Undertitan (SFD-175): when I play it, my other units get +2 Might this turn; as it is revealed
-- from my deck, I add 2 Energy
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-175" .base
  let (s2, ally) ← put s1 s.me "OGN-051" .base
  let (s3, foe) ← put s2 s.you "OGN-051" .base
  let a ← fire s3 [.played s.me u]
  let (t1, top) ← put s3 s.me "SFD-175" .mainDeck
  let b ← fire t1 [.revealed s.me top]
  let c ← fire t1 [.revealed s.you top]
  return a.mightNow ally == (s3.mightNow ally).map (· + 2) && a.mightNow u == s3.mightNow u &&
    a.mightNow foe == s3.mightNow foe &&
    (b.poolOf s.me).energy == (t1.poolOf s.me).energy + 2 && c.poolOf s.me == t1.poolOf s.me

-- Svellsongur (SFD-059): the unit it is attached to has its own triggered abilities once more
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-149" .base
  let (s2, g) ← put s1 s.me "SFD-059" .base
  let held := (attachTo u s2 g).1
  return (triggersOf s2 u s.me .play).length == 1 && (triggersOf held u s.me .play).length == 2

-- The Zero Drive (SFD-090): the unit it is attached to is banished when it dies
#guard tsf fun s => do
  let (s1, u) ← put s s.me "OGN-051" .base
  let (s2, g) ← put s1 s.me "SFD-090" .base
  let held := (attachTo u s2 g).1
  let killed := killObj held u
  let a ← fire killed.1 killed.2
  let (t1, v) ← put s s.me "OGN-051" .base
  let plain := killObj t1 v
  let b ← fire plain.1 plain.2
  let inZone (x : GameState) (z : ZoneKind) : Bool :=
    (x.zone (.player s.me z)).any (fun o => (x.cardDef? o).any (·.id == cid "OGN-051"))
  return inZone a .banishment && !inZone a .trash && inZone b .trash && !inZone b .banishment

-- Akshan, Mischievous (SFD-109): paying BodyBody more, when I play him I take an enemy gear (an
-- Equipment is attached to him)
#guard tsf fun s => do
  let (s1, a) ← put s s.me "SFD-109" .hand
  let (s2, g) ← put s1 s.you "SFD-042" .base
  let (s3, _) ← put s2 s.you "SFD-030" .base
  let base := payOf s3 a
  let more : RunePool.Payment := ⟨base.energy, base.power ++ [.body, .body]⟩
  let plain ← play s3 s.me a [] { pick := fun ts => ts == [g] }
  let paid ← cast (s3.rich s.me) s.me a more [] { pick := fun ts => ts == [g] }
  let mine (x : GameState) (code : String) : Bool :=
    (x.zone (.player s.me .base)).any (fun o => (x.cardDef? o).any (·.id == cid code) &&
      (x.obj? o).any (·.controller == s.me))
  let akshan := (paid.zone (.player s.me .base)).find? (fun o =>
    (paid.cardDef? o).any (·.id == cid "SFD-109"))
  return !mine plain "SFD-042" && plain.countIn s.you .base "SFD-042" == 1 &&
    mine paid "SFD-042" && !mine paid "SFD-030" && paid.countIn s.you .base "SFD-042" == 0 &&
    ((paid.zone (.player s.me .base)).any (fun o => (paid.cardDef? o).any
      (·.id == cid "SFD-042") && (paid.obj? o).any (fun x => x.attached == akshan)))

-- Irelia, Graceful (SFD-141): my spells that choose her cost 1 Energy or 1 Power less
#guard tsf fun s => do
  let (s1, irelia) ← put s s.me "SFD-141" .base
  let (s2, c) ← put s1 s.me "OGN-050" .hand
  let (s3, other) ← put s2 s.me "OGN-088" .base
  let d ← s3.cardDef? c
  let cost ← s3.effCost s.me c d
  let full := payOf s3 c
  let lessEnergy : RunePool.Payment := ⟨full.energy - 1, full.power⟩
  let lessPower : RunePool.Payment := ⟨full.energy, full.power.drop 1⟩
  let ok (pay : RunePool.Payment) (ts : List ObjId) : Bool :=
    castable (s3.rich s.me) s.me c pay ts
  let r1 ← cast (s3.rich s.me) s.me c lessEnergy [irelia]
  let en (x : GameState) := (x.poolOf s.me).energy
  return cost.energy ≥ 1 && !ok full [irelia] && ok lessEnergy [irelia] &&
    ok lessPower [irelia] &&
    ok full [other] && !ok lessEnergy [other] && !ok lessPower [other] &&
    en r1 + (full.energy - 1) == ((s3.rich s.me).poolOf s.me).energy &&
    ((r1.zone .chain).isEmpty || true) &&
    -- the payment is taken as a cut cost: it is not an additional cost
    !(s3.playMark s.me c lessEnergy [irelia]).paid && !(s3.playMark s.me c full []).paid &&
    (legalActions (s3.rich s.me)).contains ⟨.player s.me, .playCard c lessEnergy [irelia]⟩ &&
    !(legalActions (s3.rich s.me)).contains ⟨.player s.me, .playCard c lessEnergy [other]⟩

-- Void Hatchling (SFD-018): when I would reveal a card from my Main Deck, I look at the top card
-- first and may recycle it; revealing a card of my hand or the Rune Deck does not count
#guard tsf fun s => do
  let (s1, hatch) ← put s s.me "SFD-018" .base
  let (s2, _) ← s1.stackTop s.me ["OGN-088", "OGN-136"]
  let top ← s2.topCard s.me
  let env : Env := ({} : Env).bind pickVar (.obj top)
  let a := runEffect1 s2 s.me hatch env (.prim (.reveal (.var pickVar))) .nil effectAddPolicy
  let plain := runEffect1 (s2.modObj hatch id |>.setZone (.player s.me .base) []) s.me hatch env
    (.prim (.reveal (.var pickVar))) .nil effectAddPolicy
  let looks (r : GameState × List Frame × List Event) : Bool :=
    match r.2.1 with
    | [.run _ _ _ (.cons (.prim (.lookTop 1)) _)] => true
    | _ => false
  return looks a && !looks plain

#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-018" .base
  let (s2, bf) ← putBf s1 s.me "OGN-275"
  let (s3, _) ← putAt s2 s.me "OGN-200" bf
  let (s4, _) ← putAt s3 s.you "OGN-051" bf
  let (s5, _) ← s4.stackTop s.me ["OGN-088", "OGN-136"]
  let r ← fire s5 [.combatStarted bf s.me] { yes := true }
  return r.topCard s.me == s5.topCard s.me
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-018" .base
  let (s2, c) ← put s1 s.me "OGN-008" .hand
  let (s3, x) ← put s2 s.me "OGN-051" .hand
  let (s4, foe) ← putAt s3 s.you "OGN-116" s.bf0
  let (s5, _) ← s4.stackTop s.me ["OGN-088", "OGN-136"]
  let r ← play s5 s.me c [foe] { obj := fun o => o == x, yes := true }
  return r.topCard s.me == s5.topCard s.me && r.countIn s.me .trash "OGN-051" == 1

-- Rek'Sai, Breacher (SFD-029): a friendly unit played from somewhere other than a hand may pay
-- 1 Energy and 1 Fury Power to enter ready
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-029" .base
  let (s2, fromTrash) ← put s1 s.me "OGN-051" .trash
  let (s3, inHand) ← put s2 s.me "OGN-051" .hand
  let played := (playFree s.me s3 fromTrash)
  let handPlay := (playFree s.me s3 inHand)
  let units (x : GameState) : List ObjId :=
    (x.zone (.player s.me .base)).filter (fun o => (x.cardDef? o).any (·.id == cid "OGN-051"))
  let tiredAll (x : GameState) : Bool := (units x).all (fun o => x.tired o == some true)
  let a ← fire (played.1.rich s.me) played.2 { yes := true }
  let b ← fire (played.1.rich s.me) played.2 { yes := false }
  let c ← fire (handPlay.1.rich s.me) handPlay.2
  let d ← fire (played.1.fund s.me 0) played.2
  return tiredAll played.1 && tiredAll b && tiredAll c && tiredAll d &&
    (units a).all (fun o => a.tired o == some false) && (units a).length == 1 &&
    ((a.poolOf s.me).energy + 1 == ((played.1.rich s.me).poolOf s.me).energy)

-- (Emperor of the Sands) a Sand Soldier token is played: I may Equip an Equipment to it for 1 less
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-197" .legendZone
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, played) ← put s2 s.me "SFD-042" .hand
  let (s4, _) ← put s3 s.me "OGN-051" .base
  let funded := s4.rich s.me
  let started := funded.modObj played (fun o => { o with playedTurn := some funded.turn })
  let a ← activate started s.me l 0 []
    ⟨1, []⟩ { pick := fun ts => ts == [g] }
  let sand := (a.zone (.player s.me .base)).find? (fun o =>
    (a.cardDef? o).any (·.name == "Sand Soldier"))
  return sand.isSome && (a.obj? g).any (fun o => o.attached == sand)

-- (Akshan) the gear goes back to its owner when he leaves the board
#guard tsf fun s => do
  let (s1, a) ← put s s.me "SFD-109" .hand
  let (s2, g) ← put s1 s.you "SFD-042" .base
  let base := payOf s2 a
  let more : RunePool.Payment := ⟨base.energy, base.power ++ [.body, .body]⟩
  let paid ← cast (s2.rich s.me) s.me a more [] { pick := fun ts => ts == [g] }
  let akshan ← (paid.zone (.player s.me .base)).find? (fun o =>
    (paid.cardDef? o).any (·.id == cid "SFD-109"))
  let killed := killObj paid akshan
  let after ← fire killed.1 killed.2
  let gear (x : GameState) (p : PlayerId) : Bool :=
    (x.zone (.player p .base)).any (fun o => (x.cardDef? o).any (·.id == cid "SFD-042") &&
      (x.obj? o).any (·.controller == p))
  return gear paid s.me && !gear paid s.you && gear after s.you && !gear after s.me

-- (The Zero Drive) pay 3 Mind-ish and banish it: play every unit it banished, free; only unattached
#guard tsf fun s => do
  let (s1, u) ← put s s.me "OGN-051" .base
  let (s2, v) ← put s1 s.me "OGN-136" .base
  let (s3, g) ← put s2 s.me "SFD-090" .base
  let held := (attachTo u s3 g).1
  let k1 := killObj held u
  let dead1 ← fire k1.1 k1.2
  let (s4, _) := ((attachTo v dead1 g).1, 0)
  let k2 := killObj s4 v
  let fired ← fire k2.1 k2.2
  -- the Main Phase goes on, with the priority
  let both := { fired with pending := s3.pending }
  let (t1, _) ← put both s.me "OGN-051" .trash
  let inZone (x : GameState) (z : ZoneKind) (code : String) : Nat :=
    ((x.zone (.player s.me z)).filter (fun o => (x.cardDef? o).any (·.id == cid code))).length
  let loose := both.modObj g (fun o => { o with attached := none })
  let used ← activate loose s.me g 0 [] ⟨3, [.mind]⟩
  let blocked := activate (attachTo (v) loose g).1 s.me g 0 [] ⟨3, [.mind]⟩
  return inZone both .banishment "OGN-051" == 1 && inZone both .banishment "OGN-136" == 1 &&
    inZone used .base "OGN-051" == 1 && inZone used .base "OGN-136" == 1 &&
    inZone used .banishment "OGN-051" == 0 && inZone used .banishment "SFD-090" == 1 &&
    inZone t1 .trash "OGN-051" == 1 && inZone used .banishment "OGN-136" == 0 &&
    (blocked.map (fun x => inZone x .banishment "OGN-051")).getD 1 == 1

-- (review) Akshan: drawing or discarding him does not return the gear; the other player's Akshan is
-- not mixed up with mine
#guard tsf fun s => do
  let (s1, a) ← put s s.me "SFD-109" .hand
  let (s2, g) ← put s1 s.you "SFD-042" .base
  let base := payOf s2 a
  let more : RunePool.Payment := ⟨base.energy, base.power ++ [.body, .body]⟩
  let paid ← cast (s2.rich s.me) s.me a more [] { pick := fun ts => ts == [g] }
  let (s3, spare) ← put paid s.me "SFD-109" .mainDeck
  let moved ← moveObj s3 spare (.player s.me .hand)
  let drawn ← fire moved.1 [.moved spare moved.2 (.player s.me .hand)]
  let (t1, theirs) ← put paid s.you "SFD-109" .base
  let k := killObj t1 theirs
  let mirror ← fire k.1 k.2
  let gear (x : GameState) (p : PlayerId) : Bool :=
    (x.zone (.player p .base)).any (fun o => (x.cardDef? o).any (·.id == cid "SFD-042") &&
      (x.obj? o).any (·.controller == p))
  return gear paid s.me && gear drawn s.me && !gear drawn s.you && gear mirror s.me &&
    !gear mirror s.you

-- (Svellsongur) the Unit's passive abilities count twice as well
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-143" .base
  let (s2, g) ← put s1 s.me "SFD-059" .base
  let spent := s2.setPool s.me { spent := 2 }
  let held := (attachTo u spent g).1
  return spent.mightNow u == some 6 && held.mightNow u == some 8

-- (Prodigal Explorer) the abilities of my units that chose enemy objects count with my spells
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-199" .legendZone
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, foe) ← put s2 s.you "OGN-088" .base
  let (s4, mine) ← put s3 s.me "OGN-088" .base
  let (s5, c) ← put s4 s.me "OGN-050" .hand
  let d ← s5.cardDef? u
  let pend : PendTrigger := { source := u, card := d.id, idx := 0, controller := s.me }
  let one := putTrigger s5 pend [foe]
  let two := putTrigger one pend [foe]
  let own := putTrigger (putTrigger s5 pend [mine]) pend [mine]
  let withSpell ← play one s.me c [foe]
  let n (x : GameState) := Amount.spellsChoseEnemy.evalS x s.me l {}
  return n s5 == some 0 && n one == some 1 && n two == some 2 && n own == some 0 &&
    n withSpell == some 2

-- (Rek'Sai) the unit pays for its own domain
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-029" .base
  let (s2, fromTrash) ← put s1 s.me "OGN-051" .trash
  let d ← s2.cardDef? fromTrash
  let played := playFree s.me s2 fromTrash
  let poor := played.1.fund s.me 5
  let a ← fire (played.1.fund s.me 5 12 12 12 12 12 12) played.2 { yes := true }
  let b ← fire poor played.2 { yes := true }
  let units (x : GameState) : List ObjId :=
    (x.zone (.player s.me .base)).filter (fun o => (x.cardDef? o).any (·.id == d.id))
  return (units a).all (fun o => a.tired o == some false) &&
    (units b).all (fun o => b.tired o == some true)


-- (review) Irelia: two of her cut twice, one chosen twice cuts once, no duplicate payments
#guard tsf fun s => do
  let (s1, i1) ← put s s.me "SFD-141" .base
  let (s2, i2) ← put s1 s.me "SFD-141" .base
  let (s3, c) ← put s2 s.me "OGN-024" .hand
  let d ← s3.cardDef? c
  let cost ← s3.effCost s.me c d
  let opts := cost.cutOptions 2
  let mixed : RunePool.Payment :=
    ⟨cost.energy - 1, (payOf s3 c).power.drop 1⟩
  return s3.chooseCut s.me c [i1, i2] == 2 && s3.chooseCut s.me c [i1, i1] == 1 &&
    s3.chooseCut s.me c [] == 0 && opts.eraseDups.length == opts.length &&
    (s3.paysForXT s.me c d cost [i1, i2] mixed) &&
    !(s3.paysForXT s.me c d cost [i1] mixed)


-- Void Hatchling with a real revealing card (Apprentice Smith, SFD-041): the top card is looked at
-- first and may be recycled, so the card revealed afterwards is the next one
#guard tsf fun s => do
  let (s1, smith) ← putAt s s.me "SFD-041" s.bf0
  let (s2, _) ← put s1 s.me "SFD-018" .base
  let (s3, _) ← s2.stackTop s.me ["SFD-042", "OGN-050", "OGN-088"]
  let (t3, _) ← s1.stackTop s.me ["SFD-042", "OGN-050", "OGN-088"]
  let ev := [Event.standardMoved smith (some s.bf0)]
  let yes ← fire s3 ev { yes := true }
  let no ← fire s3 ev { yes := false }
  let plain ← fire t3 ev
  return plain.handN s.me == t3.handN s.me + 1 && no.handN s.me == s3.handN s.me + 1 &&
    yes.handN s.me == s3.handN s.me


-- Svellsongur: the Unit's activated abilities are copied too (Udyr, OGN-157: spend a buff: ...)
#guard tsf fun s => do
  let (s1, udyr) ← put s s.me "OGN-157" .base
  let (s2, g) ← put s1 s.me "SFD-059" .base
  let (s3, _) ← putAt s2 s.you "OGN-088" s.bf0
  let d ← s3.cardDef? udyr
  let copyIdx := d.fullAbilities.length
  let held := (attachTo udyr s3 g).1
  let buffed := held.buff udyr
  let loose := s3.buff udyr
  let ok (x : GameState) (idx : Nat) : Bool :=
    activatable (x.rich s.me) s.me udyr idx ⟨0, []⟩ [] true
  return ok buffed 0 && ok buffed copyIdx && ok loose 0 && !ok loose copyIdx &&
    !ok (s3.buff udyr) copyIdx && copyIdx > 0

-- Irelia: a Power cut may leave out any symbol of the cost, not only the first; the same symbols in
-- another order are one cost; the Energy does not go below a floor the cost already has
#guard
  let c : Cost := ⟨2, [.domain .fury, .domain .calm]⟩
  let o := c.cutOptions 1
  let has (e : Nat) (l : List PowerSym) : Bool :=
    o.any (fun x => x.energy == e && canonPower x.power == canonPower l)
  has 1 [.domain .fury, .domain .calm] && has 2 [.domain .calm] && has 2 [.domain .fury] &&
    !o.contains c && o.length == 3 && o.all (fun x => x.power.length ≤ 2) &&
    ((⟨2, [.domain .fury, .domain .calm, .domain .fury]⟩ : Cost).cutOptions 1).length == 3 &&
    (⟨1, [.domain .fury]⟩ : Cost).cutOptions 1 1 == [⟨1, []⟩] &&
    (⟨2, [.domain .fury]⟩ : Cost).cutOptions 1 1 == [⟨2, []⟩, ⟨1, [.domain .fury]⟩]

-- Flash (OGS-011): up to two friendly units move to their base, both of them
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGS-011" .hand
  let (s2, a) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, b) ← putAt s2 s.me "OGN-051" s.bf0
  let (s4, e) ← putAt s3 s.you "OGN-051" s.bf0
  let (lo, hi) := if a.n < b.n then (a, b) else (b, a)
  let two ← play s4 s.me c [lo, hi]
  let one ← play s4 s.me c [hi]
  return (two.obj? a).any (·.loc.isNone) && (two.obj? b).any (·.loc.isNone) &&
    (one.obj? lo).any (·.loc == some s.bf0) && (one.obj? hi).any (·.loc.isNone) &&
    (play s4 s.me c [hi, lo]).isNone && (play s4 s.me c [e]).isNone &&
    (play s4 s.me c [lo, hi, e]).isNone

-- "When you choose me" counts a choice by an ability; "when you choose me with a spell" does not:
-- Azir, Ascendant (SFD-050) chooses a friendly unit
#guard tsf fun s => do
  let (s1, az) ← put s s.me "SFD-050" .base
  let (s2, ir) ← put s1 s.me "SFD-057" .base
  let (s3, jae) ← put s2 s.me "SFD-142" .base
  let a ← activate s3 s.me az 0 [ir] ⟨0, [.calm]⟩
  let b ← activate s3 s.me az 0 [jae] ⟨0, [.calm]⟩
  return a.mightNow ir == (s3.mightNow ir).map (· + 1) && b.handN s.me == s3.handN s.me &&
    b.mightNow ir == s3.mightNow ir

-- A choice made while an effect resolves sets off "when you choose me" too (Irelia, Fervent gives
-- itself +1 Might), by an ability or by a spell; the only candidate and a chosen one both count
#guard tsf fun s => do
  let (s1, ir) ← put s s.me "SFD-057" .base
  let (s2, other) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let body : Effect := .prim (.buff (Selector.one .friendly .anywhere [.ofType .unit]))
  let picked ← runBody s3 s.me g [] body { obj := fun o => o == ir }
  let other' ← runBody s3 s.me g [] body { obj := fun o => o == other }
  let lone ← runBody (s3.modObj other (fun o => o)) s.me g [] (.prim (.buff
    (Selector.one .friendly .anywhere [.ofType .unit, .named "Irelia"])))
  return (picked.obj? ir).any (·.mightMods.length == 1) &&
    (other'.obj? ir).any (·.mightMods.isEmpty) && (lone.obj? ir).any (·.mightMods.length == 1)

-- `Prim.choose` only says the objects were chosen: Irelia, Fervent gets its +1 Might, nothing moves
#guard tsf fun s => do
  let (s1, ir) ← put s s.me "SFD-057" .base
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let r ← runBody s2 s.me g [] (.prim (.choose (.slot 0)))
  let r2 ← runBody s2 s.me g [ir] (.prim (.choose (.slot 0)))
  return (r2.obj? ir).any (·.mightMods.length == 1) && (r2.obj? ir).any (·.loc.isNone) &&
    (r.obj? ir).any (·.mightMods.isEmpty)

-- Pickpocket can kill a Gold token with no printed cost (Energy cost 0).
#guard tsf fun s => do
  let (s1, p) ← put s s.me "SFD-074" .hand
  let (s2, _) ← applyCreate s1 s.you p {} "Gold" (.const 1) .atBase false
  let g ← (s2.zone (.player s.you .base)).find? (fun o => (s2.cardDef? o).any (·.name == "Gold"))
  let a ← play s2 s.me p [] { pick := fun ts => ts == [g] }
  return (a.obj? g).isNone

-- Perched Grimwyrm needs a battlefield the player conquered, not one it only held
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, g) ← put s1 s.me "SFD-015" .hand
  let conquered := s2.modObj bf (fun o => { o with scored := [s.me] })
  let held := s2.modObj bf (fun o => { o with scored := [s.me], held := [s.me] })
  let a ← play conquered s.me g [bf]
  return unitAt a "SFD-015" bf && (play held s.me g [bf]).isNone

-- Another object's permission cannot bypass Perched Grimwyrm's location restriction.
#guard tsf fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s p "OGN-275"
  let (s, other) ← putBf s p "OGN-275"
  let (s, _) ← putAt (s.control q field) q "OGN-051" field
  let (s, _) ← put s p "UNL-117" .base
  let (s, grimwyrm) ← put s p "SFD-015" .hand
  let (s, ordinary) ← put s p "VEN-014" .hand
  let scored := s.modObj other (fun o => { o with scored := [p] })
  let scoredBoth := scored.modObj field (fun o => { o with scored := [p] })
  let paid := scored.rich p
  let invalid : Action := ⟨.player p, .playCard grimwyrm ⟨4, []⟩ [field]⟩
  let allowed ← play scored p grimwyrm [other]
  let atEnemyField ← play scoredBoth p grimwyrm [field]
  return (scored.playBfOptions p ordinary).contains field &&
    !(legalActions paid).contains invalid && ((step 100 paid invalid).toOption).isNone &&
    unitAt allowed "SFD-015" other && unitAt atEnemyField "SFD-015" field

-- Here to Help's mandatory destination must also satisfy the Unit's restriction (CR 355.17.b).
#guard tsf fun s => do
  let p := s.me
  let (s, field) ← putBf s p "OGN-275"
  let (s, help) ← put (s.control p field) p "SFD-111" .hand
  let (s, grimwyrm) ← put s p "SFD-015" .hand
  let scored := s.modObj field (fun o => { o with scored := [p] })
  let blocked ← play s p help [] { obj := (· == grimwyrm) }
  let allowed ← play scored p help [] { obj := (· == grimwyrm) }
  return blocked.locate grimwyrm == some (.player p .hand) &&
    (blocked.poolOf p).energy == 10 && unitAt allowed "SFD-015" field &&
    (allowed.poolOf p).energy == 9

-- Tianna Crownguard also stops the points an effect gives the opponent ("you score 1 point")
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "SFD-060" bf
  let (s3, g) ← put s2 s.you "SFD-042" .base
  let (s4, g2) ← put s s.you "SFD-042" .base
  let a ← runBody s3 s.you g [] (.prim (.score .you (.const 1)))
  let b ← runBody s4 s.you g2 [] (.prim (.score .you (.const 1)))
  return a.pointsOf s.you == s3.pointsOf s.you && b.pointsOf s.you == s4.pointsOf s.you + 1

-- Paying while an effect resolves uses Runes when the Pool falls short: two ready Runes are
-- exhausted for 2 Energy; with no Rune and an empty Pool nothing is paid
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-042" .base
  let exhausted (x : GameState) : Nat :=
    ((x.runesOf s.me).filter (fun r => (x.obj? r).any (·.exhausted))).length
  let ready (x : GameState) : Nat :=
    ((x.runesOf s.me).filter (fun r => (x.obj? r).any (fun o => !o.exhausted))).length
  let a ← runBody (s1.setPool s.me {}) s.me g [] (.prim (.pay ⟨2, []⟩))
  let bare := (s1.noRunes s.me).setPool s.me {}
  let b ← runBody bare s.me g [] (.prim (.pay ⟨2, []⟩))
  let can := Condition.canPay ⟨2, []⟩
  return 2 ≤ ready s1 && exhausted a == exhausted s1 + 2 && (a.poolOf s.me).energy == 0 &&
    exhausted b == exhausted bare && can.eval s1 s.me g {} == some true &&
    can.eval bare s.me g {} == some false

-- Rell attaches only the Equipment it has just played, not one played earlier in the turn
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, rell) ← putAt s1 s.me "SFD-024" bf
  let (s3, _) ← putAt s2 s.you "OGN-051" bf
  let (s4, old) ← put s3 s.me "SFD-030" .base
  let s5 := s4.modObj old (fun o => { o with playedTurn := some s.turn, playedStamp := some 1 })
  let (s6, _) ← put s5 s.me "SFD-042" .hand
  let a ← fire s6 [.combatStarted bf s.me]
  return (a.obj? old).any (·.attached.isNone) &&
    (a.zone (.player s.me .base)).any (fun o => (a.cardDef? o).any (·.id == cid "SFD-042") &&
      (a.obj? o).any (·.attached == some rell))

-- Relentless Pursuit may attach an Equipment with the unit's controller to the unit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-184" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← putBf s2 s.me "OGN-275"
  let (s4, g) ← put s3 s.me "SFD-042" .base
  let (s5, foe) ← put s4 s.you "SFD-042" .base
  let a ← play s5 s.me c [u, g] { fromEnd := some 0 }
  let ua := (a.zone .battlefieldZone).find? (fun o => (a.cardDef? o).any (·.id == cid "OGN-051"))
  let w ← ua
  return (a.obj? g).any (·.attached == some w) && (play s5 s.me c [u, foe] { fromEnd := some 0 }).isNone

-- Lonely Poro is alone as it dies: a unit that comes there before its ability resolves does not
-- change that
#guard tsf fun s => do
  let (s1, x) ← putAt s s.me "SFD-036" s.bf0
  let (st1, evs) := killObj s1 x
  let (st2, _) ← putAt st1 s.me "OGN-051" s.bf0
  let r ← fire st2 evs
  return r.handN s.me == st2.handN s.me + 1

-- Playing a card for its cost while an effect resolves pays with Runes when the Pool is empty
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-042" .base
  let (s2, u) ← put s1 s.me "OGN-003" .hand
  let exhausted (x : GameState) : Nat :=
    ((x.runesOf s.me).filter (fun r => (x.obj? r).any (·.exhausted))).length
  let d ← s2.cardDef? u
  let c ← s2.effCost s.me u d
  let play := Effect.prim (.playReduced (Selector.one .friendly .inHand [.ofType .unit])
    (.const 0) none)
  let empty := s2.setPool s.me {}
  let a ← runBody empty s.me g [] play
  let b ← runBody (empty.noRunes s.me) s.me g [] play
  return c.energy == 2 && a.countIn s.me .base "OGN-003" == 1 &&
    exhausted a == exhausted empty + 2 && b.countIn s.me .base "OGN-003" == 0

-- A Unit with Reaction (Janna) answers the Chain by being played at once, to the Base
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-053" .hand
  let (s2, plain) ← put s1 s.me "OGN-051" .hand
  let s3 := { s2.rich s.me with pending := .chainPass s.me 0 :: s2.pending }
  let act : Action := ⟨.player s.me, .playCard j (payOf s3 j) []⟩
  let no : Action := ⟨.player s.me, .playCard plain (payOf s3 plain) []⟩
  let r ← match step 100 s3 act with
    | .ok (x, _) => some x
    | .error _ => none
  return (legalReactions s3 s.me).contains act && !(legalReactions s3 s.me).contains no &&
    (r.zone (.player s.me .base)).any (fun o => (r.cardDef? o).any (·.id == cid "SFD-053"))

-- The attackers set off their abilities as the Showdown begins, before anyone passes: Fiora is
-- doubled while the Showdown is still going on
#guard tsf fun s => do
  let (s1, f) ← put s s.me "SFD-110" .base
  let (s2, _) ← putAt s1 s.you "OGN-051" s.bf0
  let s3 := s2
  let moved ← match step 100 s3 ⟨.player s.me, .standardMove f (.battlefield s.bf0)⟩ with
    | .ok (x, _) => some x
    | .error _ => none
  let settled := settleChain {} 12 moved
  let inShowdown := settled.pending.any (fun fr => match fr with | .showdown .. => true | _ => false)
  return inShowdown && settled.mightNow f == (s3.mightNow f).map (· * 2)

-- The Power of Fire Below the Mountain pays only for Gear: a Gear costing 2 Energy and 1 Power can be
-- played with it, a Unit of the same cost cannot, and without it (or with other Power left) it can
#guard tsf fun s => do
  let (s1, g) ← put s s.me "OGN-021" .hand
  let (s2, u) ← put s1 s.me "OGN-036" .hand
  let bare := (s2.noRunes s.me)
  let some_ := bare.setPool s.me { energy := 5, any := 1 }
  let restricted := some_.addTurnFx s.me .gearMana
  let more := (bare.setPool s.me { energy := 5, any := 2 }).addTurnFx s.me .gearMana
  return playable restricted s.me g (payOf restricted g) &&
    !playable restricted s.me u (payOf restricted u) &&
    playable some_ s.me u (payOf some_ u) && playable more s.me u (payOf more u)

-- (Cleanup) A unit that is lethal in the Cleanup is saved as it is by damage: Guardian Angel dies
-- instead, and Soraka heals, exhausts and recalls the weaker unit next to her
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, u) ← putAt s1 s.me "OGN-006" bf
  let (s3, g) ← put s2 s.me "SFD-051" .base
  let held := (attachTo u s3 g).1
  let lethal := held.modObj u (fun o => { o with damage := 9 })
  let isIn (x : GameState) (z : Zone) (code : String) : Bool :=
    (x.zone z).any (fun o => (x.cardDef? o).any (·.id == cid code))
  let angel ← (cleanupStep lethal).map (·.1)
  let (t1, bf2) ← putBf s s.me "OGN-275"
  let (t2, _) ← putAt t1 s.me "SFD-173" bf2
  let (t3, weak) ← putAt t2 s.me "OGN-006" bf2
  let hurt := t3.modObj weak (fun o => { o with damage := 9 })
  let soraka ← (cleanupStep hurt).map (·.1)
  let (r1, bf3) ← putBf s s.me "OGN-275"
  let (r2, v) ← putAt r1 s.me "OGN-006" bf3
  let dead := (r2.modObj v (fun o => { o with damage := 9 }))
  let bare ← (cleanupStep dead).map (·.1)
  return isIn angel (.player s.me .trash) "SFD-051" && isIn angel (.player s.me .base) "OGN-006" &&
    isIn soraka (.player s.me .base) "OGN-006" && isIn soraka .battlefieldZone "SFD-173" &&
    ((soraka.firstOf s.me .base "OGN-006").bind (fun o => soraka.obj? o)).any
      (fun o => o.damage == 0 && o.exhausted) &&
    isIn bare (.player s.me .trash) "OGN-006"

-- Not So Fast (SFD-045) also counters an enemy ability that chooses a unit of mine: the ability
-- ceases to exist (Pitiless Stalker stuns a unit when it is used)
#guard tsf fun s => do
  let (s1, mine) ← put s s.you "OGN-051" .base
  let (s2, stalker) ← put s1 s.me "RAD-104" .base
  let (s3, nsf) ← put s2 s.you "SFD-045" .hand
  match step 100 (s3.rich s.me) ⟨.player s.me, .activate stalker 0 ⟨0, []⟩ [mine]⟩ with
  | .ok (a, _) =>
    let item := (a.zone .chain).head?
    match item with
    | some it =>
      let ok := match effectOf "SFD-045" with
        | some e => targetsOk a s.you nsf a.mightTable e.choices [it]
        | none => false
      let r := (counterObj a it).1
      return ok && (r.zone .chain).isEmpty && (r.obj? it).isNone
    | none => return false
  | .error _ => return false

-- (gear-only Power) Playing a Gear with the Power that only pays for Gear uses that Power first: the
-- Power of Any domain that is left is free to pay for a Unit
#guard tsf fun s => do
  let (s1, g) ← put s s.me "OGN-021" .hand
  let (s2, u) ← put s1 s.me "OGN-036" .hand
  let bare := s2.noRunes s.me
  let two := (bare.setPool s.me { energy := 8, any := 2 }).addTurnFx s.me .gearMana
  let a ← cast two s.me g (payOf two g)
  return playable two s.me g (payOf two g) && (a.poolOf s.me).any == 1 &&
    a.restrictedNow s.me == 0 && playable a s.me u (payOf a u)

-- Temporal Portals stack (CR 820.1): each Repeat is paid on its own, and the effect is done once
-- more for each one paid. Two Portals: the spell is done three times if both are paid.
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-078" .base
  let (s1b, g2) ← put s1 s.me "SFD-078" .base
  let (s2, c) ← put s1b s.me "OGN-050" .hand
  let (s3, foe) ← put s2 s.you "OGN-088" .base
  let dC ← s3.cardDef? c
  let funded := s3.fund s.me 12 12 12 12 12 12 12
  let a ← activate funded s.me g 0 [] ⟨0, [.fury]⟩
  let a2 ← activate (a.modObj g2 id) s.me g2 0 [] ⟨0, [.fury]⟩
  let cost ← a2.effCost s.me c dC
  let once : RunePool.Payment := ⟨cost.energy, (payOf a2 c).power⟩
  let twice : RunePool.Payment := ⟨2 * cost.energy, (payOf a2 c).power ++ (payOf a2 c).power⟩
  let thrice : RunePool.Payment :=
    ⟨3 * cost.energy, (payOf a2 c).power ++ (payOf a2 c).power ++ (payOf a2 c).power⟩
  let runs (pay : RunePool.Payment) (targets : List ObjId) (pick : SpellPick) : Option (Nat × Nat) := do
    let (st, _) ← (step 100 a2 ⟨.player s.me, .playCard c pay targets none none pick⟩).toOption
    let item ← (st.zone .chain).head?
    let o ← st.obj? item
    return (o.extraPaid, (resolveFrames st []).countP (fun | .run .. => true | _ => false))
  let two : SpellPick := .withCosts (.thenRepeat .plain 1 .plain) false 1
  let three : SpellPick := .withCosts (.thenRepeat .plain 1 (.thenRepeat .plain 1 .plain)) false 2
  return runs once [foe] .plain == some (0, 1) &&
    runs twice [foe, foe] two == some (1, 2) && runs thrice [foe, foe, foe] three == some (2, 3)

-- (CR 820.2) A repeated spell locks both targets while it is cast.
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-078" .base
  let (s2, c) ← put s1 s.me "OGN-005" .hand
  let (s3, e1) ← putAt s2 s.you "OGN-088" s.bf0
  let (s4, e2) ← putAt s3 s.you "OGN-088" s.bf0
  let dC ← s4.cardDef? c
  let funded := (s4.control s.you s.bf0).fund s.me 12 12 12 12 12 12 12
  let a ← activate funded s.me g 0 [] ⟨0, [.fury]⟩
  let cost ← a.effCost s.me c dC
  let double : RunePool.Payment :=
    ⟨2 * cost.energy, (payOf a c).power ++ (payOf a c).power⟩
  let once ← cast a s.me c (payOf a c) [e1] { obj := fun o => o == e2 }
  let pick : SpellPick := .withCosts (.thenRepeat .plain 1 .plain) false 1
  let twice ← cast a s.me c double [e1, e2] { obj := fun _ => false } pick
  return once.dmg e1 == some 3 && once.dmg e2 == some 0 && twice.dmg e1 == some 3 &&
    twice.dmg e2 == some 3 && (cast a s.me c double [e1]).isNone

-- (audit) Quick-Draw gives Reaction: the Gear can answer an item of the Chain, a plain Gear cannot
#guard tsf fun s => do
  let (s1, qd) ← put s s.me "SFD-022" .hand
  let (s2, plain) ← put s1 s.me "SFD-042" .hand
  let (s3, _) ← onChain s2 s.you "OGN-004"
  let rich := s3.rich s.me
  return reactable rich s.me qd (payOf rich qd) [] && !reactable rich s.me plain (payOf rich plain) []

-- (audit) Using an Add ability is using an ability: the event is raised
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-189" .legendZone
  let r ← applyMana s1 s.me l 0 ⟨0, []⟩
  return r.2 == [Event.activated s.me l 0 (some 0)]

-- (audit) A Temporary unit that is saved (Guardian Angel) is not killed at the start of the turn
#guard tsf fun s => do
  let sprite : Object :=
    { kind := .token (cid "TKN-Sprite"), owner := s.me, controller := s.me, timestamp := ⟨0⟩ }
  let (s1, u) ← addObject s sprite (.player s.me .base)
  let (s2, g) ← put s1 s.me "SFD-051" .base
  let held := (attachTo u s2 g).1
  let rescued ← settleBeginning held s.me
  let bare ← settleBeginning s1 s.me
  return (rescued.zone (.player s.me .base)).contains u &&
    rescued.countIn s.me .trash "SFD-051" == 1 && !(bare.zone (.player s.me .base)).contains u

-- Petricite Monument's Deflect covers teammates until its Temporary trigger resolves.
#guard tsf fun s => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let team := GameState.empty { s.config with mode := .teamDuel } s.cards
  let (s, monument) ← put team p "SFD-104" .base
  let (s, friendly) ← put s ally "RAD-001" .base
  let (s, opponent) ← put s enemy "RAD-001" .base
  let s := { s with active := some p, pending := [.phase .beginning] }
  let (waiting, _) ← (advance 100 s []).toOption
  let dead := settleChain {} 16 waiting
  return waiting.hasKw friendly .deflect && !waiting.hasKw opponent .deflect &&
    waiting.inPlay.contains monument && dead.countIn p .trash "SFD-104" == 1 &&
    !dead.hasKw friendly .deflect

-- (audit) Emperor of the Sands: only an Equipment played counts, not any other Gear
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-197" .legendZone
  let (s2, g) ← put s1 s.me "SFD-117" .base
  let (s3, e) ← put s2 s.me "SFD-022" .base
  let played (st : GameState) (o : ObjId) : GameState :=
    st.modObj o (fun x => { x with playedTurn := some st.turn })
  let amt (st : GameState) : Option Nat := Amount.equipmentPlayed.evalS st s.me l Env.empty
  let gearOnly := played s3 g
  let equip := played s3 e
  return amt s3 == some 0 && amt gearOnly == some 0 && amt equip == some 1

-- (audit) Drag Under costs 2 less to play from anywhere other than the hand
#guard tsf fun s => do
  let (s1, inHand) ← put s s.me "SFD-164" .hand
  let (s2, inTrash) ← put s1 s.me "SFD-164" .trash
  let dC ← s2.cardDef? inHand
  let a ← s2.effCost s.me inHand dC
  let b ← s2.effCost s.me inTrash dC
  return a.energy == b.energy + 2

-- (audit) The gear an Akshan took is given back when that Akshan leaves, not when another Akshan
-- (the same card) does
#guard tsf fun s => do
  let (s1, a) ← put s s.me "SFD-109" .hand
  let (s2, g) ← put s1 s.you "SFD-042" .base
  let base := payOf s2 a
  let more : RunePool.Payment := ⟨base.energy, base.power ++ [.body, .body]⟩
  let paid ← cast (s2.rich s.me) s.me a more [] { pick := fun ts => ts == [g] }
  let first ← (paid.zone (.player s.me .base)).find? (fun o =>
    (paid.cardDef? o).any (·.id == cid "SFD-109"))
  let (paid2, second) ← put paid s.me "SFD-109" .base
  let kill (st : GameState) (u : ObjId) : Option GameState := do
    let r := killObj st u
    fire r.1 r.2
  let afterSecond ← kill paid2 second
  let afterFirst ← kill paid2 first
  let gears (x : GameState) (p : PlayerId) : Nat := x.countIn p .base "SFD-042"
  return gears afterSecond s.me == 1 && gears afterSecond s.you == 0 &&
    gears afterFirst s.me == 0 && gears afterFirst s.you == 1

-- (audit) A Unit that an effect moves from a Battlefield to its Base has moved: Harpoon Squad
-- gets +2 Might, and the move is counted
#guard tsf fun s => do
  let (s1, h) ← putAt s s.me "SFD-137" s.bf0
  let r := moveHome s1 h
  let home ← (r.1.zone (.player s.me .base)).find? (fun o => (r.1.cardDef? o).any (·.id == cid "SFD-137"))
  let after ← fire r.1 r.2
  return r.2 == [Event.standardMoved home none] && (r.1.obj? home).any (·.moves == 1) &&
    after.mightNow home == (r.1.mightNow home).map (· + 2)

-- (audit) A Mech played as a token counts for Forecaster, and a token played after Rally the Troops
-- enters buffed
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-065" .base
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let a ← fire s2 [.tokenPlayed s.me m] { yes := true }
  let buffed := s2.addTurnFx s.me .unitsBuffed
  let made ← applyPrim buffed s.me m Env.empty (.create "Mech" (.const 1) .atBase false)
  let plain ← applyPrim s2 s.me m Env.empty (.create "Mech" (.const 1) .atBase false)
  let newOnes (x : GameState) (y : GameState) : List ObjId :=
    (y.zone (.player s.me .base)).filter (fun o => !(x.zone (.player s.me .base)).contains o)
  return a.topCard s.me != s2.topCard s.me &&
    (newOnes buffed made.1).length == 1 && (newOnes buffed made.1).all (fun o => (made.1.obj? o).any (·.buffed)) &&
    (newOnes s2 plain.1).all (fun o => (plain.1.obj? o).any (fun x => !x.buffed))

-- (audit) A Base is "here" for the units on it: Soraka at the Base saves a weaker unit there
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-173" .base
  let (s2, weak) ← put s1 s.me "OGN-006" .base
  let hit := (dealObj 3 s2 weak).1
  let others := ((hit.zone (.player s.me .base)).filter (fun o => (hit.cardDef? o).any
    (·.id == cid "OGN-006"))).length
  return others == 1 && !(hit.zone (.player s.me .trash)).any (fun o => (hit.cardDef? o).any
    (·.id == cid "OGN-006")) &&
    (hit.zone (.player s.me .base)).any (fun o => (hit.cardDef? o).any (·.id == cid "OGN-006") &&
      (hit.obj? o).any (fun x => x.damage == 0 && x.exhausted))

-- (audit) A Unit becomes Mighty by any change of its Might: here a lasting +2 Might, which is no buff
-- and no Equipment, takes a 3 Might unit to 5
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-180" .base
  let (s2, three) ← put s1 s.me "OGN-006" .base
  let t := ((s2.tire three).rich s.me)
  let up (x : GameState) (u : ObjId) : Option Bool := x.tired u |>.map (!·)
  let boosted := (addMightMod ⟨2, .turn⟩ t three).1
  let a ← fireFrom t boosted []
  let b ← fireFrom t t []
  return (t.mightNow three).any (· < 5) && (boosted.mightNow three).any (5 ≤ ·) &&
    up a three == some true && up b three == some false

-- (audit) Ezreal, Prodigy: an optional additional cost costs 1 Energy or 1 Power less, as the player
-- wishes: Accelerate (1 Energy and 1 Power) can be paid with the Energy or with the Power only
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-149" .base
  let (s2, u) ← put s1 s.me "SFD-029" .hand
  let d ← s2.cardDef? u
  let cost ← s2.effCost s.me u d
  let costs := s2.playCostsOf s.me u d cost
  let (t1, v) ← put s s.me "SFD-029" .hand
  let dv ← t1.cardDef? v
  let costv ← t1.effCost s.me v dv
  let plain := t1.playCostsOf s.me v dv costv
  return costs.contains (cost.plus ⟨0, [.own]⟩) && costs.contains (cost.plus ⟨1, []⟩) &&
    plain.contains (costv.plus ⟨1, [.own]⟩) && !plain.contains (costv.plus ⟨0, [.own]⟩)

-- (audit) A Unit played to a Battlefield is played, not an ability: it is on the Battlefield at
-- once, the Chain is empty, and a cost cut applies (Legion Quartermaster-style cuts go through
-- `effCost`)
#guard tsf fun s => do
  let (s1, v) ← put s s.me "SFD-093" .hand
  let (s2, _) ← putAt s1 s.you "OGN-051" s.bf0
  match step 100 (s2.rich s.me) ⟨.player s.me, .playCard v (payOf s2 v) [s.bf0]⟩ with
  | .ok (a, _) =>
    let onBf := (a.zone .battlefieldZone).find? (fun o => a.isCard "SFD-093" o)
    return (a.zone .chain).isEmpty && onBf.isSome &&
      (onBf.bind (a.obj? ·)).any (fun o => o.loc == some s.bf0 && o.playedFromHand)
  | .error _ => return false

-- (audit) The payments of "pay any amount" are listed as legal actions: each way to take Power the Pool
-- holds (here 2 Mind and 1 Body: 3 * 2 - 1 = 5 ways), and none when it holds none
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-083" .base
  let funded := ((s1.noRunes s.me).setPool s.me { mind := 2, body := 1 })
  let pays := (legalActions funded).filterMap (fun a =>
    match a.kind with | .manaAbility src 0 pay _ => if src == g then some pay else none | _ => none)
  let none_ := (legalActions ((s1.noRunes s.me).setPool s.me {})).filterMap (fun a =>
    match a.kind with | .manaAbility src 0 pay _ => if src == g then some pay else none | _ => none)
  return pays.length == 5 && pays.contains ⟨0, [.mind, .mind]⟩ && pays.contains ⟨0, [.mind, .body]⟩ &&
    !pays.contains ⟨0, []⟩ && none_.isEmpty

-- (audit) A unit at a Base that is lethal in the Cleanup (its Might fell) is healed and exhausted by
-- Soraka at that Base; the Cleanup ends: a second step kills it only if it still is lethal
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-173" .base
  let (s2, weak) ← put s1 s.me "OGN-006" .base
  let hurt := s2.modObj weak (fun o => { o with damage := 9 })
  let a ← (cleanupStep hurt).map (·.1)
  let alone := (s2.modObj weak (fun o => { o with damage := 9 }))
  let (t1, w2) ← put s s.me "OGN-006" .base
  let b ← (cleanupStep (t1.modObj w2 (fun o => { o with damage := 9 }))).map (·.1)
  return (a.obj? weak).any (fun x => x.damage == 0 && x.exhausted) &&
    (a.zone (.player s.me .base)).contains weak && (cleanupStep a).isNone &&
    !(b.zone (.player s.me .base)).contains w2 && alone.dmg weak == some 9

end RiftboundTest
