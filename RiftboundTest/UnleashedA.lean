module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests: Unleashed (scenario tests of single cards)

As `SpiritforgedA.lean`: each test puts the cards it needs in the lab (the Main Phase of the first
turn), plays or fires, lets the Chain resolve, and reads what happened.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- Run a scenario in the lab; it must say `true`. -/
meta def tun (f : GameState → Option Bool) : Bool :=
  match lab with
  | some s => (f s).getD false
  | none => false

private meta def testSpell (code : String) (energy : Nat) : CardDef :=
  { id := cid code, name := code, types := [.spell], cost := some ⟨energy, []⟩,
    spellEffect := some (.of [] .nop), status := .full }

/-- Establish a main phase with the team game seat order. -/
private meta def unleashedTeamMain (labState : GameState) : GameState :=
  let initial := GameState.empty { mode := .teamDuel, ruleSet := .coreOnly } labState.cards
  { initial with
    phase := .main
    turn := 3
    active := some ⟨0⟩
    pending := [.priority ⟨0⟩]
    turnOrder := Mode.teamTurnOrder true }

-- Bandle Soldier uses its controller's Level, while Scrutinizing Sergeant counts friendly Units.
#guard tun fun labState => do
  let s := unleashedTeamMain labState
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let (s, soldier) ← put s p "UNL-151" .hand
  let (s, sergeant) ← put s p "UNL-157" .hand
  let (s, _) ← put s p "OGN-001" .base
  let (s, _) ← put s mate "OGN-001" .base
  let (s, _) ← put s enemy "OGN-001" .base
  let (s, _) ← put s p "SFD-009" .base
  let short ← play ((s.setXP p 2).setXP mate 5) p soldier
  let levelled ← play (s.setXP p 3) p soldier
  let counted ← play s p sergeant
  let shortUnit ← short.firstOf p .base "UNL-151"
  let readyUnit ← levelled.firstOf p .base "UNL-151"
  return short.tired shortUnit == some true && levelled.tired readyUnit == some false &&
    counted.xpOf p == 3 && counted.xpOf mate == 0 && counted.xpOf enemy == 0

-- Moonlight Affliction resolves as a Reaction. At zero Might, at least one damage is needed
-- for lethal damage (CR 142.4.b).
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "UNL-066" .hand
  let (s, target) ← put s q "OGN-001" .base
  let (s, other) ← put s q "OGN-001" .base
  let (s, reactionTarget) ← onChain s q "OGN-004"
  let s := s.modObj reactionTarget (fun object => { object with targets := [target] })
  let s := { s with pending := [.chainPass p 0] }
  let result ← play s p spell [target]
  let damaged := s.modObj target (fun object => { object with damage := 1 })
  let lethal ← play damaged p spell [target]
  return result.mightNow target == (s.mightNow target).map (· - 10) &&
    (result.obj? target).isSome && (result.obj? other).isSome &&
    result.countIn p .trash "UNL-066" == 1 && lethal.countIn q .trash "OGN-001" == 1 &&
    (lethal.obj? other).isSome

-- Clash of Giants makes both chosen Units deal damage before Cleanup removes either.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "UNL-110" .hand
  let (s, first) ← put s p "OGN-136" .base
  let (s, second) ← put s q "OGN-136" .base
  let (s, third) ← put s q "OGN-001" .base
  let resolved ← play s p spell [first, second]
  let unequal ← play s p spell [first, third]
  return (play s p spell [first, first]).isNone && resolved.countIn p .trash "OGN-136" == 1 &&
    resolved.countIn q .trash "OGN-136" == 1 && (resolved.obj? third).map (·.damage) == some 0 &&
    unequal.countIn p .trash "OGN-136" == 1 && (unequal.obj? third).map (·.damage) == some 2

-- The Ruination kills the Units of all seats together and applies an existing death replacement.
#guard tun fun labState => do
  let s := unleashedTeamMain labState
  let p : PlayerId := ⟨0⟩
  let partner : PlayerId := ⟨1⟩
  let q : PlayerId := ⟨2⟩
  let r : PlayerId := ⟨3⟩
  let (s, spell) ← put s p "UNL-180" .hand
  let (s, _) ← put s p "OGN-136" .base
  let (s, _) ← put s partner "OGN-136" .base
  let (s, banished) ← put s q "OGN-136" .base
  let (s, field) ← putBf s r "OGN-275"
  let (s, _) ← putAt (s.control r field) r "OGN-136" field
  let (s, gear) ← put s q "SFD-009" .base
  let resolved ← play (s.addTurnFxOn p banished .banishInstead) p spell
  return ([p, partner, r].all (fun who => resolved.countIn who .trash "OGN-136" == 1)) &&
    resolved.countIn q .banishment "OGN-136" == 1 && resolved.countIn q .trash "OGN-136" == 0 &&
    (resolved.zone (.player q .base)).contains gear && resolved.battlefields.contains field

-- Arena Kingpin enters ready and can exhaust to give even an opponent's Unit temporary Might.
#guard tun fun s => do
  let p := s.me
  let (s, card) ← put s p "UNL-001" .hand
  let (s, enemy) ← put s s.you "OGN-051" .base
  let entered ← play s p card
  let kingpin ← entered.firstOf p .base "UNL-001"
  let stronger ← activate entered p kingpin 1 [enemy]
  let (later, _) ← (advance 100 { stronger with pending := [.expireTurn, .priority p] } []).toOption
  return entered.tired kingpin == some false && stronger.tired kingpin == some true &&
    stronger.mightNow enemy == some (5 : Int) && later.mightNow enemy == some (2 : Int)

-- Prepared Neophyte needs four Energy paid for a single Spell.
#guard tun fun s => do
  let p := s.me
  let small := testSpell "TEST-NEOPHYTE-2" 2
  let large := testSpell "TEST-NEOPHYTE-4" 4
  let s := { s with cards := { cards := s.cards.cards ++ [small, large] } }
  let (s, unit) ← put s p "UNL-004" .base
  let (s, first) ← put s p small.id.code .hand
  let (s, second) ← put s p small.id.code .hand
  let (s, expensive) ← put s p large.id.code .hand
  let afterFirst ← play s p first
  let afterSecond ← play afterFirst p second
  let afterExpensive ← play afterSecond p expensive
  let later := { afterExpensive with turn := afterExpensive.turn + 1 }
  return afterSecond.mightNow unit == some (1 : Int) && afterExpensive.mightNow unit == some (5 : Int) &&
    later.mightNow unit == some (1 : Int)

-- When an effect allows casting a card owned by another seat, the payer receives the bonus.
-- A later discounted cast of the same physical card does not erase the first payment.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let spell := testSpell "TEST-NEOPHYTE-REPLAY" 4
  let s := { s with cards := { cards := s.cards.cards ++ [spell] } }
  let (s, ours) ← put s p "UNL-004" .base
  let (s, theirs) ← put s q "UNL-004" .base
  let (s, offered) ← put (s.rich p) q spell.id.code .banishment
  let price : EffectPlayPrice := .reduceEnergy 0
  let (queued, item) ← queueLimitedSpell s p offered price .normal
  let fullPrice ← (limitedSpellOptions queued p item price).head?
  let (paid, events) ← commitLimitedSpell queued p item fullPrice [] effectAddPolicy
  let recorded := paid.recordTurnEvents events
  let (trash, recycled) ← moveObj recorded item (.player q .trash)
  let reduced : EffectPlayPrice := .reduceEnergy 3
  let (queuedAgain, itemAgain) ← queueLimitedSpell (trash.rich p) p recycled reduced .normal
  let cheaper ← (limitedSpellOptions queuedAgain p itemAgain reduced).head?
  let (paidAgain, laterEvents) ← commitLimitedSpell queuedAgain p itemAgain cheaper [] effectAddPolicy
  let again := paidAgain.recordTurnEvents laterEvents
  return fullPrice.cost.energy == 4 && cheaper.cost.energy == 1 &&
    (again.obj? itemAgain).any (fun o => o.owner == q && o.controller == p) &&
    recorded.mightNow ours == some (5 : Int) && recorded.mightNow theirs == some (1 : Int) &&
    recorded.playedOther p ours && !(recorded.playedOther q theirs) &&
    again.mightNow ours == some (5 : Int) && again.mightNow theirs == some (1 : Int) &&
    (again.playLog.filter (fun play => play.types.contains .spell)).map (·.energyPaid) == [1, 4]

-- Towering Pairofant considers a Unit that its teammate controlled when it died.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let (s, guest) ← put (unleashedTeamMain labState) mate "OGN-051" .base
  let (s, card) ← put s p "UNL-008" .hand
  let fresh ← play s p card
  let afterDeath ← play (killObj s guest).1 p card
  let ordinary ← fresh.firstOf p .base "UNL-008"
  let ready ← afterDeath.firstOf p .base "UNL-008"
  return fresh.tired ordinary == some true && afterDeath.tired ready == some false &&
    afterDeath.kwAmount ready .assault == 1

-- Upstage Comedy determines both targets at finalization when Repeat is paid.
#guard tun fun s => do
  let p := s.me
  let (s, spell) ← put s p "UNL-009" .hand
  let (s, ours) ← put s p "OGN-051" .base
  let (s, theirs) ← put s s.you "OGN-051" .base
  let before := (s.tire ours).tire theirs
  let funded := before.fund p 4
  let actions := legalFrameActions funded
  let ready (energy : Nat) (targets : List ObjId) : Option Action :=
    actions.find? (fun a => match a.kind with
      | .playCard card pay ids _ _ _ => card == spell && pay.energy == energy && ids == targets
      | _ => false)
  let one ← ready 2 [ours]
  let both ← ready 4 [ours, theirs]
  let (once, _) ← (step 100 funded one).toOption
  let (repeated, _) ← (step 100 funded both).toOption
  let single := settleChain {} 12 once
  let double := settleChain {} 12 repeated
  return single.tired ours == some false && single.tired theirs == some true &&
    double.tired ours == some false && double.tired theirs == some false &&
    !(legalFrameActions (before.fund p 3)).contains both &&
    (ready 4 [ours, ours]).isSome && (ready 2 [ours, theirs]).isNone

-- Concentrate uses the paying seat's larger Level discount once, including without a Legend.
#guard tun fun s => do
  let p := s.me
  let (s, spell) ← put s p "UNL-091" .hand
  let noLegend ← (s.zone (.player p .legendZone)).foldlM (fun t id =>
    (moveObj t id (.player p .trash)).map Prod.fst) s
  let richXP := (noLegend.setXP p 11).fund p 1
  let drawn ← cast richXP p spell ⟨1, []⟩
  let cost (xp : Nat) := (noLegend.setXP p xp).energyCost? p spell
  return [0, 5, 6, 10, 11, 12].map cost == [some 5, some 5, some 3, some 3, some 1, some 1] &&
    (noLegend.setXP s.you 11).energyCost? p spell == some 5 &&
    drawn.handN p == noLegend.handN p + 1 && (drawn.poolOf p).energy == 0

-- Evershade Stalker must discard before drawing. An empty hand still draws what it can.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, stalker) ← put s p "UNL-123" .hand
  let (s, fodder) ← put s p "OGN-051" .hand
  let (queued, _) ← (step 100 (s.rich p) ⟨.player p, .playCard stalker ⟨3, []⟩ []⟩).toOption
  let (next, _) ← (step 100 queued ⟨.player p, .pass⟩).toOption
  let (waiting, _) ← (step 100 next ⟨.player q, .pass⟩).toOption
  let (done, events) ← (step 100 waiting ⟨.player p, .discardPick fodder⟩).toOption
  let empty ← (s.zone (.player p .hand)).foldlM (fun t id =>
    (moveObj t id (.player p .trash)).map Prod.fst) s
  let (empty, sole) ← put empty p "UNL-123" .hand
  let fromEmpty ← play empty p sole
  return waiting.handN p + 1 == s.handN p && waiting.pending.head? == some (.discard p 1) &&
    !(legalFrameActions waiting).contains ⟨.player p, .discardDone⟩ &&
    done.handN p == waiting.handN p && done.countIn p .trash "OGN-051" == 1 &&
    events.any (fun | .discarded q _ _ => q == p | _ => false) &&
    events.any (fun | .drew q => q == p | _ => false) && fromEmpty.handN p == 1

-- Lunar Boon reacts above an older enemy Spell, discards a chosen card, then draws two.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, previous) ← onChain s q "OGN-129"
  let (s, moon) ← put s p "UNL-125" .hand
  let (s, fodder) ← put s p "OGN-051" .hand
  let opened := { (s.fund p 3) with active := some q, pending := [.chainPass p 0, .priority q] }
  let (casted, _) ← (step 100 opened ⟨.player p, .playCard moon ⟨3, []⟩ []⟩).toOption
  let (next, _) ← (step 100 casted ⟨.player p, .pass⟩).toOption
  let (waiting, _) ← (step 100 next ⟨.player q, .pass⟩).toOption
  let (drawn, events) ← (step 100 waiting ⟨.player p, .discardPick fodder⟩).toOption
  let draws := events.countP (fun | .drew q => q == p | _ => false)
  return waiting.pending.head? == some (.discard p 1) && waiting.handN p + 1 == s.handN p &&
    drawn.zone .chain == [previous] && drawn.handN p == waiting.handN p + 1 && draws == 2 &&
    drawn.countIn p .trash "OGN-051" == 1 && (casted.poolOf p).energy == 0

-- Vault Breaker legally opens a Battlefield-to-Battlefield Standard Move for this turn.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, destination) ← putBf s s.you "OGN-276"
  let (s, unit) ← putAt (s.control p field) p "OGN-051" field
  let (s, spell) ← put s p "UNL-010" .hand
  let move : Action := ⟨.player p, .standardMove unit (.battlefield destination)⟩
  let enhanced ← play s p spell [unit]
  let (moved, _) ← (step 100 enhanced move).toOption
  let (expired, _) ← (advance 100 { enhanced with pending := [.expireTurn, .priority p] } []).toOption
  return !(legalActions s).contains move && enhanced.kwAmount unit .assault == 2 &&
    moved.hereOf unit == some destination && !(legalActions expired).contains move &&
    expired.kwAmount unit .assault == 0

-- Only the caster's facedown card doubles Monster Harpoon's damage.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let victimField := s.bf0
  let (s, ownField) ← putBf s p "OGN-276"
  let (s, victim) ← putAt (s.control q victimField) q "OGN-116" victimField
  let (s, _) ← putAt (s.control p ownField) p "OGN-051" ownField
  let (s, spell) ← put s p "UNL-014" .hand
  let hide (board : GameState) (owner : PlayerId) (field : ObjId) : Option GameState := do
    let (next, card) ← put board owner "SFD-004" .hidden
    return next.modObj card (fun object => { object with hiddenAt := some field, hiddenTurn := some 0 })
  let foe ← hide s q victimField
  let both ← hide foe p ownField
  let plain ← play foe p spell [victim]
  let doubled ← play both p spell [victim]
  return (plain.obj? victim).any (·.damage == 2) && (doubled.obj? victim).any (·.damage == 4)

-- Right of Conquest draws for its own and its teammate's Battlefields.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let foe : PlayerId := ⟨2⟩
  let (s, home) ← putBf (unleashedTeamMain labState) p "OGN-275"
  let (s, ally) ← putBf s mate "OGN-276"
  let (s, other) ← putBf s foe "OGN-277"
  let (s, _) ← putBf s foe "OGN-280"
  let (s, _) ← putAt (s.control p home) p "OGN-051" home
  let (s, _) ← putAt (s.control mate ally) mate "OGN-051" ally
  let (s, _) ← putAt (s.control foe other) foe "OGN-051" other
  let (s, spell) ← put s p "UNL-015" .hand
  let s ← (List.range 4).foldlM (fun state _ => return (← put state p "OGN-051" .mainDeck).1) s
  let resolved ← play s p spell
  return resolved.handN p == s.handN p + 2 &&
    (resolved.zone (.player p .mainDeck)).length == 1 && resolved.handN mate == s.handN mate

-- Scorchclaw meets its Level at 3 XP and gains 2 XP from holding.
#guard tun fun s => do
  let p := s.me
  let (s, card) ← put s p "UNL-016" .hand
  let low ← play (s.setXP p 2) p card
  let high ← play (s.setXP p 3) p card
  let untrained ← low.firstOf p .base "UNL-016"
  let trained ← high.firstOf p .base "UNL-016"
  let field := s.bf0
  let (s, _) ← putAt (s.control p field) p "UNL-016" field
  let hunted ← fire (s.setXP p 2) [.scored p field false]
  return low.tired untrained == some true && high.tired trained == some false &&
    low.mightNow untrained == some 3 && high.mightNow trained == some 4 && hunted.xpOf p == 4

-- Jhin's Ganking move adds Energy and flexible Power before the next player decision.
#guard tun fun s => do
  let p := s.me
  let origin := s.bf0
  let (s, destination) ← putBf s s.you "OGN-276"
  let (s, jhin) ← putAt (s.control p origin) p "UNL-022" origin
  let ready := (s.fund p 0).modObj jhin (fun object => { object with exhausted := false })
  let action : Action := ⟨.player p, .standardMove jhin (.battlefield destination)⟩
  let (moved, _) ← (step 100 ready action).toOption
  return moved.hereOf jhin == some destination && moved.hasKw jhin .deflect &&
    (moved.poolOf p).energy == 1 && (moved.poolOf p).any == 1

-- Poppy checks every opponent at entry, including one later in the FFA turn order.
#guard tun fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .ffa4 }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) initial).toOption
  let p := s.me
  let opponent ← s.pickOrder.getLast?
  let (s, poppy) ← put s p "UNL-116" .hand
  let beyond := s.gainPoints opponent (s.victoryScore - 4)
  let within := beyond.gainPoints opponent 1
  let low ← play beyond p poppy
  let high ← play within p poppy
  let lowId ← low.firstOf p .base "UNL-116"
  let highId ← high.firstOf p .base "UNL-116"
  return opponent != p && low.tired lowId == some true && low.xpOf p == 0 &&
    high.tired highId == some false && high.xpOf p == 3

-- The Attack and Defend rewards are offered when exactly one enemy Unit was present.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, hunter) ← putAt s p "UNL-143" bf
  let (one, _) ← putAt s q "OGN-051" bf
  let (two, _) ← putAt one q "OGN-051" bf
  let detects (board : GameState) (attacker : PlayerId) : Bool :=
    (board.detect [.combatStarted bf attacker]).any (·.source == hunter)
  let resolved ← fire one [.combatStarted bf p]
  return detects one p && detects one q && !detects two p && !detects two q &&
    resolved.xpOf p == one.xpOf p + 2 && resolved.mightNow hunter == (one.mightNow hunter).map (· + 2)

-- A second cheaper Spell cannot borrow the Energy spent on the first one to ready Revna.
#guard tun fun s => do
  let p := s.me
  let costly := testSpell "TEST-COSTLY-SPELL" 4
  let cheap := testSpell "TEST-CHEAP-SPELL" 3
  let board := { s with cards := ⟨s.cards.cards ++ [costly, cheap]⟩ }
  let (s, revna) ← put board p "UNL-005" .base
  let (s, heavy) ← put s p costly.id.code .hand
  let (s, light) ← put s p cheap.id.code .hand
  let s := s.tire revna
  let below ← play s p light
  let ready ← play s p heavy
  let paid ← ready.firstOf p .trash costly.id.code
  let later ← play (ready.tire revna) p light
  return below.tired revna == some true && ready.tired revna == some false &&
    ready.watchedSpellEnergy p paid == some 4 && ready.watchedSpellEnergy s.you paid == none &&
    later.tired revna == some true

-- Forgotten Library checks control and the payment of the resolving Spell.
#guard tun fun s => do
  let p := s.me
  let costly := testSpell "TEST-COSTLY-SPELL" 4
  let cheap := testSpell "TEST-CHEAP-SPELL" 3
  let board := { s with cards := ⟨s.cards.cards ++ [costly, cheap]⟩ }
  let (s, field) ← putBf board s.you "UNL-211"
  let (s, _) ← putAt s p "OGN-049" field
  let (s, heavy) ← put s p costly.id.code .hand
  let (s, light) ← put s p cheap.id.code .hand
  let withoutControl ← play s p heavy
  let choosing ← play (s.control p field) p heavy
  let .predict owner _ first _ _ _ :: _ := choosing.pending | none
  let (kept, _) ← (step 100 choosing ⟨.player p, .predictPick first false⟩).toOption
  let later ← play (settleChain {} 12 kept) p light
  let predicts (t : GameState) : Bool :=
    t.pending.head?.any (fun | .predict .. => true | _ => false)
  return owner == p && !predicts withoutControl && !predicts later

-- Forbidding Waste weakens only a lone defender at its Battlefield.
#guard tun fun s => do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨2⟩
  let teammate : PlayerId := ⟨3⟩
  let board := GameState.empty { s.config with mode := .teamDuel } s.cards
  let (s, field) ← putBf board defender "UNL-210"
  let (s, attacking) ← putAt (s.control defender field) attacker "OGN-049" field
  let (s, defending) ← putAt s defender "OGN-049" field
  let (s, elsewhere) ← put s defender "OGN-049" .base
  let combat := s.inCombatAt field attacker
  let (together, _) ← putAt combat teammate "OGN-049" field
  return s.mightNow defending == some 5 && combat.mightNow defending == some 3 &&
    combat.mightNow attacking == some 5 && combat.mightNow elsewhere == some 5 &&
    together.mightNow defending == some 5

-- Frozen Fortress belongs to its controller even on the opponent's turn. On its controller's
-- turn, lethal damage to the last Unit there prevents that Battlefield's Hold.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, fort) ← putBf s q "UNL-212"
  let (s, unit) ← putAt (s.control p fort) p "RAD-001" fort
  let (s, safe) ← put s p "RAD-001" .base
  let offTurn := { s with active := some q, pending := [.phase .beginning] }
  let (waiting, events) ← (advance 100 offTurn []).toOption
  let item ← (waiting.zone .chain).head?
  let own ← settleBeginning s p
  let openField := s.modObj fort (fun o => { o with control := none })
  return events.contains (.phaseStarted q .beginning) && waiting.inPlay.contains unit &&
    (waiting.obj? item).any (·.controller == p) &&
    waiting.pending.head? == some (.chainPass p 0) &&
    (openField.battlefieldBeginningTriggers q).any (fun t => t.source == fort && t.controller == q) &&
    own.countIn p .trash "RAD-001" == 1 && (own.obj? safe).any (·.damage == 0) &&
    own.pointsOf p == s.pointsOf p && own.controlOf fort == none

-- Simultaneous Battlefield triggers follow turn order in a free-for-all.
#guard tun fun s => do
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let ffa := GameState.empty { s.config with mode := .ffa4 } s.cards
  let (s, first) ← putBf ffa p1 "UNL-212"
  let (s, second) ← putBf s p0 "UNL-212"
  let (s, third) ← putBf s p3 "UNL-212"
  let s := ((s.control p1 first).control p0 second).control p3 third
  let s := { s with active := some p2, turnOrder := [p0, p1, p2, p3] }
  return (s.detect [.phaseStarted p2 .beginning]).map (·.source) == [third, second, first]

-- Dusk Rose Lab pays its cost during finalization. A Temporary Unit is still available while
-- its Beginning trigger waits in the same queue.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, labField) ← putBf s q "UNL-209"
  let (s, unit) ← putAt (s.control p labField) p "RAD-095" labField
  let s := (addTempKw { keyword := .temporary } .never s unit).1
  let (waiting, events) ← (advance 100 { s with pending := [.phase .beginning] } []).toOption
  let choice ← (legalFrameActions waiting).find? fun a =>
    match a.kind with | .putTrigger _ [] (.pay [id] ..) => id == unit | _ => false
  let (paid, paymentEvents) ← (step 100 waiting choice).toOption
  let finished := settleChain {} 24 paid
  return events.contains (.phaseStarted p .beginning) && waiting.inPlay.contains unit &&
    !(s.timedTriggers q .beginning).any (·.source == labField) &&
    !paid.inPlay.contains unit && paymentEvents.any (fun | .died .. => true | _ => false) &&
    !paymentEvents.any (fun | .chosenByAbility .. => true | _ => false) &&
    finished.handN p == s.handN p + 1 && finished.pointsOf p == s.pointsOf p

-- A teammate's Unit at Dusk Rose Lab cannot pay the Lab controller's cost.
#guard tun fun s => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let team := GameState.empty { s.config with mode := .teamDuel } s.cards
  let (s, labField) ← putBf team ally "UNL-209"
  let (s, own) ← putAt (s.control p labField) p "RAD-095" labField
  let (s, _) ← putAt s ally "RAD-095" labField
  let trigger ← (s.timedTriggers p .beginning).find? (·.source == labField)
  return trigPayments s trigger == [[own]]

-- Gust can return a Temporary permanent before its pending ability resolves.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, unit) ← putAt (s.control p s.bf0) p "RAD-001" s.bf0
  let (s, gust) ← put s q "OGN-169" .hand
  let s := (addTempKw { keyword := .temporary } .never s unit).1
  let (waiting, _) ← (advance 100 { s with pending := [.phase .beginning] } []).toOption
  let (response, _) ← (step 100 waiting ⟨.player p, .pass⟩).toOption
  let finished ← play response q gust [unit]
  return finished.countIn p .hand "RAD-001" == 1 && finished.countIn p .trash "RAD-001" == 0 &&
    finished.pointsOf p == s.pointsOf p

-- Honeyfruit enters exhausted. At 6 XP, the two Add abilities are separate choices and
-- share the card's Exhaust cost. The Level ability adds both resources together.
#guard tun fun s => do
  let p := s.me
  let (s, hand) ← put (s.fund p 2) p "UNL-049" .hand
  let (played, _) ← (step 100 s ⟨.player p, .playCard hand ⟨2, []⟩ []⟩).toOption
  let fruit ← played.firstOf p .base "UNL-049"
  let ordinary : Action := ⟨.player p, .manaAbility fruit 1 ⟨0, []⟩⟩
  let level : Action := ⟨.player p, .manaAbility fruit 2 ⟨0, []⟩⟩
  let chained : Action := ⟨.player p, .activate fruit 2 ⟨0, []⟩ []⟩
  let ready := (readyEffect played fruit).1
  let below := ready.setXP p 5
  let atLevel := ready.setXP p 6
  let (plain, _) ← (step 1 below ordinary).toOption
  let (both, events) ← (step 1 atLevel level).toOption
  return played.tired fruit == some true && !(step 100 (played.setXP p 6) level).isOk &&
    !(legalFrameActions below).contains level && !(step 100 below level).isOk &&
    (legalFrameActions atLevel).contains ordinary && (legalFrameActions atLevel).contains level &&
    !(legalFrameActions atLevel).contains chained && !(step 100 atLevel chained).isOk &&
    plain.poolOf p == { any := 1 } && both.poolOf p == { energy := 1, any := 1 } &&
    both.tired fruit == some true && both.xpOf p == 6 &&
    !(step 100 both ordinary).isOk && !(step 100 both level).isOk &&
    both.pending == atLevel.pending && (both.zone .chain).isEmpty &&
    events == [.activated p fruit 2 (some 0)]

-- The Level Add can fund a payment that needs both resources. It also resolves during the
-- Chain and Showdown without putting an item on the Chain or passing priority or Focus.
#guard tun fun s => do
  let p := s.me
  let (s, fruit) ← put s p "UNL-049" .base
  let (s, spell) ← put s p "UNL-103" .hand
  let (s, mover) ← put s p "V0" .base
  let s := (readyEffect (s.fund p 0) fruit).1.setXP p 6
  let payment : RunePool.Payment := ⟨1, [.calm]⟩
  let canPay (state : GameState) := ((state.poolOf p).spend payment).isSome
  let funding : EffectAdd := .ability fruit 2 0 [] none
  let add : Action := ⟨.player p, .manaAbility fruit 2 ⟨0, []⟩⟩
  let (funded, receipts) ← (applyEffectAdds s p [funding])
  let (chain, _) ← (step 100 (s.fund p 2)
    ⟨.player p, .playCard spell ⟨2, []⟩ [] none none (.mode 1)⟩).toOption
  let (showdown, _) ← (step 100 s ⟨.player p, .standardMove mover (.battlefield s.bf0)⟩).toOption
  let works (waiting : GameState) : Bool := (step 0 waiting add).toOption.any fun (done, events) =>
    done.pending == waiting.pending && done.zone .chain == waiting.zone .chain &&
    done.poolOf p == { energy := 1, any := 1 } &&
    events == [.activated p fruit 2 (some 0)]
  return effectAddChoices s p canPay == [funding] && effectAddPowerBudget s p == 6 &&
    canPay funded && receipts == [.activated p fruit 2 (some 0)] &&
    funded.tired fruit == some true && works chain && works showdown

-- Only sequences of fixed unrestricted gains have the new immediate timing.
#guard
  let energy := Effect.prim (.addEnergy .you (.const 2) none)
  let power := Effect.prim (.addPower .you (.const 1) (some .body) none)
  let gains := Effect.seqOf [power, .seqOf [energy, power]]
  let modal : EffectDef := { body := gains, modes := [⟨"Draw", [], .prim (.draw .you (.const 1)), none⟩] }
  (manaKind (.of [] gains)).any (fun kind =>
    kind.add {} ⟨0, []⟩ == { energy := 2, body := 2 }) &&
    (manaKind (.of [] (.seqOf [energy, .prim (.draw .you (.const 1))]))).isNone &&
    (manaKind modal).isNone

-- Fresh Beans asks on finalization for a Unit or Unit token played during a Showdown.
#guard tun fun s => do
  let (s, beans) ← put s s.me "UNL-011" .base
  let (s, unit) ← put s s.me "OGN-051" .base
  let openBoard ← fire s [.played s.me unit]
  let showdown := { s with pending := [.showdown s.bf0 s.me 0] }
  let chosen ← fire showdown [.played s.me unit]
  let skipped ← fire showdown [.played s.me unit] { yes := false }
  let (withToken, events) := playUnitTokenAt showdown s.me "Recruit" none
  let withDraw ← fire withToken events
  return openBoard.tired beans == some false && chosen.tired beans == some true &&
    chosen.handN s.me == s.handN s.me + 1 && skipped.tired beans == some false &&
    skipped.handN s.me == s.handN s.me && withDraw.tired beans == some true &&
    withDraw.handN s.me == s.handN s.me + 1

-- Inferna (UNL-002): Ambush: it can be played as a Reaction to a Battlefield where its player has
-- units, and not to the Base or to a Battlefield without units of that player
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "OGN-051" bf
  let (s3, other) ← putBf s2 s.me "OGN-276"
  let (s4, c) ← put s3 s.me "UNL-002" .hand
  let (s5, _) ← onChain s4 s.you "OGN-004"
  let rich := s5.rich s.me
  let pay := payOf rich c
  return reactable rich s.me c pay [bf] && !reactable rich s.me c pay [other] &&
    !reactable rich s.me c pay [] && playable rich s.me c pay (some bf) &&
    !playable rich s.me c pay (some other)

-- Mischievous Marai (UNL-003): when played to a battlefield (an open one, with Miss Fortune in
-- play), 2 damage to an enemy unit there
#guard tun fun s => do
  let (s0, _) ← put s s.me "OGN-193" .base
  let (s1, c) ← put s0 s.me "UNL-003" .hand
  let (s2, e) ← putAt s1 s.you "OGN-088" s.bf0
  let toBf ← play s2 s.me c [s.bf0] { pick := fun ts => ts == [e] }
  let toBase ← play s2 s.me c [] { pick := fun ts => ts == [e] }
  return (toBf.obj? e).any (·.damage == 2) && (toBase.obj? e).any (·.damage == 0)

/-- The place of the first activated ability of the card. -/
meta def firstAct (s : GameState) (u : ObjId) : Nat :=
  ((s.cardDef? u).map (fun d => d.fullAbilities.findIdx (fun a =>
    match a with | Ability.activated .. => true | _ => false))).getD 0

-- Smite (UNL-007): the unit it kills is banished, not put in the Trash
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-007" .hand
  let (s2, e) ← putAt s1 s.you "UNL-111" s.bf0
  let s3 ← play s2 s.me c [e]
  return s3.countIn s.you .banishment "UNL-111" == 1 && s3.countIn s.you .trash "UNL-111" == 0

-- Lotus Trap (UNL-013): the damage dealt to the unit this turn is doubled
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-013" .hand
  let (s2, e) ← putAt s1 s.you "OGN-088" s.bf0
  let s3 ← play s2 s.me c [e]
  return ((dealObj 1 s3 e).1.obj? e).any (·.damage == 2) &&
    ((dealObj 1 s2 e).1.obj? e).any (·.damage == 1)

-- Scryer's Bloom (UNL-136) enters exhausted
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-136" .hand
  let s2 ← play s1 s.me c
  let g ← s2.firstOf s.me .base "UNL-136"
  return s2.tired g == some true

-- Bloom pays Kill and Exhaust during finalization. Predict is private, and
-- choosing the kept cards in reverse order changes which card is drawn.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, bloom) ← put s p "UNL-136" .base
  let deck := Zone.player p .mainDeck
  let cards := s.zone deck
  let first ← cards[0]?
  let second ← cards[1]?
  let third ← cards[2]?
  let index := firstAct s bloom
  let action : Action := ⟨.player p, .activate bloom index ⟨1, []⟩ []⟩
  let spent := s.fund p 1
  let (used, events) ← (step 100 spent action).toOption
  let item ← (used.zone .chain).head?
  let destroyed ← used.firstOf p .trash "UNL-136"
  let countered := (counterObj used item).1
  let (passed, _) ← (step 100 used ⟨.player p, .pass⟩).toOption
  let .chainPass _ _ :: rest := passed.pending | none
  let ((predicting, looked), disclosures) ← (stepWithDisclosures 100 passed ⟨.player q, .pass⟩).toOption
  let keep (id : ObjId) : Action := ⟨.player p, .predictPick id false⟩
  let recycle (id : ObjId) : Action := ⟨.player p, .predictPick id true⟩
  let arrange : Action := ⟨.chance, .arrange [second, first]⟩
  let (keepSecond, _) ← (step 100 predicting (keep second)).toOption
  let (kept, draws) ← (step 100 keepSecond (keep first)).toOption
  let (recycleFirst, _) ← (step 100 predicting (recycle first)).toOption
  let (shuffling, _) ← (step 100 recycleFirst (recycle second)).toOption
  let (recycled, afterShuffle) ← (step 100 shuffling arrange).toOption
  let drew (es : List Event) (id : ObjId) := es.any (fun
    | .moved old _ (.player player .hand) => old == id && player == p
    | _ => false)
  return (legalFrameActions spent).contains action &&
    !(legalFrameActions (spent.tire bloom)).contains action &&
    !(legalFrameActions (s.fund p 0)).contains action &&
    (used.obj? bloom).isNone && used.countIn p .trash "UNL-136" == 1 &&
    events.contains (.moved bloom destroyed (.player p .trash)) &&
    events.contains (.died destroyed p) &&
    (used.poolOf p).energy == 0 && used.xpOf p == s.xpOf p &&
    countered.countIn p .trash "UNL-136" == 1 && countered.handN p == s.handN p &&
    chainPassWorkSupported passed q rest && predictAnswerWaits predicting (keep second) &&
    chainAnswerWorkSupported keepSecond (keep first) && predictAnswerWaits predicting (recycle first) &&
    predictAnswerWaits recycleFirst (recycle second) && chainAnswerWorkSupported shuffling arrange &&
    looked == [Event.lookedAt p first, Event.lookedAt p second] &&
    disclosures.length == 2 && disclosures.all (fun d => d.visibleTo p && !d.visibleTo q) &&
    drew draws second && (kept.zone deck).head? == some first && kept.xpOf p == s.xpOf p + 1 &&
    shuffling.handN p == s.handN p && shuffling.xpOf p == s.xpOf p &&
    (step 100 shuffling ⟨.chance, .arrange [first, first]⟩).toOption.isNone &&
    drew afterShuffle third && (recycled.zone deck).reverse.take 2 == [first, second] &&
    recycled.handN p == s.handN p + 1 && recycled.xpOf p == s.xpOf p + 1

-- Dramatic Visionary's Deathknell presents the same private two-card decision.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, unit) ← put s p "UNL-062" .base
  let deck := Zone.player p .mainDeck
  let first ← (s.zone deck)[0]?
  let second ← (s.zone deck)[1]?
  let (dead, events) := killOrSave s unit
  let predicting ← fire dead events
  let (keepSecond, _) ← (step 100 predicting ⟨.player p, .predictPick second false⟩).toOption
  let (done, _) ← (step 100 keepSecond ⟨.player p, .predictPick first false⟩).toOption
  return (predicting.resolutionZoneCardFaces p deck).any (fun faces =>
    (faces.take 2).all Option.isSome) &&
    predicting.zoneView q deck == dead.zoneView q deck &&
    predicting.countIn p .trash "UNL-062" == 1 && done.handN p == s.handN p &&
    (done.zone deck).take 2 == [second, first]

-- Hunt gains XP on the battlefield. The buff costs XP as soon as it is activated.
private meta def huntBuffCostsXP (code : String) : Bool := tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, unit) ← putAt (s.control p bf) p code bf
  let s := (s.setXP p 0).setXP q 3
  let scored ← fire s [.scored p bf true]
  let below := s.setXP p (scored.xpOf p)
  let exact := s.setXP p 2
  let action : Action := ⟨.player p, .activate unit 0 ⟨0, []⟩ []⟩
  let (queued, _) ← (step 100 exact action).toOption
  let item ← (queued.zone .chain).head?
  let resolved := settleChain {} 12 queued
  let countered := settleChain {} 12 (counterObj queued item).1
  return scored.xpOf p == 1 && !((legalFrameActions below).contains action) &&
    !(step 100 below action).isOk && (legalFrameActions exact).contains action &&
    queued.xpOf p == 0 && queued.xpOf q == 3 && !(queued.obj? unit).any (·.buffed) &&
    resolved.xpOf p == 0 && (resolved.obj? unit).any (·.buffed) &&
    countered.xpOf p == 0 && !(countered.obj? unit).any (·.buffed)

#guard huntBuffCostsXP "UNL-102"
#guard huntBuffCostsXP "UNL-162"

-- Blood Rose pays Energy at trigger finalization and chooses the Unit when activating Ready.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, rose) ← put (s.fund p 1) p "UNL-109" .base
  let (s, unit) ← put s p "OGN-049" .base
  let (s, opponent) ← put s q "OGN-049" .base
  let s := (setExhausted true s opponent).1.setXP p 2
  let triggers := s.detect [.played p unit]
  let (offered, _) ← (advance 100 { s with pending := insertTriggers triggers s.pending } []).toOption
  let buy : Action := ⟨.player p, .putTrigger 0 [] (.pay [])⟩
  let skip : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (bought, _) ← (step 100 offered buy).toOption
  let (skipped, _) ← (step 100 offered skip).toOption
  let funded := settleChain {} 12 bought
  let ready : Action := ⟨.player p, .activate rose 1 ⟨0, []⟩ [opponent]⟩
  let (queued, _) ← (step 100 funded ready).toOption
  let resolved := settleChain {} 12 queued
  return triggers.length == 1 && (s.detect [.played q opponent]).isEmpty &&
    bought.xpOf p == 2 && (bought.poolOf p).energy == 0 && !(bought.zone .chain).isEmpty &&
    skipped.xpOf p == 2 && (skipped.poolOf p).energy == 1 && (skipped.zone .chain).isEmpty &&
    funded.xpOf p == 3 && !(step 100 s ready).isOk && queued.xpOf p == 0 &&
    queued.tired rose == some true && queued.tired opponent == some true &&
    resolved.tired rose == some true && resolved.tired opponent == some false

-- Kha'Zix chooses an enemy at its battlefield and pays XP when finalizing the attack trigger.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, hunter) ← putAt (s.control q bf) p "UNL-119" bf
  let (s, victim) ← putAt s q "UNL-179" bf
  let (s, distant) ← put s q "UNL-179" .base
  let s := (s.setXP p 3).setXP q 5
  let event := Event.combatStarted bf p
  let offer (state : GameState) :=
    let pending := insertTriggers (state.detect [event]) state.pending
    (advance 100 { state with pending } []).toOption
  let (offered, _) ← offer s
  let (below, _) ← offer (s.setXP p 2)
  let choose (id : ObjId) : Action := ⟨.player p, .putTrigger 0 [id] (.pay [])⟩
  let skip : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (queued, _) ← (step 100 offered (choose victim)).toOption
  let (skipped, _) ← (step 100 offered skip).toOption
  let item ← (queued.zone .chain).head?
  let boosted := settleChain {} 12 (buffObj queued hunter).1
  let gone := settleChain {} 12 (moveHome queued victim).1
  let countered := settleChain {} 12 (counterObj queued item).1
  return (legalFrameActions offered).contains (choose victim) &&
    !(step 100 below (choose victim)).isOk && !(step 100 offered (choose distant)).isOk &&
    queued.xpOf p == 0 && queued.xpOf q == 5 && (queued.obj? victim).any (·.damage == 0) &&
    skipped.xpOf p == 3 && (skipped.zone .chain).isEmpty &&
    (boosted.obj? victim).any (·.damage == 6) && gone.xpOf p == 0 &&
    (gone.obj? victim).any (·.damage == 0) && countered.xpOf p == 0 &&
    (countered.obj? victim).any (·.damage == 0)

-- The Archer and Poro both pay Energy before responding to an attack trigger. Only the Poro
-- restricts the choice to an enemy, and that Unit must still be here when the ability resolves.
private meta def paidAttackTarget (code : String) (mustBeEnemy : Bool) : Bool := tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, attacker) ← putAt (s.control q bf) p code bf
  let (s, target) ← putAt (s.fund p 1) q "OGN-049" bf
  let (s, remote) ← put s q "OGN-049" .base
  let pending := insertTriggers (s.detect [.combatStarted bf p]) s.pending
  let (offered, _) ← (advance 100 { s with pending } []).toOption
  let choose (id : ObjId) : Action := ⟨.player p, .putTrigger 0 [id] (.pay [])⟩
  let (queued, _) ← (step 100 offered (choose target)).toOption
  let (skipped, _) ← (step 100 offered ⟨.player p, .putTrigger 0 [] .skip⟩).toOption
  let done := settleChain {} 12 queued
  let out := settleChain {} 12 (moveHome queued target).1
  let fieldOf (state : GameState) := (state.obj? target).bind (·.loc)
  let reduced := done.mightNow target == some 4 && fieldOf done == some bf
  let moved := done.where? target == some (.player q .base) && done.mightNow target == some 5
  return (step 100 offered (choose attacker)).isOk == !mustBeEnemy &&
    !(step 100 offered (choose remote)).isOk && (queued.poolOf p).energy == 0 &&
    queued.mightNow target == some 5 && fieldOf queued == some bf &&
    (skipped.poolOf p).energy == 1 && (skipped.zone .chain).isEmpty &&
    out.mightNow target == some 5 && out.where? target == some (.player q .base) &&
    (if mustBeEnemy then moved else reduced)

#guard paidAttackTarget "UNL-065" false
#guard paidAttackTarget "UNL-137" true

-- Insightful Investigator reveals the chosen opponent's hand before asking whether to spend XP.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let mode := { s.config.mode with players := 3 }
  let s := { s with config := { s.config with mode }, turnOrder := [p, q, third] }
  let (s, investigator) ← put (s.fund p 3) p "UNL-135" .hand
  let (s, wrong) ← put s q "OGN-049" .hand
  let (s, discarded) ← put s third "OGN-088" .hand
  let (s, _) ← put s third "OGN-049" .hand
  let (s, drawn) ← put s third "OGN-095" .mainDeck
  let choose (seat : PlayerId) : Action := ⟨.player p, .putTrigger 0 [] (.pay [] none (some seat))⟩
  let rec pass : Nat → GameState → List Event → Option (GameState × List Event)
    | 0, _, _ => none
    | n + 1, state, events => do
      match state.pending with
      | .chainPass seat _ :: _ =>
        let (next, more) ← (step 100 state ⟨.player seat, .pass⟩).toOption
        pass n next (events ++ more)
      | _ => some (state, events)
  let openAbility (xp : Nat) : Option (GameState × GameState × List Event) := do
    let (offered, _) ← (step 100 (s.setXP p xp)
      ⟨.player p, .playCard investigator ⟨3, []⟩ []⟩).toOption
    let (queued, _) ← (step 100 offered (choose third)).toOption
    let (ready, events) ← pass 8 queued []
    pure (offered, ready, events)
  let (offered, choice, revealed) ← openAbility 2
  let (_, short, shortReveals) ← openAbility 1
  let pay : Action := ⟨.player p, .decide true⟩
  let (paid, _) ← (step 100 choice pay).toOption
  let (declined, _) ← (step 100 choice ⟨.player p, .decide false⟩).toOption
  let take (id : ObjId) : Action := ⟨.player p, .choose id⟩
  let (done, events) ← (step 100 paid (take discarded)).toOption
  let revealedHand := Event.handRevealed third (s.zone (.player third .hand))
  return (legalFrameActions offered).contains (choose q) && !(step 100 offered (choose p)).isOk &&
    revealed == [revealedHand] && shortReveals == [revealedHand] && !(step 100 short pay).isOk &&
    choice.xpOf p == 2 && paid.xpOf p == 0 && declined.xpOf p == 2 &&
    !(step 100 paid (take wrong)).isOk && paid.zone (.player third .hand) == s.zone (.player third .hand) &&
    declined.zone (.player third .hand) == s.zone (.player third .hand) &&
    done.zone (.player q .hand) == s.zone (.player q .hand) && done.handN third == s.handN third &&
    done.countIn third .trash "OGN-088" == 1 && !(done.zone (.player third .mainDeck)).contains drawn &&
    events.contains (.drew third) && !(events.contains (.drew q))

-- Scuttle Crab draws one card when played.
#guard tun fun s => do
  let p := s.me
  let (s, crab) ← put s p "UNL-053" .hand
  let played ← play s p crab
  let deck := Zone.player p .mainDeck
  return played.countIn p .base "UNL-053" == 1 && played.handN p == s.handN p &&
    (played.zone deck).length + 1 == (s.zone deck).length

-- Scuttle Crab reveals one opponent's hand publicly, then gives only its controller
-- permission to inspect that opponent's facedown cards for the current turn.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let other : PlayerId := ⟨3⟩
  let hand := Zone.player enemy .hand
  let hidden := Zone.player enemy .hidden
  let elsewhere := Zone.player other .hidden
  let (s, crab) ← put (unleashedTeamMain labState) p "UNL-053" .base
  let (s, enemyField) ← putBf s enemy "OGN-275"
  let (s, otherField) ← putBf s other "OGN-276"
  let (s, handCard) ← put s enemy "OGN-058" .hand
  let (s, first) ← put s enemy "SFD-004" .hidden
  let (s, second) ← put s other "OGN-094" .hidden
  let placed := ((s.control enemy enemyField).control other otherField)
    |>.modObj first (fun o => { o with hiddenAt := some enemyField })
    |>.modObj second (fun o => { o with hiddenAt := some otherField })
  let (dead, death) := killObj placed crab
  let (offered, _) ← (advance 100 (dead.withTriggers death) []).toOption
  let choose (seat : PlayerId) : Action := ⟨.player p, .putTrigger 0 [] (.pay [] none (some seat))⟩
  let (queued, _) ← (step 100 offered (choose enemy)).toOption
  let rec pass : Nat → GameState → List Event → Option (GameState × List Event)
    | 0, _, _ => none
    | n + 1, state, events => do
      match state.pending with
      | .chainPass seat _ :: _ =>
        let (next, more) ← (step 100 state ⟨.player seat, .pass⟩).toOption
        pass n next (events ++ more)
      | _ => some (state, events)
  let (done, events) ← pass 8 queued []
  let expired := { done with turn := done.turn + 1 }
  let (unhidden, _) ← moveObj done first hand
  let (newlyHidden, replacement) ← moveObj unhidden handCard hidden
  let during := newlyHidden.modObj replacement (fun o => { o with hiddenAt := some enemyField })
  return (legalFrameActions offered).contains (choose other) &&
    !(step 100 offered (choose p)).isOk && !(step 100 offered (choose mate)).isOk &&
    events == [.handRevealed enemy [handCard]] && done.xpOf p == placed.xpOf p + 1 &&
    done.resolutionZoneCardFaces p hidden == some [some (cid "SFD-004")] &&
    done.resolutionZoneCardFaces mate hidden == some [none] &&
    done.resolutionZoneCardFaces other hidden == some [none] &&
    done.resolutionZoneCardFaces p elsewhere == some [none] &&
    done.resolutionZoneCardFaces p hand == some [none] &&
    during.resolutionZoneCardFaces p hidden == some [some (cid "OGN-058")] &&
    expired.resolutionZoneCardFaces p hidden == some [none]

-- Megatusk grants Ganking to its controller's units at its location for the current turn.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, tusk) ← putAt (s.control p bf) p "UNL-126" bf
  let (s, nearby) ← putAt s p "OGN-049" bf
  let (s, other) ← putAt s q "OGN-049" bf
  let (s, distant) ← put s p "OGN-049" .base
  let (s, homeTusk) ← put s p "UNL-126" .base
  let action : Action := ⟨.player p, .activate tusk 0 ⟨0, []⟩ []⟩
  let (queued, _) ← (step 100 (s.setXP p 3) action).toOption
  let granted := settleChain {} 12 queued
  let atHome ← activate (s.setXP p 3) p homeTusk 0
  let (expired, _) ← (advance 100 { granted with pending := [.expireTurn, .priority p] } []).toOption
  return !(step 100 (s.setXP p 2) action).isOk && queued.xpOf p == 0 &&
    !queued.hasKw nearby .ganking && granted.hasKw tusk .ganking && granted.hasKw nearby .ganking &&
    !granted.hasKw distant .ganking && !granted.hasKw other .ganking &&
    atHome.hasKw homeTusk .ganking && atHome.hasKw distant .ganking && !atHome.hasKw nearby .ganking &&
    !expired.hasKw nearby .ganking

-- Voidreaver's abilities spend XP and exhaust immediately. The move requires an exhausted
-- friendly Unit on a battlefield, while the buff can target an opponent's Unit.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, legend) ← put (s.control p bf) p "UNL-201" .legendZone
  let (s, tired) ← putAt s p "OGN-049" bf
  let (s, stillReady) ← putAt s p "OGN-088" bf
  let (s, opponent) ← put s q "OGN-049" .base
  let s := (setExhausted true s tired).1.setXP p 0
  let won ← fire s [.combatWon bf p]
  let exact := s.setXP p 2
  let buff : Action := ⟨.player p, .activate legend 1 ⟨0, []⟩ [opponent]⟩
  let move (target : ObjId) : Action := ⟨.player p, .activate legend 2 ⟨0, []⟩ [target]⟩
  let (buffing, _) ← (step 100 (s.setXP p (won.xpOf p)) buff).toOption
  let (moving, _) ← (step 100 exact (move tired)).toOption
  let buffed := settleChain {} 12 buffing
  let moved := settleChain {} 12 moving
  let readied := settleChain {} 12 (readyEffect moving tired).1
  return won.xpOf p == 1 && buffing.xpOf p == 0 && buffing.tired legend == some true &&
    !(buffing.obj? opponent).any (·.buffed) && (buffed.obj? opponent).any (·.buffed) &&
    !(step 100 (s.setXP p 1) (move tired)).isOk && !(step 100 exact (move stillReady)).isOk &&
    moving.xpOf p == 0 && moving.tired legend == some true &&
    moved.where? tired == some (.player p .base) && readied.where? tired == some .battlefieldZone &&
    (readied.obj? tired).any (·.loc == some bf)

-- Keeper of the Hammer gains XP on Hold and draws after paying both activation costs.
#guard tun fun s => do
  let p := s.me
  let bf := s.bf0
  let (s, legend) ← put (s.control p bf) p "UNL-203" .legendZone
  let s := s.setXP p 2
  let held ← fire s [.scored p bf false]
  let conquered ← fire s [.scored p bf true]
  let draw : Action := ⟨.player p, .activate legend 1 ⟨0, []⟩ []⟩
  let (queued, _) ← (step 100 (s.setXP p (held.xpOf p)) draw).toOption
  let resolved := settleChain {} 12 queued
  return held.xpOf p == 3 && conquered.xpOf p == 2 && !(step 100 s draw).isOk &&
    queued.xpOf p == 0 && queued.tired legend == some true && queued.handN p == s.handN p &&
    resolved.handN p == s.handN p + 1

-- Disposal Order declares one mode and a set of at most three opponent Trash cards.
-- A chance answer can change the order of that group but cannot add, omit or duplicate a card.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, order) ← put s p "UNL-103" .hand
  let (s, own) ← put s p "UNL-111" .trash
  let (s, first) ← put s q "UNL-111" .trash
  let (s, second) ← put s q "OGN-010" .trash
  let (s, left) ← put s q "VEN-074" .trash
  let (s, fourth) ← put s q "VEN-007" .trash
  let s := s.fund p 2
  let deck := Zone.player q .mainDeck
  let start := s.zone deck
  let action (targets : List ObjId) (mode : SpellPick) : Action :=
    ⟨.player p, .playCard order ⟨2, []⟩ targets none none mode⟩
  let legal := legalFrameActions s
  let chosen := action [first, second] (.mode 0)
  let (queued, events) ← (step 100 s chosen).toOption
  let (passed, _) ← (step 100 queued ⟨.player p, .pass⟩).toOption
  let ((random, _), disclosures) ← (stepWithDisclosures 100 passed ⟨.player q, .pass⟩).toOption
  let .chanceRecycleTrash owner _ cards :: _ := random.pending | none
  let orderAnswer : Action := ⟨.chance, .arrange [second, first]⟩
  let (done, moves) ← (step 100 random orderAnswer).toOption
  let topBefore := (done.zone deck).take start.length
  let bottomCodes := ((done.zone deck).drop start.length).map (fun id => (done.cardDef? id).map (·.id))
  let draw ← cast s p order ⟨2, []⟩ [] {} (.mode 1)
  return chainAnswerWorkSupported random orderAnswer && legal.contains chosen && legal.contains (action [] (.mode 0)) &&
    legal.contains (action [first, second, left] (.mode 0)) &&
    !legal.contains (action [first, second, left, fourth] (.mode 0)) &&
    !legal.contains (action [first, first] (.mode 0)) && !legal.contains (action [own] (.mode 0)) &&
    !legal.contains (action [first] (.mode 1)) && !legal.contains (action [] .plain) &&
    events.contains (.chosenBySpell p first) && events.contains (.chosenBySpell p second) &&
    random.zone deck == start && disclosures.isEmpty && owner == p && cards == [first, second] &&
    !(step 100 random ⟨.player q, .arrange [second, first]⟩).isOk &&
    !(step 100 random ⟨.chance, .arrange [first, first]⟩).isOk &&
    !(step 100 random ⟨.chance, .arrange [first, left]⟩).isOk &&
    !(step 100 random ⟨.chance, .arrange [first]⟩).isOk &&
    topBefore == start && bottomCodes == [some (cid "OGN-010"), some (cid "UNL-111")] &&
    moves.contains (.recycled q) && !moves.contains (.recycled p) &&
    (done.zone (.player q .trash)).contains left && draw.handN p == s.handN p

-- A card that leaves the Trash during a response stays out of the group. The single remaining
-- target goes to the bottom without asking for an order.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, order) ← put s p "UNL-103" .hand
  let (s, first) ← put s q "UNL-111" .trash
  let (s, second) ← put s q "OGN-010" .trash
  let s := s.fund p 2
  let action : Action := ⟨.player p, .playCard order ⟨2, []⟩ [first, second] none none (.mode 0)⟩
  let (queued, _) ← (step 100 s action).toOption
  let (changed, returned) ← moveObj queued second (.player q .hand)
  let (done, _) ← (step 100 (← (step 100 changed ⟨.player p, .pass⟩).toOption).1
    ⟨.player q, .pass⟩).toOption
  let top := s.zone (.player q .mainDeck)
  let last ← (done.zone (.player q .mainDeck)).getLast?
  return (done.zone (.player q .mainDeck)).length == top.length + 1 &&
    (done.cardDef? last).any (·.id == cid "UNL-111") &&
    (done.zone (.player q .hand)).contains returned &&
    done.pending.all (fun | .chanceRecycleTrash .. => false | _ => true)

-- In 2v2, cards can be taken from both opponents. Each goes to its own deck,
-- and the teammate's Trash cannot be targeted.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let q : PlayerId := ⟨2⟩
  let r : PlayerId := ⟨3⟩
  let empty := GameState.empty { ruleSet := .coreOnly, mode := .teamDuel } labState.cards
  let s := { empty with
    phase := .main, turn := 2, active := some p,
    pending := [.priority p], turnOrder := Mode.teamTurnOrder true }
  let (s, spell) ← put s p "UNL-103" .hand
  let (s, friend) ← put s ally "VEN-007" .trash
  let (s, first) ← put s q "VEN-007" .trash
  let (s, second) ← put s r "UNL-111" .trash
  let (s, third) ← put s q "OGN-010" .trash
  let s := s.fund p 2
  let picked (cards : List ObjId) : Action := ⟨.player p, .playCard spell ⟨2, []⟩ cards
    none none (.mode 0)⟩
  let (queued, _) ← (step 100 s (picked [first, second, third])).toOption
  let waiting := settleChain {} 12 queued
  let .chanceRecycleTrash _ _ cards :: _ := waiting.pending | none
  let (done, moved) ← (step 100 waiting ⟨.chance, .arrange [third, second, first]⟩).toOption
  let cardCodes (seat : PlayerId) := (done.zone (.player seat .mainDeck)).filterMap
    (fun id => (done.cardDef? id).map (·.id))
  return cards == [first, second, third] &&
    !(legalFrameActions s).contains (picked [friend]) &&
    (done.zone (.player ally .trash)).contains friend &&
    cardCodes q == [cid "OGN-010", cid "VEN-007"] &&
    cardCodes r == [cid "UNL-111"] &&
    (moved.filter (fun | .recycled _ => true | _ => false)) == [.recycled q, .recycled r]

-- If Runes are among the targets, their owner sets the order of the Rune Deck.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "UNL-103" .hand
  let (s, fury) ← put s q "OGN-007" .trash
  let (s, body) ← put s q "OGN-126" .trash
  let s := s.fund p 2
  let casted ← cast s p spell ⟨2, []⟩ [fury, body] { obj := (· == body) } (.mode 0)
  let deck := casted.zone (.player q .runeDeck)
  let tail := (deck.drop ((s.zone (.player q .runeDeck)).length)).filterMap
    (fun id => (casted.cardDef? id).map (·.id))
  return (casted.zone (.player q .mainDeck)) == s.zone (.player q .mainDeck) &&
    tail == [cid "OGN-126", cid "OGN-007"]

-- Crowd Favorite gets the printed Hunt XP for either kind of scoring.
#guard tun fun s => do
  let p := s.me
  let (s, _) ← putAt s p "UNL-102" s.bf0
  let held ← fire s [.scored p s.bf0 false]
  let conquered ← fire s [.scored p s.bf0 true]
  return held.xpOf p == s.xpOf p + 1 && conquered.xpOf p == s.xpOf p + 1 &&
    held.xpOf s.you == s.xpOf s.you && conquered.xpOf s.you == s.xpOf s.you

-- Vex offers the optional trigger for her controller's Stun and remembers its Battlefield.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let foe : PlayerId := ⟨2⟩
  let (s, field) ← putBf (unleashedTeamMain labState) foe "OGN-275"
  let (s, vex) ← put s p "UNL-055" .base
  let (s, enemy) ← putAt (s.control foe field) foe "OGN-136" field
  let (s, homeEnemy) ← put s foe "OGN-136" .base
  let applyStun (state : GameState) (seat : PlayerId) (unit : ObjId) :=
    applyPrim state seat vex { slots := [.obj unit] } (.stun (.slot 0))
  let (stunned, events) ← applyStun s p enemy
  let (allied, allyEvents) ← applyStun s mate enemy
  let (atHome, homeEvents) ← applyStun s p homeEnemy
  let (still, repeated) ← applyStun stunned p enemy
  let [trigger] := stunned.detect events | none
  let departed := (moveByEffect foe none (stunned.withTriggers events) enemy).1
  let (offered, _) ← (advance 100 departed []).toOption
  let accept : Action := ⟨.player p, .putTrigger 0 [] (.pay [])⟩
  let decline : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (queued, _) ← (step 100 offered accept).toOption
  let (skipped, _) ← (step 100 offered decline).toOption
  let moved := settleChain {} 16 queued
  return events == [.stunnedBy enemy p] && trigger.source == vex &&
    trigger.eventBattlefields == some [field] && (allied.detect allyEvents).isEmpty &&
    (atHome.detect homeEvents).isEmpty && repeated.isEmpty && still.hereOf enemy == some field &&
    (legalFrameActions offered).contains accept && (legalFrameActions offered).contains decline &&
    moved.hereOf vex == some field && moved.hereOf enemy == none &&
    skipped.hereOf vex == none && moved.hasKw vex .tank && moved.kwAmount vex .shield == 1

-- Yuumi's combat trigger chooses another Unit of her own controller at that Battlefield.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let teammate : PlayerId := ⟨1⟩
  let q : PlayerId := ⟨2⟩
  let (s, bf) ← putBf (unleashedTeamMain labState) p "OGN-275"
  let (s, yuumi) ← putAt s p "UNL-056" bf
  let (s, guest) ← putAt s teammate "OGN-051" bf
  let (s, foe) ← putAt s q "OGN-051" bf
  let (s, elsewhere) ← put s p "OGN-051" .base
  let (s, own) ← putAt s p "OGN-051" bf
  let offered (active : PlayerId) : Option GameState := do
    let state := s.inCombatAt bf active
    let state := { state with pending := .triggers (state.detect [.combatStarted bf active]) :: state.pending }
    return (← (advance 100 state []).toOption).1
  let check (attacker : PlayerId) : Option Bool := do
    let waiting ← offered attacker
    let targets := (legalFrameActions waiting).filterMap (fun a => match a.kind with
      | .putTrigger _ ids (.pay ..) => some ids
      | _ => none)
    let done := settleChain {} 16 waiting
    let (expired, _) ← microStep { done with pending := [.expireTurn] }
    return targets == [[own]] && done.mightNow own == some (5 : Int) && done.hasKw own .tank &&
      [yuumi, guest, foe, elsewhere].all (fun id => !done.hasKw id .tank) &&
      expired.mightNow own == some (2 : Int) && !expired.hasKw own .tank
  return (← check p) && (← check q)

-- Lillia grants Tank to its controller's Unit tokens and gains Might from that seat's token plays.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let teammate : PlayerId := ⟨1⟩
  let q : PlayerId := ⟨2⟩
  let (s, lillia) ← put (unleashedTeamMain labState) p "UNL-058" .base
  let (s, ordinary) ← put s p "OGN-051" .base
  let (s, ownEvent) := playUnitTokenAt s p "Recruit" none
  let (s, otherEvent) := playUnitTokenAt s teammate "Recruit" none
  let (s, enemyEvent) := playUnitTokenAt s q "Recruit" none
  let [.tokenPlayed _ own] := ownEvent | none
  let [.tokenPlayed _ guest] := otherEvent | none
  let [.tokenPlayed _ foe] := enemyEvent | none
  let done ← fire s (ownEvent ++ otherEvent ++ enemyEvent ++ [.played p ordinary])
  let (after, extra) := playUnitTokenAt done p "Recruit" none
  let twice ← fire after extra
  let (expired, _) ← microStep { twice with pending := [.expireTurn] }
  return done.hasKw own .tank && [guest, foe, ordinary].all (fun id => !done.hasKw id .tank) &&
    done.mightNow lillia == some (5 : Int) && twice.mightNow lillia == some (6 : Int) &&
    expired.mightNow lillia == some (4 : Int) && expired.hasKw own .tank

-- Master Yi uses the highest eligible cost reduction, and only the controller's XP matters.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, yi) ← put s p "UNL-059" .hand
  let (s, boardYi) ← put s p "UNL-059" .base
  let cost := fun xp => payOf (s.setXP p xp) yi
  let funded := (s.setXP p 11).fund p 6
  let (entered, _) ← (step 100 funded ⟨.player p, .playCard yi ⟨6, []⟩ []⟩).toOption
  return [0, 2, 3, 5, 6, 10, 11, 16].map cost ==
      [⟨12, [.calm, .calm, .calm]⟩, ⟨12, [.calm, .calm, .calm]⟩,
       ⟨10, [.calm, .calm]⟩, ⟨10, [.calm, .calm]⟩,
       ⟨8, [.calm]⟩, ⟨8, [.calm]⟩, ⟨6, []⟩, ⟨6, []⟩] &&
    entered.countIn p .base "UNL-059" == 2 && (entered.poolOf p).energy == 0 &&
    payOf (s.setXP q 16) yi == ⟨12, [.calm, .calm, .calm]⟩ &&
    !(s.setXP p 15).blocksChoice q boardYi && (s.setXP p 16).blocksChoice q boardYi &&
    !(s.setXP p 16).blocksChoice p boardYi

-- Downstage Dramatics can respond to an enemy item and draws a second card only with Repeat.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, older) ← onChain s q "OGN-129"
  let (s, spell) ← put s p "UNL-061" .hand
  let opened := { (s.fund p 4) with active := some q, pending := [.chainPass p 0, .priority q] }
  let castFor (energy draws : Nat) : Option Bool := do
    let a : Action := ⟨.player p, .playCard spell ⟨energy, []⟩ []⟩
    let (casted, _) ← (step 100 opened a).toOption
    let (response, _) ← (step 100 casted ⟨.player p, .pass⟩).toOption
    let (done, events) ← (step 100 response ⟨.player q, .pass⟩).toOption
    return a ∈ legalFrameActions opened && done.zone .chain == [older] &&
      done.handN p + 1 == opened.handN p + draws &&
      events.countP (fun | .drew drawer => drawer == p | _ => false) == draws &&
      (casted.poolOf p).energy == 4 - energy
  return (← castFor 2 1) && (← castFor 4 2) &&
    !(step 100 opened ⟨.player p, .playCard spell ⟨3, []⟩ []⟩).isOk

-- Alpha Wildclaw (UNL-057): the units of its player here with less Might can't be chosen by
-- enemies; the stronger ones, and those elsewhere, can
#guard tun fun s => do
  let (s1, _) ← putAt s s.me "UNL-057" s.bf0
  let (s2, weak) ← putAt s1 s.me "UNL-111" s.bf0
  let (s3, base) ← put s2 s.me "UNL-111" .base
  return s3.blocksChoice s.you weak && !s3.blocksChoice s.you base && !s3.blocksChoice s.me weak

-- Vilemaw (UNL-060): the enemy units here with less Might deal no combat damage
#guard tun fun s => do
  let (s1, _) ← putAt s s.me "UNL-060" s.bf0
  let (s2, weak) ← putAt s1 s.you "UNL-111" s.bf0
  let (s3, mine) ← putAt s2 s.me "UNL-111" s.bf0
  return s3.noCombatDamage weak && !s3.noCombatDamage mine

-- The Hold ability belongs to Vilemaw's controller. Conquering does not draw a card.
#guard tun fun s => do
  let p := s.me
  let (s, _) ← putAt s p "UNL-060" s.bf0
  let held ← fire s [.scored p s.bf0 false]
  let conquered ← fire s [.scored p s.bf0 true]
  return held.handN p == s.handN p + 1 && held.handN s.you == s.handN s.you &&
    conquered.handN p == s.handN p

-- Alpha Wildclaw protects only units its controller controls, even in a team duel.
#guard tun fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) initial).toOption
  let p := s.me
  let mate ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let opponent ← s.players.find? (fun q => !config.mode.sameSide p q)
  let (s, _) ← putAt s p "UNL-057" s.bf0
  let (s, ownUnit) ← putAt s p "UNL-111" s.bf0
  let (s, allied) ← putAt s mate "UNL-111" s.bf0
  return s.blocksChoice opponent ownUnit && !s.blocksChoice opponent allied &&
    !s.blocksChoice mate ownUnit

-- Wily Newtfish (UNL-108): +1 Might after the player gained XP this turn
#guard tun fun s => do
  let (s1, u) ← put s s.me "UNL-108" .base
  let s2 := gainXPOf 1 s1 s.me
  let other := gainXPOf 1 s1 s.you
  let expired := { s2 with turn := s2.turn + 1 }
  return s1.mightNow u == some 4 && s2.mightNow u == some 5 && s2.hasKw u .ganking &&
    other.mightNow u == some 4 && !other.hasKw u .ganking &&
    expired.mightNow u == some (4 : Int) && !expired.hasKw u .ganking

-- Shadow Watcher (UNL-037) enters ready if a unit of its player died in their Beginning Phase
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-037" .hand
  let d ← s1.cardDef? c
  let s2 := { s1 with phase := .beginning }.noteUnitDied s.me
  let s3 := { s2 with phase := .main }
  return !s1.readyNow s.me c d && s3.readyNow s.me c d

-- Valley of Idols (UNL-218): a unit played there is buffed for 1 Energy
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "UNL-218"
  let (s2, u) ← putAt s1 s.me "UNL-111" bf
  let s3 ← fire (s2.rich s.me) [Event.played s.me u]
  return !((s2.obj? u).any (·.buffed)) && ((s3.obj? u).any (·.buffed))

-- Vaults of Helia (UNL-219): after the player holds there, their units cost 1 more this turn
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "UNL-219"
  let (s2, c) ← put s1 s.me "UNL-111" .hand
  let s3 ← fire s2 [Event.scored s.me bf false]
  return s2.energyCost? s.me c == some 1 && s3.energyCost? s.me c == some 2

-- Mirror Image (UNL-200): a ready Reflection token at the Base becomes a copy of the unit, with
-- Temporary. The linked ability leaves an existing Reflection alone.
#guard tun fun s => do
  let old : ObjId := ⟨s.nextId⟩
  let s := createOne (cid "UNL-T06") s.me none false s
  let (s1, c) ← put s s.me "UNL-200" .hand
  let (s2, e) ← putAt s1 s.you "UNL-111" s.bf0
  let funded := s2.rich s.me
  let invalid := step 100 funded ⟨.player s.me, .playCard c ⟨3, [.mind, .fury]⟩ [e]⟩
  let s3 ← cast funded s.me c ⟨3, [.mind, .order]⟩ [e]
  let base := (s3.zone (.player s.me .base)).filter (fun u => (s3.cardDef? u).any (·.id == cid "UNL-111"))
  return invalid.toOption.isNone && base.length == 1 && base.all (fun u => s3.hasKw u .temporary) &&
    base.all (fun u => s3.tired u == some false) &&
    (s3.cardDef? old).any (·.id == cid "UNL-T06") && !s3.hasKw old .temporary

-- The Reflection is on the Board while the copy is on the Chain. Retreat can remove it there.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, mirror) ← put s p "UNL-200" .hand
  let (s, retreat) ← put s p "OGN-104" .hand
  let (s, gust) ← put s q "OGN-169" .hand
  let (s, model) ← putAt s q "UNL-111" s.bf0
  let (s, other) ← putAt s q "UNL-111" s.bf0
  let funded := (s.rich p).rich q
  let (castMirror, _) ← (step 100 funded ⟨.player p, .playCard mirror ⟨3, [.mind, .mind]⟩ [model]⟩).toOption
  let .chainPass first _ :: _ := castMirror.pending | none
  let (afterFirst, _) ← (step 100 castMirror ⟨.player first, .pass⟩).toOption
  let .chainPass second _ :: _ := afterFirst.pending | none
  let (window, events) ← (step 100 afterFirst ⟨.player second, .pass⟩).toOption
  let .chainPass current _ :: _ := window.pending | none
  let [ability] := window.zone .chain | none
  let token ← window.firstOf p .base "UNL-T06"
  let stopped ← cast window p retreat (payOf window retreat) [token]
  let (opponentWindow, _) ← (step 100 window ⟨.player p, .pass⟩).toOption
  let answered ← cast opponentWindow q gust (payOf opponentWindow gust) [other]
  return current == p && (window.obj? ability).any (fun o =>
      o.eventObjects == [token] && o.triggerSubject == some model) &&
    events.any (fun | .unitTokensFor _ _ _ _ _ [id] none => id == token | _ => false) &&
    window.tired token == some false && !window.hasKw token .temporary &&
    !(stopped.inPlay.contains token) && stopped.countIn p .base "UNL-111" == 0 &&
    (stopped.zone .chain).isEmpty && !(answered.inPlay.contains other) &&
    (answered.cardDef? token).any (·.id == cid "UNL-111") && answered.hasKw token .temporary

-- A token substituted by Heimerdinger inherits both the copy and Temporary.
#guard tun fun s => do
  let p := s.me
  let (s, _) ← putAt (s.control p s.bf0) p "RAD-132" s.bf0
  let (s, mirror) ← put s p "UNL-200" .hand
  let (s, model) ← put s s.you "UNL-111" .base
  let finished ← cast (s.rich p) p mirror ⟨3, [.order, .order]⟩ [model] { yes := false }
  let copy ← finished.firstOf p .base "UNL-111"
  let original ← (finished.obj? copy).bind (·.originalToken)
  return (finished.cards.find? original).any (·.name == "Mech") &&
    finished.hasKw copy .temporary && finished.tired copy == some false

-- Zilean's additional ready Reflection belongs to the same reflexive ability. Turning both
-- tokens into copies of Zilean does not cause an additional play (CR 375).
#guard tun fun s => do
  let p := s.me
  let (s, zilean) ← putAt (s.control p s.bf0) p "UNL-086" s.bf0
  let (s, mirror) ← put s p "UNL-200" .hand
  let resolved ← cast (s.rich p) p mirror ⟨3, [.mind, .order]⟩ [zilean]
  let copies := (resolved.zone (.player p .base)).filter fun id =>
    (resolved.obj? id).any (·.originalToken == some (cid "UNL-T06"))
  return copies.length == 2 && copies.all (fun id =>
      (resolved.cardDef? id).any (·.id == cid "UNL-086") &&
      resolved.hasKw id .temporary && resolved.tired id == some false) &&
    (resolved.zone .chain).isEmpty

-- The Deceiver pays to put her first ability on the Chain, then chooses a copy model at the
-- Battlefield of this score. A previously scored Battlefield and the new tokens are ineligible.
#guard tun fun s => do
  let p := s.me
  let first := s.bf0
  let (s, second) ← putBf s p "OGN-275"
  let (s, legend) ← put s p "UNL-199" .legendZone
  let (s, pitch) ← put s p "UNL-200" .hand
  let (s, _) ← putAt s p "UNL-111" first
  let (s, zilean) ← putAt (s.control p second) p "UNL-086" second
  let s := s.modObj first fun o => { o with scored := [p] }
  let chooseCost (conquer : Bool) :=
    let pending := insertTriggers (s.detect [.scored p second conquer]) [.priority p]
    (advance 100 { s with pending } []).toOption
  let (conquer, _) ← chooseCost true
  let (hold, _) ← chooseCost false
  let pay := Action.mk (.player p) (.putTrigger 0 [] (.pay [pitch] none none []))
  let (paid, costEvents) ← (step 100 conquer pay).toOption
  let (paidHold, _) ← (step 100 hold pay).toOption
  let (declined, _) ← (step 100 hold ⟨.player p, .putTrigger 0 [] .skip⟩).toOption
  let .chainPass firstPass _ :: _ := paid.pending | none
  let (passed, _) ← (step 100 paid ⟨.player firstPass, .pass⟩).toOption
  let .chainPass secondPass _ :: _ := passed.pending | none
  let (replacement, _) ← (step 100 passed ⟨.player secondPass, .pass⟩).toOption
  let (copyChoice, _) ← (step 100 replacement ⟨.player p, .decide true⟩).toOption
  let result := settleChain { pick := fun targets => targets == [zilean] } 12 copyChoice
  let fresh := (result.unitsAtOf second p).filter (· != zilean)
  return paid.tired legend == some true && paidHold.tired legend == some true &&
    declined.tired legend == some false && (declined.zone (.player p .hand)).contains pitch &&
    paid.countIn p .trash "UNL-200" == 1 && costEvents.contains (.exhausted legend) &&
    (paid.unitsAtOf second p) == [zilean] && copyChoice.trigPicks == [zilean] &&
    fresh.length == 2 && fresh.all (fun id => result.hasKw id .temporary &&
      result.tired id == some false && (result.cardDef? id).any (·.id == cid "UNL-086")) &&
    (result.unitsAtOf first p).length == 1

-- Keeper of Masks (UNL-081): two Reflection tokens, copies of it (so with Temporary too)
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-081" .hand
  let s2 ← play s1 s.me c
  return s2.countIn s.me .base "UNL-081" == 3

-- Keeper of Masks: the two copies also enter when the Keeper was played at a Battlefield.
-- They stay exhausted and do not trigger the Keeper's own play effect.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let old : ObjId := ⟨s.nextId⟩
  let s := createOne (cid "UNL-T06") p (some field) true (s.control p field)
  let (s, keeper) ← put s p "UNL-081" .hand
  let finished ← play s p keeper [field]
  let tokens := (finished.unitsAtOf field p).filter (fun id =>
    (finished.obj? id).any (fun o => o.originalToken == some (cid "UNL-T06")))
  let expired ← settleBeginning finished p
  return tokens.length == 2 && tokens.all (fun id => finished.tired id == some true &&
    finished.hasKw id .temporary && (finished.cardDef? id).any (·.id == cid "UNL-081")) &&
    (finished.cardDef? old).any (·.id == cid "UNL-T06") && finished.tired old == some false &&
    expired.unitsAtOf field p == [old] && expired.countIn p .trash "UNL-081" == 1

-- Lillia starts two triggers from different origins when Flash answers her first move.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, lillia) ← put (s.control p field) p "UNL-082" .base
  let (s, flash) ← put s p "OGS-011" .hand
  let (waiting, _) ← (step 100 s ⟨.player p, .standardMove lillia (.battlefield field)⟩).toOption
  let returned ← play waiting p flash [lillia]
  let fieldSprites := (returned.unitsAtOf field p).filter (fun id =>
    (returned.cardDef? id).any (·.id == cid "TKN-Sprite"))
  let sprite ← fieldSprites.head?
  return (waiting.zone .chain).length == 1 && returned.countIn p .base "UNL-082" == 1 &&
    returned.countIn p .base "TKN-Sprite" == 1 && fieldSprites.length == 1 &&
    returned.tired sprite == some true && returned.hasKw sprite .temporary

-- Mister Root gains XP on a Standard Move into a Battlefield. Flash can send it back
-- during its turn without gaining XP a second time.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, root) ← put (s.control p field) p "UNL-127" .base
  let (s, _) ← putAt s p "OGN-049" field
  let (s, flash) ← put s p "OGS-011" .hand
  let (waiting, _) ← (step 100 s ⟨.player p, .standardMove root (.battlefield field)⟩).toOption
  let arrived := settleChain {} 12 waiting
  let returned ← play arrived p flash [root]
  return arrived.xpOf p == s.xpOf p + 2 && (arrived.unitsAtOf field p).contains root &&
    returned.xpOf p == arrived.xpOf p && returned.countIn p .base "UNL-127" == 1

-- Irresistible Faefolk chooses its enemy before other players can react. Flash moves the source
-- back to Base and the chosen enemy still moves to the recorded Battlefield.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, fae) ← put (s.control p field) p "UNL-112" .base
  let (s, friend) ← put s p "OGN-049" .base
  let (s, foe) ← put s q "OGN-049" .base
  let (s, flash) ← put s p "OGS-011" .hand
  let (offered, _) ← (step 100 s ⟨.player p, .standardMove fae (.battlefield field)⟩).toOption
  let target (unit : ObjId) : Action := ⟨.player p, .putTrigger 0 [unit] (.pay [])⟩
  let (queued, events) ← (step 100 offered (target foe)).toOption
  let (declined, _) ← (step 100 offered ⟨.player p, .putTrigger 0 [] .skip⟩).toOption
  let resolved ← play queued p flash [fae]
  return (legalActions offered).contains (target foe) && !(step 100 offered (target friend)).isOk &&
    events.contains (.chosenByAbility p foe) && queued.where? foe == some (.player q .base) &&
    declined.where? foe == some (.player q .base) && (resolved.unitsAtOf field q).contains foe &&
    resolved.countIn p .base "UNL-112" == 1

-- Nilah can Accelerate and use Ganking. Each move earns XP, while playing her does not.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let other ← s.battlefields[1]?
  let (s, _) ← putAt (s.control p field) p "OGN-051" field
  let (s, _) ← putAt (s.control p other) p "OGN-051" other
  let (s, nilah) ← put (s.rich p) p "UNL-115" .hand
  let normal ← cast s p nilah ⟨3, [.body]⟩
  let paid ← cast s p nilah ⟨4, [.body, .body]⟩
  let original ← normal.firstOf p .base "UNL-115"
  let accelerated ← paid.firstOf p .base "UNL-115"
  let (queued, _) ← (step 100 paid ⟨.player p, .standardMove accelerated (.battlefield field)⟩).toOption
  let arrived := settleChain {} 12 queued
  let moved ← (arrived.unitsAtOf field p).find? (fun id => (arrived.cardDef? id).any (·.id == cid "UNL-115"))
  let ready := (readyEffect arrived moved).1
  let (queuedAgain, _) ← (step 100 ready ⟨.player p, .standardMove moved (.battlefield other)⟩).toOption
  let finished := settleChain {} 12 queuedAgain
  return normal.tired original == some true && paid.tired accelerated == some false && paid.xpOf p == s.xpOf p &&
    arrived.xpOf p == s.xpOf p + 1 && finished.xpOf p == s.xpOf p + 2 &&
    (finished.unitsAtOf other p).contains moved && finished.xpOf s.you == s.xpOf s.you

-- Smoke and Mirrors swaps units at distinct locations with Temporary. Both branches draw.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, first) ← put (s.control p field) p "RAD-001" .base
  let (s, otherBase) ← put s p "RAD-001" .base
  let (s, second) ← putAt s p "RAD-001" field
  let (s, smoke) ← put s p "UNL-083" .hand
  let unchanged ← play s p smoke [first, second]
  let marked := (addTempKw { keyword := .temporary } .never s second).1
  let swapped ← play marked p smoke [first, second]
  return !(play s p smoke [first, otherBase]).isSome &&
    unchanged.unitsAtOf field p == [second] && swapped.unitsAtOf field p == [first] &&
    (swapped.zone (.player p .base)).contains second &&
    unchanged.handN p == s.handN p && swapped.handN p == s.handN p

-- Smoke and Mirrors requires the caster's own Units, even with a teammate at a different location.
#guard tun fun s => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let team := GameState.empty { s.config with mode := .teamDuel } s.cards
  let (s, field) ← putBf team ally "VEN-158"
  let (s, first) ← put s p "RAD-001" .base
  let (s, second) ← put s ally "RAD-001" .base
  let (s, own) ← putAt (s.control p field) p "RAD-001" field
  let (s, smoke) ← put s p "UNL-083" .hand
  let s := { s with active := some p, phase := .main, pending := [.priority p] }
  let accepts (targets : List ObjId) := (play s p smoke targets).isSome
  return accepts [first, own] && !accepts [first, second] && !accepts [second, own]

-- Sumpworks Map can enter as a Reaction on the opponent's turn. It triggers on both
-- Conquer and Hold until Temporary removes it at the start of its controller's turn.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, unit) ← putAt (s.control q field) q "RAD-001" field
  let (s, gust) ← put s q "OGN-169" .hand
  let (s, map) ← put s p "UNL-085" .hand
  let s := { s with active := some q, pending := [.priority q] }
  let (chain, _) ← (step 100 (s.rich q) ⟨.player q, .playCard gust (payOf s gust) [unit]⟩).toOption
  let (answer, _) ← (step 100 chain ⟨.player q, .pass⟩).toOption
  let played ← play answer p map
  let conquered ← fire played [.scored q field true]
  let held ← fire conquered [.scored q field false, .scored p field false]
  let expired ← settleBeginning held p
  let later ← fire expired [.scored q field false]
  return played.countIn p .base "UNL-085" == 1 && conquered.handN p == played.handN p + 1 &&
    held.handN p == conquered.handN p + 1 && expired.countIn p .trash "UNL-085" == 1 &&
    later.handN p == expired.handN p

-- Sumpworks Map reacts to the opposing team's score in a team game.
#guard tun fun s => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let team := GameState.empty { s.config with mode := .teamDuel } s.cards
  let (s, field) ← putBf team ally "VEN-158"
  let (s, map) ← put s p "UNL-085" .base
  return !(s.detect [.scored ally field true]).any (·.source == map) &&
    (s.detect [.scored enemy field false]).any (·.source == map)

-- Baron Nashor (UNL-147): the Baron Pit enters the board once, and Baron Nashor goes there
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-147" .hand
  let s2 ← play s1 s.me c
  let pits := (s2.zone .battlefieldZone).filter (fun b => (s2.cardDef? b).any (·.name == "Baron Pit"))
  let nashor := (s2.zone .battlefieldZone).find? (fun u => (s2.cardDef? u).any (·.id == cid "UNL-147"))
  return pits.length == 1 && s2.battlefields.length == s1.battlefields.length + 1 &&
    nashor.any (fun u => (s2.obj? u).any (fun o => o.loc == pits.head?))

-- Arachnoid Horror (UNL-117): it, and the other friendly units, can be played to a Battlefield
-- where an enemy unit is alone
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-117" .hand
  let (s2, _) ← putAt s1 s.you "UNL-111" s.bf0
  let (s3, _) ← putAt s2 s.you "UNL-111" s.bf0
  let (s4, d) ← put s2 s.me "UNL-111" .hand
  let (s5, _) ← put s4 s.me "UNL-117" .base
  let (s6, _) ← putAt s5 s.me "UNL-117" s.bf0
  return (s2.playBfOptions s.me c).contains s.bf0 && !(s3.playBfOptions s.me c).contains s.bf0 &&
    (s5.playBfOptions s.me d).contains s.bf0 && !(s2.playBfOptions s.me d).contains s.bf0 &&
    s6.hasKw c .temporary == false

-- The Arachnoid Horror permission is shared with a teammate, and enemy teammates keep
-- each other company. An attached Gear does not keep its Unit from being alone.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let enemyAlly : PlayerId := ⟨3⟩
  let s := unleashedTeamMain labState
  let (s, field) ← putBf s enemy "VEN-158"
  let (s, arrival) ← put s ally "UNL-111" .hand
  let (s, _) ← putAt (s.control enemy field) enemy "UNL-111" field
  let (s, _) ← putAt s enemy "SFD-009" field
  let (permitted, _) ← put s p "UNL-117" .base
  let (accompanied, _) ← putAt permitted enemyAlly "UNL-111" field
  let main := { (permitted.rich ally) with active := some ally, pending := [.priority ally] }
  let recruit : Action := ⟨.player ally, .playCard arrival (payOf main arrival) [field]⟩
  let (entered, _) ← (step 100 main recruit).toOption
  return !(s.playBfOptions ally arrival).contains field &&
    !(accompanied.playBfOptions ally arrival).contains field &&
    (entered.unitsAtOf field ally).any (fun unit =>
      (entered.cardDef? unit).any (·.id == cid "UNL-111"))

-- Rengar extends Ambush at Reaction speed to an enemy Unit's Battlefield (CR 822.1.d).
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, rengar) ← put s p "UNL-120" .hand
  let (s, rival) ← putAt (s.control q field) q "UNL-111" field
  let (s, gearOnly) ← putBf s q "VEN-158"
  let (s, _) ← putAt s q "SFD-009" gearOnly
  let (s, responseTo) ← onChain s q "OGN-154"
  let reaction := { (s.rich p) with active := some q, pending := [.chainPass p 0, .priority q] }
  let playTo (ts : List ObjId) : Action := ⟨.player p, .playCard rengar (payOf reaction rengar) ts⟩
  let (played, _) ← (step 100 reaction (playTo [field])).toOption
  return (legalFrameActions reaction).contains (playTo [field]) &&
    !(step 100 reaction (playTo [gearOnly])).isOk &&
    !(step 100 reaction (playTo [])).isOk &&
    (played.unitsAtOf field p).any (fun unit =>
      (played.cardDef? unit).any (·.id == cid "UNL-120")) &&
    played.inPlay.contains rival && (played.zone .chain).contains responseTo

-- LeBlanc suppresses only her own controller's Temporary triggers at her Battlefield.
#guard tun fun s => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let team := GameState.empty { s.config with mode := .teamDuel } s.cards
  let (s, field) ← putBf team p "VEN-158"
  let (s, sheltered) ← putAt (s.control p field) p "UNL-081" field
  let (s, guest) ← putAt s ally "UNL-081" field
  let (s, outside) ← put s p "UNL-081" .base
  let (s, _) ← putAt s p "UNL-090" field
  let next ← settleBeginning s p
  return (s.temporaryBeginningTriggers ally).any (·.source == guest) &&
    next.inPlay.contains sheltered && next.inPlay.contains guest &&
    !next.inPlay.contains outside && next.countIn p .trash "UNL-081" == 1

-- Katarina, Reckless (UNL-023): she readies when her player hides a card
#guard tun fun s => do
  let (s1, k) ← put s s.me "UNL-023" .base
  let (s2, c) ← put s1 s.me "UNL-111" .hidden
  let s3 := s2.tire k
  let s4 ← fire s3 [Event.moved c c (.player s.me .hidden)]
  return s3.tired k == some true && s4.tired k == some false

-- Tricksy Tentacles (UNL-054): enemy units of total Might 8 or less are moved to one place
#guard tun fun s => do
  let (s1, c) ← put (s.control s.you s.bf0) s.me "UNL-054" .hand
  let (s2, a) ← putAt s1 s.you "OGN-135" s.bf0
  let (s3, b) ← putAt s2 s.you "OGN-135" s.bf0
  let s4 ← cast (s3.rich s.me) s.me c (payOf s3 c) [a, b] {} (.destination none)
  return (s4.obj? a).any (·.loc != some s.bf0) && (s4.obj? b).any (·.loc != some s.bf0)

-- The targets must share the same opposing controller and fit the Might budget at declaration.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let first : PlayerId := ⟨2⟩
  let second : PlayerId := ⟨3⟩
  let (s, field) ← putBf (unleashedTeamMain labState) p "OGN-275"
  let (s, spell) ← put s p "UNL-054" .hand
  let (s, small) ← put s first "OGN-051" .base
  let (s, large) ← put s first "OGN-049" .base
  let (s, tooMuch) ← put s first "OGN-049" .base
  let (s, anotherSeat) ← put s second "OGN-051" .base
  let s := s.fund p 4 (calm := 1)
  let answer (targets : List ObjId) (dest : Option ObjId := some field) : Action :=
    ⟨.player p, .playCard spell ⟨4, [.calm]⟩ targets none none (.destination dest)⟩
  let accepts (targets : List ObjId) := (step 100 s (answer targets)).isOk
  let offers (targets : List ObjId) := (legalFrameActions s).contains (answer targets)
  let (s, zeros) ← (List.range 9).foldlM (fun (board, ids) _ => do
    let (board, zero) ← put board second "UNL-053" .base
    return (board, ids ++ [zero])) (s, [])
  return (step 100 s (answer [] none)).isOk && !accepts [] &&
    !(step 100 s (answer [small, large] none)).isOk && accepts [small, large] && offers [small, large] &&
    !accepts [large, tooMuch] && !offers [large, tooMuch] &&
    !accepts [small, anotherSeat] && !offers [small, anotherSeat] &&
    (step 100 s (answer zeros)).isOk

private meta def passUntilChoice : Nat → GameState → List Event → Option (GameState × List Event)
  | 0, _, _ => none
  | n + 1, state, events => match state.pending with
    | .chainPass seat _ :: _ => do
      let (next, emitted) ← (step 100 state ⟨.player seat, .pass⟩).toOption
      passUntilChoice n next (events ++ emitted)
    | _ => some (state, events)

-- A Reaction can break the declaration's Might budget. Keep an inclusion-maximal subset
-- of the original targets and use the Base declared at finalization.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, first) ← putAt (s.control q bf) q "OGN-049" bf
  let (s, second) ← putAt s q "OGN-135" bf
  let (s, untouched) ← putAt s q "OGN-051" bf
  let (s, spell) ← put s p "UNL-054" .hand
  let (s, response) ← put s q "OGN-058" .hand
  let s := (s.fund p 4 (calm := 1)).fund q 2
  let (declared, _) ← (step 100 s
    ⟨.player p, .playCard spell ⟨4, [.calm]⟩ [first, second] none none (.destination none)⟩).toOption
  let (window, _) ← (step 100 declared ⟨.player p, .pass⟩).toOption
  let (higher, _) ← (step 100 window ⟨.player q, .playCard response ⟨2, []⟩ [second]⟩).toOption
  let (waiting, _) ← passUntilChoice 10 higher []
  let choose (id : ObjId) : Action := ⟨.player p, .choose id⟩
  let legal := legalFrameActions waiting
  let (done, events) ← (step 100 waiting (choose second)).toOption
  return legal.contains (choose first) && legal.contains (choose second) &&
    !legal.contains (choose untouched) && done.hereOf first == some bf &&
    done.hereOf second == none && (done.zone (.player q .base)).contains second &&
    done.hereOf untouched == some bf && events.contains (.movedByEffect p second)

-- A Base is a seat's physical location. If the target is stolen after finalization,
-- the declared Base becomes invalid and the Unit Recalls instead of making a Move.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let owner : PlayerId := ⟨2⟩
  let other : PlayerId := ⟨3⟩
  let (s, field) ← putBf (unleashedTeamMain labState) owner "OGN-275"
  let (s, unit) ← putAt (s.control owner field) owner "OGN-135" field
  let (s, spell) ← put s p "UNL-054" .hand
  let s := s.fund p 4 (calm := 1)
  let declare : Action := ⟨.player p, .playCard spell ⟨4, [.calm]⟩ [unit] none none (.destination none)⟩
  let (queued, _) ← (step 100 s declare).toOption
  let changed := (setController other queued unit).1
  let (done, events) ← passUntilChoice 10 changed []
  return queued.turnFx.any (fun note => note.kind == .declaredMoveBases [(unit, owner)]) &&
    (changed.obj? unit).any (·.controller == other) &&
    (done.zone (.player other .base)).contains unit && events.contains (.recalled unit) &&
    !(events.contains (.movedByEffect p unit))

-- A declared Battlefield that becomes occupied by two other War seats causes a Recall.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let third : PlayerId := ⟨2⟩
  let fourth : PlayerId := ⟨3⟩
  let initial := GameState.empty { mode := .ffa4, ruleSet := .coreOnly } labState.cards
  let s := { initial with
    phase := .main, turn := 3, active := some p
    turnOrder := [p, q, third, fourth], pending := [.priority p] }
  let (s, otherField) ← putBf s p "OGN-276"
  let (s, homeField) ← putBf s q "OGN-275"
  let (s, unit) ← putAt (s.control q homeField) q "OGN-135" homeField
  let (s, spell) ← put s p "UNL-054" .hand
  let s := s.fund p 4 (calm := 1)
  let (queued, _) ← (step 100 s ⟨.player p,
    .playCard spell ⟨4, [.calm]⟩ [unit] none none (.destination (some otherField))⟩).toOption
  let (occupied, _) ← putAt queued third "OGN-051" otherField
  let (occupied, _) ← putAt occupied fourth "OGN-051" otherField
  let (done, events) ← passUntilChoice 10 occupied []
  return (done.zone (.player q .base)).contains unit && events.contains (.recalled unit) &&
    !(events.contains (.movedByEffect p unit))

-- Diana pays when finalizing the trigger from a non-combat Showdown, then privately Predicts.
-- The revealed card is the new top, and only a Spell is drawn (Vendetta errata).
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let deck := Zone.player p .mainDeck
  let (s, diana) ← put (s.fund p 1) p "UNL-079" .base
  let (s, spell) ← put s p "OGN-095" .mainDeck
  let (s, unit) ← put s p "OGN-049" .mainDeck
  let s := (readyEffect s diana).1.setZone deck (spell :: unit :: ((s.zone deck).erase spell).erase unit)
  let (offered, opened) ← (step 100 s ⟨.player p, .standardMove diana (.battlefield bf)⟩).toOption
  let pay : Action := ⟨.player p, .putTrigger 0 [] (.pay [])⟩
  let (queued, _) ← (step 100 offered pay).toOption
  let (skipped, _) ← (step 100 offered ⟨.player p, .putTrigger 0 [] .skip⟩).toOption
  let (passed, _) ← (step 100 queued ⟨.player p, .pass⟩).toOption
  let (predicting, _) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let (kept, revealedSpell) ← (step 100 predicting ⟨.player p, .predictPick spell false⟩).toOption
  let (recycled, revealedUnit) ← (step 100 predicting ⟨.player p, .predictPick spell true⟩).toOption
  return opened.contains (.showdownOpened bf) && !(opened.contains (.combatStarted bf p)) &&
    (legalFrameActions offered).contains pay && (queued.poolOf p).energy == 0 &&
    (skipped.poolOf p).energy == 1 && queued.handN p == s.handN p &&
    (predicting.resolutionZoneCardFaces p deck).any (fun faces => (faces.take 1).all Option.isSome) &&
    predicting.zoneView q deck == s.zoneView q deck && revealedSpell.contains (.revealed p spell) &&
    revealedSpell.contains (.drew p) && kept.handN p == s.handN p + 1 &&
    revealedUnit.contains (.revealed p unit) && !(revealedUnit.contains (.drew p)) &&
    recycled.handN p == s.handN p && (recycled.zone deck).head? == some unit

-- A defending Diana watches the same opening. Returning to that Showdown after the trigger's
-- Chain resolves does not open it a second time.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, diana) ← putAt (s.control q bf) q "UNL-079" bf
  let (s, mover) ← put s p "OGN-049" .base
  let s := (readyEffect (s.fund q 1) mover).1
  let (offered, events) ← (step 100 s ⟨.player p, .standardMove mover (.battlefield bf)⟩).toOption
  let pay : Action := ⟨.player q, .putTrigger 0 [] (.pay [])⟩
  let .triggerOrder actor trigger others _ _ :: _ := offered.pending | none
  let (returned, passed) ← (step 100 offered ⟨.player q, .putTrigger 0 [] .skip⟩).toOption
  return actor == q && trigger.source == diana && others.isEmpty &&
    (legalFrameActions offered).contains pay && events.contains (.showdownOpened bf) &&
    events.contains (.combatStarted bf p) && !(passed.contains (.showdownOpened bf)) &&
    returned.pending.head?.any (fun | .showdown field .. => field == bf | _ => false)

-- Elder Dragon sees its controller's earlier damage, not a third seat's damage. Healing and
-- prevention both remove the mark that would make the damage lethal.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let s := { s with config := { s.config with mode := .ffa4 } }
  let (s, foe) ← put s q "OGN-049" .base
  let (s, ally) ← put s p "OGN-049" .base
  let prior := (dealObj 1 s foe (some p)).1
  let (withDragon, _) ← put prior p "UNL-118" .base
  let (board, _) ← put s p "UNL-118" .base
  let other := (dealObj 1 board foe (some third)).1
  let own := (dealObj 1 board ally (some p)).1
  let healed := (healOne 1 withDragon foe).1
  let shielded := board.addTurnFxOn q foe (.preventDamage 1)
  let (prevented, events) := dealObj 1 shielded foe (some p)
  return !prior.lethal foe && withDragon.lethal foe && !other.lethal foe && !own.lethal ally &&
    !healed.lethal foe && (healed.damageMarks[foe.n]?).isNone &&
    !prevented.lethal foe && (prevented.damageMarks[foe.n]?).isNone && events.isEmpty &&
    other.combatNeed foe (some p) == some 1 && other.combatNeed foe (some third) == some 4 &&
    (withDragon.mapObjects healObj).damageMarks.isEmpty

-- Ally damage does not inherit the Dragon's passive in 2v2 (CR 142.3.b).
#guard tun fun s => do
  let p : PlayerId := ⟨0⟩
  let teammate : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let s := { s with config := { s.config with mode := .teamDuel } }
  let (s, _) ← put s p "UNL-118" .base
  let (s, victim) ← put s enemy "OGN-049" .base
  let (s, ownSide) ← put s teammate "OGN-049" .base
  return !((dealObj 1 s victim (some teammate)).1.lethal victim) &&
    (dealObj 1 s victim (some p)).1.lethal victim && !((dealObj 1 s ownSide (some p)).1.lethal ownSide)

-- Each location gets its own optional target. Moving one target before resolution leaves the
-- targets originally declared at the other locations legal.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let fourth : PlayerId := ⟨3⟩
  let bf := s.bf0
  let s := { s with config := { s.config with mode := .ffa4 }, turnOrder := [p, q, third, fourth] }
  let (s, qBase) ← put s q "OGN-049" .base
  let (s, spare) ← put s q "OGN-088" .base
  let (s, thirdBase) ← put s third "OGN-049" .base
  let (s, onField) ← putAt (s.control q bf) q "OGN-049" bf
  let (s, dragon) ← put (s.rich p) p "UNL-118" .hand
  let (offered, _) ← (step 100 s ⟨.player p, .playCard dragon ⟨12, [.body, .body, .body, .body]⟩ []⟩).toOption
  let finalize (targets : List ObjId) : Action := ⟨.player p, .putTrigger 0 targets (.pay [])⟩
  let (queued, _) ← (step 100 offered (finalize [qBase, thirdBase, onField])).toOption
  let (empty, _) ← (step 100 offered (finalize [])).toOption
  let success := settleChain {} 20 queued
  let moved := settleChain {} 20 (moveHome queued onField).1
  let skipped := settleChain {} 20 empty
  return !(step 100 offered (finalize [qBase, spare])).isOk &&
    (queued.obj? qBase).any (·.damage == 0) && queued.inPlay.contains onField &&
    success.countIn q .trash "OGN-049" == 2 && success.countIn third .trash "OGN-049" == 1 &&
    success.inPlay.contains spare && moved.inPlay.contains onField &&
    moved.countIn q .trash "OGN-049" == 1 && moved.countIn third .trash "OGN-049" == 1 &&
    skipped.inPlay.contains qBase && skipped.inPlay.contains thirdBase && skipped.inPlay.contains onField

-- Real Combat Damage uses the assigning seat both for the lethal amount and the marks.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, _) ← put s p "UNL-118" .base
  let (s, attacker) ← putAt (s.control q bf) p "OGN-049" bf
  let (s, first) ← putAt s q "OGN-049" bf
  let (s, second) ← putAt s q "OGN-049" bf
  let (step1, _) ← (advance 100 { s with pending := [.combatDamage bf p] } []).toOption
  let (step2, _) ← (step 100 step1 ⟨.player p, .assignPick first⟩).toOption
  let (step3, _) ← (step 100 step2 ⟨.player p, .assignPick second⟩).toOption
  let (step4, _) ← (step 100 step3 ⟨.player p, .assignDone⟩).toOption
  let (step5, _) ← (step 100 step4 ⟨.player q, .assignPick attacker⟩).toOption
  let (done, events) ← (step 100 step5 ⟨.player q, .assignDone⟩).toOption
  return events.contains (.damaged first 1) && events.contains (.damaged second 4) &&
    events.contains (.damaged attacker 10) && done.countIn q .trash "OGN-049" == 2 &&
    done.countIn p .trash "OGN-049" == 1 && done.damageMarks.isEmpty

-- Maduli the Gatekeeper (UNL-144) can't be readied: not by the Awaken Phase, not by an effect
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-144" .hand
  let s2 ← play s1 s.me c
  let m ← s2.firstOf s.me .base "UNL-144"
  let s3 := s2.tire m
  let s4 := s3.mapObjects (readyOf s.me)
  return s3.tired m == some true && s4.tired m == some true && (readyEffect s3 m).1.tired m == some true

-- Syndra, Transcendent (UNL-146): in a showdown, the Spells of her player have Repeat for 2 Energy
-- and a Chaos rune
#guard tun fun s => do
  let (s1, _) ← putAt s s.me "UNL-146" s.bf0
  let (s2, sp) ← put s1 s.me "UNL-159" .hand
  let d ← s2.cardDef? sp
  let s3 := s2.inShowdownAt s.bf0 s.me
  return (s2.extrasRaw s.me sp d).isEmpty && (s3.extrasRaw s.me sp d).length == 1

-- Stalking Wolf (UNL-166): a Bird, Cat, Dog or Poro of its player is killed as it is played
#guard tun fun s => do
  let (s1, w) ← put s s.me "UNL-166" .hand
  let (s2, bird) ← put s1 s.me "UNL-056" .base
  let (s3, other) ← put s2 s.me "UNL-111" .base
  return s3.extraOk s.me w [bird] && !s3.extraOk s.me w [other] && !s3.extraOk s.me w []

private meta def killedForPlay (events : List Event) (owner : PlayerId) (before : ObjId) : Bool :=
  events.any fun
    | .moved old after (.player dest .trash) =>
      old == before && dest == owner && events.contains (.died after owner)
    | _ => false

-- A Battlefield destination and the pet payment are separate choices. A Wolf can Ambush to
-- the field where its only Unit is the pet it pays, including while another item is on the Chain.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let otherField := s.bf0
  let (s, field) ← putBf s p "OGN-275"
  let (s, wolf) ← put s p "UNL-166" .hand
  let (s, pet) ← putAt s p "OGN-013" field
  let (s, otherPet) ← put s p "OGN-013" .base
  let (s, invalid) ← put s q "OGN-013" .base
  let s := s.fund p 4 (order := 1)
  let payment : RunePool.Payment := ⟨4, [.order]⟩
  let deploy (dest : ObjId) (cost : ObjId) : Action :=
    ⟨.player p, .playCard wolf payment [dest] none none (.withExtraObject .plain cost)⟩
  let ambush := deploy field pet
  let noCost : Action := ⟨.player p, .playCard wolf payment [field]⟩
  let toBase : Action := ⟨.player p, .playCard wolf payment [otherPet]⟩
  let (base, _) ← (step 100 s toBase).toOption
  let (closed, item) ← onChain s q "OGN-095"
  let closed := { closed with pending := [.chainPass p 0, .priority p] }
  let (played, events) ← (step 100 closed ambush).toOption
  let arrived ← (played.unitsAtOf field p).head?
  let plan ← (permanentPlayOptions s p wolf { price := .reduceEnergy 1 }).find? (fun choice =>
    choice.battlefield == some field && choice.extraObject == some pet)
  let (byEffect, fromEffect, effectEvents) ← applyReducedPermanent s p wolf plan
  return (s.unitsAtOf field p) == [pet] &&
    (legalFrameActions closed).contains ambush && !(step 100 closed noCost).isOk &&
    !(step 100 closed (deploy field invalid)).isOk &&
    !(step 100 closed (deploy otherField pet)).isOk &&
    !(step 100 closed toBase).isOk && (base.firstOf p .base "UNL-166").isSome &&
    (base.obj? otherPet).isNone && (base.obj? pet).isSome &&
    (played.cardDef? arrived).any (·.id.code == "UNL-166") &&
    (played.unitsAtOf field p) == [arrived] && played.tired arrived == some true &&
    (played.obj? arrived).any (·.paid) && (played.zone .chain).contains item &&
    killedForPlay events p pet && events.contains (.played p arrived) &&
    !(events.contains (.chosenBySpell p field)) &&
    (byEffect.unitsAtOf field p) == [fromEffect] && killedForPlay effectEvents p pet

-- A controlled Battlefield still requires Cruel Patron's cost, and another Unit at the
-- destination may stay in play when the chosen sacrifice is at the Base.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, patron) ← put (s.control p field) p "OGN-208" .hand
  let (s, stays) ← putAt s p "OGN-013" field
  let (s, costs) ← put s p "OGN-051" .base
  let funded := s.fund p 4
  let pay : RunePool.Payment := ⟨4, []⟩
  let missing : Action := ⟨.player p, .playCard patron pay [field]⟩
  let declared : Action :=
    ⟨.player p, .playCard patron pay [field] none none (.withExtraObject .plain costs)⟩
  let (played, events) ← (step 100 funded declared).toOption
  return (legalFrameActions funded).contains declared && !(step 100 funded missing).isOk &&
    killedForPlay events p costs && (played.obj? stays).isSome &&
    (played.unitsAtOf field p).any (fun id => (played.cardDef? id).any (·.id.code == "OGN-208"))

-- Blighted Battleaxe (UNL-019): at the end of its turn, the unit that did not conquer is dealt 4
-- and the Equipment is unattached
#guard tun fun s => do
  let (s1, u) ← putAt s s.me "OGN-088" s.bf0
  let (s2, g) ← put s1 s.me "UNL-019" .base
  let s3 := s2.modObj g (fun o => { o with attached := some u })
  let ts := s3.timedTriggers s.me .endOfTurn
  return ts.any (fun t => t.source == u && t.card == cid "UNL-019")

-- Cursed Sarcophagus (UNL-148): the units of its player's Trash are banished with it
#guard tun fun s => do
  let (s1, g) ← put s s.me "UNL-148" .hand
  let (s2, _) ← put s1 s.me "UNL-111" .trash
  let (s3, _) ← put s2 s.me "OGN-007" .trash
  let s4 ← play s3 s.me g
  return s4.countIn s.me .banishment "UNL-111" == 1 && s4.countIn s.me .trash "UNL-111" == 0

-- Frigid Jewel (UNL-074): the second card drawn in the turn gives a friendly unit +2 Might
#guard tun fun s => do
  let (s1, _) ← put s s.me "UNL-074" .base
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let (s3, _) ← put s2 s.me "UNL-111" .hand
  let a ← fire { s3 with drawLog := [(s.me, s3.turn)] } [Event.drew s.me]
  let b ← fire { s3 with drawLog := [(s.me, s3.turn), (s.me, s3.turn)] } [Event.drew s.me]
  let c ← fire { s3 with drawLog := [(s.me, s3.turn), (s.me, s3.turn), (s.me, s3.turn)] }
    [Event.drew s.me]
  return a.mightNow u == s3.mightNow u && c.mightNow u == s3.mightNow u &&
    b.mightNow u == (s3.mightNow u).map (· + 2)

-- Green Father (UNL-195) and Brush (UNL-T03): the Battlefield is replaced by Brush, with its units;
-- scoring there puts the old Battlefield back
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, u) ← putAt s1 s.me "UNL-111" bf
  let some tok := s2.tokenCard "Brush" | none
  let r := replaceBf tok s.me s2 bf
  let s3 := r.1
  let brush := (s3.zone .battlefieldZone).find? (fun b => (s3.cardDef? b).any (·.name == "Brush"))
  let some nb := brush | none
  let r2 := restoreBf s3 nb
  let s4 := r2.1
  return (s3.obj? u).any (·.loc == some nb) && s3.battlefields.length == s2.battlefields.length &&
    !(s3.battlefields.contains bf) &&
    (s4.battlefields.any (fun b => (s4.cardDef? b).any (·.id == cid "OGN-275"))) &&
    !(s4.battlefields.any (fun b => (s4.cardDef? b).any (·.name == "Brush"))) &&
    (s4.obj? u).any (fun o => o.loc.any (fun l => (s4.cardDef? l).any (·.id == cid "OGN-275")))

-- Heedless Resurrection declares both objects before paying. Each of Energy and Power
-- independently limits the unit in the player's Trash.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "UNL-142" .hand
  let (s, unit) ← put s p "OGN-015" .base
  let (s, target) ← put s p "OGN-074" .trash
  let (s, other) ← put s p "UNL-111" .trash
  let (s, tooMuchEnergy) ← put s p "OGN-088" .trash
  let (s, tooMuchPower) ← put s p "OGN-150" .trash
  let (s, opposing) ← put s q "UNL-111" .trash
  let s := s.rich p
  let pick := SpellPick.withExtraObject .plain unit
  let castChoice (target : ObjId) (cost : SpellPick := pick) : Action :=
    ⟨.player p, .playCard spell (payOf s spell) [target] none none cost⟩
  let legal := legalFrameActions s
  let (casted, events) ← (step 100 s (castChoice target)).toOption
  let item ← (casted.zone .chain).head?
  let paidUnit ← casted.firstOf p .trash "OGN-015"
  let d ← casted.cardDef? item
  let effect ← d.spellEffect
  let original ← casted.obj? item
  let retarget := spellChoicesWithShowOff casted p item d effect [none] none (some false)
    original.spellPick.paidKill
  let done := settleChain {} 12 casted
  return legal.contains (castChoice target) && legal.contains (castChoice other) &&
    !(legal.contains (castChoice target .plain)) &&
    [unit, opposing, tooMuchEnergy, tooMuchPower].all (fun id => !(legal.contains (castChoice id))) &&
    original.targets == [target] && original.spellPick.paidKill == some (unit, 4, 1) &&
    events.contains (.died paidUnit p) && events.contains (.chosenBySpell p target) &&
    !(events.contains (.chosenBySpell p unit)) &&
    (casted.zone (.player p .trash)).contains target &&
    retarget.contains (.plain, [other]) && !retarget.contains (.plain, [tooMuchEnergy]) &&
    !retarget.contains (.plain, [tooMuchPower]) &&
    done.countIn p .base "OGN-074" == 1 && done.countIn p .trash "UNL-111" == 1

-- Repeat declares two Trash targets against the same Kill cost and pays it once.
#guard tun fun s => do
  let p := s.me
  let (s, spell) ← put s p "UNL-142" .hand
  let (s, unit) ← put s p "UNL-003" .base
  let (s, first) ← put s p "UNL-111" .trash
  let (s, second) ← put s p "UNL-111" .trash
  let (s, expensive) ← put s p "OGN-135" .trash
  let s := (s.rich p).addTurnFx p .nextSpellRepeat
  let pick := SpellPick.withExtraObject (.withCosts (.thenRepeat .plain 1 .plain) false 1) unit
  let act (last : ObjId) : Action :=
    ⟨.player p, .playCard spell ⟨4, [.chaos, .chaos]⟩ [first, last] none none pick⟩
  let legal := legalFrameActions s
  let (casted, _) ← (step 100 s (act second)).toOption
  let done := settleChain {} 16 casted
  return legal.contains (act second) && !legal.contains (act expensive) &&
    done.countIn p .base "UNL-111" == 2 && done.countIn p .trash "UNL-003" == 1

-- Starhound can target a pet in its controller's Trash when its play trigger finalizes.
#guard tun fun s => do
  let p := s.me
  let (s, hound) ← put s p "UNL-167" .hand
  let (s, pet) ← put s p "VEN-007" .trash
  let (s, unit) ← put s p "UNL-111" .trash
  let (s, opposing) ← put s s.you "VEN-007" .trash
  let deciding ← castStop s p hound
  let candidates := (legalFrameActions deciding).filterMap (fun act => match act.kind with
    | .putTrigger _ [id] (.pay ..) => some id
    | _ => none)
  let done ← play s p hound [] { pick := (· == [pet]) }
  return candidates == [pet] && !candidates.contains opposing &&
    done.countIn p .hand "VEN-007" == s.countIn p .hand "VEN-007" + 1 &&
    (done.zone (.player p .trash)).contains unit

-- Undying Loyalty's declared target determines the Energy discount, never the Order Power.
#guard tun fun s => do
  let p := s.me
  let (s, spell) ← put s p "UNL-168" .hand
  let (s, pet) ← put s p "VEN-007" .trash
  let (s, common) ← put s p "OGN-010" .trash
  let (s, expensive) ← put s p "OGN-135" .trash
  let (s, rivalPet) ← put s s.you "VEN-007" .trash
  let s := s.fund p 2 0 0 0 0 0 1
  let cheap : RunePool.Payment := ⟨0, [.order]⟩
  let normal : RunePool.Payment := ⟨2, [.order]⟩
  let action (pay : RunePool.Payment) (target : ObjId) : Action :=
    ⟨.player p, .playCard spell pay [target]⟩
  let legal := legalFrameActions s
  let (casted, events) ← (step 100 s (action cheap pet)).toOption
  let (removed, _) ← moveObj casted pet (.player p .mainDeck)
  let revived := settleChain {} 12 casted
  let missed := settleChain {} 12 removed
  let nonPet ← cast s p spell normal [common]
  return legal.contains (action cheap pet) && legal.contains (action normal common) &&
    !legal.contains (action normal pet) && !legal.contains (action cheap common) &&
    !legal.contains (action ⟨0, []⟩ pet) && !legal.contains (action cheap expensive) &&
    !legal.contains (action cheap rivalPet) &&
    events.contains (.chosenBySpell p pet) && (casted.poolOf p).energy == 2 &&
    (casted.poolOf p).order == 0 && revived.countIn p .base "VEN-007" == 1 &&
    missed.countIn p .base "OGN-010" == 0 && (missed.zone (.player p .trash)).contains common &&
    nonPet.countIn p .base "OGN-010" == 1 && (nonPet.poolOf p).energy == 0

-- An effect-driven cast uses the same discount, once across declared Repeat executions.
#guard tun fun s => do
  let p := s.me
  let (s, spell) ← put s p "UNL-168" .hand
  let (s, first) ← put s p "VEN-007" .trash
  let (s, second) ← put s p "VEN-007" .trash
  let s := (s.fund p 6 0 0 0 0 0 2).addTurnFx p .nextSpellRepeat
  let price := EffectPlayPrice.alternateBase ⟨3, [.domain .order]⟩
  let (queued, item) ← queueLimitedSpell s p spell price .normal
  let plans := limitedSpellOptions queued p item price
  let totals := plans.filterMap (fun plan =>
    if plan.targets == [first, second] && plan.pick.hasExecutionChoices then some plan.cost
    else none)
  return totals == [⟨3, [.domain .order, .domain .order]⟩]

-- Blast Cone (UNL-133): when its player moves an enemy unit with an effect, it can stun it
#guard tun fun s => do
  let (s1, g) ← put s s.me "UNL-133" .base
  let (s2, e) ← putAt s1 s.you "UNL-111" s.bf0
  let a ← fire s2 [Event.movedByEffect s.me e]
  let b ← fire s2 [Event.movedByEffect s.you e]
  return ((a.obj? e).any (·.stunned)) && !((b.obj? e).any (·.stunned)) &&
    (a.tired g == some true)

-- Vex (UNL-150) stuns a ready Unit without exhausting it. Only the seat that
-- played it is prevented from moving it, and the restriction expires this turn.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, vex) ← putAt s q "UNL-150" bf
  let (s, card) ← put s p "OGN-052" .hand
  let ready := s.addTurnFx p .nextUnitReady
  let played ← play ready p card
  let unit ← played.firstOf p .base "OGN-052"
  let (other, _) := moveByEffect p (some bf) played unit q
  let (recalled, recalls) := recallFx false other unit
  let expired := { played with turn := played.turn + 1 }
  let swapped (actor : PlayerId) := swapPlaces played unit vex (some q) (some actor)
  let inactive ← play (recallFx false ready vex).1 p card
  let unmarked ← inactive.firstOf p .base "OGN-052"
  return (played.obj? unit).any (·.stunned) && played.tired unit == some false &&
    !moveOk played p unit (.battlefield bf) && moveOk expired p unit (.battlefield bf) &&
    (moveByEffect q (some bf) played unit p).2.isEmpty &&
    (other.obj? unit).any (·.loc == some bf) &&
    (swapped p).2.isEmpty && !(swapped q).2.isEmpty &&
    recalls.contains (.recalled unit) && (recalled.obj? unit).any (·.loc.isNone) &&
    (inactive.obj? unmarked).any (! ·.stunned) && !inactive.moveBlockedFor p unmarked

-- The restriction remembers the opponent that played the object. A teammate's
-- play does not fire it, and a Unit token played by an opponent does.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let other : PlayerId := ⟨3⟩
  let empty := GameState.empty { mode := .teamDuel, ruleSet := .coreOnly } labState.cards
  let s := { empty with
    phase := .main, turn := 2, active := some enemy,
    turnOrder := Mode.teamTurnOrder true, pending := [.priority enemy] }
  let (s, bf) ← putBf s p "OGN-275"
  let (s, _) ← putAt s p "UNL-150" bf
  let (s, friend) ← put s ally "OGN-052" .base
  let (s, unit) ← put s other "OGN-052" .base
  let (s, tokenEvents) := playUnitTokenAt s enemy "Recruit" none
  let [Event.tokenPlayed _ token] := tokenEvents | none
  let events := [.played ally friend, .played enemy unit] ++ tokenEvents
  let queued := (setController enemy s unit).1.withTriggers events
  let transferred := (setController other (setController other queued unit).1 token).1
  let (chain, _) ← (advance 100 transferred []).toOption
  let done := settleChain {} 12 chain
  let (left, gone) ← moveObj done unit (.player other .trash)
  let (reentered, fresh) ← moveObj left gone (.player other .base)
  return (done.obj? friend).any (! ·.stunned) && !done.moveBlockedFor ally friend &&
    [unit, token].all (fun id => (done.obj? id).any (·.stunned) &&
      done.moveBlockedFor enemy id && !done.moveBlockedFor other id) &&
    fresh != unit && !reentered.moveBlockedFor enemy fresh

-- Mageseeker Investigator (UNL-163): a Standard Move pays one Power for each arriving Unit
-- after the first. The declaration and selection do not spend or exhaust anything.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let dest := MoveDest.battlefield field
  let (s, _) ← putAt (s.control q field) q "UNL-163" field
  let (s, first) ← put s p "OGN-052" .base
  let (s, second) ← put s p "OGN-052" .base
  let (s, third) ← put s p "OGN-052" .base
  let (s, left) ← putBf s p "OGN-276"
  let s := s.fund p 1 2
  let onePower : Cost := ⟨0, [.domain .fury]⟩
  let twoPower : Cost := ⟨0, [.domain .fury, .domain .fury]⟩
  let send (t : GameState) (kind : ActionKind) := (step 100 t ⟨.player p, kind⟩).toOption
  let (one, _) ← send s (.standardMove first dest)
  let (quote, _) ← send s (.startGroupMove dest onePower)
  let (selectOne, _) ← send quote (.choose first)
  let (selectTwo, _) ← send selectOne (.choose second)
  let (cancelled, _) ← send selectTwo (.decide false)
  let (pair, _) ← send selectTwo (.decide true)
  let (quoteAll, _) ← send s (.startGroupMove dest twoPower)
  let (pickedFirst, _) ← send quoteAll (.choose first)
  let (pickedSecond, _) ← send pickedFirst (.choose second)
  let (pickedThird, _) ← send pickedSecond (.choose third)
  let (group, events) ← send pickedThird (.decide true)
  let (fixed, _) ← putAt s q "RAD-062" field
  return (one.poolOf p).fury == 2 && (one.obj? first).any (·.loc == some field) &&
    (send s (.startGroupMove dest Cost.zero)).isNone &&
    (send (s.fund p 1 1) (.startGroupMove dest twoPower)).isNone &&
    (send selectTwo (.choose third)).isNone && (send pickedSecond (.decide true)).isNone &&
    (selectTwo.poolOf p).fury == 2 && selectTwo.tired first == some false &&
    cancelled.pending == s.pending && cancelled.tired second == some false &&
    (pair.poolOf p).fury == 1 && (pair.obj? third).any (·.loc.isNone) &&
    (group.poolOf p).fury == 0 &&
    events.filterMap (fun | .standardMoved id _ => some id | _ => none) == [first, second, third] &&
    [first, second, third].all (fun id => (group.obj? id).any (fun o =>
      o.loc == some field && o.exhausted)) &&
    fixed.movementFee p [field, field, left, left] == ⟨1, [.any, .any]⟩

-- An instructed group can fund its fee with a Rune. Declining the projected payment leaves
-- resources and the Board alone, and a Unit whose move was prevented incurs no extra cost.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, _) ← putAt (s.control q bf) q "UNL-163" bf
  let (s, first) ← put s p "OGN-052" .base
  let (s, second) ← put s p "OGN-052" .base
  let (s, rune) ← put (s.fund p 0) p "OGN-007" .base
  let s := s.modObj rune (fun o => { o with runeDomain := some .fury, exhausted := false })
  let env : Env := { slots := [.obj bf] }
  let body := Effect.prim (.move (Selector.all .you .atBase [.ofType .unit]) (.at_ (.slot 0)))
  let resolve (t : GameState) := (advance 100 { t with
    pending := [.run p first env (.cons body .nil)] } []).toOption
  let answer (t : GameState) (yes : Bool) := (step 100 t ⟨.player p, .decide yes⟩).toOption
  let (question, _) ← resolve s
  let (choices, _) ← answer question true
  let .eitherDo _ _ _ (.fundMoveFee _ _ [.rune _ false] false)
    (.fundMoveFee _ _ [.rune _ true] false) _ :: _ := choices.pending | none
  let (staged, _) ← answer choices false
  let (declined, _) ← answer staged false
  let (moved, _) ← answer staged true
  let (prevented, _) ← resolve (s.addTurnFxOn p second .cannotMove)
  return (staged.poolOf p).total == 0 && (staged.zone (.player p .base)).contains rune &&
    declined.zone (.player p .base) == s.zone (.player p .base) &&
    (moved.poolOf p).spent == 1 && !(moved.zone (.player p .base)).contains rune &&
    [first, second].all (fun id => (moved.obj? id).any (fun o => o.loc == some bf && !o.exhausted)) &&
    (prevented.obj? first).any (·.loc == some bf) && (prevented.obj? second).any (·.loc.isNone) &&
    (prevented.zone (.player p .base)).contains rune

-- An allied Investigator never taxes its teammate's move, but an opposing one does.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let mate : PlayerId := ⟨1⟩
  let opponent : PlayerId := ⟨2⟩
  let s := GameState.empty { mode := .teamDuel, ruleSet := .coreOnly } labState.cards
  let (s, field) ← putBf s mate "OGN-275"
  let (s, watcher) ← putAt s mate "UNL-163" field
  let (s, _) ← putAt s mate "RAD-062" field
  let opposing := (setController opponent s watcher).1
  return s.movementFee p [field, field, field] == Cost.zero &&
    opposing.movementFee p [field, field, field] == ⟨0, [.any, .any]⟩

-- Azir, Sovereign (SFD-177) finalizes the group. The Vendetta FAQ uses Azir's
-- current Battlefield on resolution, which can change after finalization.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, azir) ← putAt s p "SFD-177" field
  let (s, _) ← putAt s s.you "UNL-163" field
  let (s, other) ← putBf s p "OGN-276"
  let add (t : GameState) := playUnitTokenAt t p "Recruit" none
  let (s, [.tokenPlayed _ first]) := add s | none
  let (s, [.tokenPlayed _ second]) := add s | none
  let (s, [.tokenPlayed _ spare]) := add s | none
  let ready := s.fund p 0 1
  let events := [Event.combatStarted field p]
  let launched ← fire ready events {
    pick := fun ids => ids.length == 2 && ids.contains first && ids.contains second }
  let single ← fire ready events { pick := (· == [spare]) }
  let skipped ← fire ready events { yes := false }
  let (waiting, _) ← (advance 100 (ready.withTriggers events) []).toOption
  let (queued, _) ← (step 100 waiting ⟨.player p, .putTrigger 0 [first, second] (.pay [])⟩).toOption
  let rerouted := settleChain {} 12 (moveByEffect p (some other) queued azir).1
  let stayed := settleChain {} 12 (recallFx false queued azir).1
  return [first, second].all (fun id => (launched.obj? id).any (·.loc == some field)) &&
    (launched.obj? spare).any (·.loc.isNone) && (launched.poolOf p).fury == 0 &&
    (single.obj? spare).any (·.loc == some field) && (single.poolOf p).fury == 1 &&
    (skipped.obj? first).any (·.loc.isNone) && (skipped.poolOf p).fury == 1 &&
    [first, second].all (fun id => (rerouted.obj? id).any (·.loc == some other)) &&
    (rerouted.poolOf p).fury == 1 && (stayed.obj? first).any (·.loc.isNone)

-- Amateur Recital (UNL-207) targets during finalization. Deflect is due then,
-- and the selected Unit is only moved after the Chain resolves.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, recital) ← putBf s p "UNL-207"
  let (s, target) ← putAt s q "UNL-150" s.bf0
  let (s, home) ← put s q "OGN-052" .base
  let s := (s.control p recital).fund p 0 1
  let before := s.withTriggers [.scored p recital false]
  let (waiting, _) ← (advance 100 before []).toOption
  let place : Action := ⟨.player p, .putTrigger 0 [target] (.pay [])⟩
  let invalid : Action := ⟨.player p, .putTrigger 0 [home] (.pay [])⟩
  let (declined, _) ← (step 100 waiting ⟨.player p, .putTrigger 0 [] .skip⟩).toOption
  let (queued, events) ← (step 100 waiting place).toOption
  return (step 100 (waiting.fund p 0) place).toOption.isNone &&
    (step 100 waiting invalid).toOption.isNone && (queued.poolOf p).fury == 0 &&
    (queued.obj? target).any (·.loc.isSome) && (declined.obj? target).any (·.loc.isSome) &&
    events.contains (.chosenByAbility p target) &&
    ((settleChain {} 12 queued).obj? target).any (·.loc.isNone)

-- Comparing a small unrestricted payment with the direct enumeration checks canonical payment
-- order. A large fee with enough Power of only one kind has one allocation.
#guard tun fun s => do
  let p := s.me
  let rich := (s.fund p 1 2 1).setPool p { energy := 1, fury := 2, calm := 1, any := 1 }
  let price : Cost := ⟨1, [.any, .any, .any]⟩
  let original := ((resolutionPowerChoices [] price.power).filterMap (fun power =>
    let pay : Cost := ⟨price.energy, power⟩
    (rich.spendSymbols p pay false).map (fun pool => (pay, pool)))).eraseDupsBy (fun a b => a.2 == b.2)
  let large := s.fund p 0 20
  let due : Cost := ⟨0, List.replicate 19 .any⟩
  return rich.symbolPayments p price [] false == original &&
    (large.symbolPayments p due [] false).map (fun (_, pool) => pool.fury) == [1]

-- Alpha Strike locks the targets, splits the Unit's Might across Battlefields, and
-- earns XP on the Chain after lethal damage actually kills both Units.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, other) ← putBf s q "OGN-276"
  let (s, dealer) ← put s p "OGN-052" .base
  let (s, first) ← putAt s q "OGN-052" s.bf0
  let (s, second) ← putAt s q "OGN-052" other
  let (s, alpha) ← put s p "UNL-192" .hand
  let ready := ((s.control q s.bf0).control q other).modObj dealer
    (fun o => { o with baseMightThisTurn := some 3 })
  let ready := (ready.modObj first (fun o => { o with baseMightThisTurn := some 1 })).fund p 3 0 1
  let ready := ready.addTurnFx p (.nextSpellBonus 4)
  let pay : RunePool.Payment := ⟨3, [.calm]⟩
  let action : Action := ⟨.player p, .playCard alpha pay [dealer, first, second]⟩
  let (queued, _) ← (step 100 ready action).toOption
  let killed := settleChain {} 32 queued
  let prevention := ready.addTurnFxOn q first (.preventDamage 1)
  let saved := prevention.addTurnFxOn q second .saveOnce
  let (savedQueued, _) ← (step 100 saved action).toOption
  let spared := settleChain {} 32 savedQueued
  let body : Action := ⟨.player p, .playCard alpha ⟨3, [.body]⟩ [dealer, first, second]⟩
  let fury : Action := ⟨.player p, .playCard alpha ⟨3, [.fury]⟩ [dealer, first, second]⟩
  return (legalFrameActions (ready.fund p 3 0 0 1)).contains body &&
    !(legalFrameActions (ready.fund p 3 1)).contains fury &&
    queued.xpOf p == s.xpOf p && killed.xpOf p == s.xpOf p + 2 &&
    (killed.obj? first).isNone && (killed.obj? second).isNone &&
    !(killed.turnFx.any (fun note => match note.kind with
      | .linkedDamageDeath .. => true | _ => false)) &&
    (spared.obj? first).any (·.damage == 0) &&
    (spared.obj? second).any (fun o => o.loc.isNone && o.exhausted && o.damage == 0) &&
    spared.xpOf p == s.xpOf p

-- The chosen Unit is the damage source, so spell and ability damage protection
-- does not prevent its hit (CR 418.6.b.3).
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, dealer) ← put s p "OGN-052" .base
  let (s, hierophant) ← putAt s q "VEN-025" s.bf0
  let s ← (List.range 7).foldlM (fun t _ =>
    (put t q "OGN-042" .base).map Prod.fst) s
  let (s, alpha) ← put s p "UNL-192" .hand
  let (s, disintegrate) ← put s p "OGN-005" .hand
  let s := (s.control q s.bf0).modObj dealer (fun o => { o with baseMightThisTurn := some 5 })
  let spell ← cast (s.fund p 4) p disintegrate ⟨4, []⟩ [hierophant]
  let unit ← cast (s.fund p 3 0 1) p alpha ⟨3, [.calm]⟩ [dealer, hierophant]
  return (s.activeMods hierophant).contains .noEnemyEffectDamage &&
    (spell.obj? hierophant).any (·.damage == 0) && (unit.obj? hierophant).isNone &&
    unit.xpOf p == s.xpOf p + 1

-- The chosen dealer can lose Might after finalization. Take exactly the maximum number of
-- legal targets at resolution and deal the new amount to those targets (CR 355.14.h.1).
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, dealer) ← put s p "OGN-052" .base
  let (s, first) ← putAt s q "OGN-052" field
  let (s, second) ← putAt s q "OGN-052" field
  let (s, third) ← putAt s q "OGN-052" field
  let (s, alpha) ← put s p "UNL-192" .hand
  let (s, frigid) ← put s q "SFD-066" .hand
  let basic := ((s.control q field).fund p 3 0 1).fund q 2
  let ready := basic.modObj dealer (fun o => { o with baseMightThisTurn := some 3 })
  let pay : RunePool.Payment := ⟨3, [.calm]⟩
  let action : Action := ⟨.player p, .playCard alpha pay [dealer, first, second, third]⟩
  let (queued, _) ← (step 100 ready action).toOption
  let (answer, _) ← (step 100 queued ⟨.player p, .pass⟩).toOption
  let reduced ← cast answer q frigid ⟨2, []⟩ [dealer] { obj := (· == third) }
  return !(legalFrameActions basic).contains action &&
    (legalFrameActions ready).contains action &&
    [first, second].all (fun id => (reduced.obj? id).any (·.damage == 0)) &&
    (reduced.obj? third).any (·.damage == 1) && reduced.xpOf p == s.xpOf p &&
    !(reduced.turnFx.any (fun note => match note.kind with
      | .linkedDamageDeath .. => true | _ => false))

-- Unleashed FAQ: moving two of Alpha Strike's targets to Base preserves their
-- targeting relationships. Leaving the Board both loses the relationships and
-- makes Repulse legal against the spell choosing the sole remaining friendly Unit.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, dealer) ← put s p "OGN-052" .base
  let (s, first) ← putAt s q "OGN-052" field
  let (s, second) ← putAt s q "OGN-052" field
  let (s, third) ← putAt s q "OGN-052" field
  let (s, alpha) ← put s p "UNL-192" .hand
  let (s, repulse) ← put s q "UNL-106" .hand
  let ready := (((s.control q field).fund p 3 0 1).fund q 1 0 0 1).modObj dealer
    (fun o => { o with baseMightThisTurn := some 3 })
  let (queued, _) ← (step 100 ready ⟨.player p,
    .playCard alpha ⟨3, [.calm]⟩ [dealer, first, second, third]⟩).toOption
  let item ← (queued.zone .chain).head?
  let (answer, _) ← (step 100 queued ⟨.player p, .pass⟩).toOption
  let moved := (moveByEffect q none (moveByEffect q none answer second).1 third).1
  let (left, _) ← moveObj moved second (.player q .hand)
  let (gone, _) ← moveObj left third (.player q .hand)
  let counter : Action := ⟨.player q, .playCard repulse ⟨1, [.body]⟩ [first, item]⟩
  let (stacked, _) ← (step 100 gone counter).toOption
  let done := settleChain {} 32 stacked
  let resolving := settleChain {} 32 moved
  return !(legalFrameActions moved).contains counter && (legalFrameActions gone).contains counter &&
    done.xpOf p == s.xpOf p && (done.obj? first).any (·.damage == 0) &&
    resolving.xpOf p == s.xpOf p + 1 && (resolving.obj? first).isNone &&
    [second, third].all (fun id => (resolving.obj? id).any (fun o => o.loc.isNone && o.damage == 0))

-- Undying Legion (UNL-025): with another card played this turn, it is played from the Trash
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-111" .hand
  let (s2, l) ← put s1 s.me "UNL-025" .trash
  let before := activate s2 s.me l (firstAct s2 l)
  let s3 ← play s2 s.me c
  let s4 ← activate s3 s.me l (firstAct s3 l) [] ⟨3, [.fury]⟩
  return before.isNone && s4.countIn s.me .trash "UNL-025" == 0 && s4.countIn s.me .base "UNL-025" == 1

-- Xerath, Freed (UNL-026): activate at a Battlefield with Fury Power and damage a Unit
-- at either location, even if Xerath is moved to Base before resolution.
#guard tun fun s => do
  let (s1, xerath) ← putAt s s.me "UNL-026" s.bf0
  let (s2, home) ← put s1 s.me "UNL-026" .base
  let (s3, foe) ← put s2 s.you "OGN-088" .base
  let (s4, flash) ← put s3 s.me "OGS-011" .hand
  let funded := s4.fund s.me 2 1
  let pay : RunePool.Payment := ⟨0, [.fury]⟩
  let (queued, _) ← (step 100 funded ⟨.player s.me, .activate xerath 0 pay [foe]⟩).toOption
  let resolved ← cast queued s.me flash (payOf queued flash) [xerath]
  return !(activatable funded s.me home 0 pay [foe] true) &&
    !(activatable funded s.me xerath 0 ⟨0, []⟩ [foe] true) &&
    (queued.poolOf s.me).fury == 0 && queued.tired xerath == some true &&
    resolved.where? xerath == some (.player s.me .base) &&
    (resolved.obj? foe).any (·.damage == 3)

-- Ultrasoft Poro (UNL-160): both Deflect Birds have a normal Unit token destination,
-- even when the Poro moves to Base in response.
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt (s1.control s.me bf) s.me "OGN-088" bf
  let (s3, poro) ← putAt s2 s.me "UNL-160" s.bf0
  let (s4, home) ← put s3 s.me "UNL-160" .base
  let (s5, flash) ← put s4 s.me "OGS-011" .hand
  let (queued, _) ← (step 100 (s5.rich s.me) ⟨.player s.me, .activate poro 0 ⟨0, []⟩ []⟩).toOption
  let atBase ← play queued s.me flash [poro]
  let atField ← play queued s.me flash [poro] { yes := false }
  let birds := (atField.zone .battlefieldZone).filter (fun id =>
    (atField.cardDef? id).any (·.name == "Bird"))
  return !(activatable s5 s.me home 0 ⟨0, []⟩ [] true) &&
    atBase.where? poro == some (.player s.me .base) &&
    atBase.countNamed s.me .base "Bird" == 2 && birds.length == 2 &&
    birds.all (fun bird => (atField.obj? bird).any (·.loc == some bf) &&
      atField.mightNow bird == some 1 && atField.deflectCost s.you [bird] == 1 &&
      atField.tired bird == some true)

-- Virtuoso (UNL-181): four spells banished with it go to the Trash, and its player channels
-- and draws
#guard tun fun s => do
  let (s1, v) ← put s s.me "UNL-181" .legendZone
  let (s2, a) ← put s1 s.me "UNL-159" .banishment
  let (s3, b) ← put s2 s.me "UNL-159" .banishment
  let (s4, c) ← put s3 s.me "UNL-159" .banishment
  let s5 := [a, b, c].foldl (fun t x => t.modObj x (fun o => { o with banishedWith := some v })) s4
  let (s6, sp) ← put s5 s.me "UNL-159" .hand
  let (s7, sp') ← moveObj s6 sp .chain
  let s8 := s7.modObj sp' (fun o => { o with energyPaid := 4, playedTurn := some s7.turn })
  let s8 := { s8 with playLog := s8.recordPlayEvent s8.playLog (.played s.me sp') }
  let r ← fire s8 [.spellResolved s.me sp']
  return r.countIn s.me .trash "UNL-159" == 4 && r.countIn s.me .banishment "UNL-159" == 0

-- Audit fixes: Loyal Poro (UNL-156) draws when it did NOT die alone (the opposite of Lonely Poro)
#guard tun fun s => do
  let (s1, x) ← putAt s s.me "UNL-156" s.bf0
  let (s3, _) ← putAt s1 s.me "OGN-051" s.bf0
  let die (st : GameState) (u : ObjId) : Option GameState :=
    let (st1, evs) := killObj st u
    fire st1 evs
  let alone ← die s1 x
  let company ← die s3 x
  return alone.handN s.me == s1.handN s.me && company.handN s.me == s3.handN s.me + 1

-- Friendly company for simultaneous spell and Cleanup deaths comes from the same starting board.
#guard tun fun labState => do
  let s := unleashedTeamMain labState
  let p : PlayerId := ⟨0⟩
  let partner : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let (s, field) ← putBf s p "OGN-275"
  let (s, first) ← putAt (s.control p field) p "UNL-156" field
  let (s, second) ← putAt s partner "SFD-036" field
  let (s, isolated) ← put s enemy "UNL-156" .base
  let (s, spell) ← put s p "UNL-180" .hand
  let (s, _) ← put s p "OGN-001" .mainDeck
  let (s, _) ← put s partner "OGN-001" .mainDeck
  let (s, _) ← put s enemy "OGN-001" .mainDeck
  let (afterSpell, events) ← applyPrim s p spell {} (.kill (Selector.all .any .anywhere [.ofType .unit]))
  let dealt := [first, second, isolated].foldl
    (fun st id => st.modObj id (fun o => { o with damage := 9 })) s
  let (afterCleanup, _) ← cleanupResolveDeathGroup dealt
  let alone (st : GameState) (owner : PlayerId) (code : String) : Option Bool := do
    let id ← st.firstOf owner .trash code
    return st.hasTurnMark id .diedAlone
  let observes (st : GameState) : Bool :=
    alone st p "UNL-156" == some false && alone st partner "SFD-036" == some false &&
    alone st enemy "UNL-156" == some true
  let settled ← fire afterSpell events
  return !(s.unitIsAloneAt first) && !(s.unitIsAloneAt second) && observes afterSpell &&
    observes afterCleanup && settled.handN p == s.handN p + 1 &&
    settled.handN partner == s.handN partner && settled.handN enemy == s.handN enemy

-- Heroic Charge (UNL-155): +1 Might to a friendly unit and stun an enemy at its location
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-155" .hand
  let (s2, u) ← putAt s1 s.me "UNL-111" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-088" s.bf0
  let s4 ← play s3 s.me c [u, e]
  return (s4.obj? e).any (·.stunned) && s4.mightNow u == (s3.mightNow u).map (· + 1)

-- Flurry's mode is selected when cast. Its Birds use normal Unit token destinations.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, spell) ← put (s.control p field) p "UNL-044" .hand
  let (s, _) ← putAt s p "OGN-013" field
  let funded := s.rich p
  let payment := payOf funded spell
  let make : Action := ⟨.player p, .playCard spell payment [] none none (.mode 1)⟩
  let (waiting, _) ← (step 100 funded make).toOption
  let base := settleChain {} 16 waiting
  let deployed := settleChain { yes := false } 16 waiting
  let birds := deployed.inPlay.filter (fun id => (deployed.cardDef? id).any (·.id == cid "UNL-T02"))
  let (s, draw) ← put (funded.rich q) q "UNL-103" .hand
  let opponentTurn := { s with active := some q, pending := [.priority q] }
  let (stacked, _) ← (step 100 opponentTurn
    ⟨.player q, .playCard draw ⟨2, []⟩ [] none none (.mode 1)⟩).toOption
  let target ← (stacked.zone .chain).head?
  let (reacting, _) ← (step 100 stacked ⟨.player q, .pass⟩).toOption
  let counter : Action := ⟨.player p, .playCard spell payment [target] none none (.mode 0)⟩
  let (casting, _) ← (step 100 reacting counter).toOption
  let resolved := settleChain {} 16 casting
  return waiting.countIn p .base "UNL-T02" == 0 && base.countIn p .base "UNL-T02" == 4 &&
    birds.length == 4 && birds.all (fun id => (deployed.obj? id).any (·.loc == some field) &&
      deployed.mightNow id == some 1 && deployed.deflectOf id == 1 && deployed.tired id == some true) &&
    !(step 100 funded ⟨.player p, .playCard spell payment [] none none (.mode 0)⟩).isOk &&
    !(step 100 reacting ⟨.player p, .playCard spell payment [target] none none (.mode 1)⟩).isOk &&
    (resolved.zone .chain).isEmpty && resolved.countIn q .trash "UNL-103" == 1 &&
    resolved.zone (.player q .hand) == reacting.zone (.player q .hand) &&
    resolved.countIn p .base "UNL-T02" == 0

-- Gutter Palace pays for its activation before anyone can respond.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, palace) ← put (s.control p field) p "UNL-088" .base
  let (s, _) ← putAt s p "OGN-013" field
  let noHand := s.setZone (.player p .hand) []
  let (s, chosen) ← put noHand p "OGN-010" .hand
  let (s, keep) ← put s p "OGN-013" .hand
  let activation : Action := ⟨.player p, .activate palace 1 ⟨0, []⟩ [] [chosen]⟩
  let missing : Action := ⟨.player p, .activate palace 1 ⟨0, []⟩ []⟩
  let (waiting, events) ← (step 100 s activation).toOption
  let item ← (waiting.zone .chain).head?
  let resolved := settleChain { yes := false } 12 waiting
  let countered := settleChain {} 12 (counterObj waiting item).1
  let bird ← resolved.inPlay.find? (fun id => (resolved.cardDef? id).any (·.id == cid "UNL-T02"))
  let discarded ← waiting.firstOf p .trash "OGN-010"
  return !(step 100 noHand missing).isOk && !(step 100 s missing).isOk &&
    (legalFrameActions s).contains activation && waiting.tired palace == some true &&
    waiting.zone (.player p .hand) == [keep] && events.contains (.discarded p discarded true) &&
    waiting.countIn p .base "UNL-T02" == 0 && (resolved.obj? bird).any (·.loc == some field) &&
    resolved.deflectOf bird == 1 && resolved.tired bird == some true &&
    countered.tired palace == some true && countered.zone (.player p .hand) == [keep] &&
    countered.countIn p .trash "OGN-010" == 1 && countered.countIn p .base "UNL-T02" == 0

-- Gutter Palace wins before Hold or Draw and counts only Units the active seat controls.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let init := GameState.empty { labState.config with mode := Mode.teamDuel } labState.cards
  let s := { init with
    turnOrder := Mode.teamTurnOrder true, active := some p,
    phase := .awaken, pending := [.phase .beginning, .phase .main, .priority p] }
  let (s, first) ← putBf s p "OGN-275"
  let (s, second) ← putBf s ally "OGN-275"
  let (s, palace) ← put (s.control p first |>.control p second) p "UNL-088" .base
  let (s, _) ← putAt s ally "OGN-013" first
  let three ← [first, first, second].foldlM (fun g bf => (putAt g p "OGN-013" bf).map Prod.fst) s
  let (field, _) ← putAt three p "OGN-013" second
  let (base, _) ← put three p "OGN-013" .base
  let (fifth, _) ← putAt field p "OGN-013" second
  let hand (g : GameState) (count : Nat) :=
    (List.range count).foldlM (fun t _ => (put t p "OGN-010" .hand).map Prod.fst) g
  let ready ← hand field 4
  let baseOnly ← hand base 4
  let fiveUnits ← hand fifth 4
  let threeCards ← hand field 3
  let fiveCards ← hand field 5
  let triggered (g : GameState) (seat : PlayerId) :=
    (g.timedTriggers seat .beginning).any (·.source == palace)
  let (waiting, events) ← (advance 100 ready []).toOption
  let won := settleChain {} 12 waiting
  return triggered ready p && !triggered ready ally && !triggered baseOnly p &&
    !triggered fiveUnits p && !triggered threeCards p && !triggered fiveCards p &&
    events == [.phaseStarted p .beginning] && waiting.result.isNone &&
    won.result == some (.won [p, ally]) && won.points == ready.points &&
    won.zone (.player p .hand) == ready.zone (.player p .hand) && won.pending.isEmpty

-- Walking Roost lets its controller target one enemy seat. The selected seat chooses the location.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let firstEnemy : PlayerId := ⟨2⟩
  let chosen : PlayerId := ⟨3⟩
  let init := GameState.empty { labState.config with mode := Mode.teamDuel } labState.cards
  let s := { init with
    turnOrder := Mode.teamTurnOrder true, active := some p,
    phase := .main, pending := [.priority p] }
  let (s, field) ← putBf s chosen "OGN-275"
  let (s, _) ← putAt (s.control chosen field) chosen "OGN-013" field
  let (s, roost) ← put (s.fund p 5) p "UNL-130" .hand
  let (choosing, _) ← (step 100 s ⟨.player p, .playCard roost ⟨5, []⟩ []⟩).toOption
  let pick (q : PlayerId) : Action := ⟨.player p, .putTrigger 0 [] (.pay [] none (some q))⟩
  let (waiting, _) ← (step 100 choosing (pick chosen)).toOption
  let item ← (waiting.zone .chain).head?
  let rec pass : Nat → GameState → Option GameState
    | 0, _ => none
    | n + 1, g => match g.pending with
      | .chainPass seat _ :: _ => (step 100 g ⟨.player seat, .pass⟩).toOption.bind (pass n ∘ Prod.fst)
      | _ => some g
  let placing ← pass 8 waiting
  let (deployed, _) ← (step 100 placing ⟨.player chosen, .decide false⟩).toOption
  let bird ← deployed.inPlay.find? (fun id => (deployed.cardDef? id).any (·.id == cid "UNL-T02"))
  return ((legalFrameActions choosing).contains (pick firstEnemy)) &&
    !(step 100 choosing (pick ally)).isOk && !(step 100 choosing (pick p)).isOk &&
    (waiting.obj? item).any (·.targetPlayer == some chosen) &&
    !(step 100 placing ⟨.player p, .decide false⟩).isOk &&
    (deployed.obj? bird).any (fun o => o.loc == some field && o.controller == chosen) &&
    (deployed.inPlay.filter (fun id => (deployed.cardDef? id).any (·.id == cid "UNL-T02"))) == [bird]

-- Carrion Dredger's Deathknell plays the Bird at Base even with an available Battlefield.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s q "OGN-275"
  let (s, victim) ← putAt (s.control q field) q "UNL-153" field
  let (s, kill) ← put s p "OGS-012" .hand
  let done ← play s p kill [victim]
  let bird ← done.firstOf q .base "UNL-T02"
  return done.countIn q .trash "UNL-153" == 1 && done.countIn q .base "UNL-T02" == 1 &&
    done.mightNow bird == some 1 &&
    done.deflectOf bird == 1 && done.tired bird == some true && done.where? bird == some (.player q .base)

-- Trapping Grounds and Yeti Brawler require three excess damage in the Combat of the Conquer.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let other := s.bf0
  let (s, trapping) ← putBf s q "UNL-217"
  let (s, mover) ← put s p "OGN-010" .base
  let fight (field : ObjId) (might : Nat) := do
    let (g, attacker) ← putAt s p "UNL-018" field
    let (g, defender) ← putAt g q "OGN-013" field
    let g := (g.control q field).modObj attacker (fun o => { o with baseMightThisTurn := some might })
    let (g, _) ← (advance 100 (g.inCombatAt field p) []).toOption
    let (g, _) ← (step 100 g ⟨.player p, .assignPick defender⟩).toOption
    let (g, _) ← (step 100 g ⟨.player p, .assignDone⟩).toOption
    let (g, _) ← (step 100 g ⟨.player q, .assignPick attacker⟩).toOption
    let (g, events) ← (step 100 g ⟨.player q, .assignDone⟩).toOption
    return (settleChain {} 16 g, events)
  let (three, hit) ← fight trapping 5
  let (two, miss) ← fight trapping 4
  let (previous, _) ← fight other 7
  let (g, _) ← (step 100 previous ⟨.player p, .standardMove mover (.battlefield trapping)⟩).toOption
  let (g, _) ← (step 100 g ⟨.player p, .pass⟩).toOption
  let (g, openConquest) ← (step 100 g ⟨.player q, .pass⟩).toOption
  let after := settleChain {} 16 g
  let cards (x : GameState) := (x.countIn p .base "UNL-T02", x.countNamed p .base "Gold")
  let bird ← three.firstOf p .base "UNL-T02"
  return hit.contains (.scored p trapping true) && miss.contains (.scored p trapping true) &&
    openConquest.contains (.scored p trapping true) && cards three == (1, 2) && cards two == (0, 0) &&
    cards previous == (0, 2) && cards after == (0, 2) && three.deflectOf bird == 1 &&
    three.tired bird == some true && three.mightNow bird == some 1

-- Piltover Enforcer can be declined. Acceptance exhausts the Legend during finalization.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, legend) ← put s p "UNL-187" .legendZone
  let (s, unit) ← put s p "OGN-010" .base
  let s := (s.tire unit).addTurnFxOn p field (.excessDamage 3)
  let combat : CombatParticipation := { battlefield := field, attacker := p, defender := s.you, units := [] }
  let ready := { s with combat := some combat, pending := [.combatFinish field] }
  let (choosing, _) ← (advance 100 (ready.withTriggers [.scored p field true]) []).toOption
  let accept : Action := ⟨.player p, .putTrigger 0 [unit]⟩
  let decline : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (waiting, _) ← (step 100 choosing accept).toOption
  let (declined, _) ← (step 100 choosing decline).toOption
  let item ← (waiting.zone .chain).head?
  let countered := settleChain {} 12 (counterObj waiting item).1
  let resolved := settleChain {} 12 waiting
  return (legalFrameActions choosing).contains accept && !(step 100 (choosing.tire legend) accept).isOk &&
    (waiting.obj? item).any (·.targets == [unit]) && waiting.tired legend == some true &&
    waiting.tired unit == some true && resolved.tired unit == some false &&
    declined.tired legend == some false && declined.tired unit == some true &&
    countered.tired legend == some true && countered.tired unit == some true

-- Sprite Burst offers a separate legal location for each ready Sprite.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, _) ← putAt (s.control p field) p "OGN-013" field
  let (s, burst) ← put (s.fund p 5) p "UNL-069" .hand
  let (s, _) ← (step 100 s ⟨.player p, .playCard burst ⟨5, []⟩ []⟩).toOption
  let (s, _) ← (step 100 s ⟨.player p, .pass⟩).toOption
  let (placing, _) ← (step 100 s ⟨.player s.you, .pass⟩).toOption
  let (next, first) ← (step 100 placing ⟨.player p, .decide true⟩).toOption
  let (done, second) ← (step 100 next ⟨.player p, .decide false⟩).toOption
  let base ← done.firstOf p .base "TKN-Sprite"
  let deployed ← (done.unitsAt field).find? (fun id => (done.cardDef? id).any (·.id == cid "TKN-Sprite"))
  let ready (id : ObjId) := done.tired id == some false && done.hasKw id .temporary &&
    done.mightNow id == some 3
  return first.contains (.tokenPlayed p base) && second.contains (.tokenPlayed p deployed) &&
    ready base && ready deployed

-- Bashful Bloom counts allied and gained Temporary when pricing the activation.
-- Losing a counted Unit in response leaves the payment and token play in place.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let s := GameState.empty { labState.config with mode := Mode.teamDuel } labState.cards
  let s := { s with
    active := some p, turnOrder := Mode.teamTurnOrder true, phase := .main, pending := [.priority p] }
  let (s, field) ← putBf s p "OGN-275"
  let (s, _) ← putAt (s.control p field) p "OGN-013" field
  let (s, legend) ← put (s.fund p 4) p "UNL-189" .legendZone
  let (s, _) ← put s p "UNL-078" .base
  let (s, marked) ← put s p "OGN-010" .base
  let withEnemy := createOne (cid "TKN-Sprite") enemy none true s
  let withAlly := createOne (cid "TKN-Sprite") ally none true withEnemy
  let withKeyword := withAlly.modObj marked (fun o =>
    { o with tempKws := (⟨.temporary, .none⟩, .never) :: o.tempKws })
  let activation (cost : Nat) : Action := ⟨.player p, .activate legend 0 ⟨cost, []⟩ []⟩
  let paid (g : GameState) (cost : Nat) := (legalFrameActions g).contains (activation cost)
  let many := (List.range 3).foldl (fun g _ => createOne (cid "TKN-Sprite") p none true g) withKeyword
  let (waiting, _) ← (step 100 withKeyword (activation 2)).toOption
  let (removed, _) := killObj waiting marked
  let done := settleChain { yes := false } 16 removed
  let sprite ← (done.unitsAt field).find? (fun id => (done.cardDef? id).any (·.id == cid "TKN-Sprite"))
  return paid withEnemy 4 && paid withAlly 3 && paid withKeyword 2 && paid many 0 &&
    !paid withKeyword 1 && !paid withKeyword 3 && !(step 100 withKeyword (activation 3)).isOk &&
    !(step 100 (withKeyword.tire legend) (activation 2)).isOk &&
    waiting.poolOf p == { energy := 2 } && waiting.tired legend == some true &&
    done.poolOf p == waiting.poolOf p && done.tired sprite == some false &&
    done.mightNow sprite == some 3 && done.hasKw sprite .temporary

-- At Beginning, old Sprites expire. Fountain's Deathknell and Sprite Queen create fresh ready ones.
#guard tun fun s => do
  let p := s.me
  let (s, fountain) ← put s p "UNL-078" .hand
  let (s, queen) ← put s p "UNL-084" .hand
  let placed ← play s p fountain
  let stocked ← play placed p queen
  let sprites (g : GameState) := (g.zone (.player p .base)).filter (fun id =>
    (g.cardDef? id).any (·.id == cid "TKN-Sprite"))
  let old := sprites stocked
  let (waiting, events) ← (advance 100 { stocked with pending := [.phase .beginning, .priority p] } []).toOption
  let done := settleChain {} 16 waiting
  let fresh := sprites done
  return (sprites placed).length == 1 && old.length == 2 && fresh.length == 2 &&
    events.contains (.phaseStarted p .beginning) && done.countIn p .trash "UNL-078" == 1 &&
    done.countIn p .base "UNL-084" == 1 &&
    old.all (fun id => (done.obj? id).isNone) &&
    fresh.all (fun id => done.tired id == some false && done.hasKw id .temporary && done.mightNow id == some 3)

-- Back Off (UNL-042): played from the hand, it draws 1
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-042" .hand
  let (s2, e) ← putAt s1 s.you "OGN-088" s.bf0
  let s3 ← play s2 s.me c [e]
  return (s3.obj? e).any (·.stunned) && s3.handN s.me == s2.handN s.me

-- A facedown Back Off still stuns the target, and the player keeps their current hand.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, spell) ← put (s.control p field) p "UNL-042" .hidden
  let s := s.modObj spell (fun o => { o with hiddenAt := some field, hiddenTurn := some 0 })
  let (s, target) ← putAt s s.you "OGN-088" field
  let (casting, _) ← (step 100 (s.fund p 0) ⟨.player p, .activate spell 1 ⟨0, []⟩ [target]⟩).toOption
  let resolved := settleChain {} 12 casting
  return resolved.handN p == s.handN p && (resolved.obj? target).any (·.stunned)

-- Sacrifice (UNL-173): draw 2 and channel one rune (not two)
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-173" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let big := s2.modObj u (fun o => { o with mightMods := [{ amount := 9, ends := .never }] })
  let s3 ← play big s.me c [u]
  return s3.countIn s.me .trash "UNL-111" == 1

#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-173" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let big := s2.modObj u (fun o => { o with mightMods := [{ amount := 9, ends := .never }] })
  let s3 ← play big s.me c [u]
  let deck (st : GameState) : Nat := (st.zone (.player s.me .runeDeck)).length
  return deck s3 + 1 == deck big

#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-173" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let big := s2.modObj u (fun o => { o with mightMods := [{ amount := 9, ends := .never }] })
  let s3 ← play big s.me c [u]
  return s3.handN s.me == big.handN s.me + 1

-- Ashe, Focused (UNL-169): when played, a card from the opponent's hand is banished with it
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-169" .hand
  let (s2, _) ← put s1 s.you "OGN-007" .hand
  let s3 ← play s2 s.me c
  return s3.countIn s.you .banishment "OGN-007" == 1 && s3.countIn s.you .hand "OGN-007" == 0


-- Green Father (UNL-195): when its player conquers, it may exhaust to replace that Battlefield by
-- Brush (the Battlefield is picked while the effect resolves)
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, g) ← put s1 s.me "UNL-195" .legendZone
  let s3 := s2.modObj bf (fun o => { o with scored := [s.me] })
  let r ← fire s3 [Event.scored s.me bf true]
  return (r.zone .battlefieldZone).any (fun b => (r.cardDef? b).any (·.name == "Brush")) &&
    !((r.zone .battlefieldZone).contains bf) && r.tired g == some true

-- Determined Sentry (UNL-111): it cannot move to the Base; an ordinary unit can
#guard tun fun s => do
  let (s1, u) ← putAt s s.me "UNL-111" s.bf0
  let (s2, v) ← putAt s1 s.me "OGN-088" s.bf0
  return !moveOk s2 s.me u .base && moveOk s2 s.me v .base

-- Abandon returns the Spell and opens a private Predict decision for the printed top card.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let deck := Zone.player p .mainDeck
  let (s, spell) ← put s p "UNL-131" .hand
  let (s, target) ← onChain s q "OGN-004"
  let first ← (s.zone deck).head?
  let (waiting, _) ← (step 100 (s.rich p) ⟨.player p, .playCard spell (payOf s spell) [target]⟩).toOption
  let chooser ← match waiting.pending.head? with
    | some (.chainPass chooser _) => some chooser
    | _ => none
  let (passing, _) ← (step 100 waiting ⟨.player chooser, .pass⟩).toOption
  let other ← match passing.pending.head? with
    | some (.chainPass other _) => some other
    | _ => none
  let ((predicting, _), disclosures) ←
    (stepWithDisclosures 100 passing ⟨.player other, .pass⟩).toOption
  let (kept, _) ← (step 100 predicting ⟨.player p, .predictPick first false⟩).toOption
  let (recycled, _) ← (step 100 predicting ⟨.player p, .predictPick first true⟩).toOption
  return predicting.handN q == s.handN q + 1 && predicting.countIn q .trash "OGN-004" == 0 &&
    disclosures.any (fun d => d.visibleTo p && !d.visibleTo q) &&
    (kept.zone deck).head? == some first && (recycled.zone deck).getLast? == some first

-- Frisky Hunter (UNL-033) and Lord Broadmane (UNL-012): played to the Base, "here" is the Base
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-033" .hand
  let s2 ← play s1 s.me c
  return s2.countNamed s.me .base "Bird" == 1

#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-012" .hand
  let (s2, u) ← put s1 s.me "OGN-088" .base
  let s3 ← play s2 s.me c
  return s3.hasKw u .assault

-- Deadly Flourish (UNL-073): when the unit it damaged dies this turn, its caster plays a Gold
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-073" .hand
  let (s2, e) ← putAt s1 s.you "OGN-135" s.bf0
  let s3 ← play s2 s.me c [e]
  return s3.countNamed s.me .base "Gold" == 1 && s3.countNamed s.you .base "Gold" == 0

-- Tactical Retreat (UNL-175): the next time the unit would die this turn it is healed, exhausted and
-- recalled instead (it does not die: no Deathknell, same unit); the next time after that, it dies
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-175" .hand
  let (s2, u) ← putAt s1 s.me "UNL-156" s.bf0
  let (s3, _) ← putAt s2 s.me "OGN-135" s.bf0
  let s4 ← play s3 s.me c [u]
  let hurt := s4.modObj u (fun o => { o with damage := 5 })
  let (saved, evs) := killOrSave hurt u
  let a ← fire saved evs
  let (again, evs2) := killOrSave a u
  let b ← fire again evs2
  return (a.obj? u).any (fun o => o.exhausted && o.damage == 0 && o.loc.isNone) &&
    a.handN s.me == hurt.handN s.me && (b.obj? u).isNone && b.countIn s.me .trash "UNL-156" == 1

-- Two resolved Tactical Retreats can save a Unit from two separate deaths that turn.
#guard tun fun s => do
  let p := s.me
  let (s, first) ← put s p "UNL-175" .hand
  let (s, second) ← put s p "UNL-175" .hand
  let (s, unit) ← putAt s p "OGN-136" s.bf0
  let once ← play s p first [unit]
  let twice ← play once p second [unit]
  let (firstSave, _) := killOrSave twice unit
  let (secondSave, _) := killOrSave firstSave unit
  let (dead, _) := killOrSave secondSave unit
  return (firstSave.obj? unit).isSome && (firstSave.tacticalRetreatFor unit).isSome &&
    (secondSave.obj? unit).isSome && (secondSave.tacticalRetreatFor unit).isNone &&
    (dead.obj? unit).isNone

-- Soul Sword (UNL-039): +1 Might, and one more at Level 3
#guard tun fun s => do
  let (s1, u) ← put s s.me "OGN-135" .base
  let (s2, g) ← put s1 s.me "UNL-039" .base
  let s3 := s2.modObj g (fun o => { o with attached := some u })
  let lo := s3.setXP s.me 2
  let hi := s3.setXP s.me 3
  return lo.mightNow u == (s2.mightNow u).map (· + 1) && hi.mightNow u == (s2.mightNow u).map (· + 2)

-- Ivern (UNL-051): when the unit it draws is a Poro (or another pet), a friendly unit is buffed
#guard tun fun s => do
  let (s1, iv) ← put s s.me "UNL-051" .base
  let few := s1.setZone (.player s.me .mainDeck) []
  let (p1, _) ← put few s.me "UNL-156" .mainDeck
  let (n1, _) ← put few s.me "UNL-111" .mainDeck
  let pet ← fire p1 [Event.played s.me iv]
  let plain ← fire n1 [Event.played s.me iv]
  return (pet.obj? iv).any (·.buffed) && !((plain.obj? iv).any (·.buffed)) &&
    pet.handN s.me == p1.handN s.me + 1

-- Rift Herald's move keeps the Look private, offers only looked-at Units, and draws the one revealed.
#guard tun fun s => do
  let p := s.me
  let z := Zone.player p .mainDeck
  let (s, herald) ← put s p "UNL-179" .base
  let (s, outside) ← put s p "OGN-096" .mainDeck
  let (s, unit) ← put s p "UNL-111" .mainDeck
  let (s, spell) ← put s p "UNL-007" .mainDeck
  let (s, other) ← put s p "UNL-152" .mainDeck
  let seen := [other, spell, unit]
  let rest := (s.zone z).drop 3
  let s := s.modObj herald fun o => { o with exhausted := false }
  let act (t : GameState) (who : PlayerId) (a : ActionKind) := (step 100 t ⟨.player who, a⟩).toOption
  let (moved, _) ← act s p (.standardMove herald (.battlefield s.bf0))
  let (passed, _) ← act moved p .pass
  let (looking, looked) ← act passed s.you .pass
  let (choosing, _) ← act looking p (.decide true)
  let (recycling, events) ← act choosing p (.choose unit)
  let drawn ← recycling.firstOf p .hand "UNL-111"
  let (done, recycled) ← (step 100 recycling ⟨.chance, .arrange [spell, other]⟩).toOption
  let (declined, _) ← act looking p (.decide false)
  let (untaken, _) ← (step 100 declined ⟨.chance, .arrange seen.reverse⟩).toOption
  return rest.head? == some outside && looked == seen.map (.lookedAt p) &&
    (legalFrameActions choosing).map Action.kind == [.choose other, .choose unit] &&
    events.filter (fun | .revealed .. => true | _ => false) == [.revealed p unit] &&
    events.contains (.moved unit drawn (.player p .hand)) && events.contains (.drew p) &&
    events.contains (.drewGroup p (s.handN p)) && drawn != unit && done.handN p == s.handN p + 1 &&
    (act recycling p (.arrange [spell, other])).isNone &&
    recycled.contains (.recycled p) && done.zone z == rest ++ [spell, other] &&
    untaken.handN p == s.handN p && untaken.zone z == rest ++ seen.reverse

-- Deathknell can be declined even with a legal Unit. It ignores Energy, pays Power, and plays at the Base.
#guard tun fun s => do
  let p := s.me
  let (s, herald) ← put s p "UNL-179" .base
  let (s, unit) ← put s p "OGN-234" .hand
  let (s, _) ← put s p "UNL-007" .hand
  let s := s.control p s.bf0
  let funded := s.fund p 0 (order := 2)
  let (dead, events) := killObj funded herald
  let accepted ← fire dead events
  let refused ← fire dead events { yes := false }
  let poor ← fire (dead.setPool p { order := 1 }) events
  let entered ← accepted.firstOf p .base "OGN-234"
  return (accepted.obj? entered).any (fun o => o.loc.isNone && o.energyPaid == 0 && o.exhausted) &&
    (accepted.poolOf p).order == 0 && !(accepted.zone (.player p .hand)).contains unit &&
    (refused.zone (.player p .hand)).contains unit && (refused.poolOf p).order == 2 &&
    (poor.zone (.player p .hand)).contains unit && (poor.poolOf p).order == 1

-- Ruined Rex chooses an enemy Unit and deals exactly four damage to it.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, rex) ← put s p "UNL-067" .base
  let (s, friendly) ← put s p "OGN-001" .base
  let (s, base) ← put s q "OGN-001" .base
  let (s, field) ← putAt s q "OGN-234" s.bf0
  let (dead, events) := killObj s rex
  let targets ← firePicks dead events
  let done ← fire dead events { pick := (· == [field]) }
  return targets.length == 2 && targets.contains base && targets.contains field &&
    (done.obj? field).any (·.damage == 4) && (done.obj? base).any (·.damage == 0) &&
    (done.obj? friendly).any (·.damage == 0)

-- Black Rose Dignitary gets Assault on attack and channels its controller's Rune exhausted on death.
#guard tun fun s => do
  let p := s.me
  let (s, unit) ← putAt s p "UNL-152" s.bf0
  let (dead, events) := killObj s unit
  let done ← fire dead events
  let newRunes := (done.zone (.player p .base)).filter (fun id => !(s.zone (.player p .base)).contains id)
  return s.combatMight unit true == 3 && s.combatMight unit false == 2 &&
    newRunes.length == 1 && newRunes.all (fun id =>
      (done.cardDef? id).any (·.hasType .rune) && done.tired id == some true) &&
    (done.zone (.player p .runeDeck)).length + 1 == (s.zone (.player p .runeDeck)).length &&
    done.zone (.player s.you .runeDeck) == s.zone (.player s.you .runeDeck)

-- Additional costs are paid as the card is played (CR 357.2): Sacrifice and Heedless Resurrection kill
-- the unit while the spell is cast, before it resolves, and cannot be cast without one
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-173" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let big := s2.modObj u (fun o => { o with mightMods := [{ amount := 9, ends := .never }] })
  let r ← match step 100 (big.rich s.me) ⟨.player s.me, .playCard c (payOf big c) [u]⟩ with
    | .ok (s3, _) => some s3
    | .error _ => none
  return r.countIn s.me .trash "UNL-111" == 1 && r.handN s.me == big.handN s.me - 1 &&
    (play s2 s.me c [u]).isNone

#guard tun fun s => do
  let p := s.me
  let (s, spell) ← put s p "UNL-142" .hand
  let (s, unit) ← put s p "UNL-003" .base
  let funded := s.rich p
  let pick := SpellPick.withExtraObject .plain unit
  let action (target : ObjId) : Action :=
    ⟨.player p, .playCard spell (payOf funded spell) [target] none none pick⟩
  let (s, target) ← put funded p "UNL-111" .trash
  let (s, fallback) ← put s p "UNL-111" .trash
  let (queued, _) ← (step 100 s (action target)).toOption
  let item ← (queued.zone .chain).head?
  let (removed, _) ← moveObj queued target (.player p .mainDeck)
  let done := settleChain {} 12 removed
  let countered := settleChain {} 12 (counterObj queued item).1
  return !(legalFrameActions funded).any (fun act => match act.kind with
      | .playCard card .. => card == spell
      | _ => false) &&
    (done.zone (.player p .trash)).contains fallback && done.countIn p .base "UNL-111" == 0 &&
    done.countIn p .trash "UNL-003" == 1 && countered.countIn p .trash "UNL-003" == 1 &&
    countered.countIn p .base "UNL-111" == 0

-- A spell played by another effect uses the same target limit and records the payment.
-- Its chosen unit can Accelerate during its own finalization.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s q "UNL-142" .hand
  let (s, unit) ← put s p "OGN-135" .base
  let (s, target) ← put s p "OGN-010" .trash
  let (s, tooMuchPower) ← put s p "OGN-150" .trash
  let price := EffectPlayPrice.ignoreBase
  let (queued, item) ← queueLimitedSpell (s.fund p 1 1) p spell price .normal
  let plans := limitedSpellOptions queued p item price
  let plan ← plans.find? (fun plan => plan.targets == [target] && plan.pick.extraObject == some unit)
  let (paid, _) ← commitLimitedSpell queued p item plan [] effectAddPolicy
  let ready := settleChain { yes := false } 12 { paid with pending := [.chainPass p 0] }
  let revived ← ready.firstOf p .base "OGN-010"
  return !(plans.any (fun plan => plan.targets == [tooMuchPower])) &&
    (paid.obj? item).any (fun o => o.spellPick.paidKill == some (unit, 3, 0)) &&
    ready.tired revived == some false && (ready.poolOf p).energy == 0

-- Safety Inspector (UNL-164): the additional cost is 3 XP; if it is paid, only the opponents kill a unit
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-164" .hand
  let (s2, u) ← put s1 s.me "OGN-135" .base
  let (s3, e) ← put s2 s.you "OGN-135" .base
  let s4 := s3.setXP s.me 3
  let leg ← (s4.zone (.player s.me .legendZone)).head?
  let paid ← play s4 s.me c [leg]
  let free ← play s4 s.me c []
  return (paid.obj? u).isSome && (paid.obj? e).isNone && paid.xpOf s.me == 0 &&
    (free.zone (.player s.me .base)).length + 1 == (paid.zone (.player s.me .base)).length &&
    (free.obj? e).isNone && free.xpOf s.me == 3


-- Poppy, Defender of the Meek (UNL-178): the additional cost is 3 XP; paid, she costs 3 Energy less
-- (and only then); not paid, the full cost, and no XP is spent
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-178" .hand
  let s2 := s1.setXP s.me 3
  let leg ← (s2.zone (.player s.me .legendZone)).head?
  let less : RunePool.Payment := ⟨3, [.order]⟩
  let full : RunePool.Payment := ⟨6, [.order]⟩
  let paid ← cast (s2.rich s.me) s.me c less [leg]
  let free ← cast (s2.rich s.me) s.me c full []
  let pu ← paid.firstOf s.me .base "UNL-178"
  let fu ← free.firstOf s.me .base "UNL-178"
  return paid.xpOf s.me == 0 && free.xpOf s.me == 3 &&
    (cast (s2.rich s.me) s.me c less []).isNone &&
    (cast (s1.setXP s.me 2 |>.rich s.me) s.me c less [leg]).isNone &&
    paid.tired pu == some true && free.tired fu == some true

-- In Limited, spending XP is an explicit choice independent of the destination and Ambush.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let empty := GameState.empty { ruleSet := .tournament .draft, mode := .duel } labState.cards
  let s := { empty with
    phase := .main, turn := 2, active := some p, pending := [.priority p], turnOrder := [p, q] }
  let (s, c) ← put s p "UNL-178" .hand
  let (s, bf) ← putBf s p "OGN-275"
  let (s, _) ← putAt s p "OGN-051" bf
  let funded := (s.fund p 6 (order := 1)).setXP p 4
  let xp := SpellPick.withXP .plain
  let paid : Action := ⟨.player p, .playCard c ⟨3, [.order]⟩ [] none none xp⟩
  let full : Action := ⟨.player p, .playCard c ⟨6, [.order]⟩ []⟩
  let (atBase, _) ← (step 100 funded paid).toOption
  let (free, _) ← (step 100 funded full).toOption
  let new ← atBase.firstOf p .base "UNL-178"
  let (closed, _) ← onChain funded q "OGN-004"
  let closed := { closed with pending := [.chainPass p 0, .priority p] }
  let ambush : Action := ⟨.player p, .playCard c ⟨3, [.order]⟩ [bf] none none xp⟩
  let (atBattlefield, _) ← (step 100 closed ambush).toOption
  let there ← (atBattlefield.zone .battlefieldZone).find? (fun id =>
    (atBattlefield.cardDef? id).any (·.id == cid "UNL-178"))
  let terms : EffectPlayTerms := { price := .reduceEnergy 1 }
  let plan ← (permanentPlayOptions funded p c terms).find? (fun plan =>
    plan.spendXP && plan.battlefield == some bf)
  let (fromEffect, effectCard, _) ← applyReducedPermanent funded p c plan
  let (otherHand, borrowed) ← put (funded.setXP q 7) q "UNL-178" .hand
  let borrowedPlan ← (permanentPlayOptions otherHand p borrowed terms).find? (fun plan =>
    plan.spendXP && plan.battlefield == some bf)
  let (playedBorrowed, _, _) ← applyReducedPermanent otherHand p borrowed borrowedPlan
  return (funded.zone (.player p .legendZone)).isEmpty &&
    (legalFrameActions funded).contains paid && (legalFrameActions funded).contains full &&
    !(legalFrameActions (funded.setXP p 2)).contains paid &&
    !(legalFrameActions (funded.setXP p 2)).contains ⟨.player p, .playCard c ⟨3, [.order]⟩ []⟩ &&
    atBase.xpOf p == 1 && free.xpOf p == 4 && atBase.tired new == some true &&
    (legalFrameActions closed).contains ambush && !(legalFrameActions closed).contains paid &&
    atBattlefield.xpOf p == 1 && atBattlefield.tired there == some true &&
    (atBattlefield.obj? there).any (·.loc == some bf) &&
    plan.extraObject.isNone && plan.cost.energy == 2 && fromEffect.xpOf p == 1 &&
    (fromEffect.obj? effectCard).any (fun o => o.exhausted && o.loc == some bf) &&
    playedBorrowed.xpOf p == 1 && playedBorrowed.xpOf q == 7

-- When the cost is paid, only the player who paid skips the Kill instruction in 2v2.
#guard tun fun labState => do
  let p : PlayerId := ⟨0⟩
  let teammate : PlayerId := ⟨1⟩
  let opp : PlayerId := ⟨2⟩
  let last : PlayerId := ⟨3⟩
  let empty := GameState.empty { ruleSet := .tournament .sealed, mode := .teamDuel } labState.cards
  let s := { empty with
    phase := .main, turn := 2, active := some p, pending := [.priority p], turnOrder := Mode.teamTurnOrder true }
  let (s, c) ← put s p "UNL-164" .hand
  let (s, own) ← put s p "OGN-135" .base
  let (s, allyFirst) ← put s teammate "OGN-135" .base
  let (s, allySecond) ← put s teammate "OGN-135" .base
  let (s, foe) ← put s opp "OGN-135" .base
  let (s, foeMate) ← put s last "OGN-135" .base
  let s := ((s.rich p).setXP p 3).setXP teammate 5
  let xp := SpellPick.withXP .plain
  let says : Says := { obj := fun id => id == own || id == allySecond }
  let paid ← cast s p c (payOf s c) [] says xp
  let free ← cast s p c (payOf s c) [] says
  return (paid.obj? own).isSome && (free.obj? own).isNone &&
    (paid.obj? allyFirst).isSome && (paid.obj? allySecond).isNone &&
    (paid.obj? foe).isNone && (paid.obj? foeMate).isNone &&
    paid.xpOf p == 0 && paid.xpOf teammate == 5 && free.xpOf p == 3 &&
    (cast (s.setXP p 2) p c (payOf s c) [] says xp).isNone

-- Atakhan (UNL-170): killing a friendly unit as the additional cost makes it cost that unit's Energy
-- and Power less
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-170" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let some d := s2.cardDef? u | none
  let some k := d.cost | none
  let some ca := (s2.cardDef? c).bind (·.cost) | none
  let less : RunePool.Payment :=
    ⟨ca.energy - k.energy, (ca.power.drop k.power.length).map (fun x => match x with | .domain d => d | _ => .fury)⟩
  let full : RunePool.Payment := ⟨ca.energy, ca.power.map (fun x => match x with | .domain d => d | _ => .fury)⟩
  let paid ← cast (s2.rich s.me) s.me c less [u]
  let free ← cast (s2.rich s.me) s.me c full []
  return paid.countIn s.me .trash "UNL-111" == 1 && paid.countIn s.me .base "UNL-170" == 1 &&
    free.countIn s.me .base "UNL-111" == 1 && free.countIn s.me .base "UNL-170" == 1 &&
    (cast (s2.rich s.me) s.me c less []).isNone

-- Conscription records the optional payment separately from the target's Might.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, c) ← put s p "UNL-140" .hand
  let (s, small) ← putAt s q "OGN-135" s.bf0
  let (s, big) ← putAt s q "UNL-170" s.bf0
  let s := (s.rich p).setXP p 5
  let pay := payOf s c
  let xp := SpellPick.withXP .plain
  let act (target : ObjId) (pick : SpellPick) : Action :=
    ⟨.player p, .playCard c pay [target] none none pick⟩
  let legal := legalFrameActions s
  let (free, _) ← (step 100 s (act small .plain)).toOption
  let (paid, _) ← (step 100 s (act small xp)).toOption
  let item ← (paid.zone .chain).head?
  let (paidBig, _) ← (step 100 s (act big xp)).toOption
  let (passed, _) ← (step 100 paidBig ⟨.player p, .pass⟩).toOption
  let (afterBig, resolved) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let d ← paid.cardDef? item
  let effect ← d.spellEffect
  let grow (t : GameState) := t.modObj small (fun o => { o with
    mightMods := [{ amount := 10, ends := .never }] })
  let afterFree := settleChain {} 12 (grow free)
  let afterPaid := settleChain {} 12 (grow paid)
  let recalled (state : GameState) (id : ObjId) := (state.obj? id).any (fun o =>
    o.controller == p && o.exhausted && o.loc.isNone) && (state.zone (.player p .base)).contains id
  return (s.mightNow small).any (· ≤ 3) && (s.mightNow big).any (· > 3) &&
    legal.contains (act small .plain) && legal.contains (act small xp) &&
    legal.contains (act big xp) && !(legal.contains (act big .plain)) &&
    !(legalFrameActions (s.setXP p 4)).contains (act small xp) &&
    free.xpOf p == 5 && paid.xpOf p == 0 && paidBig.xpOf p == 0 &&
    (paid.obj? item).any (fun o => o.paid && o.spellPick.paysXP) &&
    (counterObj paid item).1.xpOf p == 0 &&
    (spellChoicesWithShowOff paid p item d effect [none] none (some true)).contains (xp, [big]) &&
    recalled (settleChain {} 12 free) small &&
    (afterFree.obj? small).any (fun o => o.controller == q && o.loc.isSome) &&
    recalled afterPaid small && recalled afterBig big &&
    resolved.filter (fun e => e == .exhausted big || e == .recalled big) == [.exhausted big, .recalled big]

-- A Repeat shares the declaration for every execution and pays XP once.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, c) ← put s p "UNL-140" .hand
  let (s, first) ← putAt s q "UNL-170" s.bf0
  let (s, second) ← putAt s q "UNL-170" s.bf0
  let s := ((s.rich p).setXP p 7).addTurnFx p .nextSpellRepeat
  let pay : RunePool.Payment := ⟨10, [.chaos, .chaos, .chaos, .chaos]⟩
  let xp := SpellPick.withXP .plain
  let act (last : SpellPick) : Action :=
    ⟨.player p, .playCard c pay [first, second] none none (.withCosts (.thenRepeat xp 1 last) false 1)⟩
  let (casted, _) ← (step 100 s (act xp)).toOption
  let done := settleChain {} 16 casted
  return (legalFrameActions s).contains (act xp) && !(legalFrameActions s).contains (act .plain) &&
    casted.xpOf p == 2 && done.xpOf p == 2 &&
    [first, second].all ((done.zone (.player p .base)).contains)

-- A Spell finalized by an effect keeps the same choice and spends the acting seat's XP.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, c) ← put s q "UNL-140" .hand
  let (s, target) ← putAt s q "UNL-170" s.bf0
  let s := (s.setXP p 5).setXP q 7
  let price := EffectPlayPrice.ignoreBase
  let (queued, item) ← queueLimitedSpell s p c price .normal
  let plans := limitedSpellOptions queued p item price
  let plan ← plans.find? (fun plan => plan.pick.paysXP && plan.targets == [target])
  let (paid, _) ← commitLimitedSpell queued p item plan [] effectAddPolicy
  return !(plans.any (fun plan => !plan.pick.paysXP && plan.targets == [target])) &&
    !(limitedSpellOptions (queued.setXP p 4) p item price).contains plan &&
    paid.xpOf p == 0 && paid.xpOf q == 7 && (paid.obj? item).any (fun o => o.paid)

-- Showdown (CR 347-348): the player with Focus can play a Spell with Action, but not one without a
-- speed; the Chain resolves above the Showdown, and the Showdown goes on
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-155" .hand
  let (s2, d) ← put s1 s.me "UNL-054" .hand
  let (s3, u) ← putAt s2 s.me "UNL-111" s.bf0
  let (s4, e) ← putAt s3 s.you "OGN-088" s.bf0
  let sd := { s4 with pending := .showdown s.bf0 s.me 0 :: s4.pending }
  let r ← play sd s.me c [u, e]
  let back := match r.pending with | .showdown _ q 0 :: _ => q == s.me | _ => false
  let rich := sd.rich s.me
  let acts := legalFrameActions rich
  let inList (card : ObjId) := acts.any (fun a => match a.kind with
    | .playCard x _ _ _ _ _ => x == card | _ => false)
  return (r.obj? e).any (·.stunned) && back && inList c && !inList d &&
    (cast rich s.me d (payOf rich d) [e] {} (.destination none)).isNone

-- Shadow is already Ready at the instant of its Battlefield play. Paying,
-- effect-driven play and placement at Base use their respective entry states.
#guard tun fun s => do
  let p := s.me
  let field := s.bf0
  let (s, shadow) ← put (s.control p field) p "UNL-194" .hand
  let ready := s.rich p
  let payment := payOf ready shadow
  let (entered, events) ← (step 100 ready ⟨.player p, .playCard shadow payment [field]⟩).toOption
  let (base, _) ← (step 100 ready ⟨.player p, .playCard shadow payment []⟩).toOption
  let (free, freeEvents) := playFreeAt p field s shadow
  let played (es : List Event) := es.findSome? (fun | .played _ unit => some unit | _ => none)
  let fieldId ← played events
  let freeId ← played freeEvents
  let baseId ← base.firstOf p .base "UNL-194"
  return entered.tired fieldId == some false && (entered.zone .chain).isEmpty &&
    (entered.obj? fieldId).any (·.loc == some field) &&
    free.tired freeId == some false && (free.obj? freeId).any (·.loc == some field) &&
    base.tired baseId == some true

-- Shadow (UNL-194): in a Showdown, the defender stuns an attacking enemy unit with its Action ability
#guard tun fun s => do
  let (s1, sh) ← putAt s s.you "UNL-194" s.bf0
  let (s2, a) ← putAt s1 s.me "OGN-088" s.bf0
  let s3 := s2.modObj s.bf0 (fun o => { o with contested := some s.me })
  let sd := { s3 with pending := .showdown s.bf0 s.you 0 :: s3.pending }
  let idx := firstAct sd sh
  let r ← activate sd s.you sh idx [a] ⟨1, [.fury]⟩
  let back := match r.pending with | .showdown _ q 0 :: _ => q == s.you | _ => false
  return (r.obj? a).any (·.stunned) && back && (r.obj? sh).any (·.exhausted)

-- Shadow Watcher enters ready from the turn player's own Beginning Phase death.
#guard tun fun s => do
  let p := s.me
  let (s, watcher) ← put s p "UNL-037" .hand
  let beginning := { s with phase := .beginning }
  let died := beginning.noteUnitDied p
  let otherDied := beginning.noteUnitDied s.you
  let normal ← play { (s.noteUnitDied p) with phase := .main } p watcher
  let ready ← play { died with phase := .main } p watcher
  let enemy ← play { otherDied with phase := .main } p watcher
  let nr ← normal.firstOf p .base "UNL-037"
  let r ← ready.firstOf p .base "UNL-037"
  let e ← enemy.firstOf p .base "UNL-037"
  return normal.tired nr == some true && ready.tired r == some false && enemy.tired e == some true

-- Lord Broadmane can Ambush at a friendly battlefield and grants Assault only to
-- the other friendly units at that location.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, broadmane) ← put s p "UNL-012" .hand
  let (s, ally) ← putAt s p "OGN-088" field
  let (s, remote) ← put s p "OGN-088" .base
  let (s, _) ← onChain s q "OGN-004"
  let ready := s.rich p
  let payment := payOf ready broadmane
  let (played, _) ← (step 100 ready ⟨.player p, .playCard broadmane payment [field]⟩).toOption
  let done := settleChain {} 16 played
  let placed ← done.inPlay.find? (fun u => (done.cardDef? u).any (·.id == cid "UNL-012"))
  return reactable ready p broadmane payment [field] && !reactable ready p broadmane payment [] &&
    done.hasKw ally .assault && !done.hasKw remote .assault && !done.hasKw placed .assault

-- Teammate deaths satisfy Shadow Watcher's friendly condition. Lord Broadmane's
-- grant is limited to units its player controls.
#guard tun fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (runUntilTurn 100 1 2000 (Rng.ofSeed 1) initial).toOption
  let p := s.me
  let mate ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← s.players.find? (fun q => !config.mode.sameSide p q)
  let field := s.bf0
  let (s, broadmane) ← put (s.control p field) p "UNL-012" .hand
  let (s, watcher) ← put s p "UNL-037" .hand
  let (s, own) ← putAt s p "OGN-088" field
  let (s, allied) ← putAt s mate "OGN-088" field
  let buffed ← play s p broadmane [field]
  let beginning := { s with phase := .beginning }
  let allyDied := beginning.noteUnitDied mate
  let enemyDied := beginning.noteUnitDied enemy
  let ally ← play { allyDied with phase := .main } p watcher
  let opp ← play { enemyDied with phase := .main } p watcher
  let ready ← ally.firstOf p .base "UNL-037"
  let tired ← opp.firstOf p .base "UNL-037"
  return buffed.hasKw own .assault && !buffed.hasKw allied .assault &&
    ally.tired ready == some false && opp.tired tired == some true

-- Frisky Hunter creates an exhausted Bird with Deflect alongside it at a battlefield.
#guard tun fun s => do
  let p := s.me
  let (s, hunter) ← put (s.control p s.bf0) p "UNL-033" .hand
  let done ← play s p hunter [s.bf0]
  let bird ← done.inPlay.find? (fun u => (done.cardDef? u).any (·.name == "Bird"))
  return (done.obj? bird).any (fun o => o.loc == some s.bf0 && o.controller == p) &&
    done.mightNow bird == some 1 && done.hasKw bird .deflect && done.tired bird == some true

-- Paying Equip gives the Might bonus to the selected Unit. Ordinary Equip requires unattached Gear.
#guard tun fun s => do
  let p := s.me
  let (s, first) ← put s p "OGN-135" .base
  let (s, second) ← put s p "OGN-135" .base
  let (s, sword) ← put s p "UNL-039" .base
  let equipped ← activate s p sword 0 [first] ⟨0, [.calm]⟩
  let leveled := equipped.setXP p 3
  return equipped.mightNow first == (s.mightNow first).map (· + 1) &&
    leveled.mightNow first == (s.mightNow first).map (· + 2) &&
    leveled.mightNow second == s.mightNow second &&
    (activate leveled p sword 0 [second] ⟨0, [.calm]⟩).isNone

-- Determined Sentry can still be Recalled because that instruction is not a Move.
#guard tun fun s => do
  let p := s.me
  let (s, sentry) ← putAt s p "UNL-111" s.bf0
  let (recalled, events) := recallObj s sentry
  let atBase ← recalled.firstOf p .base "UNL-111"
  return !moveOk s p sentry .base && events == [.recalled atBase] &&
    (recalled.obj? atBase).any (·.loc.isNone)

-- Soul Harvest accepts a Unit with exactly 3 Might at a battlefield.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, harvest) ← put s p "UNL-159" .hand
  let (s, field) ← putAt s q "OGN-135" s.bf0
  let (s, base) ← put s q "OGN-135" .base
  let (s, stronger) ← putAt s q "OGN-088" s.bf0
  let s := s.buff stronger
  let finished ← play s p harvest [field]
  return s.mightNow field == some 3 && (s.mightNow stronger).any (· > 3) &&
    (play s p harvest [base]).isNone && (play s p harvest [stronger]).isNone &&
    (finished.obj? field).isNone && finished.countIn q .trash "OGN-135" == 1

-- A later death earns Gold during the spell's turn. The delayed trigger expires with the turn.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, flourish) ← put s p "UNL-073" .hand
  let (s, unit) ← putAt s q "OGN-088" s.bf0
  let damaged ← play s p flourish [unit]
  let (dead, death) := killOrSave damaged unit
  let paid ← fire dead death
  let following := { damaged with turn := damaged.turn + 1 }
  let (late, lateDeath) := killOrSave following unit
  let expired ← fire late lateDeath
  let gold ← (paid.zone (.player p .base)).find? (fun id =>
    (paid.cardDef? id).any (·.name == "Gold"))
  return (damaged.obj? unit).any (·.damage == 3) &&
    damaged.countNamed p .base "Gold" == 0 && paid.countNamed p .base "Gold" == 1 &&
    paid.tired gold == some true && expired.countNamed p .base "Gold" == 0

-- A second draw by the opponent cannot trigger your Jewel, and the Might expires.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, _) ← put s p "UNL-074" .base
  let (s, unit) ← put s p "OGN-135" .base
  let logs := [p, q, p, q].map (fun seat => (seat, s.turn))
  let drawing := { s with drawLog := logs }
  let yours ← fire drawing [.drew p] { pick := fun targets => targets == [unit] }
  let theirs ← fire drawing [.drew q] { pick := fun targets => targets == [unit] }
  let (expired, _) ← (advance 100 { yours with pending := [.expireTurn, .priority p] } []).toOption
  return yours.mightNow unit == (s.mightNow unit).map (· + 2) &&
    theirs.mightNow unit == s.mightNow unit && expired.mightNow unit == s.mightNow unit

-- Tactical Retreat cannot target an enemy, and unused protection expires after this turn.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let (s, retreat) ← put s p "UNL-175" .hand
  let (s, ally) ← putAt s p "OGN-135" s.bf0
  let (s, enemy) ← put s q "OGN-135" .base
  let armed ← play s p retreat [ally]
  let following := { armed with turn := armed.turn + 1 }
  let (dead, _) := killOrSave following ally
  return (play s p retreat [enemy]).isNone && (armed.tacticalRetreatFor ally).isSome &&
    (following.tacticalRetreatFor ally).isNone && (dead.obj? ally).isNone

-- Rengar enters Ready through Accelerate, contributes Assault on attack, has
-- Deflect against foes and can move between battlefields while ready.
#guard tun fun s => do
  let p := s.me
  let q := s.you
  let first := s.bf0
  let second ← s.battlefields.find? (· != first)
  let (s, rengar) ← put (s.control p first) p "UNL-024" .hand
  let base := payOf s rengar
  let accelerated : RunePool.Payment := ⟨base.energy + 1, base.power ++ [.fury]⟩
  let (ready, _) ← (step 100 (s.rich p) ⟨.player p, .playCard rengar accelerated [first]⟩).toOption
  let normal ← play s p rengar [first]
  let find (state : GameState) := state.inPlay.find? (fun u => (state.cardDef? u).any (·.id == cid "UNL-024"))
  let a ← find ready
  let n ← find normal
  return ready.tired a == some false && normal.tired n == some true &&
    ready.combatMight a true == ready.mightEff a + 2 && ready.combatMight a false == ready.mightEff a &&
    ready.deflectCost q [a] == 1 && ready.deflectCost p [a] == 0 &&
    moveOk ready p a (.battlefield second) && !moveOk normal p n (.battlefield second)

end RiftboundTest
