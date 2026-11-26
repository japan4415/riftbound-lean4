module

import Riftbound.Rules.PlayerRemoval
meta import Riftbound.Rules.PlayerRemoval
import Riftbound.Rules.Frames
meta import Riftbound.Rules.Frames
import Riftbound.Rules.TeamSetup
meta import Riftbound.Rules.TeamSetup
import RiftboundDriver.Trace
meta import RiftboundDriver.Trace
import RiftboundDriver.Replay
meta import RiftboundDriver.Replay
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-! # Tests for removing a player's objects and continuing play (CR 652) -/

namespace RiftboundTest

open Riftbound

private meta def replayConcessions (mode : Mode) : Except String Unit := do
  let order : Option (List PlayerId) :=
    if mode == .ffa4 then some [⟨2⟩, ⟨0⟩, ⟨3⟩, ⟨1⟩] else none
  let config : GameConfig := { ruleSet := .coreOnly, mode }
  let game : RiftboundDriver.GameInputs :=
    { decks := .core (List.replicate mode.players goodDeck), openingOrder := order, answers := #[] }
  let mut state ← game.initial db config
  let mut rng := RiftboundDriver.Rng.ofSeed 21
  let mut answers : Array RiftboundDriver.ReplayAnswer := #[]
  let record (s : GameState) (a : Action) :=
    (step 100 s a).mapError reprStr
  for _ in [:50] do
    if state.phase == .main then break
    let some (action, nextRng) := RiftboundDriver.autoAnswer rng state | throw "setup stopped early"
    let (next, _) ← record state action
    state := next
    rng := nextRng
    answers := answers.push (.observed action)
  let some winner := state.active | throw "setup did not reach a turn"
  let departing := state.turnOrder.filter (· != winner)
  let mut sawReplacement := false
  for p in departing do
    let action : Action := ⟨.player p, .concede⟩
    let (next, _) ← record state action
    if next.participates p then throw "a conceded seat is still in play"
    sawReplacement := sawReplacement || next.battlefields.any (fun bf =>
      (next.cardDef? bf).any (fun (card : CardDef) => card.id == concessionBattlefieldToken.id))
    state := next
    answers := answers.push (.observed action)
  unless sawReplacement && state.result == some (.won [winner]) do throw "incorrect concession result"
  let input : RiftboundDriver.FreeForAllInputs := { mode, game := { game with answers } }
  let saved ← input.record db
  let restored : RiftboundDriver.RecordedFreeForAll ←
    Lean.fromJson? (← Lean.Json.parse (Lean.toJson saved).compress)
  let verified ← restored.verify db
  unless verified.result == state.result && verified.exact && restored.game.checkpoints.size == answers.size + 1 do
    throw "verification did not reproduce the complete game"

#guard (replayConcessions .ffa3).isOk
#guard (replayConcessions .ffa4).isOk

private meta def strengthField : CardDef :=
  { (battlefield 0) with abilities := [.passive .always
    [.mightPlus (.all .any .here [.ofType .unit]) (.const 1)]] }

private meta def removalState : GameState :=
  let cards : CardDB := ⟨db.cards.map (fun card =>
    if card.id == strengthField.id then strengthField else card)⟩
  GameState.empty { ruleSet := .coreOnly, mode := .ffa4 } cards.withLimitedBlank

-- A departure before opening hands leaves the original turn order intact, while dealing
-- and offering mulligans only to the remaining seats in that order.
#guard (do
  let order : List PlayerId := [⟨2⟩, ⟨3⟩, ⟨0⟩, ⟨1⟩]
  let s := { removalState with turnOrder := order, pending := [.setupHands] }
  let (next, _) ← microStep (s.withdrawSeat ⟨3⟩)
  return next.turnOrder == order &&
    next.pending == [Frame.draw ⟨2⟩ 4, .draw ⟨0⟩ 4, .draw ⟨1⟩ 4,
      .mulligan ⟨2⟩ 0, .mulligan ⟨0⟩ 0, .mulligan ⟨1⟩ 0, .beginTurn]).getD false

-- Borrowed cards are banished to their owner. A remaining unit, Hidden card and Chain target
-- all retain the location of the original physical Battlefield.
#guard (do
  let departing : PlayerId := ⟨1⟩
  let remaining : PlayerId := ⟨2⟩
  let s := removalState
  let board := { newCard s.cards s departing (cid "B0") with
    control := some remaining, scored := [remaining] }
  let (s, field) ← addObject s board .battlefieldZone
  let (s, unit) ← addObject s { newCard s.cards s remaining (cid "V0") with loc := some field }
    .battlefieldZone
  let (s, hidden) ← addObject s
    { newCard s.cards s remaining (cid "SP0") with hiddenAt := some field } (.player remaining .hidden)
  let (s, ownHidden) ← addObject s
    { newCard s.cards s departing (cid "SP0") with hiddenAt := some field } (.player departing .hidden)
  let (s, ownRune) ← addObject s (newCard s.cards s departing (cid "R1")) (.player departing .base)
  let (s, ownLegend) ← addObject s (newCard s.cards s departing (cid "L1")) (.player departing .legendZone)
  let (s, borrowed) ← addObject s { newCard s.cards s remaining (cid "V1") with
      controller := departing } (.player departing .base)
  let (s, taken) ← addObject s { newCard s.cards s departing (cid "V2") with
      controller := remaining } (.player remaining .base)
  let (s, borrowedSpell) ← addObject s { newCard s.cards s remaining (cid "SP0") with
      controller := departing } .chain
  let (s, remainingSpell) ← addObject s { newCard s.cards s remaining (cid "SP0") with
      targets := [field] } .chain
  let ability : Object :=
    { kind := .chainAbility (cid "V1") 0 borrowed,
      owner := remaining, controller := departing, timestamp := ⟨0⟩ }
  let (s, retiredAbility) ← addObject s ability .chain
  let (next, events) ← removePlayerObjects s departing limitedBlankBattlefield.id
  let outside := next.zone (.player departing .outOfGame)
  let banished := next.zone (.player remaining .banishment)
  let trash := next.zone (.player remaining .trash)
  let physical := fun st : GameState => (st.physIds.map PhysId.n).mergeSort
  return next.battlefields == [field] && next.controlOf field == some remaining &&
    (next.obj? field).any (fun (o : Object) => o.scored == [remaining]) &&
    (next.cardDef? field).any (fun (d : CardDef) => d.id == limitedBlankBattlefield.id && d.abilities.isEmpty) &&
    (next.obj? unit).any (fun (o : Object) => o.loc == some field) &&
    (next.obj? hidden).any (fun (o : Object) => o.hiddenAt == some field) &&
    s.mightNow unit == some 3 && next.mightNow unit == some 2 &&
    next.zone .chain == [remainingSpell] &&
    (next.obj? remainingSpell).any (fun (o : Object) => o.targets == [field]) &&
    ([ownHidden, ownRune, ownLegend, taken, borrowed, borrowedSpell, retiredAbility].all
      (fun id => (next.obj? id).isNone)) &&
    outside.length == 5 && banished.length == 1 && trash.length == 1 &&
    (events.any (fun e => match e with | .moved id _ _ => id == field | _ => false)) &&
    physical next == physical s).getD false

-- A token standing in for the departing contribution also becomes blank. Its already replaced
-- original physical card is still removed from the game.
#guard (do
  let departing : PlayerId := ⟨1⟩
  let remaining : PlayerId := ⟨2⟩
  let s := removalState
  let (s, field) ← addObject s (newCard s.cards s departing (cid "B0")) .battlefieldZone
  let brush : CardDef := { (battlefield 1) with id := cid "TKN-TestBrush" }
  let s := { s with cards := ⟨brush :: s.cards.cards⟩ }
  let (s, _) := replaceBf brush remaining s field
  let token ← s.battlefields.head?
  let (next, _) ← removePlayerObjects s departing limitedBlankBattlefield.id
  return s.contributedBattlefield departing == some token && next.battlefields == [token] &&
    (next.obj? token).any (fun (o : Object) =>
      o.replaces.isNone && o.kind == ObjKind.token limitedBlankBattlefield.id) &&
    (next.zone (.player departing .banishment)).isEmpty &&
    (next.zone (.player departing .outOfGame)).length == 1).getD false

-- An archived trace retains the old Battlefield at its earlier checkpoint and writes the
-- replacement's definition under the same identifier at the departure checkpoint.
#guard (do
  let departing : PlayerId := ⟨1⟩
  let s := removalState
  let (s, field) ← addObject s (newCard s.cards s departing (cid "B0")) .battlefieldZone
  let (first, seen) := RiftboundDriver.stepJson 0 none [] s {}
  let (next, events) ← removePlayerObjects s departing limitedBlankBattlefield.id
  let next := next.withdrawSeat departing
  let (concession, seen) :=
    RiftboundDriver.stepJson 1 (some ⟨.player departing, .concede⟩) events next seen
  let (later, _) := RiftboundDriver.stepJson 2 none [] next seen
  let entry := fun card : CardId =>
    RiftboundDriver.jstr (toString field.n) ++ ":{\"card\":" ++ RiftboundDriver.jstr card.code
  return (first.splitOn (entry (cid "B0"))).length == 2 &&
    (first.splitOn "\"departed\"").length == 1 &&
    (concession.splitOn (entry limitedBlankBattlefield.id)).length == 2 &&
    (concession.splitOn "\"departed\":[1]").length == 2 &&
    (later.splitOn (entry limitedBlankBattlefield.id)).length == 1).getD false

-- The count drops only for a seat that already passed. Removing the holder either hands off
-- or ends a window whose remaining seats have all passed.
#guard
  let a : PlayerId := ⟨3⟩
  let b : PlayerId := ⟨0⟩
  let c : PlayerId := ⟨2⟩
  let d : PlayerId := ⟨1⟩
  let order := [a, b, c, d]
  passAfterPlayerRemoval order b c 2 == some (c, 1) &&
    passAfterPlayerRemoval order d c 2 == some (c, 2) &&
    passAfterPlayerRemoval order d d 2 == some (a, 2) &&
    (passAfterPlayerRemoval order c c 3).isNone &&
    passAfterPlayerRemoval order d a 1 == some (a, 0)

-- A setup decision survives exactly when it still belongs to a remaining seat. The undealt
-- turn order stays at the bottom while the departing seat's shuffle and pick disappear.
#guard
  let first : PlayerId := ⟨0⟩
  let departing : PlayerId := ⟨1⟩
  let pending := [Frame.chanceShuffle (.player departing .runeDeck), .chanceBattlefield first,
    .chanceBattlefield departing, .chanceTurnOrder]
  let next := removalState.withdrawSeat departing
  pending.flatMap (fun frame => Frame.afterPlayerRemoval frame removalState next departing) ==
    [Frame.chanceBattlefield first, .chanceTurnOrder]

-- Applying a departure during setup leaves another seat's unchosen Battlefield available.
#guard (do
  let first : PlayerId := ⟨0⟩
  let departing : PlayerId := ⟨1⟩
  let s := { removalState with pending := [Frame.chanceShuffle (.player departing .runeDeck),
    .chanceBattlefield departing, .chanceBattlefield first, .chanceTurnOrder] }
  let (s, field) ← addObject s (newCard s.cards s first (cid "B0")) (.player first .outOfGame)
  let (s, _) ← addObject s (newCard s.cards s departing (cid "R1")) (.player departing .runeDeck)
  let (next, _) ← applyFreeForAllConcession s departing limitedBlankBattlefield.id
  let (picked, _) ← applyFrame0 next ⟨.chance, .pick 0⟩
  return next.pending == [Frame.chanceBattlefield first, .chanceTurnOrder] &&
    next.zone (.player first .outOfGame) == [field] &&
    next.zone (.player departing .runeDeck) == [] && picked.battlefields.length == 1 &&
    picked.pending == [Frame.chanceTurnOrder]).getD false

-- Every remaining seat has already passed. Resolve the Chain first, then the waiting
-- Showdown. For an empty Chain the Chain window is simply discarded.
#guard (do
  let a : PlayerId := ⟨0⟩
  let b : PlayerId := ⟨1⟩
  let c : PlayerId := ⟨2⟩
  let d : PlayerId := ⟨3⟩
  let s := { removalState with turnOrder := [a, b, c, d], active := some a }
  let (s, _) ← addObject s (newCard s.cards s c (cid "SP0")) .chain
  let field : ObjId := ⟨20⟩
  let pending := [Frame.chainPass b 3, .showdown field b 3, .priority a]
  let next := s.withdrawSeat b
  let empty := next.setZone .chain []
  return pending.flatMap (fun frame => Frame.afterPlayerRemoval frame s next b) ==
      [Frame.resolveChain, .endShowdown field, .priority a] &&
    pending.flatMap (fun frame => Frame.afterPlayerRemoval frame s empty b) ==
      [Frame.endShowdown field, .priority a]).getD false

-- Applying the departure at the turn player's priority queues the next turn, preserves
-- the Battlefield location, and ends the game when only one seat is left.
#guard (do
  let a : PlayerId := ⟨0⟩
  let b : PlayerId := ⟨1⟩
  let c : PlayerId := ⟨2⟩
  let d : PlayerId := ⟨3⟩
  let s := { removalState with
    turnOrder := [a, b, c, d]
    active := some b
    turn := 2
    phase := .main
    pending := [.priority b] }
  let (s, field) ← addObject s (newCard s.cards s b (cid "B0")) .battlefieldZone
  let (next, _) ← applyFreeForAllConcession s b limitedBlankBattlefield.id
  let (started, _) ← (advance 80 next []).toOption
  let (lastTwo, _) ← applyFreeForAllConcession next c limitedBlankBattlefield.id
  let (won, _) ← applyFreeForAllConcession lastTwo d limitedBlankBattlefield.id
  return next.result.isNone && next.pending == [Frame.cleanup, .expireTurn, .beginTurn] &&
    next.battlefields == [field] &&
    (next.cardDef? field).any (fun (card : CardDef) => card.id == limitedBlankBattlefield.id) &&
    started.active == some c && started.turn == 3 &&
    won.result == some (GameResult.won [a]) && won.pending.isEmpty).getD false

-- The normal step API exposes concessions, removes the seat and supplies the blank token.
#guard (do
  let a : PlayerId := ⟨0⟩
  let b : PlayerId := ⟨1⟩
  let c : PlayerId := ⟨2⟩
  let d : PlayerId := ⟨3⟩
  let concede (p : PlayerId) : Action := ⟨.player p, .concede⟩
  let s := { removalState with
    turnOrder := [a, b, c, d]
    active := some b
    turn := 2
    phase := .main
    pending := [.priority b] }
  let (s, field) ← addObject s (newCard s.cards s b (cid "B0")) .battlefieldZone
  let (next, _) ← (step 80 s (concede b)).toOption
  let (lastTwo, _) ← (step 80 next (concede d)).toOption
  let (won, _) ← (step 80 lastTwo (concede a)).toOption
  return (legalActions s).contains (concede b) &&
    next.active == some c && next.participatingOrder == [a, c, d] &&
    next.battlefields == [field] &&
    (next.cardDef? field).any (fun (card : CardDef) =>
      card.id == concessionBattlefieldToken.id && card.fullAbilities.isEmpty) &&
    !(legalActions next).contains (concede b) && (step 80 next (concede b)).toOption.isNone &&
    lastTwo.participatingOrder == [a, c] &&
    won.result == some (GameResult.won [c]) && (legalActions won).isEmpty).getD false

-- A skipped seat does not increment the turn number. An inserted extra turn does not
-- advance the regular cycle, and each continuing seat keeps its own turn count.
#guard
  let a : PlayerId := ⟨3⟩
  let b : PlayerId := ⟨0⟩
  let c : PlayerId := ⟨2⟩
  let d : PlayerId := ⟨1⟩
  let s := { removalState with turnOrder := [a, b, c, d] }
  let first := beginTurnStep s []
  let departure := ({ first with extraTurns := [b, d, b] } : GameState).withdrawSeat b
  let extra := beginTurnStep departure []
  let next := beginTurnStep extra []
  let following := beginTurnStep next []
  first.active == some a && !departure.participates b &&
    departure.participatingOrder == [a, c, d] &&
    extra.turn == 2 && extra.active == some d && extra.departures.skippedTurns == 0 &&
    next.turn == 3 && next.active == some c && next.departures.skippedTurns == 1 &&
    following.turn == 4 && following.active == some d &&
    following.turnsTaken a == 1 && following.turnsTaken c == 1 && following.turnsTaken d == 2

-- An ordinary pass skips departed seats. Only continuing seats need to pass.
#guard (do
  let a : PlayerId := ⟨3⟩
  let b : PlayerId := ⟨0⟩
  let c : PlayerId := ⟨2⟩
  let d : PlayerId := ⟨1⟩
  let s := { removalState with
    turnOrder := [a, b, c, d], active := some b, pending := [Frame.chainPass a 0] }
  let s := s.withdrawSeat b
  let (first, _) ← applyFrame0 s ⟨.player a, .pass⟩
  let (second, _) ← applyFrame0 first ⟨.player c, .pass⟩
  let (last, _) ← applyFrame0 second ⟨.player d, .pass⟩
  return first.pending == [Frame.chainPass c 1] &&
    second.pending == [Frame.chainPass d 2] &&
    last.pending == [Frame.resolveChain] &&
    s.chainPrioritySeat == c && s.participatingCount == 3).getD false

-- Closing the Showdown as work awards the uncontested Battlefield to the remaining unit's
-- controller. If another side is still there, the same work proceeds to Combat Damage.
#guard (do
  let a : PlayerId := ⟨0⟩
  let b : PlayerId := ⟨1⟩
  let s := { removalState with active := some a, phase := .main }
  let (s, bf) ← addObject s { newCard s.cards s a (cid "B0") with contested := some a }
    .battlefieldZone
  let (s, _) ← addObject s { newCard s.cards s a (cid "V0") with loc := some bf } .battlefieldZone
  let closing := { s with pending := [Frame.endShowdown bf, .priority a] }
  let (scored, es) ← microStep0 closing
  let (opposed, _) ← addObject closing { newCard s.cards s b (cid "V1") with loc := some bf }
    .battlefieldZone
  let (combat, _) ← microStep0 opposed
  return scored.controlOf bf == some a && scored.pointsOf a == 1 &&
    es.contains (.controlChanged bf (some a)) && combat.pointsOf a == 0 &&
    combat.pending == [Frame.combatDamage bf a, .priority a]).getD false

-- A departed seat's historical points do not compete with the remaining seats.
#guard
  let departed : PlayerId := ⟨1⟩
  let eligible : PlayerId := ⟨2⟩
  let s := (removalState.gainPoints departed 10).gainPoints eligible 8
  s.winner == some departed &&
    ({ s with departures := { seats := [departed] } } : GameState).winner == some eligible

-- A trigger detected by a departure cannot belong to the withdrawn seat. When the remaining
-- trigger requires a fresh Chain window, priority follows the former turn player.
#guard (do
  let a : PlayerId := ⟨0⟩
  let b : PlayerId := ⟨1⟩
  let c : PlayerId := ⟨2⟩
  let d : PlayerId := ⟨3⟩
  let s := { removalState with turnOrder := [a, b, c, d], active := some b }
  let (s, src) ← addObject s (newCard s.cards s c (cid "SP0")) .chain
  let continuing : PendTrigger := { source := src, card := cid "SP0", idx := 0, controller := c }
  let departed := { continuing with controller := b }
  let next := s.withdrawSeat b
  return s.detect [] [continuing, departed] == [departed, continuing] &&
    next.detect [] [continuing, departed] == [continuing] &&
    triggerFrames next [.priority b] == [Frame.chainPass c 0]).getD false

-- A withdrawn seat cannot remain an obligatory player target or a participant in a group choice.
#guard
  let a : PlayerId := ⟨3⟩
  let b : PlayerId := ⟨0⟩
  let c : PlayerId := ⟨2⟩
  let d : PlayerId := ⟨1⟩
  let s := ({ removalState with turnOrder := [a, b, c, d], active := some b } : GameState).withdrawSeat b
  s.pickOrder == [c, d, a] && (PlayerSel.eachPlayerFromNext.resolve s c) == some [c, d, a] &&
    (PlayerSel.eachOpponent.resolve s c) == some [d, a] &&
    ((PlayerSel.chosen 0).resolve s c { playerTargets := [b] }).isNone &&
    s.playerTargetOptions c (some .enemy) == [some d, some a]

end RiftboundTest
