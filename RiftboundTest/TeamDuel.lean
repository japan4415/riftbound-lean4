module

import Riftbound.Engine.Step
meta import Riftbound.Engine.Step
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-! # Tests: two-sided games with four seats -/

namespace RiftboundTest

open Riftbound

private meta def teamState : GameState :=
  GameState.empty { ruleSet := .tournament .constructed, mode := .teamDuel } db

-- Both starting teams are legal; switching their A and B seats is illegal in a tournament.
#guard
  let s := { teamState with pending := [.chanceTurnOrder] }
  let allows (order : List PlayerId) : Bool := decide (Legal s ⟨.chance, .arrangePlayers order⟩)
  allows (Mode.teamTurnOrder true) && allows (Mode.teamTurnOrder false) &&
    !allows [⟨1⟩, ⟨2⟩, ⟨0⟩, ⟨3⟩] && !allows [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]

-- Both teammates read the same score. A win names both winners, with one event per seat.
#guard
  let s := (teamState.gainPoints ⟨1⟩ 10).gainPoints ⟨3⟩ 8
  s.players.map s.pointsOf == [10, 10, 8, 8] && s.winner.isNone &&
    let (finished, events) := cleanupFrame (s.gainPoints ⟨0⟩ 1) []
    finished.result == some (.won [⟨0⟩, ⟨1⟩]) && events == [.won ⟨0⟩, .won ⟨1⟩]

-- A teammate cannot score the same Battlefield for a second point on the same turn.
#guard
  let battlefield := newCard db teamState ⟨0⟩ ⟨"B0"⟩
  match addObject teamState battlefield .battlefieldZone with
  | none => false
  | some (start, id) =>
    let first := scoreBf start ⟨1⟩ id false
    let second := scoreBf first.1 ⟨0⟩ id true
    let opposing := scoreBf second.1 ⟨3⟩ id true
    first.1.pointsOf ⟨0⟩ == 1 && second.2.2.isEmpty &&
      opposing.1.players.map opposing.1.pointsOf == [1, 1, 1, 1]

-- The engine lists concessions from all seats. A single concession ends the team's game.
#guard
  let concede : Action := ⟨.player ⟨1⟩, .concede⟩
  (concedeActions teamState).length == 4 && (legalActions teamState).contains concede &&
    (step 100 teamState concede).toOption.any (fun (s, _) =>
      s.result == some (.won [⟨2⟩, ⟨3⟩]) && (legalActions s).isEmpty)

-- At time, compare the teams' shared scores and award the win to both opposing seats.
#guard
  let start := { ((teamState.gainPoints ⟨1⟩ 4).gainPoints ⟨3⟩ 6) with
    pending := [.priority ⟨0⟩], turn := 1, active := some ⟨0⟩ }
  match step 100 start ⟨.clock, .timeCalled⟩ with
  | .error _ => false
  | .ok (timed, _) =>
    timed.clock == some 4 &&
      (beginTurnStep { timed with turn := 4 } []).result == some (.won [⟨2⟩, ⟨3⟩])

-- Burn Out may award the point to either member of the opposing team.
#guard
  let s := { teamState with pending := [.chooseBurnOut ⟨0⟩] }
  let give (p : PlayerId) : Action := ⟨.player ⟨0⟩, .burnOutTarget p⟩
  legalFrameActions s == [give ⟨2⟩, give ⟨3⟩] && (step 100 s (give ⟨1⟩)).toOption.isNone &&
    (step 100 s (give ⟨3⟩)).toOption.any (fun (next, _) => next.players.map next.pointsOf == [0, 0, 1, 1])

private meta def scoredStepBoard : Option (GameState × ObjId × ObjId) := do
  let start := { teamState with active := some ⟨0⟩, turn := 1 }
  let held := { newCard db start ⟨1⟩ (cid "B0") with control := some ⟨1⟩ }
  let (s, first) ← addObject start held .battlefieldZone
  let (s, second) ← addObject s (newCard db s ⟨0⟩ (cid "B1")) .battlefieldZone
  let unit := { newCard db s ⟨1⟩ (cid "V0") with loc := some first }
  let (s, _) ← addObject s unit .battlefieldZone
  return (s, first, second)

-- A control change later in the turn keeps the scoring-step disqualification in effect.
#guard match scoredStepBoard with
  | none => false
  | some (s, held, _) =>
    let snapshot := (hold s ⟨0⟩).1
    let openField := snapshot.modObj held (fun b => { b with control := none })
    (scoreBf openField ⟨0⟩ held true).2.2.isEmpty &&
      (scoreBf openField ⟨2⟩ held true).1.pointsOf ⟨3⟩ == 1

-- The ally's occupation satisfies the Final Point condition during this side's turn only.
#guard match scoredStepBoard with
  | none => false
  | some (s, _, field) =>
    let onFinalPoint := (s.gainPoints ⟨0⟩ 10).gainPoints ⟨2⟩ 10
    let ready := (hold onFinalPoint ⟨0⟩).1
    (scoreBf onFinalPoint ⟨0⟩ field true).1.pointsOf ⟨0⟩ == 10 &&
      (scoreBf ready ⟨0⟩ field true).1.pointsOf ⟨1⟩ == 11 &&
      (scoreBf ready ⟨2⟩ field true).1.pointsOf ⟨2⟩ == 10

-- The regular and instructed move checks both reject a location occupied by an ally.
#guard (do
  let (s, held, empty) ← scoredStepBoard
  let s := { s with phase := .main }
  let unit := newCard db s ⟨0⟩ (cid "V1")
  let (s, id) ← addObject s unit (.player ⟨0⟩ .base)
  return !s.effectMoveBattlefieldOk unit held && s.effectMoveBattlefieldOk unit empty &&
    !moveOk s ⟨0⟩ id (.battlefield held) && moveOk s ⟨0⟩ id (.battlefield empty)).getD false

-- An instructed move to the ally's Battlefield recalls the Unit.
#guard (do
  let (s, held, openField) ← scoredStepBoard
  let unit := { newCard db s ⟨0⟩ (cid "V1") with loc := some openField }
  let (s, id) ← addObject s unit .battlefieldZone
  let (recalled, events) := moveByEffect ⟨0⟩ (some held) s id
  return (recalled.zone (.player ⟨0⟩ .base)).contains id &&
    (recalled.obj? id).any (fun o : Object => o.loc.isNone) && events == [Event.recalled id]).getD false

-- The two participants must be opponents. The defender is the actual opposing occupant,
-- regardless of who is next in the turn order.
#guard (do
  let (s, held, _) ← scoredStepBoard
  let ally := { newCard db s ⟨0⟩ (cid "V1") with loc := some held }
  let opp := { newCard db s ⟨3⟩ (cid "V2") with loc := some held }
  let (allies, _) ← addObject s ally .battlefieldZone
  let (opponents, _) ← addObject s opp .battlefieldZone
  let pending : List Frame := [.showdown held ⟨1⟩ 0]
  return !allies.isCombat held && (allies.observeCombat pending).1.isNone &&
    opponents.isCombat held && opponents.defenderAt held ⟨1⟩ == (⟨3⟩ : PlayerId) &&
    (opponents.observeCombat pending).1.any (fun r : CombatParticipation =>
      r.attacker == (⟨1⟩ : PlayerId) && r.defender == (⟨3⟩ : PlayerId))).getD false

-- Board effects can select a friendly teammate's Unit. The same side filter on a hand still
-- selects the acting player's own cards.
#guard (do
  let (s, field, _) ← scoredStepBoard
  let (s, own) ← addObject s (newCard db s ⟨0⟩ (cid "V0")) (.player ⟨0⟩ .hand)
  let (s, _) ← addObject s (newCard db s ⟨1⟩ (cid "V1")) (.player ⟨1⟩ .hand)
  let actor : PlayerId := ⟨0⟩
  let units := FilterList.ofList [.ofType .unit]
  return (s.candidates actor field {} .friendly .atBattlefield units) == some (s.unitsOf ⟨1⟩ field) &&
    (s.candidates actor field {} .enemy .atBattlefield units) == some [] &&
    (s.pickCandidates actor field {} .friendly .inHand .nil) == some [own] &&
    PlayerSel.resolve s actor .eachOpponent == (some [⟨2⟩, ⟨3⟩] : Option (List PlayerId))).getD false

-- An invited teammate funds and casts an ordinary spell. The turn player stays active and
-- takes back priority when the spell finishes. Declining also gives back priority.
#guard (do
  let turnPlayer : PlayerId := ⟨0⟩
  let guest : PlayerId := ⟨1⟩
  let start := { teamState with
    phase := .main, turn := 1, active := some turnPlayer,
    turnOrder := Mode.teamTurnOrder true, pending := [.priority turnPlayer] }
  let (s, rune) ← addObject start (newCard db start guest (cid "R1")) (.player guest .base)
  let (s, spell) ← addObject s (newCard db s guest (cid "SP0")) (.player guest .hand)
  let (s, unit) ← addObject s (newCard db s guest (cid "V0")) (.player guest .hand)
  let (s, _) ← addObject s (newCard db s guest (cid "V1")) (.player guest .mainDeck)
  let invite : Action := ⟨.player turnPlayer, .inviteTeammate guest⟩
  let decline : Action := ⟨.player guest, .pass⟩
  let pay : RunePool.Payment := { energy := 1, power := [] }
  let cast : Action := ⟨.player guest, .playCard spell pay []⟩
  let playUnit : Action := ⟨.player guest, .playCard unit pay []⟩
  let (offered, _) ← (step 100 s invite).toOption
  let (returned, _) ← (step 100 offered decline).toOption
  let (funded, _) ← (step 100 offered ⟨.player guest, .runeAbility rune .exhaust⟩).toOption
  let (chained, _) ← (step 100 funded cast).toOption
  let finished ← ([(⟨1⟩ : PlayerId), ⟨3⟩, ⟨0⟩, ⟨2⟩].foldlM (m := Option) (fun state seat =>
    ((step 100 state ⟨.player seat, .pass⟩).toOption).map Prod.fst) chained)
  return (legalFrameActions s).contains invite && !(legalFrameActions s).contains cast &&
    (step 100 s ⟨.player turnPlayer, .inviteTeammate ⟨2⟩⟩).toOption.isNone &&
    offered.pending == [Frame.teamInvitation guest, Frame.priority turnPlayer] &&
    returned.pending == [Frame.priority turnPlayer] && (legalFrameActions funded).contains cast &&
    !(legalFrameActions funded).contains playUnit && (step 100 funded playUnit).toOption.isNone &&
    chained.pending == [Frame.chainPass guest 0, Frame.priority turnPlayer] &&
    finished.pending == [Frame.priority turnPlayer] && finished.active == some turnPlayer &&
    (finished.zone (.player guest .mainDeck)).isEmpty).getD false

#guard (do
  let turnPlayer : PlayerId := ⟨0⟩
  let guest : PlayerId := ⟨1⟩
  let abilityCard := { vanilla 0 with
    id := cid "Invitation Ability",
    abilities := [.activated [.exhaustSelf] .normal (EffectDef.of [] (.prim (.draw .you (.const 1)))) .unlimited] }
  let testDB : CardDB := ⟨db.cards ++ [abilityCard]⟩
  let s := GameState.empty teamState.config testDB
  let s := { s with phase := .main, active := some turnPlayer, pending := [.priority turnPlayer] }
  let (s, src) ← addObject s (newCard testDB s guest abilityCard.id) (.player guest .base)
  let ability : Action := ⟨.player guest, .activate src 0 ⟨0, []⟩ []⟩
  let (offered, _) ← (step 100 s ⟨.player turnPlayer, .inviteTeammate guest⟩).toOption
  let (chained, _) ← (step 100 offered ability).toOption
  return (legalFrameActions offered).contains ability && !(legalFrameActions s).contains ability &&
    chained.pending == [Frame.chainPass guest 0, Frame.priority turnPlayer] &&
    (chained.obj? src).any (fun o : Object => o.exhausted)).getD false

-- If the last seat gets an early extra turn, its bonus is paid then. No later extra turn
-- may receive the same opening bonus again.
#guard
  let s := { teamState with
    turnOrder := Mode.teamTurnOrder true, turn := 3, active := some ⟨1⟩, extraTurns := [⟨3⟩] }
  let early := beginTurnStep s []
  let regular := beginTurnStep early []
  let late := beginTurnStep { regular with extraTurns := [⟨2⟩] } []
  [early.channelCount, regular.channelCount, late.channelCount] == [3, 2, 2]

-- Effects that check enemy control or earlier enemy choices ignore teammates' objects.
#guard (do
  let (s, held, _) ← scoredStepBoard
  let s := { s with phase := .main }
  let (s, source) ← addObject s (newCard db s ⟨0⟩ (cid "V0")) (.player ⟨0⟩ .base)
  let ally ← (s.unitsOf ⟨1⟩ held).head?
  let (s, enemy) ← addObject s (newCard db s ⟨2⟩ (cid "V1")) (.player ⟨2⟩ .base)
  let watched (target : ObjId) :=
    (s.recordTurnEvents [.chosenBySpell ⟨0⟩ target]).turnFx.any (·.kind == TurnEffect.choseEnemyUnit)
  let opposed := s.modObj held (fun o => { o with control := some ⟨2⟩ })
  return Filter.holds s source {} held .controlledByOpponent == some false &&
    Filter.holds opposed source {} held .controlledByOpponent == some true && !watched ally && watched enemy)
  |>.getD false

#guard
  let s := { teamState with turnOrder := Mode.teamTurnOrder true, active := some ⟨2⟩ }
  let trigger (p : PlayerId) : PendTrigger := { source := ⟨p.n⟩, card := cid "V0", idx := 0, controller := p }
  let pending := [⟨3⟩, ⟨0⟩, ⟨1⟩, ⟨2⟩].map trigger
  (s.detect [] pending).map PendTrigger.controller == ([⟨2⟩, ⟨1⟩, ⟨3⟩, ⟨0⟩] : List PlayerId)

-- A staged non-combat Showdown precedes a Combat. With two Combats, the turn player can
-- open either Battlefield, including the second one on the board.
#guard (do
  let current : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let opponent : PlayerId := ⟨2⟩
  let s := { teamState with
    phase := .main, active := some current, turn := 1, turnOrder := Mode.teamTurnOrder true }
  let (s, a) ← addObject s { newCard db s current (cid "B0") with contested := some current } .battlefieldZone
  let (s, b) ← addObject s { newCard db s opponent (cid "B1") with contested := some opponent } .battlefieldZone
  let put (s : GameState) (p : PlayerId) (bf : ObjId) :=
    (addObject s { newCard db s p (cid "V0") with loc := some bf } .battlefieldZone).map Prod.fst
  let s ← put s current a
  let s ← put s opponent a
  let s ← put s opponent b
  let onlyNoncombat := s.stagedShowdowns [.priority current]
  let s ← put s ally b
  let (choice, opening) := cleanupFrame s [.priority current]
  let select (p : PlayerId) (field : ObjId) : Action := ⟨.player p, .choose field⟩
  let (resolved, events) ← (step 100 choice (select current b)).toOption
  return onlyNoncombat == [(b, opponent)] && opening.isEmpty &&
    (legalFrameActions choice).contains (select current a) &&
    (legalFrameActions choice).contains (select current b) &&
    (step 100 choice (select ally b)).toOption.isNone &&
    (resolved.combat.any (fun fight : CombatParticipation => fight.battlefield == b)) &&
    events.contains (Event.combatStarted b opponent)).getD false

end RiftboundTest
