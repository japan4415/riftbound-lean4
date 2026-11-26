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

end RiftboundTest
