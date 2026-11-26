module

import RiftboundDriver.TeamMatch
meta import RiftboundDriver.TeamMatch
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-! # Tests: four registered decks from shuffles through a recorded match -/

namespace RiftboundTest

open Lean Riftbound RiftboundDriver RiftboundCards

private meta def matchDB : CardDB :=
  ⟨db.cards ++ [{ legend with id := cid "L2", name := "Second Legend", sets := [testSet] }] ++
    ([4, 5].map (fun n => { battlefield n with sets := [testSet] }))⟩

private meta def teamRegistrations : List ConstructedDeck :=
  let b := { goodDeck with legend := cid "L2", battlefields := [cid "B3", cid "B4", cid "B5"] }
  [⟨goodDeck, []⟩, ⟨b, []⟩, ⟨goodDeck, []⟩, ⟨b, []⟩]

private meta def eventDate : RulesDate := ⟨2026, 11, 23⟩

private meta def teamEnv : LegalityEnv := constructedLegality .twoVTwo (.global eventDate) [testSet]

private meta def collect (turn : Nat) :
    Nat → Rng → GameState → Array ReplayAnswer → Except String (GameState × Array ReplayAnswer)
  | 0, _, _, _ => .error "setup did not reach the chosen turn"
  | n + 1, rng, state, answers => do
    if state.turn >= turn then return (state, answers)
    let answer := match state.pending with
      | .chanceBattlefield _ :: _ => some (⟨.chance, .pick 0⟩, rng)
      | _ => playAnswer rng state
    let some (action, nextRng) := answer | throw "no answer in team setup"
    let (next, _) ← (step 100 state action).mapError (fun e => reprStr e)
    collect turn n nextRng next (answers.push (.observed action))

private meta def exampleMatch : Except String Unit := do
  let order := Mode.teamTurnOrder true
  let some initial := GameState.initialTeamConstructed matchDB teamEnv order teamRegistrations
    | throw "invalid four-seat setup"
  let (first, earlyAnswers) ← collect 1 40 (Rng.ofSeed 21) initial #[]
  unless first.turnOrder == order && first.active == some ⟨0⟩ && first.battlefields.length == 3 &&
      (first.zone (.player ⟨0⟩ .outOfGame)).length == 3 &&
      (first.zone (.player ⟨0⟩ .hand)).length == 4 do throw "incorrect starting seat or Battlefield setup"
  let invite : Action := ⟨.player ⟨0⟩, .inviteTeammate ⟨1⟩⟩
  let decline : Action := ⟨.player ⟨1⟩, .pass⟩
  let (invited, _) ← (step 100 first invite).mapError (fun e => reprStr e)
  let (resumed, _) ← (step 100 invited decline).mapError (fun e => reprStr e)
  let earlyAnswers := earlyAnswers.push (.observed invite) |>.push (.observed decline)
  let (lastSeat, answers) ← collect 4 20 (Rng.ofSeed 22) resumed earlyAnswers
  unless lastSeat.active == some ⟨3⟩ && (lastSeat.zone (.player ⟨3⟩ .runeDeck)).length == 9 do
    throw "the last seat did not get the extra Rune"
  let game : TeamGameRecord := {
    decks := teamRegistrations, chooser := some ⟨0⟩, order,
    battlefields := [(⟨2⟩, cid "B0"), (⟨1⟩, cid "B3"), (⟨3⟩, cid "B3")],
    points := (0, 0), ending := .draw, answers := answers.push (.observed ⟨.judge, .declareDraw⟩) }
  let win : TeamGameRecord := { game with
    chooser := none, ending := .concede ⟨1⟩, answers := answers.push (.observed ⟨.player ⟨1⟩, .concede⟩) }
  let recorded ← TeamMatchRecord.record {
    seats := ⟨(⟨0⟩, ⟨1⟩), (⟨2⟩, ⟨3⟩)⟩,
    tournament := ⟨eventDate, .twoVTwo, .global eventDate⟩, legalSets := [testSet],
    winsRequired := 1, games := #[game, win], ending := .finalGame } matchDB
  let restored : RecordedTeamMatch ← fromJson? (← Json.parse (toJson recorded).compress)
  let result ← restored.verify matchDB
  unless result.wins == (0, 1) && result.result == .won ⟨1⟩ &&
      restored.games.all (·.summary.exact) do throw "incorrect recorded team winner"
  let some checkpoint := restored.games[0]?.bind (·.checkpoints[2]?) | throw "missing checkpoint"
  let changed := restored.games.modify 0 (fun g =>
    { g with checkpoints := g.checkpoints.set! 2 { checkpoint with state := "0" } })
  unless (match { restored with games := changed }.verify matchDB with
      | .error e => e.contains "team game 1: checkpoint 2"
      | .ok _ => false) do throw "a changed team checkpoint was accepted"
  let interrupted : TeamGameRecord := { game with ending := .matchEnded, answers }
  let stopped := { restored.input with games := #[interrupted], ending := .concede ⟨3⟩ }
  let archive ← stopped.record matchDB
  let summary ← archive.verify matchDB
  unless summary.wins == (0, 0) && summary.result == .won ⟨0⟩ &&
      (archive.games[0]?.any (·.summary.result.isNone)) do throw "an interrupted game was counted"
  let agreed ← ({ stopped with ending := .agreedDraw } : TeamMatchRecord).check matchDB
  unless agreed == { summary with result := .draw } do throw "an agreed match draw was rejected"
  if (({ stopped with ending := .finalGame } : TeamMatchRecord).check matchDB).isOk then
    throw "an unfinished game was accepted as decisive"
  if (({ stopped with games := #[interrupted, win] } : TeamMatchRecord).check matchDB).isOk then
    throw "another game was accepted after an interruption"
  let completed := { interrupted with answers := win.answers }
  if (({ stopped with games := #[completed] } : TeamMatchRecord).record matchDB).isOk then
    throw "a completed game was accepted as interrupted"

#guard exampleMatch.toOption.isSome

-- The same Legend and the same Battlefield may be registered only on opposing teams.
#guard
  let dup := List.replicate 4 (⟨goodDeck, []⟩ : ConstructedDeck)
  (GameState.initialTeamConstructed matchDB teamEnv (Mode.teamTurnOrder true) dup).isNone

end RiftboundTest
