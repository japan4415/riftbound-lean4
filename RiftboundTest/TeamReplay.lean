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
    if state.turn >= turn || state.result.isSome then return (state, answers)
    let answer := match state.pending with
      | .chanceBattlefield _ :: _ => some (⟨.chance, .pick 0⟩, rng)
      | _ => playAnswer rng state
    let some (action, nextRng) := answer | throw "no answer in team setup"
    let (next, _) ← (step 100 state action).mapError (fun e => reprStr e)
    collect turn n nextRng next (answers.push (.observed action))

private meta def recordGroupMove (start : GameState) (answers : Array ReplayAnswer) :
    Except String (GameState × Array ReplayAnswer) := do
  let player : PlayerId := ⟨0⟩
  let answer (state : GameState) (tape : Array ReplayAnswer) (kind : ActionKind) := do
    let action := Action.mk (.player player) kind
    let (next, _) ← (step 100 state action).mapError reprStr
    pure (next, tape.push (.observed action))
  let mut state := start
  let mut tape := answers
  let runes := (state.zone (.player player .base)).filter (fun id => state.hasType id .rune)
  for rune in runes.take 2 do
    let next ← answer state tape (.runeAbility rune .exhaust)
    state := next.1
    tape := next.2
  for _ in [:2] do
    let some play := (legalPlays state player).head? | throw "no Unit available for the group"
    let next ← answer state tape play.kind
    state := next.1
    tape := next.2
  let (lastSeat, tapeAtFour) ← collect 4 25 (Rng.ofSeed 22) state tape
  unless lastSeat.active == some ⟨3⟩ && (lastSeat.zone (.player ⟨3⟩ .runeDeck)).length == 9 do
    throw "the last seat did not get the extra Rune"
  let (nextTurn, tapeAtFive) ← collect 5 10 (Rng.ofSeed 23) lastSeat tapeAtFour
  state := nextTurn
  tape := tapeAtFive
  let some field := state.battlefields.head? | throw "no destination for the group"
  let [first, second] := state.groupMoveChoices player (.battlefield field) | throw "expected two ready Units"
  for kind in [ActionKind.startGroupMove (.battlefield field) Cost.zero, .choose first, .choose second, .decide true] do
    let next ← answer state tape kind
    state := next.1
    tape := next.2
  unless state.unitsOf player field == [second, first] || state.unitsOf player field == [first, second] do
    throw "the group was not moved together"
  return (state, tape)

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
  let (moved, groupAnswers) ← recordGroupMove resumed earlyAnswers
  let (afterShowdown, answers) ← collect 6 15 (Rng.ofSeed 24) moved groupAnswers
  let game : TeamGameRecord := {
    decks := teamRegistrations, chooser := some ⟨0⟩, order,
    battlefields := [(⟨2⟩, cid "B0"), (⟨1⟩, cid "B3"), (⟨3⟩, cid "B3")],
    points := (afterShowdown.pointsOf ⟨0⟩, afterShowdown.pointsOf ⟨2⟩), ending := .draw,
    answers := answers.push (.observed ⟨.judge, .declareDraw⟩) }
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
  let tied := { interrupted with points := (11, 11) }
  let tiedCheck ← ({ stopped with games := #[tied] } : TeamMatchRecord).check matchDB
  unless tiedCheck.result == .won ⟨0⟩ do throw "a tied victory score ended the game"
  let goAhead := { interrupted with points := (12, 11), ending := .scored }
  let scored ← ({ stopped with games := #[goAhead], ending := .finalGame } : TeamMatchRecord).check matchDB
  unless scored.result == .won ⟨0⟩ && scored.wins == (1, 0) do throw "a score above the threshold was rejected"
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

private meta def suddenDeathMatch : Except String Unit := do
  let order := Mode.teamTurnOrder true
  let some initial := GameState.initialTeamConstructed matchDB teamEnv order teamRegistrations
      (.tournamentElimination .constructed (.regular true)) | throw "invalid four-seat setup"
  let (first, setup) ← collect 1 40 (Rng.ofSeed 21) initial #[]
  let clock := Action.mk .clock .timeCalled
  let (timed, _) ← (step 100 first clock).mapError reprStr
  let (moved, tape) ← recordGroupMove timed (setup.push (.observed clock))
  let (finish, answers) ← collect 6 15 (Rng.ofSeed 24) moved tape
  unless finish.turn == 5 && finish.result == some (.won [⟨0⟩, ⟨1⟩]) do
    throw "the first scoring side did not win sudden death"
  let game : TeamGameRecord := {
    decks := teamRegistrations, chooser := some ⟨0⟩, order,
    battlefields := [(⟨2⟩, cid "B0"), (⟨1⟩, cid "B3"), (⟨3⟩, cid "B3")],
    points := (1, 0), ending := .suddenDeath ⟨0⟩, timed := true, answers }
  let input : TeamMatchRecord := {
    seats := ⟨(⟨0⟩, ⟨1⟩), (⟨2⟩, ⟨3⟩)⟩,
    tournament := ⟨eventDate, .twoVTwo, .global eventDate⟩, legalSets := [testSet],
    winsRequired := 2, elimination? := some {}, games := #[game], ending := .finalGame }
  let archive ← input.record matchDB
  let restored : RecordedTeamMatch ← fromJson? (← Json.parse (toJson archive).compress)
  let result ← restored.verify matchDB
  unless result.wins == (1, 0) && result.result == .won ⟨0⟩ do
    throw "the recorded sudden-death point did not decide the match"
  if ({ input with games := #[{ game with ending := .time }] }.record matchDB).isOk then
    throw "a sudden-death point was accepted as a deadline result"

#guard suddenDeathMatch.toOption.isSome

private meta def teamBStarts : Except String Unit := do
  let order : List PlayerId := [⟨1⟩, ⟨3⟩, ⟨0⟩, ⟨2⟩]
  let some initial := GameState.initialTeamConstructed matchDB teamEnv order teamRegistrations
    | throw "the B starting seat was refused"
  let (start, setup) ← collect 1 40 (Rng.ofSeed 21) initial #[]
  unless start.active == some ⟨1⟩ && (start.zone (.player ⟨1⟩ .outOfGame)).length == 3 do
    throw "the starting B seat contributed a Battlefield or failed to go first"
  let game : TeamGameRecord := {
    decks := teamRegistrations, chooser := some ⟨0⟩, order,
    battlefields := [(⟨3⟩, cid "B3"), (⟨0⟩, cid "B0"), (⟨2⟩, cid "B0")],
    points := (0, 0), ending := .draw, answers := setup.push (.observed ⟨.judge, .declareDraw⟩) }
  let next := { game with
    chooser := none, ending := .concede ⟨3⟩, answers := setup.push (.observed ⟨.player ⟨3⟩, .concede⟩) }
  let input : TeamMatchRecord := {
    seats := ⟨(⟨0⟩, ⟨1⟩), (⟨2⟩, ⟨3⟩)⟩,
    tournament := ⟨eventDate, .twoVTwo, .global eventDate⟩, legalSets := [testSet],
    winsRequired := 1, games := #[game, next], ending := .finalGame }
  let archive ← input.record matchDB
  let result ← archive.verify matchDB
  unless result.result == .won ⟨0⟩ do throw "the B-start match did not replay to its observed result"
  let changed := { next with order := Mode.teamTurnOrder true }
  let invalid : TeamMatchRecord := { input with games := #[game, changed] }
  if (invalid.check matchDB).isOk then throw "the starting seat changed after a draw"

#guard teamBStarts.toOption.isSome

-- The same Legend and the same Battlefield may be registered only on opposing teams.
#guard
  let dup := List.replicate 4 (⟨goodDeck, []⟩ : ConstructedDeck)
  (GameState.initialTeamConstructed matchDB teamEnv (Mode.teamTurnOrder true) dup).isNone

end RiftboundTest
