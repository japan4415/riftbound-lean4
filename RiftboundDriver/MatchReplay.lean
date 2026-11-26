module

public import RiftboundDriver.Replay

/-!
# Replay across games

The match keeps its original registration and rule environment. Each new game has its own deck
configuration and answers. The transitions are validated before accepting the match outcome.
-/

public section

namespace RiftboundDriver

open Lean Riftbound RiftboundCards

/-- The official event selection used to obtain the Constructed legality environment. -/
structure ReplayTournament where
  /-- The local date of the event. -/
  date : RulesDate
  /-- The selected competitive format. -/
  format : ConstructedFormat
  /-- The global date or the locally applicable set season. -/
  banPeriod : BanListPeriod
deriving DecidableEq, Repr, ToJson, FromJson

/-- How the recorded match ended. -/
inductive ReplayMatchEnd where
  /-- The last game decided the match, including time called during that game. -/
  | finalGame
  /-- Time was called while waiting to begin another game (TR 408.2.d). -/
  | timeBetweenGames
  /-- A seat conceded the match (TR 410.2). -/
  | concede (seat : PlayerId)
  /-- Both seats agreed to a draw of the match (TR 410.2). -/
  | agreedDraw
deriving DecidableEq, Repr, ToJson, FromJson

/-- The match format, rule environment and recorded game input streams. -/
structure MatchInputs where
  /-- The game configuration, including the pinned legality environment of a tournament. -/
  config : GameConfig
  /-- Optional event metadata identifying the official Constructed ban list. -/
  tournament : Option ReplayTournament := none
  /-- The number of wins that finishes the match. -/
  winsRequired : Nat
  /-- The engine's per-answer work limit, retained so it is the same when verifying. -/
  fuel : Nat := 100
  /-- The games in chronological order. -/
  games : Array GameInputs
  /-- How the match ended. -/
  ending : ReplayMatchEnd
deriving DecidableEq, Repr, ToJson, FromJson

/-- The result of running every game and applying the match transitions. -/
structure ReplayMatchResult where
  /-- The number of games won by each seat. -/
  wins : Nat × Nat
  /-- The final match outcome. -/
  result : MatchResult
  /-- Whether every game was reproduced without any inferred answers. -/
  exact : Bool
  /-- Whether all checked registrations consist exclusively of fully verified card definitions. -/
  cardsFullyChecked : Bool
deriving DecidableEq, Repr, ToJson, FromJson

/-- The on-disk archive for independent replay and verification. -/
structure RecordedMatch where
  /-- Rules and card database identity. -/
  rules : ReplayRules
  /-- The match inputs. -/
  input : MatchInputs
  /-- Evidence for every game. -/
  games : Array RecordedGame
  /-- The match outcome. -/
  summary : ReplayMatchResult
deriving DecidableEq, Repr, ToJson, FromJson

/-- Resolve the official ban list for the event and its selected card sets. -/
def ReplayTournament.legality (event : ReplayTournament) (format : ConstructedFormat)
    (sets : List SetCode) : Except String LegalityEnv := do
  if !decide event.date.WellFormed then throw "invalid local tournament date"
  if let .global date := event.banPeriod then
    if date != event.date then throw "the global ban-list date differs from the event date"
  if event.format != format then throw "the event uses the wrong Constructed format"
  return constructedLegality format event.banPeriod sets

/-- Check the tournament metadata against the legality environment of a Duel. -/
def checkReplayEvent (config : GameConfig) (event : Option ReplayTournament)
    : Except String Unit := do
  if let some event := event then
    let some env := config.formatLegality | throw "the tournament needs pinned format legality"
    let official ← event.legality .standard env.legalSets
    if config.ruleSet != .tournament .constructed || env != official then
      throw "the pinned environment disagrees with the official event ban list"

/-- An inter-game registration must use the same pool and keep the same fixed slots. -/
def sameRegisteredPool (old new : ConstructedDeck) : Bool :=
  let a := old.deck
  let b := new.deck
  a.legend == b.legend && decide (a.runes.Perm b.runes) &&
    decide (a.battlefields.Perm b.battlefields) && decide (a.reserveLegends.Perm b.reserveLegends) &&
    decide (List.Perm (a.main ++ old.sideboard) (b.main ++ new.sideboard))

/-- Compare Constructed registrations, allowing a reordering of the same cards. -/
def sameRegistration (old new : ConstructedDeck) : Bool :=
  sameRegisteredPool old new && old.deck.chosenChampion == new.deck.chosenChampion &&
    decide (old.deck.main.Perm new.deck.main) && decide (old.sideboard.Perm new.sideboard)

private def checkDecks (state : MatchState) (previous next : ReplayDecks) : Except String Unit := do
  if previous == next then return
  match previous, next with
  | .constructed old, .constructed new =>
    if old.length != new.length then throw "the number of registrations changed"
    for (a, b) in old.zip new do
      if !state.sideboardAllowed && !sameRegistration a b then
        throw "deck changes are unavailable before this game"
      if state.sideboardAllowed && !sameRegisteredPool a b then
        throw "a Constructed change must use the registered cards and preserve the fixed slots"
  | _, _ => throw "the deck change has no verifiable registered sideboard"

private def checkOrder (config : GameConfig) (state : MatchState)
    (chooser : Option PlayerId) (order : List PlayerId) : Except String Unit := do
  if !config.ruleSet.isTournament || order.isEmpty then return
  match state.nextOrder with
  | .chance =>
    if !(chooser.any (fun p => p.n < 2)) then throw "the seat chosen by chance is missing"
  | .loserChooses p =>
    if chooser != some p then throw s!"seat {p.n} must choose who goes first"
  | .same p =>
    if chooser.isSome || order.head? != some p then
      throw s!"seat {p.n} must still go first after a draw"

private def checkBattlefields (state : MatchState) (previous next : ReplayGameResult) :
    Except String Unit := do
  if !state.reuseBattlefields then return
  for (seat, field) in next.battlefields do
    if let some prior := previous.battlefields.lookup seat then
      if prior != field then throw s!"seat {seat.n} must use the same Battlefield after a draw"

/-- Determine the final match outcome from its game wins and how it was ended. -/
def concludeReplayMatch (state : MatchState) (timed : Bool) (ending : ReplayMatchEnd) :
    Except String MatchResult :=
  match state.winner, timed, ending with
  | some winner, _, .finalGame => pure (.won winner)
  | none, true, .finalGame => pure state.onTime
  | none, false, .timeBetweenGames =>
    if state.games > 0 then pure state.onTime else throw "no game has been played"
  | none, false, .agreedDraw => pure MatchState.agreedDrawMatch
  | none, false, .concede p =>
    if p.n < 2 then pure (MatchState.concedeMatch p) else throw "invalid concession seat"
  | _, _, _ => throw "the stated match ending disagrees with the game results"

private def runMatch (input : MatchInputs) (db : CardDB) (rules : ReplayRules)
    (expected : Option (Array RecordedGame)) : Except String RecordedMatch := do
  if input.config.mode != Mode.duel then throw "a replayable Duel match requires the 1v1 mode"
  if input.winsRequired != 1 && input.winsRequired != 2 then throw "invalid number of wins required"
  if input.config.ruleSet == .coreOnly && input.ending == .timeBetweenGames then
    throw "the match clock requires Tournament Rules"
  if expected.any (fun games => games.size != input.games.size) then
    throw "the recorded game count differs"
  checkReplayEvent input.config input.tournament
  let mut state := MatchState.start input.winsRequired
  let mut games : Array RecordedGame := #[]
  let mut previous : Option RecordedGame := none
  let mut timed := false
  for (game, index) in input.games.toList.zipIdx do
    let result := do
      if state.finished || timed then throw "a game starts after the match is over"
      if let some prior := previous then checkDecks state prior.input.decks game.decks
      let recorded ← match expected.bind (·[index]?) with
        | some saved =>
          if saved.input != game then throw "the saved game input differs"
          let _ ← saved.verify db input.config input.fuel
          pure saved
        | none => game.record db input.config input.fuel
      checkOrder input.config state game.chooser recorded.summary.turnOrder
      if let some prior := previous then checkBattlefields state prior.summary recorded.summary
      pure recorded
    let recorded ← result.mapError (fun error => s!"game {index + 1}: {error}")
    if let some result := recorded.summary.result then
      let first := recorded.summary.turnOrder.head?
      state := { state.record result (first.getD ⟨0⟩) with lastFirst := first }
    else if index + 1 != input.games.size ||
        !(match input.ending with | .concede _ | .agreedDraw => true | _ => false) then
      throw s!"game {index + 1}: the recorded answers do not finish the game"
    timed := recorded.summary.timed && recorded.summary.result.isSome
    games := games.push recorded
    previous := some recorded
  let outcome ← concludeReplayMatch state timed input.ending
  return { rules, input, games, summary := {
    wins := (state.wins0, state.wins1), result := outcome
    exact := games.all (·.summary.exact)
    cardsFullyChecked := games.all (fun game => game.summary.uncheckedCards.all List.isEmpty)
  } }

/-- Record a complete 1v1 match using the same engine and setup checks as a played game. -/
def MatchInputs.record (input : MatchInputs) (db : CardDB := RiftboundCards.db) :
    Except String RecordedMatch :=
  runMatch input db (ReplayRules.current db) none

/-- Finalize a match using evidence captured while each game was played. -/
def MatchInputs.recordPlayed (input : MatchInputs) (games : Array RecordedGame) (db : CardDB) :
    Except String RecordedMatch :=
  runMatch input db (ReplayRules.current db) (some games)

/-- Read a saved match, checking its pinned rules, every game and its final outcome. -/
def RecordedMatch.verify (saved : RecordedMatch) (db : CardDB := RiftboundCards.db) :
    Except String ReplayMatchResult := do
  let rules := ReplayRules.current db
  if saved.rules != rules then throw "the replay format, rules edition or card definitions differ"
  let actual ← runMatch saved.input db rules (some saved.games)
  if actual.summary != saved.summary then throw "the final match outcome differs"
  return actual.summary

end RiftboundDriver

end
