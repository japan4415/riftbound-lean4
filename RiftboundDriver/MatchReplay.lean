module

public import RiftboundDriver.LimitedReplay

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
  /-- The judge applied a Match Loss to the seat and their team (TR 701.2.c). -/
  | matchLoss (seat : PlayerId)
  /-- The seat was disqualified and loses the current match (TR 701.2.d.1). -/
  | disqualification (seat : PlayerId)
deriving DecidableEq, Repr, ToJson, FromJson

/-- A seat that lost by a judge's penalty. -/
def ReplayMatchEnd.penalizedSeat : ReplayMatchEnd → Option PlayerId
  | .matchLoss seat | .disqualification seat => some seat
  | _ => none

/-- The individual named by a concession or penalty. -/
def ReplayMatchEnd.affectedSeat : ReplayMatchEnd → Option PlayerId
  | .concede seat => some seat
  | ending => ending.penalizedSeat

/-- Translate an individual result to the side responsible for it. -/
def ReplayMatchEnd.mapSeat (ending : ReplayMatchEnd) (f : PlayerId → PlayerId) : ReplayMatchEnd :=
  match ending with
  | .concede seat => .concede (f seat)
  | .matchLoss seat => .matchLoss (f seat)
  | .disqualification seat => .disqualification (f seat)
  | other => other

/-- An external match result can interrupt a game or the preparations for the next game. -/
def ReplayMatchEnd.interrupts : ReplayMatchEnd → Bool
  | .concede _ | .agreedDraw | .matchLoss _ | .disqualification _ => true
  | _ => false

/-- Opt in to TR 408.4. A time call between games is recorded separately from in-game answers. -/
structure ReplayElimination where
  /-- The number of completed games at a between-game call that required a new game. -/
  timeAfterGames? : Option Nat := none
deriving DecidableEq, Repr, ToJson, FromJson

/-- The match format, rule environment and recorded game input streams. -/
structure MatchInputs where
  /-- The game configuration, including the pinned legality environment of a tournament. -/
  config : GameConfig
  /-- Optional event metadata identifying the official Constructed ban list. -/
  tournament : Option ReplayTournament := none
  /-- The observed Sealed or Draft pool for each seat. Required to verify Limited sideboarding. -/
  limitedPools? : Option (List (List CardId)) := none
  /-- The timed single-elimination procedure, when selected for this match. -/
  elimination? : Option ReplayElimination := none
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
  /-- Whether all games were reproduced from directly and uniquely observed inputs. -/
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
    if config.ruleSet.tournamentFormat != some .constructed || env != official then
      throw "the pinned environment disagrees with the official event ban list"

/-- Compare Constructed registrations, allowing a reordering of the same cards. -/
def sameRegistration (old new : ConstructedDeck) : Bool :=
  sameRegisteredPool old new && old.deck.chosenChampion == new.deck.chosenChampion &&
    decide (old.deck.main.Perm new.deck.main) && decide (old.sideboard.Perm new.sideboard)

/-- Check changes between games. A supplied Limited pool validates the allocation separately. -/
def checkReplayDeckChange (state : MatchState) (previous next : ReplayDecks)
    (limitedPoolKnown : Bool) : Except String Unit := do
  if previous == next then return
  match previous, next with
  | .constructed old, .constructed new =>
    if old.length != new.length then throw "the number of registrations changed"
    for (a, b) in old.zip new do
      if !state.sideboardAllowed && !sameRegistration a b then
        throw "deck changes are unavailable before this game"
      if state.sideboardAllowed && !sameRegisteredPool a b then
        throw "a Constructed change must use the registered cards and preserve the fixed slots"
  | .limited old, .limited new =>
    if !limitedPoolKnown then throw "the deck change has no verifiable registered sideboard"
    if old.length != new.length then throw "the number of registrations changed"
    unless state.sideboardAllowed ||
        (old.zip new).all (fun (a, b) => sameLimitedRegistration a b (state.target == 2)) do
      throw "Limited deck changes are unavailable before this game"
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

/-- A normal draw reuses its Battlefields; Game Loss penalties use the exception in TR 406.1.c. -/
def reuseReplayBattlefields (state : MatchState) (previousWasGameLoss : Bool) : Bool :=
  state.reuseBattlefields && !previousWasGameLoss

private def checkBattlefields (reuse : Bool) (previous next : ReplayGameResult) :
    Except String Unit := do
  if !reuse then return
  for (seat, field) in next.battlefields do
    if let some prior := previous.battlefields.lookup seat then
      if prior != field then throw s!"seat {seat.n} must use the same Battlefield after a draw"

/-- Timed single elimination starts a new game whenever completed games leave no match leader
(TR 408.4.a, 408.4.c.1, 408.4.d). -/
def needsTimedTiebreaker (state : MatchState) (elimination : Bool) : Bool :=
  elimination && state.onTime == .draw

/-- Resolve whether the game starts after time has been called and check the recorded boundary. -/
def gameStartsAfterTime (state : MatchState) (timed : Bool) (clock : Option ReplayElimination) :
    Except String Bool := do
  if state.finished || (timed && !needsTimedTiebreaker state clock.isSome) then
    throw "a game starts after the match is over"
  if (clock.bind (·.timeAfterGames?)) != some state.games then return timed
  if timed || !needsTimedTiebreaker state clock.isSome then
    throw "the between-game time call does not require a new game"
  return true

/-- A between-game time call requires a completed game and the next game in a full record,
unless the match was interrupted before the tiebreaker started. -/
def checkReplayClockBoundary (clock : Option ReplayElimination) (games : Nat)
    (ending : ReplayMatchEnd) (allowIncomplete : Bool := false) : Except String Unit := do
  if let some completed := clock.bind (·.timeAfterGames?) then
    if completed == 0 || (!allowIncomplete &&
        (completed > games || (completed == games && !ending.interrupts))) then
      throw "the between-game time call must precede a recorded tiebreaker game"

/-- Validate a time call immediately before a match interruption between games. -/
def checkInterruptedClockBoundary (state : MatchState) (timed : Bool)
    (clock : Option ReplayElimination) (games : Nat) : Except String Unit := do
  if (clock.bind (·.timeAfterGames?)) == some games then
    unless state.games == games do throw "the time call requires a completed game"
    let _ ← gameStartsAfterTime state timed clock

/-- Obtain a game's rule configuration from the match phase and the existing game wins. -/
def replayGameConfig (config : GameConfig) (state : MatchState)
    (elimination afterTime : Bool) : GameConfig :=
  match config.ruleSet, elimination with
  | .tournament f, true =>
    let game := if afterTime then EliminationGame.tiebreaker else .regular (state.wins0 == state.wins1)
    { config with ruleSet := .tournamentElimination f game }
  | _, _ => config

/-- Determine the final match outcome from its game wins and how it was ended. -/
def concludeReplayMatch (state : MatchState) (timed : Bool) (ending : ReplayMatchEnd)
    (elimination : Bool := false) :
    Except String MatchResult :=
  match state.winner, timed, ending with
  | some winner, _, .finalGame => pure (.won winner)
  | none, true, .finalGame =>
    if needsTimedTiebreaker state elimination then throw "a timed tiebreaker game is required"
    else pure state.onTime
  | none, false, .timeBetweenGames =>
    if state.games == 0 then throw "no game has been played"
    else if needsTimedTiebreaker state elimination then throw "a timed tiebreaker game is required"
    else pure state.onTime
  | none, _, .agreedDraw =>
    if !timed || needsTimedTiebreaker state elimination then pure MatchState.agreedDrawMatch
    else throw "the match is over"
  | none, _, .concede p =>
    if timed && !needsTimedTiebreaker state elimination then throw "the match is over"
    else if p.n < 2 then pure (MatchState.concedeMatch p) else throw "invalid concession seat"
  | none, _, .matchLoss p | none, _, .disqualification p =>
    if timed && !needsTimedTiebreaker state elimination then throw "the match is over"
    else if p.n < 2 then pure (MatchState.concedeMatch p) else throw "invalid penalty seat"
  | _, _, _ => throw "the stated match ending disagrees with the game results"

private def runMatchProgress (input : MatchInputs) (db : CardDB) (rules : ReplayRules)
    (expected : Option (Array RecordedGame)) (refreshCoverage : Bool) (inspectAt : Option Nat)
    (upgradePermanentChoices : Bool := false) :
    Except String (Sum ReplayInspection RecordedMatch) := do
  if input.config.mode != Mode.duel then throw "a replayable Duel match requires the 1v1 mode"
  if input.winsRequired != 1 && input.winsRequired != 2 then throw "invalid number of wins required"
  if let .tournamentElimination .. := input.config.ruleSet then
    throw "choose single elimination on the match, rather than setting a per-game procedure"
  if input.elimination?.isSome && !input.config.ruleSet.isTournament then
    throw "single elimination uses Tournament Rules"
  if input.config.ruleSet == .coreOnly && input.ending == .timeBetweenGames then
    throw "the match clock requires Tournament Rules"
  if input.ending.penalizedSeat.isSome && !input.config.ruleSet.isTournament then
    throw "match penalties require Tournament Rules"
  if expected.any (fun games => games.size != input.games.size) then
    throw "the recorded game count differs"
  checkReplayEvent input.config input.tournament
  checkReplayClockBoundary input.elimination? input.games.size input.ending inspectAt.isSome
  if let some pools := input.limitedPools? then
    unless input.config.ruleSet.isLimited && pools.length == 2 do
      throw "two recorded pools are required for this Limited match"
    pools.forM (checkLimitedPool db)
  let mut state := MatchState.start input.winsRequired
  let mut games : Array RecordedGame := #[]
  let mut previous : Option RecordedGame := none
  let mut timed := false
  let mut usedFields := ([], [])
  let mut penaltyFields := []
  for (game, index) in input.games.toList.zipIdx do
    let result := do
      if game.bo1Setup?.isSome && (index != 0 || input.winsRequired != 1) then
        throw "the optional Best of 1 setup is only used to start a Best of 1 match"
      let afterTime ← gameStartsAfterTime state timed input.elimination?
      let config := replayGameConfig input.config state input.elimination?.isSome afterTime
      if let some prior := previous then
        checkReplayDeckChange state prior.input.decks game.decks input.limitedPools?.isSome
      if let some pools := input.limitedPools? then
        let .limited ds := game.decks | throw "the registrations must use the Limited format"
        unless ds.length == 2 do throw "the two seat registrations are required"
        checkLimitedBattlefieldCount db ds (allPlayers 2) (state.target == 2)
        for ((pool, deck), seat) in (pools.zip ds).zipIdx do
          checkLimitedCopies pool (limitedAllocation [deck]) s!"seat {seat}"
      let played : Sum ReplayInspection RecordedGame ←
        if inspectAt == some index then
          Sum.inl <$> game.inspect db config input.fuel
        else
          Sum.inr <$> (match expected.bind (·[index]?) with
            | some saved => do
              if saved.input != game then throw "the saved game input differs"
              saved.checkEvidence db config input.fuel refreshCoverage upgradePermanentChoices
            | none => game.record db config input.fuel)
      let summary := match played with
        | .inl inspection => inspection.summary game.decks
        | .inr recorded => recorded.summary
      checkOrder input.config state game.chooser summary.turnOrder
      let reuse := reuseReplayBattlefields state (previous.any (fun (prior : RecordedGame) => prior.gameLossSeats.isSome))
      if let some prior := previous then checkBattlefields reuse prior.summary summary
      checkPenaltyBattlefields penaltyFields summary.battlefields
      let used ← match input.limitedPools? with
        | some [a, b] => do
          let selected (p : PlayerId) := (summary.battlefields.lookup p).toList
          pure (← useLimitedBattlefields a usedFields.1 (selected ⟨0⟩) reuse,
            ← useLimitedBattlefields b usedFields.2 (selected ⟨1⟩) reuse)
        | _ => pure usedFields
      pure (played, used)
    let (played, used) ← result.mapError (fun error => s!"game {index + 1}: {error}")
    match played with
      | .inl inspection =>
        let (chooser, forcedFirst) := if input.config.ruleSet.isTournament then
          match state.nextOrder with
          | .same p => (none, some p)
          | .loserChooses p => (some p, none)
          | .chance => (inspection.chooser, none)
          else (inspection.chooser, none)
        return .inl { inspection with
          chooser, forcedFirst, exact := inspection.exact && games.all (·.summary.exact) }
      | .inr recorded =>
        usedFields := used
        penaltyFields := penaltyFields ++ recorded.penaltyBattlefields
        if let some result := recorded.summary.result then
          let first := recorded.summary.turnOrder.head?
          state := { state.record result (first.getD ⟨0⟩) with lastFirst := first }
        else if index + 1 != input.games.size || !input.ending.interrupts then
          throw s!"game {index + 1}: the recorded answers do not finish the game"
        timed := recorded.summary.timed && recorded.summary.result.isSome
        games := games.push recorded
        previous := some recorded
  checkInterruptedClockBoundary state timed input.elimination? input.games.size
  let outcome ← concludeReplayMatch state timed input.ending input.elimination?.isSome
  return .inr { rules, input, games, summary := {
    wins := (state.wins0, state.wins1), result := outcome
    exact := games.all (·.summary.exact)
    cardsFullyChecked := games.all (fun game => game.summary.uncheckedCards.all List.isEmpty)
  } }

private def runMatch (input : MatchInputs) (db : CardDB) (rules : ReplayRules)
    (expected : Option (Array RecordedGame)) (refreshCoverage : Bool := false)
    (upgradePermanentChoices : Bool := false) :
    Except String RecordedMatch := do
  match ← runMatchProgress input db rules expected refreshCoverage none upgradePermanentChoices with
  | .inr saved => return saved
  | .inl _ => throw "unexpected inspection while recording a match"

/-- Inspect a 1-based game, checking earlier games before replaying the supplied prefix. -/
def MatchInputs.inspect (input : MatchInputs) (number : Nat) (db : CardDB := RiftboundCards.db) :
    Except String ReplayInspection := do
  unless 0 < number && number <= input.games.size do throw "the game number is outside the match"
  match ← runMatchProgress input db (ReplayRules.current db) none false (some (number - 1)) with
  | .inl inspection => return inspection
  | .inr _ => throw "the requested game was not inspected"

/-- Record a complete 1v1 match using the same engine and setup checks as a played game. -/
def MatchInputs.record (input : MatchInputs) (db : CardDB := RiftboundCards.db) :
    Except String RecordedMatch :=
  runMatch input db (ReplayRules.current db) none

/-- Finalize a match using evidence captured while each game was played. -/
def MatchInputs.recordPlayed (input : MatchInputs) (games : Array RecordedGame) (db : CardDB) :
    Except String RecordedMatch :=
  runMatch input db (ReplayRules.current db) (some games)

private def RecordedMatch.checkArchive (saved : RecordedMatch) (db : CardDB)
    (allowCardUpdate : Bool) : Except String RecordedMatch := do
  let rules := ReplayRules.current db
  if allowCardUpdate then saved.rules.checkEditions rules
  else if saved.rules != rules then throw "the replay format, rules edition or card definitions differ"
  let refreshCoverage := saved.rules.cards != rules.cards
  let actual ← runMatch saved.input db rules (some saved.games) refreshCoverage
    (allowCardUpdate && saved.rules.upgradesPermanentChoices rules)
  let summary := if refreshCoverage then
    { saved.summary with cardsFullyChecked := actual.summary.cardsFullyChecked }
    else saved.summary
  if actual.summary != summary then throw "the final match outcome differs"
  return actual

/-- Read a saved match, checking its pinned rules, every game and its final outcome. -/
def RecordedMatch.verify (saved : RecordedMatch) (db : CardDB := RiftboundCards.db) :
    Except String ReplayMatchResult :=
  (saved.checkArchive db false).map (·.summary)

/-- Revalidate every checkpoint of an archived Duel against the current cards. -/
def RecordedMatch.revalidate (saved : RecordedMatch) (db : CardDB := RiftboundCards.db) :
    Except String RecordedMatch :=
  saved.checkArchive db true

end RiftboundDriver

end
