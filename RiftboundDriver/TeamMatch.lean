module

public import RiftboundDriver.MatchReplay
public import RiftboundDriver.LimitedReplay

/-!
# Match records for two teams

Validate a four-seat event's setup and match administration against observed game results.
When the inputs are available, run them through the engine and compare each game's outcome.
-/

public section

namespace RiftboundDriver

open Lean Riftbound RiftboundCards

/-- Fixed A/B seats on each team, in team order (TR 603.7). -/
structure TeamSeats where
  /-- Team 0's A and B players. -/
  team0 : PlayerId × PlayerId
  /-- Team 1's A and B players. -/
  team1 : PlayerId × PlayerId
deriving DecidableEq, Repr, ToJson, FromJson

/-- Fixed engine seat numbering for both teams' A and B players. -/
def TeamSeats.standard : TeamSeats := ⟨(⟨0⟩, ⟨1⟩), (⟨2⟩, ⟨3⟩)⟩

private def TeamSeats.players (seats : TeamSeats) : List PlayerId :=
  [seats.team0.1, seats.team0.2, seats.team1.1, seats.team1.2]

/-- The team containing this player's seat. -/
def TeamSeats.teamOf (seats : TeamSeats) (seat : PlayerId) : Option PlayerId :=
  if seat == seats.team0.1 || seat == seats.team0.2 then some ⟨0⟩
  else if seat == seats.team1.1 || seat == seats.team1.2 then some ⟨1⟩
  else none

/-- Convert a result naming both winning seats into a result naming the winning team. -/
def TeamSeats.normalizeResult (seats : TeamSeats) : GameResult → Except String GameResult
  | .draw => pure .draw
  | .won (first :: rest) => do
    let some team := seats.teamOf first | throw "the winner seat is not registered"
    let roster := if team.n == 0 then seats.team0 else seats.team1
    unless decide ((first :: rest).Perm [roster.1, roster.2]) do throw "both winning seats must be teammates"
    pure (.won [team])
  | .won [] => throw "a win requires a winning team"

/-- The eight opened booster packs per team, with copies retained (TR 603.6). -/
structure TeamSealedPools where
  /-- Team 0's opened packs and their contents. -/
  team0 : List (List CardId)
  /-- Team 1's opened packs and their contents. -/
  team1 : List (List CardId)
  /-- Limited bans that applied at the event (TR 602.1.b). -/
  banned? : Option (List CardId) := none
deriving DecidableEq, Repr, ToJson, FromJson

/-- The observed reason a team game ended. -/
inductive TeamGameEnd where
  /-- A team reached the victory score (CR 491.3). -/
  | scored
  /-- The players agreed to a draw or a judge declared it. -/
  | draw
  /-- A seat conceded and their team lost (CR 491.6.a.1). -/
  | concede (seat : PlayerId)
  /-- The last extra turn finished with neither team having won. -/
  | time
  /-- This team scored the match-winning point in sudden death (TR 408.4.c.3). -/
  | suddenDeath (team : PlayerId)
  /-- Match concession or an agreed match draw interrupted the game. -/
  | matchEnded
  /-- The judge ended the game by applying Game Loss penalties to these seats. -/
  | gameLoss (seats : List PlayerId)
deriving DecidableEq, Repr, ToJson, FromJson

/-- The seats named by a Game Loss ruling. -/
def TeamGameEnd.gameLossSeats : TeamGameEnd → Option (List PlayerId)
  | .gameLoss seats => some seats
  | _ => none

/-- Observations about a team game, through its own ending or the end of the match. -/
structure TeamGameRecord where
  /-- Constructed registrations, indexed by player ID. -/
  decks? : Option (List ConstructedDeck) := none
  /-- Sealed registrations, indexed by player ID. -/
  sealedDecks? : Option (List LimitedDeck) := none
  /-- The team entitled to choose the first turn, if any. -/
  chooser : Option PlayerId := none
  /-- All four seats in their actual turn order. -/
  order : List PlayerId
  /-- Evidence when the starting order was not observed directly. -/
  openingOrderEvidence? : Option ReplayOpeningOrderEvidence := none
  /-- The three Battlefield selections, keyed by the contributing seat (CR 491.5). -/
  battlefields : List (PlayerId × CardId)
  /-- The final shared points, for team 0 and team 1. -/
  points : Nat × Nat
  /-- The observed game ending. -/
  ending : TeamGameEnd
  /-- Whether the match clock was called during this game. -/
  timed : Bool := false
  /-- Observed or inferred answers to replay, in the order the engine applied them. -/
  answers : Array ReplayAnswer := #[]
  /-- Independently observed facts to check when replaying the answers. -/
  observations? : Option (List ReplayObservation) := none
deriving DecidableEq, Repr, ToJson, FromJson

/-- A Constructed or Sealed tournament record for two teams with two players each. -/
structure TeamMatchRecord where
  /-- The team's fixed seating for this match. -/
  seats : TeamSeats
  /-- Tournament metadata for the Constructed 2v2 ban list. -/
  tournament? : Option ReplayTournament := none
  /-- Shared packs when this is a Sealed event. -/
  sealed? : Option TeamSealedPools := none
  /-- The applicable card sets at the event. -/
  legalSets : List SetCode
  /-- The number of games needed to win. -/
  winsRequired : Nat
  /-- The timed single-elimination procedure, when selected for this match. -/
  elimination? : Option ReplayElimination := none
  /-- The games in chronological order, including an interrupted final game if recorded. -/
  games : Array TeamGameRecord
  /-- The match ending. A concession names an individual seat. -/
  ending : ReplayMatchEnd
deriving DecidableEq, Repr, ToJson, FromJson

/-- The inferred result from the recorded seat assignments, game endings and scores. -/
structure TeamMatchResult where
  /-- Game wins by team. -/
  wins : Nat × Nat
  /-- A winner is named by team number (0 or 1). -/
  result : MatchResult
  /-- Per-game registrations below full card coverage, indexed by seat. -/
  uncheckedCards : Array (List (List (CardId × ImplStatus)))
deriving DecidableEq, Repr, ToJson, FromJson

/-- Team match input and the evidence from executing each game. -/
structure RecordedTeamMatch where
  /-- The rule editions and card definitions used for replay. -/
  rules : ReplayRules
  /-- Observed match setup, results and action streams. -/
  input : TeamMatchRecord
  /-- Checkpoints and results computed by the engine. -/
  games : Array RecordedGame
  /-- The resulting match outcome. -/
  summary : TeamMatchResult
deriving DecidableEq, Repr, ToJson, FromJson

private def TeamGameRecord.registrations (game : TeamGameRecord) : Except String ReplayDecks :=
  match game.decks?, game.sealedDecks? with
  | some ds, none => pure (.constructed ds)
  | none, some ds => pure (.limited ds)
  | _, _ => throw "provide either Constructed or Sealed registrations"

private def checkConstructedTeamDecks (decks : List ConstructedDeck) (seats : TeamSeats) (db : CardDB)
    (env : LegalityEnv) : Except String Unit := do
  if decks.length != 4 then throw "the four seat registrations are required"
  for (d, seat) in decks.zipIdx do
    if !decide (ConstructedDeckValid db env d) then throw s!"seat {seat} has an illegal registration"
  for (a, b) in [seats.team0, seats.team1] do
    let some first := decks[a.n]? >>= (·.deck.resolve db) | throw "missing teammate registration"
    let some second := decks[b.n]? >>= (·.deck.resolve db) | throw "missing teammate registration"
    if first.legend.nameKey == second.legend.nameKey ||
        first.battlefields.any (fun card => second.battlefields.any (·.nameKey == card.nameKey)) then
      throw "teammates share a Champion Legend or Battlefield"

private def checkSealedTeamDecks (decks : List LimitedDeck) (seats : TeamSeats) (db : CardDB)
    (env : LegalityEnv) (packs : TeamSealedPools) : Except String Unit := do
  if decks.length != 4 then throw "the four seat registrations are required"
  let db := db.withLimitedBlank
  for (d, seat) in decks.zipIdx do
    if !decide (SealedDeckValid db env d) then throw s!"seat {seat} has an illegal Sealed deck"
  for ((a, b), pool) in [(seats.team0, packs.team0.flatten), (seats.team1, packs.team1.flatten)] do
    let some first := decks[a.n]? | throw "missing teammate registration"
    let some second := decks[b.n]? | throw "missing teammate registration"
    unless teamSealedRegistrationOk db first second do
      throw "teammates share a Champion Legend or Battlefield"
    checkLimitedCopies pool (limitedAllocation [first, second]) s!"seats {a.n} and {b.n}"

private def registeredBattlefields (decks : ReplayDecks) (seat : PlayerId) : List CardId :=
  match decks with
  | .constructed ds => (ds[seat.n]?.map (·.deck.battlefields)).getD []
  | .limited ds => (ds[seat.n]?.map (·.battlefields)).getD []
  | .core _ => []

private def teamGameResult (game : TeamGameRecord) (seats : TeamSeats) (config : GameConfig) :
    Except String (Option GameResult) := do
  let (a, b) := game.points
  let won (team : Nat) := GameResult.won [⟨team⟩]
  let scoringWinner :=
    if a >= 11 && a > b then some (won 0)
    else if b >= 11 && b > a then some (won 1)
    else none
  let clock := config.ruleSet.callClock 0
  match game.ending with
  | .scored =>
    if scoringWinner.isSome then return scoringWinner
    throw "a scoring winner must reach the victory score and lead the other team"
  | .suddenDeath team =>
    if game.timed && clock.allowsSuddenDeath && team.n < 2 then return some (.won [team])
    throw "this game cannot end with the stated sudden-death winner"
  | .gameLoss affected =>
    if scoringWinner.isSome then throw "a team already won by scoring"
    let result ← judgeGameLossResult seats.players (fun p q => seats.teamOf p == seats.teamOf q) affected
    return some (← seats.normalizeResult result)
  | _ =>
    if scoringWinner.isSome then throw "a team already won by scoring"
    match game.ending with
    | .draw => return some .draw
    | .concede seat =>
      let some team := seats.teamOf seat | throw "the concession seat is not in the match"
      return some (.won [MatchState.other team])
    | .time =>
      if !game.timed then throw "the team game ended on time without a time call"
      let some result := clock.resultOnTime a b
        | throw "tied points and tied game wins require sudden death"
      return some result
    | .matchEnded => return none
    | .scored => throw "missing victory score"
    | .suddenDeath _ => throw "missing sudden-death winner"
    | .gameLoss _ => throw "missing Game Loss"

private def checkTeamSetup (seats : TeamSeats) (game : TeamGameRecord) (state : MatchState)
    (decks : ReplayDecks) (previous : Option TeamGameRecord) : Except String PlayerId := do
  if !(Mode.teamTurnOrderChoices seats.team0 seats.team1).contains game.order then
    throw "turn order must start at a seat in the alternating A/B cycle"
  let some firstTeam := game.order.head?.bind seats.teamOf | throw "the starting seat is missing"
  match state.nextOrder with
  | .chance =>
    if !(game.chooser.any (·.n < 2)) then throw "the team chosen by chance is missing"
  | .loserChooses team =>
    if game.chooser != some team then throw s!"team {team.n} must choose who goes first"
  | .same team =>
    if game.chooser.isSome || firstTeam != team ||
        !(previous.any (fun prior => prior.order == game.order)) then
      throw "a draw preserves the same turn order"
  let contributors := game.battlefields.map Prod.fst
  let expected := game.order.drop 1
  let canEndInSetup := game.ending.gameLossSeats.isSome || game.ending == .matchEnded
  if !(decide (contributors.Perm expected) ||
      (canEndInSetup && decide contributors.Nodup && contributors.all expected.contains)) then
    throw "the three non-starting players each contribute one Battlefield"
  for (seat, id) in game.battlefields do
    if !(registeredBattlefields decks seat).contains id then
      throw s!"seat {seat.n} did not register Battlefield {id.code}"
  if let some prev := previous then
    if reuseReplayBattlefields state prev.ending.gameLossSeats.isSome then
      let same := if canEndInSetup then game.battlefields.all prev.battlefields.contains
        else decide (prev.battlefields.Perm game.battlefields)
      unless same do throw "a draw preserves the same Battlefields"
    let prior ← prev.registrations
    checkReplayDeckChange state prior decks true
  return firstTeam

/-- The game configuration shared by team recording and trace export. -/
def TeamMatchRecord.replayConfig (input : TeamMatchRecord) : Except String GameConfig := do
  let (format, env) ← match input.tournament?, input.sealed? with
    | some event, none => do pure (Format.constructed, ← event.legality .twoVTwo input.legalSets)
    | none, some packs =>
      pure (Format.sealed, ⟨input.legalSets, packs.banned?.getD []⟩)
    | _, _ => throw "provide either Constructed event metadata or the Sealed pools"
  return { ruleSet := .tournament format, mode := .teamDuel, formatLegality := some env }

/-- Validate the recorded packs before allocating their cards. -/
def TeamSealedPools.check (pools : TeamSealedPools) (db : CardDB) : Except String Unit := do
  for packs in [pools.team0, pools.team1] do
    unless packs.length == 8 && packs.all (!·.isEmpty) do
      throw "each Sealed team needs its eight opened booster packs"
    checkLimitedPool db packs.flatten

/-- Count each newly contributed physical Battlefield against its team's pool. -/
def TeamSealedPools.useBattlefields (pools : TeamSealedPools) (seats : TeamSeats)
    (used : List CardId × List CardId) (selected : List (PlayerId × CardId)) (reuse : Bool) :
    Except String (List CardId × List CardId) := do
  let forTeam (n : Nat) := (selected.filter (fun (p, _) => seats.teamOf p == some ⟨n⟩)).map Prod.snd
  return (← useLimitedBattlefields pools.team0.flatten used.1 (forTeam 0) reuse,
    ← useLimitedBattlefields pools.team1.flatten used.2 (forTeam 1) reuse)

/-- Validate the next four registrations using the event's format and card pool. -/
def TeamMatchRecord.checkRegistrations (input : TeamMatchRecord) (decks : ReplayDecks)
    (order : List PlayerId) (db : CardDB) (env : LegalityEnv) : Except String Unit := do
  match decks, input.sealed? with
  | .constructed ds, none => checkConstructedTeamDecks ds input.seats db env
  | .limited ds, some pools =>
    checkSealedTeamDecks ds input.seats db env pools
    checkLimitedBattlefieldCount db.withLimitedBlank ds (order.drop 1) (input.winsRequired == 2)
  | _, _ => throw "the four registrations must use the tournament format"

private def TeamGameRecord.replayInputs (game : TeamGameRecord) (decks : ReplayDecks) :
    GameInputs :=
  { decks, answers := game.answers, chooser := game.chooser, openingOrder := some game.order,
    openingOrderEvidence? := game.openingOrderEvidence?, observations? := game.observations? }

private def runTeamMatchProgress (input : TeamMatchRecord) (db : CardDB)
    (readGame : GameConfig → Nat → TeamGameRecord → ReplayDecks →
      Except String (Option GameResult × Option RecordedGame)) (inspectAt : Option Nat)
    (captureFailure : Bool := false) :
    Except String (Sum ReplayInspection (TeamMatchResult × Array RecordedGame)) := do
  if !decide (input.seats.players.Perm (allPlayers 4)) then throw "the teams must use four different seats"
  if input.winsRequired != 1 && input.winsRequired != 2 then throw "invalid number of wins required"
  checkReplayClockBoundary input.elimination? input.games.size input.ending inspectAt.isSome
  let baseConfig ← input.replayConfig
  let some env := baseConfig.formatLegality | throw "missing tournament eligibility"
  if let some sealed := input.sealed? then sealed.check db
  let mut state := MatchState.start input.winsRequired
  let mut previous : Option TeamGameRecord := none
  let mut uncheckedCards := #[]
  let mut recorded := #[]
  let mut timed := false
  let mut used := ([], [])
  let mut penaltyFields := []
  for (game, index) in input.games.toList.zipIdx do
    let next := do
      if let some evidence := game.openingOrderEvidence? then evidence.check
      let afterTime ← gameStartsAfterTime state timed input.elimination?
      let config := replayGameConfig baseConfig state input.elimination?.isSome afterTime
      let inspecting := inspectAt == some index
      if !inspecting && afterTime && !game.timed then
        throw "a tiebreaker game starts with time already called"
      let decks ← game.registrations
      input.checkRegistrations decks game.order db env
      let inspection ← if inspecting then
        some <$> (game.replayInputs decks).inspect db config (captureFailure := captureFailure)
        else pure none
      let checkedGame := match inspection with
        | some inspection => { game with battlefields := inspection.position.fields.reverse, ending := .matchEnded }
        | none => game
      checkPenaltyBattlefields penaltyFields checkedGame.battlefields
      let reuse := reuseReplayBattlefields state
        (previous.any (fun (prior : TeamGameRecord) => prior.ending.gameLossSeats.isSome))
      let used ← match input.sealed? with
        | none => pure used
        | some pools =>
          pools.useBattlefields input.seats used checkedGame.battlefields reuse
      let first ← checkTeamSetup input.seats checkedGame state decks previous
      if let some inspection := inspection then return Sum.inl inspection
      let (result, evidence) ← readGame config index game decks
      if let some finished := result then
        pure (.inr (state.record finished first, game.timed, evidence, used, decks))
      else
        unless index + 1 == input.games.size && input.ending.interrupts do
          throw "only a match concession or agreed match draw can interrupt the last game"
        pure (.inr (state, false, evidence, used, decks))
    match ← next.mapError (fun error => s!"team game {index + 1}: {error}") with
    | .inl inspection =>
      return .inl (inspection.withEarlierGames recorded)
    | .inr (m, gameTimed, evidence, fields, decks) =>
      state := m
      if let some game := evidence then recorded := recorded.push game
      timed := gameTimed
      used := fields
      if game.ending.gameLossSeats.isSome then
        penaltyFields := penaltyFields ++ game.battlefields.filter (·.2 != limitedBlankBattlefield.id)
      previous := some game
      uncheckedCards := uncheckedCards.push (decks.uncheckedCards db)
  let ending ← match input.ending.affectedSeat with
    | some seat =>
      let some team := input.seats.teamOf seat | throw "the ending seat is not in the match"
      pure (input.ending.mapSeat (fun _ => team))
    | none => pure input.ending
  checkInterruptedClockBoundary state timed input.elimination? input.games.size
  let result ← concludeReplayMatch state timed ending input.elimination?.isSome
  return .inr ({ wins := (state.wins0, state.wins1), result, uncheckedCards }, recorded)

private def runTeamMatch (input : TeamMatchRecord) (db : CardDB)
    (readGame : GameConfig → Nat → TeamGameRecord → ReplayDecks →
      Except String (Option GameResult × Option RecordedGame)) :
    Except String (TeamMatchResult × Array RecordedGame) := do
  match ← runTeamMatchProgress input db readGame none with
  | .inr result => return result
  | .inl _ => throw "unexpected inspection while recording a team match"

/-- Check the registrations, setup, reported shared scores and match outcome. -/
def TeamMatchRecord.check (input : TeamMatchRecord) (db : CardDB := RiftboundCards.db) :
    Except String TeamMatchResult :=
  (runTeamMatch input db fun config _ game _ =>
    (teamGameResult game input.seats config).map (·, none)).map Prod.fst

private def confirmTeamGame (observation : TeamGameRecord) (played : RecordedGame)
    (seats : TeamSeats) (config : GameConfig) : Except String (Option GameResult) := do
  let actual := played.summary
  if actual.turnOrder != observation.order || !decide (actual.battlefields.Perm observation.battlefields) then
    throw "the replayed setup differs from the observed order or Battlefield choices"
  let (a, b) := observation.points
  if actual.points != [a, a, b, b] || actual.timed != observation.timed then
    throw "the replayed score or clock differs from the observations"
  let expected ← teamGameResult observation seats config
  if expected.isNone then
    if actual.result.isSome then throw "a game result precedes the recorded match ending"
    return none
  let some result := actual.result | throw "the recorded answers do not finish the team game"
  let winningEvents := (played.checkpoints.back?).any (fun w =>
    w.events.any (fun | .won _ => true | _ => false))
  if played.gameLossSeats != observation.ending.gameLossSeats then
    throw "the recorded Game Loss ruling differs"
  let endingAction := played.input.answers.back?.bind ReplayAnswer.action?
  if let .scored := observation.ending then
    if !winningEvents then throw "the last answer did not produce a scoring win"
  else
    if winningEvents then throw "scoring ended the game before the recorded ending"
    if let .concede p := observation.ending then
      if endingAction != some ⟨.player p, .concede⟩ then throw "the recorded seat did not concede"
    if let .draw := observation.ending then
      if endingAction != some ⟨.judge, .declareDraw⟩ then throw "the judge did not declare a draw"
    if let .time := observation.ending then
      if actual.suddenDeathTurn?.isSome ||
          endingAction.any (fun a => a.kind == .concede || a.kind == .declareDraw) then
        throw "the game did not end at the extra-turn deadline"
    if let .suddenDeath team := observation.ending then
      unless actual.suddenDeathTurn?.isSome && (played.checkpoints.back?).any (fun w =>
          w.events.any (fun
            | .pointsGained p (_ + 1) => seats.teamOf p == some team
            | _ => false)) &&
          !(endingAction.any (fun a => a.kind == .concede || a.kind == .declareDraw)) do
        throw "the last answer did not score the stated sudden-death point"
  let normalized ← seats.normalizeResult result
  if some normalized != expected then throw "the replayed game outcome differs"
  return some normalized

private def playTeamMatchProgress (input : TeamMatchRecord) (db : CardDB)
    (expected : Option (Array RecordedGame)) (refreshCoverage : Bool) (inspectAt : Option Nat)
    (upgradePermanentChoices : Bool := false) (captureFailure : Bool := false) :
    Except String (Sum ReplayInspection RecordedTeamMatch) := do
  if input.seats != TeamSeats.standard then
    throw "engine inputs number the first team's A/B seats 0 and 1 and the other team's seats 2 and 3"
  if expected.any (fun games => games.size != input.games.size) then throw "the game count differs"
  let progress ← runTeamMatchProgress input db (fun config index game decks => do
    let replay := game.replayInputs decks
    let recorded ← match expected.bind (·[index]?) with
      | none => replay.record db config
      | some saved => do
        if saved.input != replay then throw "the saved game inputs differ"
        saved.checkEvidence db config 100 refreshCoverage upgradePermanentChoices
    let result ← confirmTeamGame game recorded input.seats config
    pure (result, some recorded)) inspectAt captureFailure
  match progress with
  | .inl inspection => return .inl inspection
  | .inr (summary, games) => return .inr { rules := ReplayRules.current db, input, games, summary }

private def playTeamMatch (input : TeamMatchRecord) (db : CardDB)
    (expected : Option (Array RecordedGame)) (refreshCoverage : Bool := false)
    (upgradePermanentChoices : Bool := false) :
    Except String RecordedTeamMatch := do
  match ← playTeamMatchProgress input db expected refreshCoverage none upgradePermanentChoices with
  | .inr saved => return saved
  | .inl _ => throw "unexpected inspection while recording a team match"

/-- Inspect a 1-based team game using its declared seating and the preceding completed games. -/
def TeamMatchRecord.inspect (input : TeamMatchRecord) (number : Nat)
    (db : CardDB := RiftboundCards.db) (captureFailure : Bool := false) :
    Except String ReplayInspection := do
  unless 0 < number && number <= input.games.size do throw "the game number is outside the match"
  match ← playTeamMatchProgress input db none false (some (number - 1))
      (captureFailure := captureFailure) with
  | .inl inspection => return inspection
  | .inr _ => throw "the requested game was not inspected"

/-- Execute each recorded team game and check it against the observations. -/
def TeamMatchRecord.record (input : TeamMatchRecord) (db : CardDB := RiftboundCards.db) :
    Except String RecordedTeamMatch :=
  playTeamMatch input db none

/-- Verify and package the checkpoints captured by a live team match. -/
def TeamMatchRecord.recordPlayed (input : TeamMatchRecord) (games : Array RecordedGame) :
    Except String RecordedTeamMatch :=
  playTeamMatch input RiftboundCards.db (some games)

private def RecordedTeamMatch.checkArchive (saved : RecordedTeamMatch) (db : CardDB)
    (allowCardUpdate : Bool) : Except String RecordedTeamMatch := do
  let rules := ReplayRules.current db
  if allowCardUpdate then saved.rules.checkEditions rules
  else if saved.rules != rules then throw "the replay format, rules or card definitions differ"
  let refreshCoverage := saved.rules.cards != rules.cards
  let replay ← playTeamMatch saved.input db (some saved.games) refreshCoverage
    (allowCardUpdate && saved.rules.upgradesPermanentChoices rules)
  let summary := if refreshCoverage then
    { saved.summary with uncheckedCards := replay.summary.uncheckedCards }
    else saved.summary
  if replay.summary != summary then throw "the final team match outcome differs"
  return replay

/-- Verify team game inputs against the saved checkpoints and the match outcome. -/
def RecordedTeamMatch.verify (saved : RecordedTeamMatch) (db : CardDB := RiftboundCards.db) :
    Except String TeamMatchResult :=
  (saved.checkArchive db false).map (·.summary)

/-- Revalidate every checkpoint of an archived team match against the current cards. -/
def RecordedTeamMatch.revalidate (saved : RecordedTeamMatch) (db : CardDB := RiftboundCards.db) :
    Except String RecordedTeamMatch :=
  saved.checkArchive db true

end RiftboundDriver

end
