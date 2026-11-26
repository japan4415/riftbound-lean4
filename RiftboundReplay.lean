import RiftboundDriver.TeamMatch
import RiftboundDriver.SeatTrace

open Lean Riftbound RiftboundDriver

private def readJson (path : String) : IO Json := do
  let text ← IO.FS.readFile path
  IO.ofExcept (Json.parse text)

private def writeJson (path : String) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.compress ++ "\n")

private def collectGame {α : Type} (input : GameInputs) (config : GameConfig) (fuel : Nat)
    (initial : GameState → α)
    (collect : α → Nat → ReplayAnswer → GameState → Option Action → ReplayPosition →
      List Event → α) : Except String α := do
  let mut state ← input.initial RiftboundCards.db config
  let mut acc := initial state
  let mut history := [ReplayPosition.fromState state]
  for (answer, index) in input.answers.toList.zipIdx do
    let (action, next, events) ← input.advance history answer (index + 1) fuel (observeFaces := true)
    acc := collect acc (index + 1) answer state action next events
    history := next :: history
    state := next.state
  return acc

private def gameTrace (input : GameInputs) (config : GameConfig) (fuel : Nat) :
    Except String String := do
  let initial (state : GameState) :=
    let (row, seen) := stepJson 0 none [] state {}
    ([row], seen)
  let collect acc index answer (state : GameState) action (next : ReplayPosition) events :=
    let sideboard := answer == .bo1Sideboard
    let priorSeen := if answer.rewinds then {} else acc.2
    let (row, seen) := stepJson index action events next.state priorSeen state.pending.head? sideboard
      (input.isBo1Initiative state action) answer.penalizedSeats
      (answer.correctionJson ++ cardDisclosureFields next.disclosures)
    (row :: acc.1, seen)
  let (steps, _) ← collectGame input config fuel initial collect
  return jobj [("players", toString config.mode.players), ("steps", jarr steps.reverse)]

private def rewindField : ReplayAnswer → List (String × String)
  | .judgeRewind target => [("judgeRewind", toString target)]
  | .judgePrivateRewind rewind => [("judgeRewind", toString rewind.target)]
  | .judgeTimelineRewind rewind => [("judgeRewind", toString rewind.target)]
  | _ => []

private def seatGameTrace (input : GameInputs) (config : GameConfig) (fuel : Nat)
    (seat : PlayerId) (includeBoard : Bool) : Except String String := do
  let initial (state : GameState) :=
    if includeBoard then [jobj [("i", "0"), ("state", seatStateJson state seat)]] else []
  let collect (steps : List String) index answer state action (next : ReplayPosition) _ :=
    let faces := next.disclosures.filter (CardDisclosure.visibleTo seat)
    if !includeBoard && faces.isEmpty then steps else
      let items := faces.map (fun d =>
        jobj [("cards", jarr (d.cards.map (fun c => jstr c.code))),
          ("public", toString d.onlyFor.isNone)])
      let disclosures := if items.isEmpty then [] else [("disclosures", jarr items)]
      let board := if includeBoard then
        let penalties := (answer.penalizedSeats.map fun seats =>
          ("gameLoss", jarr (seats.map (fun p => toString p.n)))).toList
        [("state", seatStateJson next.state seat)] ++ rewindField answer ++ penalties ++
          (if answer == .bo1Sideboard then [("bo1Sideboard", "true")] else []) ++
          (if input.isBo1Initiative state action then [("bo1Initiative", "true")] else [])
        else []
      jobj ([("i", toString index)] ++ board ++ disclosures) :: steps
  let steps ← collectGame input config fuel initial collect
  return jobj [("steps", jarr steps.reverse)]

private def seatOutput (position : String) (players : Nat) (exact : Bool)
    (games : PlayerId → Except String (List String)) (extra : List (String × String)) :
    Except String String := do
  let some seat := position.toNat? | throw "the viewing seat must be a nonnegative integer"
  unless seat < players do throw "the viewing seat is outside the game"
  let rows ← games ⟨seat⟩
  return jobj ([("seat", toString seat), ("exact", toString exact), ("games", jarr rows)] ++ extra)

private def seatMatchFields (wins : Nat × Nat) (result : MatchResult) : List (String × String) :=
  let winner := match result with | .won p => toString p.n | .draw => "null"
  [("winner", winner), ("wins", jarr [toString wins.1, toString wins.2])]

private def teamSeatsField (saved : RecordedTeamMatch) : String × String :=
  let seats (team : PlayerId × PlayerId) := jarr [toString team.1.n, toString team.2.n]
  let teams := saved.input.seats
  ("teams", jarr [seats teams.team0, seats teams.team1])

private def replayTraceJson (games : List String) (wins : List Nat) (outcome : MatchResult)
    (allObserved cardsChecked : Bool) (extra : List (String × String) := [])
    (limited : Bool := false) (ffaConcession : Bool := false) : String :=
  let db := if limited then RiftboundCards.db.withLimitedBlank else RiftboundCards.db
  let db := if ffaConcession then db.withConcessionBattlefield else db
  let cards := db.cards.map (fun card => (card.id.code, cardJson card))
  let winner := match outcome with | .won p => toString p.n | .draw => "null"
  jobj ([("cards", jobj cards), ("games", jarr games), ("winner", winner),
    ("wins", jarr (wins.map toString)), ("exact", toString allObserved),
    ("cardsFullyChecked", toString cardsChecked)] ++ extra)

private def matchPenaltyTrace (ending : ReplayMatchEnd) : List (String × String) :=
  if ending.penalizedSeat.isSome then [("matchPenalty", (toJson ending).compress)] else []

private def matchTrace (saved : RecordedMatch) : Except String String := do
  let summary ← saved.verify
  let games ← saved.games.toList.mapM (fun game =>
    gameTrace game.input (game.eliminationConfig?.getD saved.input.config) saved.input.fuel)
  return replayTraceJson games [summary.wins.1, summary.wins.2] summary.result
    summary.exact summary.cardsFullyChecked
    (matchPenaltyTrace saved.input.ending) (limited := saved.input.config.ruleSet.isLimited)

private def teamEvidence (saved : RecordedTeamMatch) (summary : TeamMatchResult) : Bool × Bool :=
  (saved.games.all (·.summary.exact), summary.uncheckedCards.all (·.all List.isEmpty))

private def teamVerificationJson (saved : RecordedTeamMatch) (summary : TeamMatchResult) : Json :=
  let (allObserved, cardsChecked) := teamEvidence saved summary
  (toJson summary)
    |>.setObjValAs! "exact" allObserved
    |>.setObjValAs! "cardsFullyChecked" cardsChecked

private def teamMatchTrace (saved : RecordedTeamMatch) : Except String String := do
  let summary ← saved.verify
  let config ← saved.input.replayConfig
  let games ← saved.games.toList.mapM (fun game =>
    gameTrace game.input (game.eliminationConfig?.getD config) 100)
  let (allObserved, cardsChecked) := teamEvidence saved summary
  return replayTraceJson games [summary.wins.1, summary.wins.2] summary.result allObserved cardsChecked
    ([teamSeatsField saved] ++ matchPenaltyTrace saved.input.ending)
    config.ruleSet.isLimited

private def ffaVerificationJson (summary : ReplayGameResult) : Json :=
  (toJson summary).setObjValAs! "cardsFullyChecked" (summary.uncheckedCards.all List.isEmpty)

private def ffaTrace (saved : RecordedFreeForAll) : Except String String := do
  let summary ← saved.verify
  let outcome : MatchResult ← match summary.result with
    | some (.won [seat]) => pure (.won seat)
    | some .draw => pure .draw
    | _ => throw "invalid free-for-all outcome"
  let game ← gameTrace saved.game.input { ruleSet := .coreOnly, mode := saved.mode } saved.fuel
  let wins := (allPlayers saved.mode.players).map (fun seat =>
    if outcome == .won seat then 1 else 0)
  let ffaConcession := saved.game.input.answers.any fun answer =>
    match answer with
    | .observed action | .inferred action _ => action.kind == .concede
    | _ => false
  return replayTraceJson [game] wins outcome summary.exact (summary.uncheckedCards.all List.isEmpty)
    (ffaConcession := ffaConcession)

private def matchSeatTrace (saved : RecordedMatch) (seat : String) (includeBoard : Bool) :
    Except String String := do
  let summary ← saved.verify
  let games viewer := saved.games.toList.mapM (fun game =>
    seatGameTrace game.input (game.eliminationConfig?.getD saved.input.config) saved.input.fuel
      viewer includeBoard)
  let extra := if includeBoard then seatMatchFields summary.wins summary.result ++ matchPenaltyTrace saved.input.ending
    else []
  seatOutput seat saved.input.config.mode.players summary.exact games extra

private def teamMatchSeatTrace (saved : RecordedTeamMatch) (seat : String) (includeBoard : Bool) :
    Except String String := do
  let summary ← saved.verify
  let config ← saved.input.replayConfig
  let games viewer := saved.games.toList.mapM (fun game =>
    seatGameTrace game.input (game.eliminationConfig?.getD config) 100 viewer includeBoard)
  let extra := if includeBoard then
    [teamSeatsField saved] ++ seatMatchFields summary.wins summary.result ++
      matchPenaltyTrace saved.input.ending
    else []
  seatOutput seat config.mode.players (saved.games.all (·.summary.exact)) games extra

private def ffaSeatTrace (saved : RecordedFreeForAll) (seat : String) (includeBoard : Bool) :
    Except String String := do
  let summary ← saved.verify
  let games viewer :=
    (seatGameTrace saved.game.input { ruleSet := .coreOnly, mode := saved.mode } saved.fuel
      viewer includeBoard).map List.singleton
  seatOutput seat saved.mode.players summary.exact games []

/-- Record, verify or generate a viewer trace from the inputs of a saved game or match. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["record", input, output] =>
      let script : MatchInputs ← IO.ofExcept (fromJson? (← readJson input))
      let saved ← IO.ofExcept (script.record)
      writeJson output (toJson saved)
      IO.println (toJson saved.summary).compress
      return 0
    | ["verify", input] =>
      let saved : RecordedMatch ← IO.ofExcept (fromJson? (← readJson input))
      let result ← IO.ofExcept (saved.verify)
      IO.println (toJson result).compress
      return 0
    | ["view", input, output] =>
      let saved : RecordedMatch ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (matchTrace saved)
      IO.FS.writeFile output (trace ++ "\n")
      return 0
    | ["check-team", input] =>
      let observed : TeamMatchRecord ← IO.ofExcept (fromJson? (← readJson input))
      let result ← IO.ofExcept observed.check
      IO.println (toJson result).compress
      return 0
    | ["record-team", input, output] =>
      let observed : TeamMatchRecord ← IO.ofExcept (fromJson? (← readJson input))
      let saved ← IO.ofExcept observed.record
      writeJson output (toJson saved)
      IO.println (teamVerificationJson saved saved.summary).compress
      return 0
    | ["verify-team", input] =>
      let saved : RecordedTeamMatch ← IO.ofExcept (fromJson? (← readJson input))
      let result ← IO.ofExcept saved.verify
      IO.println (teamVerificationJson saved result).compress
      return 0
    | ["view-team", input, output] =>
      let saved : RecordedTeamMatch ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (teamMatchTrace saved)
      IO.FS.writeFile output (trace ++ "\n")
      return 0
    | ["record-ffa", input, output] =>
      let script : FreeForAllInputs ← IO.ofExcept (fromJson? (← readJson input))
      let saved ← IO.ofExcept script.record
      writeJson output (toJson saved)
      IO.println (ffaVerificationJson saved.game.summary).compress
      return 0
    | ["verify-ffa", input] =>
      let saved : RecordedFreeForAll ← IO.ofExcept (fromJson? (← readJson input))
      let result ← IO.ofExcept saved.verify
      IO.println (ffaVerificationJson result).compress
      return 0
    | ["view-ffa", input, output] =>
      let saved : RecordedFreeForAll ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (ffaTrace saved)
      IO.FS.writeFile output (trace ++ "\n")
      return 0
    | [kind@"disclosures", input, seat, output]
    | [kind@"view-seat", input, seat, output] =>
      let saved : RecordedMatch ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (matchSeatTrace saved seat (kind != "disclosures"))
      IO.FS.writeFile output (trace ++ "\n")
      return 0
    | [kind@"disclosures-team", input, seat, output]
    | [kind@"view-team-seat", input, seat, output] =>
      let saved : RecordedTeamMatch ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (teamMatchSeatTrace saved seat (kind != "disclosures-team"))
      IO.FS.writeFile output (trace ++ "\n")
      return 0
    | [kind@"disclosures-ffa", input, seat, output]
    | [kind@"view-ffa-seat", input, seat, output] =>
      let saved : RecordedFreeForAll ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (ffaSeatTrace saved seat (kind != "disclosures-ffa"))
      IO.FS.writeFile output (trace ++ "\n")
      return 0
    | _ =>
      IO.eprintln "usage: riftbound-replay record INPUT.json ARCHIVE.json | verify ARCHIVE.json | view ARCHIVE.json TRACE.json | check-team TEAM.json | record-team TEAM.json ARCHIVE.json | verify-team ARCHIVE.json | view-team ARCHIVE.json TRACE.json | record-ffa INPUT.json ARCHIVE.json | verify-ffa ARCHIVE.json | view-ffa ARCHIVE.json TRACE.json"
      IO.eprintln "       riftbound-replay disclosures[-team|-ffa] ARCHIVE.json SEAT OUTPUT.json"
      IO.eprintln "       riftbound-replay view[-team|-ffa]-seat ARCHIVE.json SEAT OUTPUT.json"
      return 2
  catch error =>
    IO.eprintln error.toString
    return 1
