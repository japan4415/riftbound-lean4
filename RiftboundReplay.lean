import RiftboundDriver.TeamMatch
import RiftboundDriver.SeatTrace

open Lean Riftbound RiftboundDriver

private def readJson (path : String) : IO Json := do
  let text ← IO.FS.readFile path
  IO.ofExcept (Json.parse text)

/-- Publish a derived file after writing it completely. Keep the input even when an output name
is a symbolic or hard link to the recording. -/
private def writeOutput (input output : System.FilePath) (content : String) : IO Unit := do
  let source ← IO.FS.realPath input
  let some name := output.fileName | throw (IO.userError "the replay output needs a file name")
  let alreadyExists ← output.pathExists
  let target ← if alreadyExists then IO.FS.realPath output
    else (· / name) <$> IO.FS.realPath (output.parent.getD ".")
  if source == target then
    throw (IO.userError "the replay output must be a different file from the input")
  if alreadyExists then
    unless (← target.metadata).type == .file do
      throw (IO.userError "the replay output must be a regular file")
  let random ← IO.getRandomBytes 16
  let suffix := "-".intercalate (random.toList.map toString)
  let staging := target.parent.getD "." / (".riftbound-replay-" ++ suffix)
  IO.FS.createDir staging
  let file := staging / "output"
  try
    IO.FS.writeFile file (content ++ "\n")
    IO.FS.rename file target
  finally
    if ← file.pathExists then IO.FS.removeFile file
    IO.FS.removeDir staging

private def writeJson (input output : System.FilePath) (value : Json) : IO Unit :=
  writeOutput input output value.compress

private def playerOrders : List PlayerId → List (List PlayerId)
  | [] => [[]]
  | player :: rest => (playerOrders rest).flatMap fun order =>
    (List.range (order.length + 1)).map fun index => order.take index ++ [player] ++ order.drop index

private def inspectionJson (number : Nat) (inspection : ReplayInspection) : Except String Json := do
  let state := inspection.position.state
  let frame := state.pending.head?
  let live := state.result.isNone
  let chance := if live && !inspection.bo1Sideboard then ReplayChanceDecision.pending state else none
  let turnOrders := match chance with
    | some .turnOrder => (playerOrders state.participatingSeats).filterMap fun order =>
      let action : Action := ⟨.chance, .arrangePlayers order⟩
      if inspection.forcedFirst.any (fun p => order.head? != some p) || !decide (Legal state action) then
        none else some action
    | _ => []
  let external : List Action := [⟨.clock, .timeCalled⟩, ⟨.judge, .declareDraw⟩]
  let options := if live then legalActions state ++ turnOrders ++ external.filter (fun a => decide (Legal state a))
    else []
  let options := if inspection.bo1Sideboard then
    options.filter (fun a => a.kind == .concede || a.kind == .declareDraw)
    else options
  let choices ← options.mapM fun action => do
    let detail ← Json.parse (actionJson action frame (some state))
    let coded := (ReplayCardPick.fromAction? state action).map ReplayAnswer.observedCardPick <|>
      (ReplayStandardMove.fromAction? state action).map ReplayAnswer.observedStandardMove <|>
      (ReplayGroupMove.fromAction? state action).map ReplayAnswer.observedGroupMove <|>
      (ReplayCardPlay.fromAction? state action).map ReplayAnswer.observedCardPlay <|>
      (ReplayAbilityUse.fromAction? state action).map ReplayAnswer.observedAbilityUse <|>
      (ReplayTriggerUse.fromAction? state action).map ReplayAnswer.observedTriggerUse
    let byCode := coded.map fun answer => ("answerByCode", toJson answer)
    let byLocation := (ReplayCardPick.fromActionAtLocation? state action).map fun choice =>
      ("answerByLocation", toJson (ReplayAnswer.observedCardPick choice))
    pure (Json.mkObj ([("detail", detail), ("answer", toJson (ReplayAnswer.observed action))] ++
      byCode.toList ++ byLocation.toList))
  let candidate (id : ObjId) :=
    [("object", toJson id), ("card", toJson ((state.obj? id).bind (·.kind.cardId?)))]
  let decision := if !live then Json.null else if inspection.bo1Sideboard then
    Json.mkObj [("kind", toJson "bo1Sideboard"), ("answer", toJson ReplayAnswer.bo1Sideboard)]
    else match chance with
    | some (.cardOrder candidates) =>
      Json.mkObj [("kind", toJson "cardOrder"), ("cards", toJson (candidates.map (Json.mkObj ∘ candidate)))]
    | some (.battlefield seat candidates) =>
      let cards := candidates.zipIdx.map fun (id, index) =>
        let answer := ReplayAnswer.observed ⟨.chance, .pick index⟩
        let byCode := ((state.obj? id).bind (·.kind.cardId?)).map fun card =>
          ("answerByCode", toJson (ReplayAnswer.observedChance (.battlefield card)))
        Json.mkObj (candidate id ++ [("answer", toJson answer)] ++ byCode.toList)
      Json.mkObj [("kind", toJson "battlefield"), ("seat", toJson seat), ("cards", toJson cards)]
    | some .turnOrder =>
      Json.mkObj [("kind", toJson "turnOrder"), ("chooser", toJson inspection.chooser),
        ("forcedFirst", toJson inspection.forcedFirst), ("bo1Initiative", toJson inspection.bo1Initiative)]
    | none =>
      frame.map (fun next => Json.mkObj [("kind", toJson (ctorName next))]) |>.getD Json.null
  let board ← Json.parse (stateJson state {}).1
  return Json.mkObj [
    ("game", toJson number), ("checkpoint", toJson inspection.checkpoint),
    ("nextAnswer", toJson (if live then some (inspection.checkpoint + 1) else none)),
    ("missing", toJson inspection.missing), ("exactPrefix", toJson inspection.exact),
    ("checkedObservations", toJson inspection.checkedObservations),
    ("pendingObservations", toJson inspection.pendingObservations),
    ("turnOrder", toJson state.turnOrder), ("clockCalled", toJson state.clock.isSome),
    ("state", board), ("decision", decision), ("choices", toJson choices)]

private def withInspectionDefaults (input : Json) (defaults : List (String × Json)) : Json :=
  match input with
  | .obj _ => defaults.foldl (fun json (field, value) =>
      if (json.getObjVal? field).isOk then json else json.setObjVal! field value) input
  | _ => input

private def inspectInput (command : String) (input : Json) (number : Nat) :
    Except String ReplayInspection := do
  if command == "inspect-ffa" then
    unless number == 1 do throw "the game number must be 1 for free-for-all"
    let script : FreeForAllInputs ← fromJson? input
    return ← script.inspect
  let input := withInspectionDefaults input [("ending", toJson ReplayMatchEnd.finalGame)]
  if command == "inspect" then
    let script : MatchInputs ← fromJson? input
    return ← script.inspect number
  let games ← input.getObjValAs? (Array Json) "games"
  unless 0 < number && number <= games.size do throw "the game number is outside the match"
  let index := number - 1
  let game := withInspectionDefaults games[index]! [
    ("ending", toJson TeamGameEnd.matchEnded), ("points", toJson ((0, 0) : Nat × Nat)),
    ("battlefields", Json.arr #[]), ("timed", toJson false)]
  let script : TeamMatchRecord ← fromJson? (input.setObjVal! "games" (toJson (games.set! index game)))
  script.inspect number

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
      (answer.correctionJson ++ cardDisclosureFields next.disclosures) (some state)
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
    | [command@"inspect", input, game, output]
    | [command@"inspect-team", input, game, output]
    | [command@"inspect-ffa", input, game, output] =>
      let some number := game.toNat? | throw (IO.userError "the game number must be a positive integer")
      let inspection ← IO.ofExcept (inspectInput command (← readJson input) number)
      writeJson input output (← IO.ofExcept (inspectionJson number inspection))
      return 0
    | ["record", input, output] =>
      let script : MatchInputs ← IO.ofExcept (fromJson? (← readJson input))
      let saved ← IO.ofExcept (script.record)
      writeJson input output (toJson saved)
      IO.println (toJson saved.summary).compress
      return 0
    | ["verify", input] =>
      let saved : RecordedMatch ← IO.ofExcept (fromJson? (← readJson input))
      let result ← IO.ofExcept (saved.verify)
      IO.println (toJson result).compress
      return 0
    | ["revalidate", input, output] =>
      let saved : RecordedMatch ← IO.ofExcept (fromJson? (← readJson input))
      let updated ← IO.ofExcept saved.revalidate
      writeJson input output (toJson updated)
      IO.println (toJson updated.summary).compress
      return 0
    | ["view", input, output] =>
      let saved : RecordedMatch ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (matchTrace saved)
      writeOutput input output trace
      return 0
    | ["check-team", input] =>
      let observed : TeamMatchRecord ← IO.ofExcept (fromJson? (← readJson input))
      let result ← IO.ofExcept observed.check
      IO.println (toJson result).compress
      return 0
    | ["record-team", input, output] =>
      let observed : TeamMatchRecord ← IO.ofExcept (fromJson? (← readJson input))
      let saved ← IO.ofExcept observed.record
      writeJson input output (toJson saved)
      IO.println (teamVerificationJson saved saved.summary).compress
      return 0
    | ["verify-team", input] =>
      let saved : RecordedTeamMatch ← IO.ofExcept (fromJson? (← readJson input))
      let result ← IO.ofExcept saved.verify
      IO.println (teamVerificationJson saved result).compress
      return 0
    | ["revalidate-team", input, output] =>
      let saved : RecordedTeamMatch ← IO.ofExcept (fromJson? (← readJson input))
      let updated ← IO.ofExcept saved.revalidate
      writeJson input output (toJson updated)
      IO.println (teamVerificationJson updated updated.summary).compress
      return 0
    | ["view-team", input, output] =>
      let saved : RecordedTeamMatch ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (teamMatchTrace saved)
      writeOutput input output trace
      return 0
    | ["record-ffa", input, output] =>
      let script : FreeForAllInputs ← IO.ofExcept (fromJson? (← readJson input))
      let saved ← IO.ofExcept script.record
      writeJson input output (toJson saved)
      IO.println (ffaVerificationJson saved.game.summary).compress
      return 0
    | ["verify-ffa", input] =>
      let saved : RecordedFreeForAll ← IO.ofExcept (fromJson? (← readJson input))
      let result ← IO.ofExcept saved.verify
      IO.println (ffaVerificationJson result).compress
      return 0
    | ["revalidate-ffa", input, output] =>
      let saved : RecordedFreeForAll ← IO.ofExcept (fromJson? (← readJson input))
      let updated ← IO.ofExcept saved.revalidate
      writeJson input output (toJson updated)
      IO.println (ffaVerificationJson updated.game.summary).compress
      return 0
    | ["view-ffa", input, output] =>
      let saved : RecordedFreeForAll ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (ffaTrace saved)
      writeOutput input output trace
      return 0
    | [kind@"disclosures", input, seat, output]
    | [kind@"view-seat", input, seat, output] =>
      let saved : RecordedMatch ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (matchSeatTrace saved seat (kind != "disclosures"))
      writeOutput input output trace
      return 0
    | [kind@"disclosures-team", input, seat, output]
    | [kind@"view-team-seat", input, seat, output] =>
      let saved : RecordedTeamMatch ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (teamMatchSeatTrace saved seat (kind != "disclosures-team"))
      writeOutput input output trace
      return 0
    | [kind@"disclosures-ffa", input, seat, output]
    | [kind@"view-ffa-seat", input, seat, output] =>
      let saved : RecordedFreeForAll ← IO.ofExcept (fromJson? (← readJson input))
      let trace ← IO.ofExcept (ffaSeatTrace saved seat (kind != "disclosures-ffa"))
      writeOutput input output trace
      return 0
    | _ =>
      IO.eprintln "usage: riftbound-replay record INPUT.json ARCHIVE.json | verify ARCHIVE.json | view ARCHIVE.json TRACE.json | check-team TEAM.json | record-team TEAM.json ARCHIVE.json | verify-team ARCHIVE.json | view-team ARCHIVE.json TRACE.json | record-ffa INPUT.json ARCHIVE.json | verify-ffa ARCHIVE.json | view-ffa ARCHIVE.json TRACE.json"
      IO.eprintln "       riftbound-replay revalidate[-team|-ffa] ARCHIVE.json UPDATED.json"
      IO.eprintln "       riftbound-replay inspect[-team|-ffa] INPUT.json GAME OUTPUT.json"
      IO.eprintln "       riftbound-replay disclosures[-team|-ffa] ARCHIVE.json SEAT OUTPUT.json"
      IO.eprintln "       riftbound-replay view[-team|-ffa]-seat ARCHIVE.json SEAT OUTPUT.json"
      return 2
  catch error =>
    IO.eprintln error.toString
    return 1
