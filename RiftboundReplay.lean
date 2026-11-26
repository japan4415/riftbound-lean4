import RiftboundDriver.TeamMatch
import RiftboundDriver.Trace

open Lean Riftbound RiftboundDriver

private def readJson (path : String) : IO Json := do
  let text ← IO.FS.readFile path
  IO.ofExcept (Json.parse text)

private def writeJson (path : String) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.compress ++ "\n")

private def gameTrace (input : GameInputs) (config : GameConfig) (fuel : Nat) :
    Except String String := do
  let mut state ← input.initial RiftboundCards.db config
  let (initial, firstSeen) := stepJson 0 none [] state {}
  let mut seen := firstSeen
  let mut steps := [initial]
  for (answer, index) in input.answers.toList.zipIdx do
    let (action, next, events) ← input.applyAnswer state answer (index + 1) fuel
    let sideboard := answer == .bo1Sideboard
    let (row, nextSeen) := stepJson (index + 1) action events next seen state.pending.head? sideboard
      (input.isBo1Initiative state action) answer.penalizedSeats
    state := next
    seen := nextSeen
    steps := row :: steps
  return jobj [("players", toString state.playerCount), ("steps", jarr steps.reverse)]

private def matchTraceJson (games : List String) (wins : Nat × Nat) (outcome : MatchResult)
    (allObserved cardsChecked : Bool) (extra : List (String × String) := [])
    (limited : Bool := false) : String :=
  let db := if limited then RiftboundCards.db.withLimitedBlank else RiftboundCards.db
  let cards := db.cards.map (fun card => (card.id.code, cardJson card))
  let winner := match outcome with | .won p => toString p.n | .draw => "null"
  jobj ([("cards", jobj cards), ("games", jarr games), ("winner", winner),
    ("wins", jarr [toString wins.1, toString wins.2]), ("exact", toString allObserved),
    ("cardsFullyChecked", toString cardsChecked)] ++ extra)

private def matchPenaltyTrace (ending : ReplayMatchEnd) : List (String × String) :=
  if ending.penalizedSeat.isSome then [("matchPenalty", (toJson ending).compress)] else []

private def matchTrace (saved : RecordedMatch) : Except String String := do
  let summary ← saved.verify
  let games ← saved.games.toList.mapM (fun game =>
    gameTrace game.input (game.eliminationConfig?.getD saved.input.config) saved.input.fuel)
  return matchTraceJson games summary.wins summary.result summary.exact summary.cardsFullyChecked
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
  let seats (team : PlayerId × PlayerId) := jarr [toString team.1.n, toString team.2.n]
  let teams := saved.input.seats
  return matchTraceJson games summary.wins summary.result allObserved cardsChecked
    ([("teams", jarr [seats teams.team0, seats teams.team1])] ++ matchPenaltyTrace saved.input.ending)
    config.ruleSet.isLimited

/-- Record, verify or generate a viewer trace from all the inputs of a saved match. -/
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
    | _ =>
      IO.eprintln "usage: riftbound-replay record INPUT.json ARCHIVE.json | verify ARCHIVE.json | view ARCHIVE.json TRACE.json | check-team TEAM.json | record-team TEAM.json ARCHIVE.json | verify-team ARCHIVE.json | view-team ARCHIVE.json TRACE.json"
      return 2
  catch error =>
    IO.eprintln error.toString
    return 1
