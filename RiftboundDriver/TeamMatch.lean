module

public import RiftboundDriver.MatchReplay

/-!
# Match records for two teams

Validate a four-seat event's setup and match administration against observed game results.
The Duel engine does not execute the optional action stream of a team game.
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

private def TeamSeats.players (seats : TeamSeats) : List PlayerId :=
  [seats.team0.1, seats.team0.2, seats.team1.1, seats.team1.2]

private def TeamSeats.order (seats : TeamSeats) (team0First : Bool) : List PlayerId :=
  let (first, second) := if team0First then (seats.team0, seats.team1) else (seats.team1, seats.team0)
  [first.1, second.1, first.2, second.2]

private def TeamSeats.teamOf (seats : TeamSeats) (seat : PlayerId) : Option PlayerId :=
  if seat == seats.team0.1 || seat == seats.team0.2 then some ⟨0⟩
  else if seat == seats.team1.1 || seat == seats.team1.2 then some ⟨1⟩
  else none

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
deriving DecidableEq, Repr, ToJson, FromJson

/-- Observations about a completed team game. -/
structure TeamGameRecord where
  /-- The four registrations, indexed by player ID. -/
  decks : List ConstructedDeck
  /-- The team entitled to choose the first turn, if any. -/
  chooser : Option PlayerId := none
  /-- All four seats in their actual turn order. -/
  order : List PlayerId
  /-- The three Battlefield selections, keyed by the contributing seat (CR 491.5). -/
  battlefields : List (PlayerId × CardId)
  /-- The final shared points, for team 0 and team 1. -/
  points : Nat × Nat
  /-- The observed game ending. -/
  ending : TeamGameEnd
  /-- Whether the match clock was called during this game. -/
  timed : Bool := false
  /-- Observed or inferred answers retained with the record for future review. -/
  answers : Array ReplayAnswer := #[]
deriving DecidableEq, Repr, ToJson, FromJson

/-- A Constructed tournament record for two teams with two players each. -/
structure TeamMatchRecord where
  /-- The team's fixed seating for this match. -/
  seats : TeamSeats
  /-- Tournament metadata for the Constructed 2v2 ban list. -/
  tournament : ReplayTournament
  /-- The applicable card sets at the event. -/
  legalSets : List SetCode
  /-- The number of games needed to win. -/
  winsRequired : Nat
  /-- The completed games in chronological order. -/
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

private def checkTeamDecks (game : TeamGameRecord) (seats : TeamSeats) (db : CardDB)
    (env : LegalityEnv) : Except String Unit := do
  if game.decks.length != 4 then throw "the four seat registrations are required"
  for (d, seat) in game.decks.zipIdx do
    if !decide (ConstructedDeckValid db env d) then throw s!"seat {seat} has an illegal registration"
  for (a, b) in [seats.team0, seats.team1] do
    let some first := game.decks[a.n]? >>= (·.deck.resolve db) | throw "missing teammate registration"
    let some second := game.decks[b.n]? >>= (·.deck.resolve db) | throw "missing teammate registration"
    if first.legend.nameKey == second.legend.nameKey ||
        first.battlefields.any (fun card => second.battlefields.any (·.nameKey == card.nameKey)) then
      throw "teammates share a Champion Legend or Battlefield"

private def teamGameResult (game : TeamGameRecord) (seats : TeamSeats) : Except String GameResult := do
  let (a, b) := game.points
  let won (team : Nat) := GameResult.won [⟨team⟩]
  match game.ending with
  | .scored =>
    if a >= 11 && b < 11 then return won 0
    if b >= 11 && a < 11 then return won 1
    throw "exactly one team must reach the victory score"
  | _ =>
    if a >= 11 || b >= 11 then throw "a team already reached the victory score"
    match game.ending with
    | .draw => return .draw
    | .concede seat =>
      let some team := seats.teamOf seat | throw "the concession seat is not in the match"
      return .won [MatchState.other team]
    | .time =>
      if !game.timed then throw "the team game ended on time without a time call"
      return if a >= b + 2 then won 0 else if b >= a + 2 then won 1 else .draw
    | .scored => throw "missing victory score"

private def checkTeamSetup (seats : TeamSeats) (game : TeamGameRecord) (state : MatchState)
    (previous : Option TeamGameRecord) : Except String PlayerId := do
  let team0 := game.order == seats.order true
  if !team0 && game.order != seats.order false then throw "turn order must be A, A, B, B across the teams"
  let firstTeam : PlayerId := ⟨if team0 then 0 else 1⟩
  match state.nextOrder with
  | .chance =>
    if !(game.chooser.any (·.n < 2)) then throw "the team chosen by chance is missing"
  | .loserChooses team =>
    if game.chooser != some team then throw s!"team {team.n} must choose who goes first"
  | .same team =>
    if game.chooser.isSome || firstTeam != team then throw "a draw preserves the same starting team"
  let contributors := game.battlefields.map Prod.fst
  if !decide (contributors.Perm (game.order.drop 1)) then
    throw "the three non-starting players each contribute one Battlefield"
  for (seat, id) in game.battlefields do
    if !(game.decks[seat.n]?.any (·.deck.battlefields.contains id)) then
      throw s!"seat {seat.n} did not register Battlefield {id.code}"
  if let some prev := previous then
    if state.reuseBattlefields && !decide (prev.battlefields.Perm game.battlefields) then
      throw "a draw preserves the same Battlefields"
    unless (prev.decks.zip game.decks).all (fun (a, b) =>
        sameRegistration a b || (state.sideboardAllowed && sameRegisteredPool a b)) do
      throw "a team registration changed outside its permitted sideboard window or pool"
  return firstTeam

/-- Check a recorded team's registrations, setup, shared scores and match outcome. -/
def TeamMatchRecord.check (input : TeamMatchRecord) (db : CardDB := RiftboundCards.db) :
    Except String TeamMatchResult := do
  if !decide (input.seats.players.Perm (allPlayers 4)) then throw "the teams must use four different seats"
  if input.winsRequired != 1 && input.winsRequired != 2 then throw "invalid number of wins required"
  let env ← input.tournament.legality .twoVTwo input.legalSets
  let mut state := MatchState.start input.winsRequired
  let mut previous : Option TeamGameRecord := none
  let mut uncheckedCards := #[]
  let mut timed := false
  for (game, index) in input.games.toList.zipIdx do
    let next := do
      if state.finished || timed then throw "a game starts after the match is over"
      checkTeamDecks game input.seats db env
      let first ← checkTeamSetup input.seats game state previous
      let result ← teamGameResult game input.seats
      pure (state.record result first)
    state ← next.mapError (fun error => s!"team game {index + 1}: {error}")
    timed := game.timed
    previous := some game
    uncheckedCards := uncheckedCards.push ((ReplayDecks.constructed game.decks).uncheckedCards db)
  let ending ← match input.ending with
    | .concede seat =>
      let some team := input.seats.teamOf seat | throw "the concession seat is not in the match"
      pure (ReplayMatchEnd.concede team)
    | other => pure other
  let result ← concludeReplayMatch state timed ending
  return { wins := (state.wins0, state.wins1), result, uncheckedCards }

end RiftboundDriver

end
