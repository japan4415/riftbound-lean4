module

public import RiftboundDriver.ReplayCodec
public import RiftboundCards.Registry

/-!
# Replayable engine inputs

A recording contains the submitted decks and the exact answers passed to the engine, including
chance and external actors. The same input stream can be verified against saved checkpoints.
-/

public section

namespace RiftboundDriver

open Lean Riftbound

/-- The cards each seat submitted for a game. -/
inductive ReplayDecks where
  /-- Decks checked under the Core Rules. -/
  | core (decks : List Deck)
  /-- Constructed registrations, including the cards outside the Main Deck. -/
  | constructed (decks : List ConstructedDeck)
  /-- Registered Sealed or Draft decks. -/
  | limited (decks : List LimitedDeck)
deriving DecidableEq, Repr, ToJson, FromJson

/-- A recorded answer, including how it was observed. -/
inductive ReplayAnswer where
  /-- The answer was recorded directly. -/
  | observed (action : Action)
  /-- The answer is a reconstruction of an incompletely observed choice. -/
  | inferred (action : Action) (evidence : String)
  /-- Available evidence did not establish an answer. -/
  | unknown (description : String)
deriving DecidableEq, Repr, ToJson, FromJson

/-- Resolve a recorded answer, retaining a diagnostic for missing or undocumented input. -/
def ReplayAnswer.resolve (answer : ReplayAnswer) (index : Nat) : Except String Action :=
  match answer with
  | .observed a => pure a
  | .inferred a evidence =>
    if evidence.trimAscii.toString.isEmpty then
      throw s!"answer {index}: an inferred answer needs an explanation"
    else pure a
  | .unknown description => throw s!"answer {index} is unobserved: {description}"

/-- The data required to set up and replay one game. -/
structure GameInputs where
  /-- The submitted decks for all seats, in seat order. -/
  decks : ReplayDecks
  /-- Exact answers in the order they were applied. -/
  answers : Array ReplayAnswer
  /-- The seat entitled to choose first or second, when the match made such a choice. -/
  chooser : Option PlayerId := none
  /-- Four-seat tournament turn order determined before the engine shuffles the decks. -/
  openingOrder : Option (List PlayerId) := none
deriving DecidableEq, Repr, ToJson, FromJson

/-- Rules pinned by a saved recording. -/
structure ReplayRules where
  /-- The version of the replay format and engine fingerprint representation. -/
  schema : Nat
  /-- The edition of the Core Rules. -/
  core : RulesDate
  /-- The edition of the Tournament Rules. -/
  tournament : RulesDate
  /-- An identifier for the exact card definitions, in their engine order. -/
  cards : String
deriving DecidableEq, Repr, ToJson, FromJson

/-- Rules metadata for replays produced by this driver. -/
def ReplayRules.current (db : CardDB) : ReplayRules :=
  ⟨1, coreRulesVersion, tournamentRulesVersion, toString (hash (reprStr db))⟩

/-- The replay comparison data for the state and events after one answer. -/
structure ReplayCheckpoint where
  /-- A diagnostic fingerprint of the complete mutable state. -/
  state : String
  /-- The events in the order the engine emitted them. -/
  events : List Event
deriving DecidableEq, Repr, ToJson, FromJson

/-- What the engine established by the end of a game. -/
structure ReplayGameResult where
  /-- The actual first turn order selected during setup. -/
  turnOrder : List PlayerId
  /-- The Battlefields selected during setup, keyed by the seat that brought them. -/
  battlefields : List (PlayerId × CardId)
  /-- The final score of each seat, in seat order. -/
  points : List Nat
  /-- The game outcome. An unfinished game has no result. -/
  result : Option GameResult
  /-- Whether time had been called in this game. -/
  timed : Bool
  /-- The last turn number when play continued beyond the scheduled turns (TR 408.4.c.3). -/
  suddenDeathTurn? : Option Nat := none
  /-- Whether all answers were directly observed. -/
  exact : Bool
  /-- Registered cards below `full`, in seat order. -/
  uncheckedCards : List (List (CardId × ImplStatus))
deriving DecidableEq, Repr, ToJson, FromJson

/-- One game as recorded and checked by the engine. -/
structure RecordedGame where
  /-- The submitted decks and the input stream. -/
  input : GameInputs
  /-- Rules derived from the preceding games of a single-elimination match. -/
  eliminationConfig? : Option GameConfig := none
  /-- A checkpoint for the initial state and for each successful answer. -/
  checkpoints : Array ReplayCheckpoint
  /-- The resulting setup details, score and winner. -/
  summary : ReplayGameResult
deriving DecidableEq, Repr, ToJson, FromJson

/-- Set up the recorded decks using the existing deck validation paths and pinned format legality. -/
def ReplayDecks.initial (decks : ReplayDecks) (db : CardDB) (config : GameConfig)
    (openingOrder : Option (List PlayerId) := none) :
    Except String GameState := do
  if config.mode.isTeamDuel then
    let some env := config.formatLegality | throw "team replay requires pinned format legality"
    let some order := openingOrder | throw "team replay requires the starting turn order"
    let setup := match decks, config.ruleSet.tournamentFormat with
      | .constructed registrations, some .constructed =>
        GameState.initialTeamConstructed db env order registrations config.ruleSet
      | .limited registrations, some .sealed =>
        GameState.initialTeamSealed db.withLimitedBlank env order registrations config.ruleSet
      | _, _ => none
    let some state := setup
      | throw "the team game cannot be set up from the submitted registrations and order"
    return state
  if openingOrder.isSome then throw "only four-seat matches set the starting order before setup"
  let state ← match decks, config.ruleSet.tournamentFormat, config.formatLegality with
    | .core ds, none, none => pure (GameState.initial db config ds)
    | .constructed ds, some .constructed, some env =>
      pure (GameState.initialConstructed db env config ds)
    | .limited ds, some format, some env =>
      if format.isLimited then pure (GameState.initialLimited db.withLimitedBlank env config ds)
      else throw "Limited decks require Sealed or Draft"
    | _, _, _ => throw "deck type, rules and format legality do not agree"
  match state with
  | some s => pure s
  | none => throw "the game cannot be set up from the submitted decks"

private def deckIds (d : Deck) : List CardId :=
  d.legend :: d.main ++ d.runes ++ d.battlefields ++ d.reserveLegends

/-- List the cards below full coverage in each seat's registration. -/
def ReplayDecks.uncheckedCards (decks : ReplayDecks) (db : CardDB) :
    List (List (CardId × ImplStatus)) :=
  let ids : List (List CardId) := match decks with
    | .core ds => ds.map deckIds
    | .constructed ds => ds.map (fun (d : ConstructedDeck) => deckIds d.deck ++ d.sideboard)
    | .limited ds => ds.map (fun (d : LimitedDeck) =>
      d.legend.toList ++ d.main ++ d.runes ++ d.battlefields ++ d.reserveLegends)
  ids.map (fun seat => seat.eraseDups.filterMap (fun id => do
    let card ← db.find? id
    if card.status == .full then none else some (id, card.status)))

/-- Capture the state fingerprint and the events that the engine actually returned. -/
def ReplayCheckpoint.capture (s : GameState) (events : List Event) : ReplayCheckpoint :=
  -- Card definitions are immutable and fingerprinted once in ReplayRules.
  ⟨toString (hash (reprStr { s with cards := ⟨[]⟩ })), events⟩

/-- Save the computed per-game single-elimination rules with the evidence and viewer trace. -/
def replayEliminationConfig (config : GameConfig) : Option GameConfig :=
  match config.ruleSet with
  | .tournamentElimination .. => some config
  | _ => none

/-- Summarize the engine state together with its recorded Battlefield selections. -/
def ReplayGameResult.fromState (s : GameState) (decks : ReplayDecks)
    (battlefields : List (PlayerId × CardId)) (exact : Bool) : ReplayGameResult :=
  { turnOrder := s.turnOrder
    battlefields
    points := (allPlayers s.playerCount).map s.pointsOf
    result := s.result
    timed := s.clock.isSome
    suddenDeathTurn? := s.clock.bind (fun clock =>
      if clock.allowsSuddenDeath && decide (clock.lastTurn < s.turn) then some s.turn else none)
    exact
    uncheckedCards := decks.uncheckedCards s.cards }

/-- Resolve a setup pick to the seat and Battlefield card it identifies in the initial zones. -/
def pickedBattlefield (s : GameState) (action : Action) : Option (PlayerId × CardId) := do
  let .chanceBattlefield p :: _ := s.pending | none
  let .pick i := action.kind | none
  let id ← (s.zone (.player p .outOfGame))[i]?
  let card ← s.cardDef? id
  pure (p, card.id)

private def checkCheckpoint (expected : Option (Array ReplayCheckpoint))
    (index : Nat) (actual : ReplayCheckpoint) : Except String Unit := do
  if let some witnesses := expected then
    if witnesses[index]? != some actual then
      throw s!"checkpoint {index}: state or events differ"

private def runGame (input : GameInputs) (db : CardDB) (config : GameConfig)
    (fuel : Nat) (expected : Option (Array ReplayCheckpoint)) : Except String RecordedGame := do
  if expected.any (fun witnesses => witnesses.size != input.answers.size + 1) then
    throw "the checkpoint count does not match the input stream"
  let mut s ← input.decks.initial db config input.openingOrder
  let initial := ReplayCheckpoint.capture s []
  checkCheckpoint expected 0 initial
  let mut checkpoints := #[initial]
  let mut fields : List (PlayerId × CardId) := []
  let mut exact := true
  for (answer, index) in input.answers.toList.zipIdx do
    let action ← answer.resolve (index + 1)
    if let .inferred .. := answer then exact := false
    let field := pickedBattlefield s action
    match step fuel s action with
    | .error error => throw s!"answer {index + 1}: {repr error}"
    | .ok (next, events) =>
      if let some entry := field then fields := entry :: fields
      let witness := ReplayCheckpoint.capture next events
      checkCheckpoint expected (index + 1) witness
      checkpoints := checkpoints.push witness
      s := next
  return {
    input, eliminationConfig? := replayEliminationConfig config, checkpoints,
    summary := ReplayGameResult.fromState s input.decks fields.reverse exact }

/-- Play recorded answers with the engine, retaining the exact input, checkpoints and outcome. -/
def GameInputs.record (input : GameInputs) (db : CardDB) (config : GameConfig)
    (fuel : Nat := 100) : Except String RecordedGame :=
  runGame input db config fuel none

/-- Replay one game and report the first recorded checkpoint that disagrees. -/
def RecordedGame.verify (saved : RecordedGame) (db : CardDB) (config : GameConfig)
    (fuel : Nat := 100) : Except String ReplayGameResult := do
  if saved.eliminationConfig? != replayEliminationConfig config then
    throw "the saved single-elimination clock procedure differs"
  let actual ← runGame saved.input db config fuel (some saved.checkpoints)
  if saved.summary != actual.summary then throw "the final game outcome differs"
  return actual.summary

end RiftboundDriver

end
