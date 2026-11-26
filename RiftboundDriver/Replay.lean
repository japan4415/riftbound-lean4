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

/-- A private deck whose randomized portion can be shuffled by a judge (TR 701.4). -/
inductive JudgeDeck where
  /-- The player's Main Deck. -/
  | mainDeck
  /-- The player's Rune Deck. -/
  | runeDeck
deriving DecidableEq, Repr, ToJson, FromJson

/-- A deck for which the judge found no randomized portion and could complete the remedy
without a shuffle (TR 701.4.b.1). -/
structure JudgeUnshuffledDeck where
  /-- The seat whose deck had no randomized portion. -/
  seat : PlayerId
  /-- Which of that seat's decks was left as it was. -/
  deck : JudgeDeck
deriving DecidableEq, Repr, ToJson, FromJson

/-- The observed positions and outcome of a remedy shuffle. -/
structure JudgeShuffle where
  /-- The owner of the affected deck. -/
  seat : PlayerId
  /-- The affected deck. -/
  deck : JudgeDeck
  /-- Zero-based positions, in ascending order, included in the random portion. -/
  positions : List Nat
  /-- The resulting object IDs at those positions, in the same order. -/
  order : List ObjId
deriving DecidableEq, Repr, ToJson, FromJson

/-- The judge's candidate set and the observed result of undoing one private draw (TR 701.5.d.3). -/
structure JudgeDrawReturn where
  /-- The hand object's ID created by the recorded draw. -/
  drawn : ObjId
  /-- Candidate physical cards, identified by their object IDs at the rewind target. -/
  candidates : List ObjId
  /-- The candidate the judge returned to the deck. -/
  returned : ObjId
deriving DecidableEq, Repr, ToJson, FromJson

/-- A rewind with observed private draws and any subsequent remedy shuffles. -/
structure JudgePrivateRewind where
  /-- The game checkpoint to restore. -/
  target : Nat
  /-- The judge's recorded random selections, keyed by the corresponding draw. -/
  returns : List JudgeDrawReturn
  /-- Optional remedy shuffles before play resumes. Order IDs refer to the rewind target
  (TR 701.5.d.4). -/
  shuffles? : Option (List JudgeShuffle) := none
  /-- The judge's recorded exceptions when there was no randomized portion of a deck. -/
  unshuffledDecks? : Option (List JudgeUnshuffledDeck) := none
deriving DecidableEq, Repr, ToJson, FromJson

/-- A judge's recorded rewind across earlier administrative actions. -/
structure JudgeTimelineRewind where
  /-- The checkpoint on the active line to restore. -/
  target : Nat
  /-- The judge's final scheduled turn when the called clock is carried across the rewind. -/
  deadline? : Option Nat := none
  /-- Checkpoints of all earlier remedies the judge explicitly reversed, latest first. -/
  rulings? : Option (List Nat) := none
  /-- Private draw selections made while restoring this state. -/
  returns? : Option (List JudgeDrawReturn) := none
  /-- Optional remedy shuffles using object IDs at the rewind target. -/
  shuffles? : Option (List JudgeShuffle) := none
  /-- The judge's recorded exceptions when there was no randomized portion of a deck. -/
  unshuffledDecks? : Option (List JudgeUnshuffledDeck) := none
deriving DecidableEq, Repr, ToJson, FromJson

/-- A recorded answer, including how it was observed. -/
inductive ReplayAnswer where
  /-- The answer was recorded directly. -/
  | observed (action : Action)
  /-- The answer is a reconstruction of an incompletely observed choice. -/
  | inferred (action : Action) (evidence : String)
  /-- Available evidence did not establish an answer. -/
  | unknown (description : String)
  /-- The initial Constructed Best of 1 sideboard window closes (TR 406.1.h.5). -/
  | bo1Sideboard
  /-- The judge applies simultaneous Game Loss penalties to these seats (TR 701.2.b). -/
  | gameLoss (seats : List PlayerId)
  /-- The judge restores the state at a preceding game checkpoint (TR 701.5). -/
  | judgeRewind (target : Nat)
  /-- The judge reorders a private deck's randomized portion (TR 701.4). -/
  | judgeShuffle (shuffle : JudgeShuffle)
  /-- Rewind with the judge's observed selections for private draws. -/
  | judgePrivateRewind (rewind : JudgePrivateRewind)
  /-- Rewind across a time call or earlier correction under a recorded ruling. -/
  | judgeTimelineRewind (rewind : JudgeTimelineRewind)
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
  | .bo1Sideboard => throw s!"answer {index}: Best of 1 sideboarding is a setup step"
  | .gameLoss _ => throw s!"answer {index}: a Game Loss is a judge ruling"
  | .judgeRewind _ | .judgeShuffle _ | .judgePrivateRewind _ | .judgeTimelineRewind _ =>
    throw s!"answer {index}: a correction is a judge ruling"

private def unshuffledDecksJson (decks : Option (List JudgeUnshuffledDeck)) :
    List (String × String) :=
  let recorded := decks.getD []
  if recorded.isEmpty then [] else [("rewindUnshuffledDecks", (toJson recorded).compress)]

/-- Additional trace metadata for a judge correction, independent of in-game actions. -/
def ReplayAnswer.correctionJson : ReplayAnswer → List (String × String)
  | .judgeRewind target => [("judgeRewind", toString target)]
  | .judgeShuffle shuffle => [("judgeShuffle", (toJson shuffle).compress)]
  | .judgePrivateRewind rewind =>
    [("judgeRewind", toString rewind.target), ("privateDrawReturns", toString rewind.returns.length),
     ("rewindShuffles", toString (rewind.shuffles?.getD []).length)] ++
      unshuffledDecksJson rewind.unshuffledDecks?
  | .judgeTimelineRewind rewind =>
    [("judgeRewind", toString rewind.target), ("privateDrawReturns", toString (rewind.returns?.getD []).length),
     ("rewindShuffles", toString (rewind.shuffles?.getD []).length),
     ("rewindRulings", toString (rewind.rulings?.getD []).length)] ++
      (rewind.deadline?.map (fun deadline => ("rewindDeadline", toString deadline))).toList ++
      unshuffledDecksJson rewind.unshuffledDecks?
  | _ => []

/-- Whether a trace row needs to rescan object metadata after restoring an earlier state. -/
def ReplayAnswer.rewinds : ReplayAnswer → Bool
  | .judgeRewind _ | .judgePrivateRewind _ | .judgeTimelineRewind _ => true
  | _ => false

/-- A Game Loss affects the whole side; if neither side remains, the game is a draw (TR 701.2.b). -/
def judgeGameLossResult (players : List PlayerId) (sameSide : PlayerId → PlayerId → Bool)
    (seats : List PlayerId) : Except String GameResult := do
  unless !seats.isEmpty && decide seats.Nodup && seats.all players.contains do
    throw "a Game Loss requires distinct registered seats"
  let remaining := players.filter (fun p => !(seats.any (sameSide p)))
  return if remaining.isEmpty then .draw else .won remaining

/-- The affected seats, if the final answer was a Game Loss. -/
def ReplayAnswer.penalizedSeats : ReplayAnswer → Option (List PlayerId)
  | .gameLoss seats => some seats
  | _ => none

/-- Evidence for the starting turn order supplied before a team game's answer stream. -/
inductive ReplayOpeningOrderEvidence where
  /-- The order was reconstructed from indirect evidence. -/
  | inferred (evidence : String)
  /-- The order could not be determined. -/
  | unknown (description : String)
deriving DecidableEq, Repr, ToJson, FromJson

/-- Reject an undocumented inference or a starting order that could not be established. -/
def ReplayOpeningOrderEvidence.check : ReplayOpeningOrderEvidence → Except String Unit
  | .inferred evidence =>
    if evidence.trimAscii.toString.isEmpty then
      throw "an inferred starting turn order needs an explanation"
    else pure ()
  | .unknown description => throw s!"starting turn order is unobserved: {description}"

/-- The data required to set up and replay one game. -/
structure GameInputs where
  /-- The submitted decks for all seats, in seat order. -/
  decks : ReplayDecks
  /-- Recorded answers in the order they were applied. -/
  answers : Array ReplayAnswer
  /-- The seat entitled to choose first or second, when the match made such a choice. -/
  chooser : Option PlayerId := none
  /-- Four-seat War or team turn order, known before choosing the three Battlefields. -/
  openingOrder : Option (List PlayerId) := none
  /-- Evidence when the supplied starting order was not observed directly. -/
  openingOrderEvidence? : Option ReplayOpeningOrderEvidence := none
  /-- The original registrations when the event uses the optional Constructed Best of 1 setup.
  The game decks describe the configuration after the initial sideboard window (TR 406.1.h). -/
  bo1Setup? : Option (List ConstructedDeck) := none
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

/-- A revalidation can compare fingerprints only within the same format and rule editions. -/
def ReplayRules.checkEditions (saved current : ReplayRules) : Except String Unit := do
  unless saved.schema == current.schema && saved.core == current.core &&
      saved.tournament == current.tournament do
    throw "the replay format or rules editions differ"

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
  /-- Whether all answers and the supplied starting turn order were directly observed. -/
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

/-- The seats sanctioned by the judge, when the game ended with a Game Loss. -/
def RecordedGame.gameLossSeats (game : RecordedGame) : Option (List PlayerId) :=
  game.input.answers.back?.bind ReplayAnswer.penalizedSeats

/-- The named Battlefields revealed before a Game Loss cannot be reused (TR 406.1.c).
Each unlimited blank in Limited can be represented by a new physical copy. -/
def RecordedGame.penaltyBattlefields (game : RecordedGame) : List (PlayerId × CardId) :=
  if game.gameLossSeats.isSome then
    game.summary.battlefields.filter (·.2 != limitedBlankBattlefield.id)
  else []

/-- Ensure a seat uses a different Battlefield from any game ended by a Game Loss. -/
def checkPenaltyBattlefields (forbidden selected : List (PlayerId × CardId)) : Except String Unit := do
  for (seat, card) in selected do
    if forbidden.contains (seat, card) then
      throw s!"seat {seat.n} must use a different Battlefield after a Game Loss: {card.code}"

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
  if config.mode == Mode.ffa4 then
    let some order := openingOrder | throw "War replay requires the starting turn order"
    let .core submitted := decks | throw "War replay requires Core Rules decks"
    unless config.ruleSet == .coreOnly && config.formatLegality.isNone do
      throw "War replay requires the Core Rules"
    let some state := GameState.initialFfa4 db order submitted
      | throw "the War game cannot be set up from the submitted decks and order"
    return state
  if openingOrder.isSome then throw "a supplied starting order requires War or a team game"
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

/-- A Constructed sideboard must use the registered pool and preserve the fixed slots (TR 403.4). -/
def sameRegisteredPool (old new : ConstructedDeck) : Bool :=
  let a := old.deck
  let b := new.deck
  a.legend == b.legend && decide (a.runes.Perm b.runes) &&
    decide (a.battlefields.Perm b.battlefields) && decide (a.reserveLegends.Perm b.reserveLegends) &&
    decide (List.Perm (a.main ++ old.sideboard) (b.main ++ new.sideboard))

/-- Initialize the replay at the official setup boundary. In the optional Best of 1 procedure,
put out the Legends and Battlefield candidates before committing the cards from the closed decks. -/
def GameInputs.initial (input : GameInputs) (db : CardDB) (config : GameConfig) :
    Except String GameState := do
  if let some evidence := input.openingOrderEvidence? then
    unless config.mode.isTeamDuel || config.mode == Mode.ffa4 do
      throw "supplied starting turn order evidence requires War or a team game"
    evidence.check
  let some registered := input.bo1Setup? | return ← input.decks.initial db config input.openingOrder
  unless config.mode == Mode.duel && config.ruleSet.tournamentFormat == some .constructed &&
      input.openingOrder.isNone do
    throw "the optional Best of 1 setup requires a Constructed Duel"
  let some env := config.formatLegality | throw "the Best of 1 setup needs pinned format legality"
  let .constructed submitted := input.decks | throw "the Best of 1 setup needs final registrations"
  unless registered.length == 2 && submitted.length == 2 do
    throw "two original and two final registrations are required"
  let mut s := GameState.empty config db
  for ((original, final), index) in (registered.zip submitted).zipIdx do
    unless decide (ConstructedDeckValid db env original) &&
        decide (ConstructedDeckValid db env final) do
      throw s!"seat {index} has an illegal Best of 1 registration"
    unless sameRegisteredPool original final do
      throw s!"seat {index} must sideboard from the registered pool and preserve the fixed slots"
    let p : PlayerId := ⟨index⟩
    let placed := do
      let next ← addCards db p (.player p .legendZone) s [original.deck.legend]
      addCards db p (.player p .outOfGame) next original.deck.battlefields
    let some next := placed
      | throw s!"seat {index} could not place the Legend and Battlefields"
    s := next
  return { s with pending := [.chanceBattlefield ⟨0⟩, .chanceBattlefield ⟨1⟩, .chanceTurnOrder] }

private def addBo1Deck (db : CardDB) (s : GameState) (p : PlayerId) (deck : Deck) :
    Option GameState := do
  let s ← addCards db p (.player p .reserveLegends) s deck.reserveLegends
  let s ← addCards db p (.player p .championZone) s [deck.chosenChampion]
  let s ← addCards db p (.player p .mainDeck) s (deck.main.erase deck.chosenChampion)
  addCards db p (.player p .runeDeck) s deck.runes

/-- Whether the optional Best of 1 setup is waiting for the initiative choice. -/
def GameInputs.awaitsBo1Initiative (input : GameInputs) (s : GameState) : Bool :=
  input.bo1Setup?.isSome && s.phase == .setup && s.pending == [.chanceTurnOrder] && s.result.isNone

/-- Identify the initiative answer in this setup for trace presentation. -/
def GameInputs.isBo1Initiative (input : GameInputs) (s : GameState) (action : Option Action) : Bool :=
  input.awaitsBo1Initiative s && action.any (fun a => match a.kind with
    | .arrangePlayers _ => true
    | _ => false)

/-- Whether the optional Best of 1 setup is waiting for the final registrations. -/
def GameInputs.awaitsBo1Sideboard (input : GameInputs) (s : GameState) : Bool :=
  input.bo1Setup?.isSome && s.phase == .setup && s.pending == [.setupHands] && s.result.isNone

/-- A remedy shuffle leaves known positions and the game's trigger stream alone (TR 701.4). -/
def JudgeShuffle.apply (shuffle : JudgeShuffle) (s : GameState) : Except String GameState := do
  unless s.config.ruleSet.isTournament && s.result.isNone && s.phase != .setup do
    throw "a judge shuffle requires ongoing tournament play"
  unless s.players.contains shuffle.seat do throw "invalid judge shuffle seat"
  let kind := match shuffle.deck with | .mainDeck => ZoneKind.mainDeck | .runeDeck => .runeDeck
  let zone := Zone.player shuffle.seat kind
  let previous := s.zone zone
  unless !shuffle.positions.isEmpty && decide (shuffle.positions.Pairwise (· < ·)) do
    throw "judge shuffle positions must be nonempty and strictly increasing"
  let some selected := shuffle.positions.mapM (fun i => previous[i]?)
    | throw "a judge shuffle position is outside the deck"
  unless decide (selected.Perm shuffle.order) do
    throw "a judge shuffle must keep exactly the objects selected from that deck"
  let changes := shuffle.positions.zip shuffle.order
  return s.reorder zone (previous.zipIdx.map (fun (card, i) => (changes.lookup i).getD card))

private def GameInputs.applyAnswerWith (input : GameInputs) (s : GameState) (answer : ReplayAnswer)
    (index fuel : Nat) (observeFaces : Bool) :
    Except String (Option Action × (GameState × List Event) × List CardDisclosure) := do
  if let .judgeShuffle shuffle := answer then
    let next ← (shuffle.apply s).mapError (fun error => s!"answer {index}: {error}")
    return (none, (next, []), [])
  if let .gameLoss seats := answer then
    unless s.config.ruleSet.isTournament && s.config.mode.hasTwoSides && s.result.isNone do
      throw s!"answer {index}: a Game Loss requires an ongoing tournament game"
    let result ← (judgeGameLossResult s.players s.config.mode.sameSide seats).mapError
      (fun error => s!"answer {index}: {error}")
    return (none, ({ s with result := some result, pending := [] }, []), [])
  let awaitingSideboard := input.awaitsBo1Sideboard s
  if let .bo1Sideboard := answer then
    unless awaitingSideboard do throw s!"answer {index}: no Best of 1 sideboard window is open"
    let .constructed registrations := input.decks | throw "the Best of 1 setup needs final registrations"
    let mut next := s
    for (registration, seat) in registrations.zipIdx do
      let some built := addBo1Deck s.cards next ⟨seat⟩ registration.deck
        | throw s!"seat {seat} could not set out the final registration"
      next := built
    let shuffles := (startFrames s.playerCount).filter (fun | .chanceShuffle _ => true | _ => false)
    return (none, ({ next with pending := shuffles ++ [.setupHands] }, []), [])
  let action ← answer.resolve index
  if awaitingSideboard && action.kind != .concede && action.kind != .declareDraw then
    throw s!"answer {index}: close the Best of 1 sideboard window before shuffling"
  let transition := if input.isBo1Initiative s (some action) then
    if Legal s action then
      match applyFrame0 s action with
      | some (next, events) => .ok ((next, events),
          if observeFaces then CardDisclosure.capture s next 0 events else [])
      | none => .error (.internal "applyFrame0")
    else .error .illegal
  else if observeFaces then stepWithDisclosures fuel s action
  else (step fuel s action).map (·, [])
  let (result, disclosures) ← transition.mapError (fun error => s!"answer {index}: {repr error}")
  return (some action, result, disclosures)

/-- Reproduce an answer, including the administrative boundary before shuffling in TR 406.1.h. -/
def GameInputs.applyAnswer (input : GameInputs) (s : GameState) (answer : ReplayAnswer)
    (index fuel : Nat) : Except String (Option Action × GameState × List Event) := do
  let (action, (next, events), _) ← input.applyAnswerWith s answer index fuel false
  return (action, next, events)

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

/-- Encode XP in the old legend field when the seat has a Legend, preserving existing
checkpoints for games where XP was tracked correctly. Seats without a Legend keep the XP field. -/
private def replayXP (s : GameState) : GameState :=
  if s.experience.isEmpty then s else
    s.players.foldl (fun state p =>
      match s.xpOf p, (s.zone (.player p .legendZone)).head? with
      | n + 1, some legend =>
        (state.modObj legend (fun o => { o with xp := n + 1 })).setXP p 0
      | _, _ => state) s

/-- Capture the state fingerprint and the events that the engine actually returned. -/
def ReplayCheckpoint.capture (s : GameState) (events : List Event) : ReplayCheckpoint :=
  -- Card definitions are immutable and fingerprinted once in ReplayRules.
  ⟨toString (hash (reprStr (replayXP { s with cards := ⟨[]⟩ }))), events⟩

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

private inductive RewindBoundary where
  | play
  | clock
  | ruling
  | setup
deriving DecidableEq

private structure ObservedDraw where
  seat : PlayerId
  source : ObjId
  drawn : ObjId
  wasRevealed : Bool

private abbrev DeckKnowledge := PlayerId × PhysId

/-- Information gained from a deck and the withdrawals that may follow it in the same answer. -/
private inductive DeckObservation where
  | seen (viewer : PlayerId) (card : PhysId)
  | withdrawn (card : PhysId)

/-- The state and setup observations at a chronological checkpoint. -/
structure ReplayPosition where
  /-- The state at the checkpoint. -/
  state : GameState
  /-- Setup observations made by this checkpoint, newest first. -/
  fields : List (PlayerId × CardId) := []
  /-- Events in the action that produced this checkpoint. -/
  events : List Event := []
  /-- Faces shown during the answer that produced this position. -/
  disclosures : List CardDisclosure := []
  /-- Publicly revealed cards still identifiable in a player's Main Deck or hand. -/
  private knownCards : List ObjId := []
  /-- Faces that were known at this checkpoint, keyed by seat and physical deck card. -/
  private knownDeckCards : List (PlayerId × PhysId) := []
  /-- What the preceding answer showed or took from a deck, in event order. -/
  private deckObservations : List DeckObservation := []
  /-- Draws made by this answer, newest first. -/
  private draws : List ObservedDraw := []
  /-- The kind of transition that ended at this checkpoint. -/
  private boundary : RewindBoundary := .setup
  /-- A rewind's parent on the active line, skipping the abandoned operations. -/
  private rewindParent : Option Nat := none

/-- Capture a state without a preceding recorded action. -/
def ReplayPosition.fromState (state : GameState) (fields : List (PlayerId × CardId) := [])
    (disclosures : List CardDisclosure := []) : ReplayPosition :=
  { state, fields, disclosures }

/-- One draw from a position in the deck at the rewind target. -/
private structure DrawSlot extends ObservedDraw where
  index : Nat

private def notePublicMove (known : List ObjId) (source moved : ObjId) : List ObjId :=
  if known.contains source then moved :: known.erase source else known

private def observeDraws (known : List ObjId) (draws : List ObservedDraw) :
    List Event → List ObjId × List ObservedDraw
  | .revealed _ card :: rest => observeDraws (card :: known.erase card) draws rest
  | .handRevealed _ cards :: rest => observeDraws ((cards ++ known).eraseDups) draws rest
  | .moved source drawn (.player seat .hand) :: .drew p :: rest =>
    let draws := if seat == p then ⟨seat, source, drawn, known.contains source⟩ :: draws else draws
    observeDraws (notePublicMove known source drawn) draws rest
  | .moved source moved _ :: rest => observeDraws (notePublicMove known source moved) draws rest
  | _ :: rest => observeDraws known draws rest
  | [] => (known, draws)

private def DrawSlot.atTarget (base : GameState) (draw : ObservedDraw) : Option DrawSlot := do
  let index ← (base.zone (.player draw.seat .mainDeck)).findIdx? (· == draw.source)
  pure { toObservedDraw := draw, index }

private def JudgeShuffle.selectedCards (shuffle : JudgeShuffle) (before : GameState) : List ObjId :=
  let kind := match shuffle.deck with | .mainDeck => ZoneKind.mainDeck | .runeDeck => .runeDeck
  let deck := before.zone (.player shuffle.seat kind)
  shuffle.positions.filterMap (fun index => deck[index]?)

private def JudgeShuffle.obscuredCards (shuffle : JudgeShuffle) (before : GameState) : List ObjId :=
  if shuffle.deck == .mainDeck then shuffle.selectedCards before else []

private def obscuredDeckCards (before : GameState) (answer : ReplayAnswer) (action : Option Action) : List ObjId :=
  match answer with
  | .judgeShuffle shuffle => shuffle.obscuredCards before
  | _ =>
    match action, before.pending with
    | some ⟨.chance, .arrange _⟩, .chanceShuffle (.player p .mainDeck) :: _ =>
      before.zone (.player p .mainDeck)
    | some ⟨.chance, .arrange _⟩, .chancePredict _ _ _ bottom :: _ => bottom
    | some ⟨.chance, .arrange _⟩, .chanceRecycleTrash _ _ cards :: _ => cards
    | _, _ => []

private def trackedInPrivateZones (s : GameState) (known : List ObjId) : List ObjId :=
  known.filter (fun id => match s.locate id with
    | some (.player _ .mainDeck) | some (.player _ .hand) => true
    | _ => false)

private def physicalCard (s : GameState) (id : ObjId) : Option PhysId :=
  (s.obj? id).bind (·.kind.phys?)

private def deckPhysicalCards (s : GameState) : List PhysId :=
  s.players.flatMap (fun seat =>
    (s.zone (.player seat .mainDeck) ++ s.zone (.player seat .runeDeck)).filterMap (physicalCard s))

/-- A move may rename an object between the look and the draw. Follow the actual physical cards
through the answer without using its final zones to decide where the look took place. -/
private def observeDeckCards (before after : GameState) (events : List Event) : List DeckObservation :=
  go [] events
where
  go (moved : List (ObjId × (Zone × PhysId))) : List Event → List DeckObservation
    | [] => []
    | event :: rest =>
      let location (id : ObjId) := (moved.lookup id).map Prod.fst <|> before.locate id
      let physical (id : ObjId) := (moved.lookup id).map Prod.snd <|> physicalCard before id
      let seen (id : ObjId) (audience : List PlayerId) :=
        match location id, physical id with
        | some (.player _ .mainDeck), some card | some (.player _ .runeDeck), some card =>
          audience.map (fun seat => DeckObservation.seen seat card)
        | _, _ => []
      match event with
      | .lookedAt viewer id => seen id [viewer] ++ go moved rest
      | .revealed _ id => seen id before.players ++ go moved rest
      | .moved old next dest =>
        match physical old <|> physicalCard after next with
        | none => go moved rest
        | some card =>
          let withdrew := match location old, dest, rest with
            | _, .player seat .hand, .drew drawer :: _ => seat == drawer
            | some (.player seat .runeDeck), .player owner .base, _ => seat == owner
            | _, _, _ => false
          let later := go ((next, (dest, card)) :: moved) rest
          if withdrew then .withdrawn card :: later else later
      | _ => go moved rest

private def obscuredDeckPhysicalCards (before : GameState) (answer : ReplayAnswer)
    (action : Option Action) : List PhysId :=
  let ids := match answer with
    | .judgeShuffle shuffle => shuffle.selectedCards before
    | _ =>
      match action, before.pending with
      | some ⟨.chance, .arrange _⟩, .chanceShuffle (.player p .runeDeck) :: _ =>
        before.zone (.player p .runeDeck)
      | _, _ => obscuredDeckCards before answer action
  ids.filterMap (physicalCard before)

private def DeckObservation.remember (known : List DeckKnowledge) :
    DeckObservation → List DeckKnowledge
  | .seen seat card => if known.contains (seat, card) then known else (seat, card) :: known
  | .withdrawn card => known.filter (fun knownCard => knownCard.2 != card)

/-- What a rewind would expose again in an unreordered deck (TR 701.5.d.4). -/
private def rewindDeckKnowledge (target : ReplayPosition) (chronology : List ReplayPosition) :
    List DeckKnowledge :=
  let newlySeen := chronology.foldl (fun known pos =>
    pos.deckObservations.foldl DeckObservation.remember known) []
  if newlySeen.isEmpty then [] else
    let deck := deckPhysicalCards target.state
    newlySeen.filter (fun known => !target.knownDeckCards.contains known && deck.contains known.2)

private def shuffleAfterRewind (base current : GameState) (shuffle : JudgeShuffle) :
    Except String GameState := do
  let kind := match shuffle.deck with | .mainDeck => ZoneKind.mainDeck | .runeDeck => .runeDeck
  let cards := current.zone (.player shuffle.seat kind)
  let order ← shuffle.order.mapM (fun ref => do
    let some phys := physicalCard base ref | throw "a rewind shuffle must name a card at the rewind target"
    let some id := cards.find? (fun id => physicalCard current id == some phys)
      | throw "a rewind shuffle card is not in the restored deck"
    pure id)
  ({ shuffle with order }).apply current

private def exchangeDrawSlot (s : GameState) (draw : DrawSlot) (returned : ObjId) :
    Except String GameState := do
  let deck := Zone.player draw.seat .mainDeck
  let hand := Zone.player draw.seat .hand
  let some slot := (s.zone deck)[draw.index]? | throw "the original draw position is missing"
  if slot == returned then return s
  if (s.zone deck).contains returned then
    return s.reorder deck ((s.zone deck).map (fun id =>
      if id == slot then returned else if id == returned then slot else id))
  let some place := (s.zone hand).findIdx? (· == returned)
    | throw "the selected card is no longer in the hand"
  let some (afterDraw, _) := moveObj s slot hand (.atIndex place)
    | throw "the drawn card could not be kept in the hand"
  let some (restored, _) := moveObj afterDraw returned deck (.atIndex draw.index)
    | throw "the selected card could not be returned to the deck"
  return restored

private def applyDrawReturns (base : GameState) (known : List ObjId) (returns : List JudgeDrawReturn) :
    List DrawSlot → GameState → Except String GameState
  | [], s => pure s
  | draw :: more, s => do
    let some choice := returns.find? (·.drawn == draw.drawn) | applyDrawReturns base known returns more s
    let deck := s.zone (.player draw.seat .mainDeck)
    -- Earlier private draws are still in the hand at this stage of reversing the actions.
    let drawCards := (draw :: more).filterMap (fun slot =>
      if slot.seat == draw.seat && !slot.wasRevealed then deck[slot.index]? else none)
    let hiddenHand := (s.zone (.player draw.seat .hand)).filter (fun id => !known.contains id)
    let available := hiddenHand ++ drawCards
    let findAvailable (ref : ObjId) : Option ObjId := do
      let phys ← physicalCard base ref
      available.find? (fun id => physicalCard s id == some phys)
    unless decide choice.candidates.Nodup && choice.candidates.contains choice.returned &&
        choice.candidates.all (fun id => (findAvailable id).isSome) do
      throw "private draw candidates must be distinct cards available in the affected hand"
    let some chosen := findAvailable choice.returned
      | throw "the card being returned is no longer available for this draw"
    let next ← exchangeDrawSlot s draw chosen
    applyDrawReturns base known returns more next

private def applyRewindRemedies (target : ReplayPosition) (undone chronology : List ReplayPosition)
    (returns : List JudgeDrawReturn) (shuffles : List JudgeShuffle)
    (unshuffled : List JudgeUnshuffledDeck) : Except String ReplayPosition := do
  let restored ← if returns.isEmpty then pure target.state else do
    let draws := undone.flatMap (fun pos => pos.draws.filterMap (DrawSlot.atTarget target.state))
    let named : List ObjId := returns.map (·.drawn)
    unless decide named.Nodup && named.all (fun id => draws.any (·.drawn == id)) do
      throw "each private return needs a distinct undone draw from the target deck"
    if draws.any (fun draw => draw.wasRevealed && named.contains draw.drawn) then
      throw "a publicly revealed draw must restore the revealed card"
    unless decide ((draws.map (·.source)).Nodup) do
      throw "the rewind contains repeated draws from the same original slot"
    applyDrawReturns target.state target.knownCards returns draws target.state
  let shuffle (acc : GameState × List ObjId × List PhysId) (change : JudgeShuffle) := do
    let (state, known, shuffled) := acc
    let obscured := change.obscuredCards state
    let covered := (change.selectedCards state).filterMap (physicalCard state)
    let next ← shuffleAfterRewind target.state state change
    let shuffled := if covered.length < 2 then shuffled else covered ++ shuffled
    return (next, known.filter (fun id => !obscured.contains id), shuffled)
  let (state, known, shuffled) ← shuffles.foldlM shuffle (restored, target.knownCards, [])
  let learned := rewindDeckKnowledge target chronology
  let required := (learned.map Prod.snd).eraseDups
  unless decide unshuffled.Nodup do throw "each unshuffled deck must be named once"
  let waived ← unshuffled.flatMapM (fun deck => do
    let kind := match deck.deck with | .mainDeck => ZoneKind.mainDeck | .runeDeck => .runeDeck
    let cards := (state.zone (.player deck.seat kind)).filterMap (physicalCard state)
    unless restored.players.contains deck.seat && cards.any required.contains do
      throw "an unshuffled deck must contain a card affected by the rewind"
    if shuffles.any (fun change => change.seat == deck.seat && change.deck == deck.deck) then
      throw "a deck cannot be both shuffled and left unshuffled in one rewind"
    return cards.filter required.contains)
  unless required.all (fun card => shuffled.contains card || waived.contains card) do
    throw "a rewind must shuffle deck cards seen without drawing or channeling them"
  let remainingDeck := deckPhysicalCards state
  let remembered := target.knownDeckCards ++ learned.filter (fun card => waived.contains card.2)
  let knownDeckCards := remembered.filter (fun card =>
    remainingDeck.contains card.2 && !shuffled.contains card.2)
  return { target with state, knownCards := trackedInPrivateZones state known, knownDeckCards }

/-- Knowledge from an abandoned line remains when an earlier deck order is restored. -/
private def rewindChronology (history : List ReplayPosition) (target index : Nat) :
    List ReplayPosition :=
  (history.take (index - (target + 1))).reverse

private def rewindPath (history : List ReplayPosition) (target index : Nat) :
    Except String (List (Nat × ReplayPosition) × ReplayPosition) := do
  let some prior := history.head? | throw "the initial checkpoint is missing"
  unless prior.state.config.ruleSet.isTournament && prior.state.result.isNone &&
      prior.state.phase != .setup do
    throw "rewinding requires ongoing tournament play"
  unless target + 1 < index do throw "a rewind must target an earlier checkpoint within play"
  let mut next := index - 1
  let mut undone := []
  for (position, offset) in history.zipIdx do
    let checkpoint := index - (offset + 1)
    if checkpoint == next then
      if checkpoint == target then return (undone.reverse, position)
      if checkpoint < target then throw "the target checkpoint was abandoned by an earlier rewind"
      undone := (checkpoint, position) :: undone
      next := position.rewindParent.getD (checkpoint - 1)
  throw "rewind checkpoint not found"

private def simpleRewind (history : List ReplayPosition) (target index : Nat) :
    Except String (List ReplayPosition × ReplayPosition) := do
  let (undone, position) ← rewindPath history target index
  unless undone.all (fun (_, step) => decide (step.boundary = .play)) do
    throw "a rewind must target an earlier checkpoint within play without crossing a ruling or clock call"
  return (undone.map Prod.snd, position)

private def retainedClock (before target : GameState) (crossedCall : Bool) (deadline : Option Nat) :
    Except String (Option RoundClock) := do
  match deadline with
  | none =>
    if crossedCall || before.clock != target.clock then
      throw "a rewind across a time call must record the final scheduled turn"
    return target.clock
  | some lastTurn =>
    let some clock := before.clock | throw "a rewind cannot add a time call"
    unless lastTurn > 0 && (lastTurn >= target.turn ||
        (clock.allowsSuddenDeath && clock.lastTurn < before.turn)) do
      throw "the final scheduled turn precedes the restored turn outside sudden death"
    return some (match clock with
      | .swiss _ => .swiss lastTurn
      | .elimination _ tied => .elimination lastTurn tied)

private def timelineRewind (history : List ReplayPosition) (before : GameState)
    (rewind : JudgeTimelineRewind) (index : Nat) : Except String ReplayPosition := do
  let (undone, position) ← rewindPath history rewind.target index
  if undone.any (fun (_, step) => decide (step.boundary = .setup)) then
    throw "a rewind cannot reverse setup or a terminal ruling"
  let rulings := undone.filterMap (fun (checkpoint, step) =>
    if step.boundary = .ruling then some checkpoint else none)
  unless rulings == rewind.rulings?.getD [] do
    throw "the rewind must name each reversed ruling, latest first"
  let crossedCall := undone.any (fun (_, step) => decide (step.boundary = .clock))
  let clock ← retainedClock before position.state crossedCall rewind.deadline?
  let restored ← applyRewindRemedies position (undone.map Prod.snd)
    (rewindChronology history rewind.target index) (rewind.returns?.getD []) (rewind.shuffles?.getD [])
    (rewind.unshuffledDecks?.getD [])
  return { restored with state := { restored.state with clock } }

/-- Advance a live game, verifier or trace from its checkpoint history, newest first. -/
def GameInputs.advance (input : GameInputs) (history : List ReplayPosition)
    (answer : ReplayAnswer) (index fuel : Nat) (observeFaces : Bool := false) :
    Except String (Option Action × ReplayPosition × List Event) := do
  let some prior := history.head? | throw "the initial checkpoint is missing"
  let correction : Option (Nat × Except String ReplayPosition) := match answer with
    | .judgeRewind target => some (target, do
      let (undone, pos) ← simpleRewind history target index
      applyRewindRemedies pos undone (rewindChronology history target index) [] [] [])
    | .judgePrivateRewind rewind => some (rewind.target, do
      let (undone, pos) ← simpleRewind history rewind.target index
      let shuffles := rewind.shuffles?.getD []
      let unshuffled := rewind.unshuffledDecks?.getD []
      if rewind.returns.isEmpty && shuffles.isEmpty && unshuffled.isEmpty then
        throw "a private rewind needs a draw return or a recorded shuffle decision"
      applyRewindRemedies pos undone (rewindChronology history rewind.target index)
        rewind.returns shuffles unshuffled)
    | .judgeTimelineRewind rewind =>
      some (rewind.target, timelineRewind history prior.state rewind index)
    | _ => none
  if let some (target, result) := correction then
    let pos ← result.mapError (fun error => s!"answer {index}: {error}")
    let restored := { pos with
      boundary := .ruling
      rewindParent := some target
      events := []
      disclosures := []
      deckObservations := []
      draws := [] }
    return (none, restored, [])
  let (action, (state, events), disclosures) ← input.applyAnswerWith prior.state answer index fuel observeFaces
  let boundary := if prior.state.phase == .setup then .setup else
    match answer, action with
    | .judgeShuffle _, _ => .ruling
    | _, some a =>
      if a.kind == .timeCalled && a.actor == .clock then .clock
      else if a.actor == .judge || a.actor == .clock then .setup else .play
    | _, none => .setup
  let fields := (action.bind (pickedBattlefield prior.state)).toList ++ prior.fields
  let obscured := obscuredDeckCards prior.state answer action
  let (known, draws) := observeDraws (prior.knownCards.filter (fun id => !obscured.contains id)) [] events
  let deckObservations := observeDeckCards prior.state state events
  let obscuredDeck := obscuredDeckPhysicalCards prior.state answer action
  let previous := prior.knownDeckCards.filter (fun known => !obscuredDeck.contains known.2)
  let observed := deckObservations.foldl DeckObservation.remember previous
  let knownDeckCards := if observed.isEmpty then [] else
    let remainingDeck := deckPhysicalCards state
    observed.filter (fun known => remainingDeck.contains known.2)
  let position := { state, fields, boundary, events, disclosures, draws, deckObservations,
                    knownCards := trackedInPrivateZones state known, knownDeckCards }
  return (action, position, events)

private def checkCheckpoint (expected : Option (Array ReplayCheckpoint))
    (index : Nat) (actual : ReplayCheckpoint) : Except String Unit := do
  if let some witnesses := expected then
    let some witness := witnesses[index]? | throw s!"checkpoint {index}: missing evidence"
    if witness.state != actual.state then throw s!"checkpoint {index}: state fingerprint differs"
    if witness.events != actual.events then throw s!"checkpoint {index}: events differ"

private def runGame (input : GameInputs) (db : CardDB) (config : GameConfig)
    (fuel : Nat) (expected : Option (Array ReplayCheckpoint)) : Except String RecordedGame := do
  if expected.any (fun witnesses => witnesses.size != input.answers.size + 1) then
    throw "the checkpoint count does not match the input stream"
  let s ← input.initial db config
  let initial := ReplayCheckpoint.capture s []
  checkCheckpoint expected 0 initial
  let mut checkpoints := #[initial]
  let mut history := [ReplayPosition.fromState s]
  let mut exact := input.openingOrderEvidence?.isNone
  for (answer, index) in input.answers.toList.zipIdx do
    if let .inferred .. := answer then exact := false
    let (_, next, events) ← input.advance history answer (index + 1) fuel
    let witness := ReplayCheckpoint.capture next.state events
    checkCheckpoint expected (index + 1) witness
    checkpoints := checkpoints.push witness
    history := next :: history
  let some final := history.head? | throw "the final checkpoint is missing"
  return {
    input, eliminationConfig? := replayEliminationConfig config, checkpoints,
    summary := ReplayGameResult.fromState final.state input.decks final.fields.reverse exact }

/-- Play recorded answers with the engine, retaining the exact input, checkpoints and outcome. -/
def GameInputs.record (input : GameInputs) (db : CardDB) (config : GameConfig)
    (fuel : Nat := 100) : Except String RecordedGame :=
  runGame input db config fuel none

/-- Replay one game against its saved evidence, recomputing coverage when the card table changes. -/
def RecordedGame.checkEvidence (saved : RecordedGame) (db : CardDB) (config : GameConfig)
    (fuel : Nat) (refreshCoverage : Bool := false) : Except String RecordedGame := do
  if saved.eliminationConfig? != replayEliminationConfig config then
    throw "the saved single-elimination clock procedure differs"
  let actual ← runGame saved.input db config fuel (some saved.checkpoints)
  let summary := if refreshCoverage then
    { saved.summary with uncheckedCards := actual.summary.uncheckedCards }
    else saved.summary
  if summary != actual.summary then throw "the final game outcome differs"
  return actual

/-- Replay one game and report the first recorded checkpoint that disagrees. -/
def RecordedGame.verify (saved : RecordedGame) (db : CardDB) (config : GameConfig)
    (fuel : Nat := 100) : Except String ReplayGameResult :=
  (saved.checkEvidence db config fuel).map (·.summary)

/-- The recorded inputs to one free-for-all game under the Core Rules. -/
structure FreeForAllInputs where
  /-- Skirmish or War (CR 489-490). -/
  mode : Mode
  /-- The registered decks, decisions and any supplied opening order. -/
  game : GameInputs
  /-- The per-answer work limit, retained for verification. -/
  fuel : Nat := 100
deriving DecidableEq, Repr, ToJson, FromJson

/-- The archive for one completed free-for-all game. -/
structure RecordedFreeForAll where
  /-- The pinned replay format, rules editions and card definitions. -/
  rules : ReplayRules
  /-- The starting mode to replay. -/
  mode : Mode
  /-- The engine's work limit for each answer. -/
  fuel : Nat
  /-- The game input, outcome and all checkpoints. -/
  game : RecordedGame
deriving DecidableEq, Repr, ToJson, FromJson

private def freeForAllConfig (mode : Mode) : Except String GameConfig := do
  unless mode.isFreeForAll do throw "free-for-all replay requires Skirmish or War"
  return { ruleSet := .coreOnly, mode }

private def requireFinishedFreeForAll (summary : ReplayGameResult) : Except String Unit := do
  unless summary.result.isSome do throw "the free-for-all game has no final result"

/-- Play a complete Skirmish or War game and retain its inputs, outcome and checkpoints. -/
def FreeForAllInputs.record (input : FreeForAllInputs) (db : CardDB := RiftboundCards.db) :
    Except String RecordedFreeForAll := do
  let game ← input.game.record db (← freeForAllConfig input.mode) input.fuel
  requireFinishedFreeForAll game.summary
  return { rules := ReplayRules.current db, mode := input.mode, fuel := input.fuel, game }

private def RecordedFreeForAll.checkArchive (saved : RecordedFreeForAll) (db : CardDB)
    (allowCardUpdate : Bool) : Except String RecordedFreeForAll := do
  let rules := ReplayRules.current db
  if allowCardUpdate then saved.rules.checkEditions rules
  else if saved.rules != rules then throw "the replay format, rules edition or card definitions differ"
  let game ← (do
    let game ← saved.game.checkEvidence db (← freeForAllConfig saved.mode) saved.fuel
      (refreshCoverage := saved.rules.cards != rules.cards)
    requireFinishedFreeForAll game.summary
    pure game).mapError (fun error => s!"game 1: {error}")
  return { saved with rules, game }

/-- Check the outcome and each checkpoint of an archived Skirmish or War game. -/
def RecordedFreeForAll.verify (saved : RecordedFreeForAll) (db : CardDB := RiftboundCards.db) :
    Except String ReplayGameResult :=
  (saved.checkArchive db false).map (·.game.summary)

/-- Revalidate every checkpoint of an archived Skirmish or War game against the current cards. -/
def RecordedFreeForAll.revalidate (saved : RecordedFreeForAll)
    (db : CardDB := RiftboundCards.db) : Except String RecordedFreeForAll :=
  saved.checkArchive db true

end RiftboundDriver

end
