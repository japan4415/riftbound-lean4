module

public import RiftboundDriver.Trace
public import RiftboundDriver.TeamMatch

/-!
# Driver: live play

A game that a person plays through the viewer. The engine decides what can be answered
(`legalActions`) and what an answer does (`step`); this file only keeps the game between requests,
answers the questions of the seats that nobody controls (the chance decisions and the automatic
player, as `demoAnswer` does), and writes what happened as JSON. The viewer draws it and has no
rules. Like the trace, this library is not covered by the proofs (design.md §4).

The rules of the game can be chosen (Core Rules, Constructed, Sealed, Draft); under the Tournament
Rules the clock and the judge can be called, and a match (a Best of 1 or 3) can be played: the
result of each game goes to `MatchState`, which says whether the match is over and who chooses who
goes first in the next game (TR 407); a person who chooses answers on screen.
-/

@[expose] public section

namespace RiftboundDriver

open Lean Riftbound

/-- The kind of game: the rules and the decks (the decks are those of the demo). -/
inductive LiveKind where
  /-- The demo decks under the Core Rules. -/
  | core
  /-- The demo decks, Constructed, under the Tournament Rules. -/
  | constructed
  /-- Sealed decks without a Legend or a Chosen Champion. -/
  | sealed
  /-- Draft decks without a Legend or a Chosen Champion. -/
  | draft
deriving DecidableEq, Repr

/-- The kind named by a word of the protocol. -/
def LiveKind.ofString : String → Option LiveKind
  | "core" => some .core
  | "constructed" => some .constructed
  | "sealed" => some .sealed
  | "draft" => some .draft
  | _ => none

/-- Registrations, rules and first-game initiative for a recorded live match. -/
structure LiveSetup where
  /-- Rules and the pinned legality environment. -/
  config : GameConfig
  /-- Tournament details, for official Constructed events. -/
  tournament : Option ReplayTournament := none
  /-- Whether to apply the timed single-elimination procedure (TR 408.4). -/
  singleElimination? : Option Bool := none
  /-- Whether to use the optional initial sideboard window for Constructed Best of 1 (TR 406.1.h). -/
  bo1Sideboarding? : Option Bool := none
  /-- The starting registrations in seat order. -/
  decks : ReplayDecks
  /-- The number of game wins that finishes the match. -/
  winsRequired : Nat
  /-- The per-answer engine work limit. -/
  fuel : Nat := 100
  /-- The seat selected by chance to decide who goes first in the first game. -/
  firstChooser : PlayerId
  /-- The seat chosen to go first. -/
  first : PlayerId
deriving ToJson, FromJson

/-- Tournament 2v2 registrations and the observed initiative decision for the first game. -/
structure LiveTeamSetup where
  /-- Applied eligibility for a Constructed tournament. -/
  tournament? : Option ReplayTournament := none
  /-- The shared pools at a Sealed tournament. -/
  sealed? : Option TeamSealedPools := none
  /-- Sets used by the tournament. -/
  legalSets : List SetCode
  /-- Starting deck registrations in A/B seat order, for team 0 then team 1. -/
  decks : ReplayDecks
  /-- Wins required for the match. -/
  winsRequired : Nat
  /-- Whether to use the timed elimination procedure. -/
  singleElimination? : Option Bool := none
  /-- The team selected by chance to choose the opening order. -/
  firstChooser : PlayerId
  /-- The four seats in their chosen turn order. -/
  order : List PlayerId
deriving ToJson, FromJson

/-- The common match metadata used to validate starting games and export the match. -/
def LiveTeamSetup.matchRecord (setup : LiveTeamSetup) (games : Array TeamGameRecord)
    (ending : ReplayMatchEnd) (timeAfterGames : Option Nat) : TeamMatchRecord :=
  { seats := TeamSeats.standard, tournament? := setup.tournament?, sealed? := setup.sealed?,
    legalSets := setup.legalSets, winsRequired := setup.winsRequired, games, ending,
    elimination? := if setup.singleElimination?.getD false then some { timeAfterGames? := timeAfterGames }
      else none }

/-- A game in progress: the state, the objects the viewer has seen, the number of steps written,
the generator for the chance decisions, the seats a person controls, and the match it belongs to. -/
structure LiveGame where
  /-- The state of the game. -/
  s : GameState
  /-- The objects the viewer already knows (so that a step tells only what is new). -/
  seen : Std.HashSet Nat
  /-- The number of the next step. -/
  i : Nat
  /-- The generator for the chance decisions and the automatic player. -/
  rng : Rng
  /-- The players a person controls. -/
  humans : List PlayerId
  /-- The kind of game, for the next game of a match. -/
  kind : LiveKind := .core
  /-- The seed of this game. -/
  seed : Nat := 0
  /-- The turn order to answer the question about it with; `none`: by chance. -/
  order : Option (List PlayerId) := none
  /-- The match this game belongs to, if it is played as one. -/
  match_ : Option MatchState := none
  /-- The result of this game has been given to the match. -/
  recorded : Bool := false
  /-- The decks of the players: those of the Core Rules and Constructed games. -/
  decks : List Deck := [demoDeck, demoDeck]
  /-- The sideboards of the players (Constructed, TR 601.1.c). -/
  sides : List (List CardId) := [demoSideboard, demoSideboard]
  /-- The real match registration, if started with one. -/
  setup : Option LiveSetup := none
  /-- The real team registration, if this is a 2v2 match. -/
  teamSetup : Option LiveTeamSetup := none
  /-- This game's starting registration and initiative, separate from edits for the next game. -/
  input : Option GameInputs := none
  /-- Answers already given, newest first so undo snapshots share the earlier entries. -/
  answersRev : List ReplayAnswer := []
  /-- Evidence for setup and each answer, newest first. -/
  checkpointsRev : List ReplayCheckpoint := []
  /-- The states behind the checkpoints of a recorded game, newest first. -/
  history : List ReplayPosition := []
  /-- Completed games in chronological order, up to the start of this game. -/
  completed : Array RecordedGame := #[]
  /-- Battlefield cards selected for this game, keyed by the seat that brought them. -/
  fields : List (PlayerId × CardId) := []
  /-- When replaying a draw, require the same Battlefield selections. -/
  reuseFields : List (PlayerId × CardId) := []
  /-- A between-game time call that sent a tied match to a tiebreaker. -/
  timeAfterGames : Option Nat := none
  /-- A Game Loss issued between games is applied when the next game starts (TR 701.2.b.1). -/
  queuedGameLoss : Option (List PlayerId) := none
  /-- The reason the match ended. -/
  ending : Option ReplayMatchEnd := none

/-- The player whose answer the game waits for, if it is a player's. -/
def LiveGame.waiting (g : LiveGame) : Option PlayerId :=
  match (legalFrameActions g.s).head? with
  | some ⟨.player p, _⟩ => some p
  | _ => none

/-- The answers a person can give now: those of the players they control, a concession included.
-/
def LiveGame.legal (g : LiveGame) : List Action :=
  if g.ending.isSome then [] else
  (legalActions g.s).filter (fun a =>
    match a.actor with
    | .player p => g.humans.contains p
    | _ => false)

/-- The controlled seat deciding initiative after the Battlefield draws. -/
def LiveGame.bo1Chooser (g : LiveGame) : Option PlayerId := do
  let input ← g.input
  if g.ending.isNone && input.awaitsBo1Initiative g.s then
    input.chooser.filter g.humans.contains
  else none

/-- Whether setup is at the optional Best of 1 sideboard window. -/
def LiveGame.bo1SideboardOpen (g : LiveGame) : Bool :=
  g.ending.isNone && g.input.any (·.awaitsBo1Sideboard g.s)

/-- The game waits for a person. -/
def LiveGame.needsHuman (g : LiveGame) : Bool :=
  g.s.result.isNone && (g.bo1Chooser.isSome ||
    (g.bo1SideboardOpen && !g.humans.isEmpty) || g.waiting.any g.humans.contains)

/-- Whether this recorded match uses the single-elimination clock. -/
def LiveGame.singleElimination (g : LiveGame) : Bool :=
  g.setup.any (fun setup => setup.singleElimination?.getD false) ||
    g.teamSetup.any (fun setup => setup.singleElimination?.getD false)

/-- Convert a seat to a team number when applying the two sides' match rules. -/
def LiveGame.matchSide (g : LiveGame) (seat : PlayerId) : PlayerId :=
  if g.teamSetup.isSome then (TeamSeats.standard.teamOf seat).getD seat else seat

/-- Resolve a match ending from the match's point of view while storing the original seat. -/
def LiveGame.matchEnding (g : LiveGame) (ending : ReplayMatchEnd) : ReplayMatchEnd :=
  ending.mapSeat g.matchSide

/-- The last answer was an administrative Game Loss. -/
def LiveGame.endedByGameLoss (g : LiveGame) : Bool :=
  (g.answersRev.head?.bind ReplayAnswer.penalizedSeats).isSome

/-- Apply the same transition that an exported match uses to reproduce an answer. -/
def LiveGame.applyReplay (g : LiveGame) (answer : ReplayAnswer) :
    Except String (LiveGame × String) := do
  if g.ending.isSome then throw "the match is over"
  let (action, position, es) ← match g.input with
    | some input => input.advance g.history answer g.i (g.setup.map (·.fuel) |>.getD 100)
    | none => do
      let a ← answer.resolve g.i
      let (next, events) ← (step 100 g.s a).mapError (fun e => s!"the engine refused the answer: {repr e}")
      let fields := (pickedBattlefield g.s a).toList ++ g.fields
      pure (some a, { state := next, fields }, events)
  let initiative := g.input.any (fun input => input.isBo1Initiative g.s action)
  let priorSeen := if answer.rewinds then {} else g.seen
  let (j, seen') := stepJson g.i action es position.state priorSeen g.s.pending.head? (answer == .bo1Sideboard)
    initiative answer.penalizedSeats answer.correctionJson
  return ({ g with
    s := position.state, seen := seen', i := g.i + 1,
    answersRev := if g.input.isSome then answer :: g.answersRev else g.answersRev,
    checkpointsRev := if g.input.isSome then ReplayCheckpoint.capture position.state es :: g.checkpointsRev
      else g.checkpointsRev,
    history := if g.input.isSome then position :: g.history else g.history,
    fields := position.fields }, j)

/-- Give an answer: the step as JSON, and the game after it. -/
def LiveGame.apply (g : LiveGame) (a : Action) : Except String (LiveGame × String) :=
  g.applyReplay (.observed a)

/-- When the game is over, its result goes to the match, once (TR 404). -/
def LiveGame.settle (g : LiveGame) : Except String LiveGame := do
  match g.match_, g.s.result with
  | some m, some r =>
    if g.recorded then return g
    else
      let first := g.s.turnOrder.head?.map g.matchSide
      let r ← if g.teamSetup.isSome then TeamSeats.standard.normalizeResult r else pure r
      let next := { m.record r (first.getD ⟨0⟩) with lastFirst := first }
      return { g with
        match_ := some next, recorded := true,
        ending := if next.finished ||
          (g.s.clock.isSome && !needsTimedTiebreaker next g.singleElimination)
          then some .finalGame else none }
  | _, _ => return g

/-- A forced answer during setup, when match decisions already determine the choice. -/
def LiveGame.setupAnswer (g : LiveGame) : Except String (Option (Action × Rng)) := do
  match g.s.pending with
  | .chanceTurnOrder :: _ => return g.order.map (fun order => (⟨.chance, .arrangePlayers order⟩, g.rng))
  | .chanceBattlefield seat :: _ =>
    let candidates := g.s.zone (.player seat .outOfGame)
    if let some card := g.reuseFields.lookup seat then
      let some index := candidates.findIdx? (fun id => (g.s.cardDef? id).any (·.id == card))
        | throw s!"seat {seat.n} cannot reuse Battlefield {card.code}"
      return some (⟨.chance, .pick index⟩, g.rng)
    let forbidden := g.completed.toList.flatMap RecordedGame.penaltyBattlefields
    if !(forbidden.any (·.1 == seat)) then return none
    let allowed := candidates.zipIdx.filter (fun (id, _) =>
      (g.s.cardDef? id).any (fun c => !forbidden.contains (seat, c.id)))
    let (pick, rng) := g.rng.below allowed.length
    let some (_, index) := allowed[pick]? | throw s!"seat {seat.n} has no Battlefield after Game Loss"
    return some (⟨.chance, .pick index⟩, rng)
  | _ => return none

/-- Answer for the seats nobody controls until the game is over or a person is to answer. The steps
that were made, in order. -/
def LiveGame.autoRun : Nat → LiveGame → List String → Except String (LiveGame × List String)
  | 0, g, acc => do
    if g.s.result.isSome || g.needsHuman then return (← g.settle, acc.reverse)
    else throw "the automatic player reached its action limit"
  | n + 1, g, acc => do
    if g.s.result.isSome || g.needsHuman then return (← g.settle, acc.reverse)
    if g.bo1SideboardOpen then
      let (next, json) ← g.applyReplay .bo1Sideboard
      return ← LiveGame.autoRun n next (json :: acc)
    let planned ← g.setupAnswer
    let answer := planned.orElse (fun _ => demoAnswer g.rng g.s)
    let some (action, rng) := answer | throw "no answer for the automatic player"
    let (next, json) ← { g with rng }.apply action
    LiveGame.autoRun n next (json :: acc)

/-- The answers a person can give, as JSON: the number to send back, and the answer. -/
def LiveGame.legalJson (g : LiveGame) : String :=
  jarr ((g.legal.zipIdx).map (fun (a, k) =>
    jobj [("k", toString k), ("a", actionJson a g.s.pending.head? (some g.s))]))

/-- The match as JSON: the wins, the games, the winner, how the next game's order is decided, and
whether the sideboard may be used (TR 403.5, 403.10, 404, 407). -/
def LiveGame.matchJson (g : LiveGame) : String :=
  match g.match_ with
  | none => "null"
  | some m =>
    let result := g.ending.bind (fun ending =>
      (concludeReplayMatch m (g.s.result.isSome && g.s.clock.isSome)
        (g.matchEnding ending) g.singleElimination).toOption)
    jobj [("target", toString m.target), ("wins", jarr [toString m.wins0, toString m.wins1]),
      ("games", toString m.games), ("finished", toString g.ending.isSome),
      ("singleElimination", toString g.singleElimination),
      ("timedTiebreaker", toString (g.ending.isNone && g.s.result.isSome &&
        (g.s.clock.isSome || g.timeAfterGames.isSome) && needsTimedTiebreaker m g.singleElimination)),
      ("winner", match result with | some (.won p) => toString p.n | _ => "null"),
      ("sideboard", toString (m.sideboardAllowed || g.bo1SideboardOpen)),
      ("sameBattlefields", toString (reuseReplayBattlefields m g.endedByGameLoss)),
      ("matchPenalty", if g.ending.any (·.penalizedSeat.isSome) then (toJson g.ending).compress else "null"),
      ("order", jstr (match m.nextOrder with
        | .chance => "chance" | .loserChooses p => s!"loser{p.n}" | .same f => s!"same{f.n}"))]

/-- Whether the clock may call time and the judge declare a draw now (TR 408.2, 410.1, 505.6). -/
def LiveGame.externalJson (g : LiveGame) : String :=
  let ok (a : Action) : String := toString (g.ending.isNone && decide (Legal g.s a))
  let seatsJson (seats : List PlayerId) := jarr (seats.map (fun p => toString p.n))
  let penaltySeats := if g.input.isSome && g.ending.isNone && g.s.config.ruleSet.isTournament then
    g.s.players else []
  jobj [("clock", ok ⟨.clock, .timeCalled⟩), ("judge", ok ⟨.judge, .declareDraw⟩),
    ("penaltySeats", seatsJson penaltySeats), ("queuedGameLoss", seatsJson (g.queuedGameLoss.getD [])),
    ("correction", toString (!penaltySeats.isEmpty && g.s.result.isNone && g.s.phase != .setup)),
    ("betweenGames", toString (g.ending.isNone && g.match_.isSome &&
      g.s.result.isSome && g.s.config.ruleSet.isTournament && g.s.clock.isNone &&
      g.timeAfterGames.isNone))]

/-- The cards of a list with how many of each, in the order they first appear. -/
def countIds (l : List CardId) : List (CardId × Nat) :=
  l.foldl (fun acc c =>
    if acc.any (fun x => x.1 == c) then acc.map (fun x => if x.1 == c then (x.1, x.2 + 1) else x)
    else acc ++ [(c, 1)]) []

/-- The player whose deck a person changes between games: the first player they control. -/
def LiveGame.sideSeat (g : LiveGame) : Option PlayerId := g.humans.head?

/-- A seat's Main Deck and sideboard, with card names and counts for the live controls. -/
def LiveGame.sideEntry (g : LiveGame) (p : PlayerId) (allowed : Bool) : String :=
  match g.decks[p.n]?, g.sides[p.n]? with
  | some d, some side =>
    let group (l : List CardId) : String :=
      jarr ((countIds l).map (fun (c, n) =>
        jobj [("id", jstr c.code), ("name", jstr ((g.s.cards.find? c).map (·.name) |>.getD c.code)),
          ("n", toString n)]))
    jobj [("player", toString p.n), ("allowed", toString allowed),
      ("main", group d.main), ("side", group side),
      ("mainCount", toString d.main.length), ("sideCount", toString side.length)]
  | _, _ => "null"

/-- The sideboard of the match as JSON, for a Constructed match: the Main Deck and the sideboard of
the player, and whether the players may use the sideboard now (TR 403.5, 403.10). `null`
otherwise. -/
def LiveGame.sideJson (g : LiveGame) : String :=
  match g.match_, g.sideSeat, g.kind with
  | some m, some p, .constructed =>
    g.sideEntry p (m.sideboardAllowed && g.s.result.isSome && g.ending.isNone)
  | _, _, _ => "null"

/-- The available controls during the optional Best of 1 setup. -/
def LiveGame.bo1Json (g : LiveGame) : String :=
  let chooser := g.bo1Chooser
  if chooser.isNone && !g.bo1SideboardOpen then "null"
  else
    let sideboards := if g.bo1SideboardOpen then g.humans.eraseDups.map (g.sideEntry · true) else []
    jobj [("chooser", chooser.elim "null" (fun p => toString p.n)), ("sideboards", jarr sideboards)]

/-- What a request returns: the steps made, the answers a person can give, whether the game is
over, the match, and what the clock and the judge can do. -/
def LiveGame.reply (g : LiveGame) (steps : List String) (extra : List (String × String) := []) :
    String :=
  jobj (extra ++ [("steps", jarr steps), ("legal", g.legalJson),
    ("over", toString (g.s.result.isSome || g.ending.isSome)),
    ("archiveAvailable", toString ((g.setup.isSome || g.teamSetup.isSome) && g.ending.isSome)),
    ("match", g.matchJson), ("external", g.externalJson), ("sideboard", g.sideJson), ("bo1", g.bo1Json),
    ("teamFormat", if g.teamSetup.isNone then "null"
      else jstr (if g.s.config.ruleSet.isLimited then "sealed" else "constructed"))])

/-- What the reply to an undo says: the answers a person can give again, and how many steps the
viewer keeps (the steps made until then). -/
def LiveGame.undoReply (g : LiveGame) : String :=
  g.reply [] [("truncate", toString g.i)]

/-- The game before any answer, for the kind of game, from the decks of the players. -/
def LiveKind.initial (decks : List Deck) (sides : List (List CardId) := []) :
    LiveKind → Option GameState
  | .core => GameState.initial demoDB demoConfig decks
  | .constructed =>
    let registrations := decks.zipIdx.map (fun (deck, seat) =>
      ({ deck, sideboard := sides[seat]?.getD [] } : ConstructedDeck))
    GameState.initialConstructed demoDB demoEnv
      { ruleSet := .tournament .constructed, mode := Mode.duel } registrations
  | .sealed =>
    GameState.initialLimited demoDB { legalSets := [], banned := [] }
      { ruleSet := .tournament .sealed, mode := Mode.duel } [demoLimitedDeck, demoLimitedDeck]
  | .draft =>
    GameState.initialLimited demoDB { legalSets := [], banned := [] }
      { ruleSet := .tournament .draft, mode := Mode.duel } [demoLimitedDeck, demoLimitedDeck]

/-- A new game: the first step, and the game after the answers of the seats nobody controls. -/
def LiveGame.begin (g : LiveGame) : Except String (LiveGame × List String) := do
  let (j0, seen) := stepJson 0 none [] g.s {}
  let checkpointsRev := if g.input.isSome then [ReplayCheckpoint.capture g.s []] else []
  let history : List ReplayPosition := if g.input.isSome then [{ state := g.s }] else []
  let game := { g with i := 1, seen, checkpointsRev, history, queuedGameLoss := none }
  let (next, steps) ← match g.queuedGameLoss with
    | some seats => do
      let (next, row) ← game.applyReplay (.gameLoss seats)
      pure (← next.settle, [row])
    | none => game.autoRun 100000 []
  return (next, j0 :: steps)

/-- Start a live game with the demo registrations. -/
def liveNew (kind : LiveKind) (seed : Nat) (humans : List PlayerId) (order : Option (List PlayerId))
    (m : Option MatchState) (decks : List Deck := [demoDeck, demoDeck])
    (sides : List (List CardId) := [demoSideboard, demoSideboard])
    (reuseFields : List (PlayerId × CardId) := []) : Except String (LiveGame × List String) := do
  let some s := kind.initial decks sides | throw "the demo game cannot be set up"
  LiveGame.begin {
    s, seen := {}, i := 0, rng := Rng.ofSeed seed, humans, kind, seed, order,
    match_ := m, decks, sides, reuseFields }

/-- The current Constructed registrations, including any edits for the next game. -/
def LiveGame.registrations (g : LiveGame) : List ConstructedDeck :=
  g.decks.zipWith (fun deck sideboard => { deck, sideboard }) g.sides

/-- Capture the input, evidence and outcome of the current game in its present state. -/
def LiveGame.gameRecord (g : LiveGame) (input : GameInputs) : RecordedGame :=
  { input := { input with answers := g.answersRev.reverse.toArray }
    eliminationConfig? := replayEliminationConfig g.s.config
    checkpoints := g.checkpointsRev.reverse.toArray
    summary := ReplayGameResult.fromState g.s input.decks g.fields.reverse true }

/-- Recover the team's game outcome and its ending from the observed engine transitions. -/
def RecordedGame.teamObservation (game : RecordedGame) : Except String TeamGameRecord := do
  let summary := game.summary
  let [a, _, b, _] := summary.points | throw "a team result needs four seat scores"
  let closingAction : Option Action ← if summary.result.isNone || game.gameLossSeats.isSome then pure none
    else game.input.answers.back?.mapM (fun answer => answer.resolve game.input.answers.size)
  let ending ← if let some seats := game.gameLossSeats then pure (TeamGameEnd.gameLoss seats)
  else match summary.result, closingAction with
    | none, _ => pure TeamGameEnd.matchEnded
    | some _, some (Action.mk (.player p) .concede) => pure (.concede p)
    | some .draw, some (Action.mk .judge .declareDraw) => pure .draw
    | some result, _ => do
      if game.checkpoints.back?.any (fun w => w.events.any (fun | .won _ => true | _ => false)) then
        pure .scored
      else if summary.suddenDeathTurn?.isSome then
        let .won [team] ← TeamSeats.standard.normalizeResult result
          | throw "the sudden-death game has no winning team"
        pure (.suddenDeath team)
      else pure .time
  let (decks?, sealedDecks?) ← match game.input.decks with
    | .constructed decks => pure (some decks, none)
    | .limited decks => pure (none, some decks)
    | .core _ => throw "the game has no tournament team registrations"
  return {
    decks?, sealedDecks?, chooser := game.input.chooser, order := summary.turnOrder,
    openingOrderEvidence? := game.input.openingOrderEvidence?, battlefields := summary.battlefields,
    points := (a, b), ending, timed := summary.timed, answers := game.input.answers }

/-- Check that the declared Battlefields for Sealed Best of 3 still have available copies. -/
def LiveTeamSetup.checkBattlefieldHistory (setup : LiveTeamSetup) (decks : ReplayDecks)
    (order : List PlayerId) (completed : Array RecordedGame) (reuse : Bool) : Except String Unit := do
  let some pools := setup.sealed? | return ()
  let .limited registrations := decks | throw "the game needs Sealed registrations"
  unless setup.winsRequired == 2 do return ()
  let selected ← order.drop 1 |>.mapM fun seat => do
    let some card := registrations[seat.n]?.bind (·.battlefields.head?)
      | throw s!"seat {seat.n} needs a declared Battlefield"
    return (seat, card)
  let mut used := ([], [])
  let mut priorWasDraw := false
  for game in completed do
    used ← pools.useBattlefields TeamSeats.standard used game.summary.battlefields priorWasDraw
    priorWasDraw := game.summary.result == some .draw && game.gameLossSeats.isNone
  if reuse && !decide (selected.Perm ((completed.back?).map (·.summary.battlefields) |>.getD [])) then
    throw "a draw preserves the same Battlefields"
  let _ ← pools.useBattlefields TeamSeats.standard used selected reuse

/-- Set up a recorded team game from the same registered decks and choices as offline replay. -/
def liveNewTeam (setup : LiveTeamSetup) (seed : Nat) (humans : List PlayerId)
    (state : MatchState) (input : GameInputs) (completed : Array RecordedGame := #[])
    (timeAfterGames : Option Nat := none) (queuedGameLoss : Option (List PlayerId) := none) :
    Except String (LiveGame × List String) := do
  let db := RiftboundCards.db
  let record := setup.matchRecord #[] .agreedDraw timeAfterGames
  let base ← record.replayConfig
  let some env := base.formatLegality | throw "missing tournament eligibility"
  let some order := input.openingOrder | throw "the starting turn order is missing"
  let timed := completed.back?.any (·.summary.timed)
  let afterTime ← gameStartsAfterTime state timed record.elimination?
  record.checkRegistrations input.decks order db env
  let reuse := reuseReplayBattlefields state (completed.back?.any (·.gameLossSeats.isSome))
  if queuedGameLoss.isNone then setup.checkBattlefieldHistory input.decks order completed reuse
  let config := replayGameConfig base state record.elimination?.isSome afterTime
  let s ← input.initial db config
  let registrations := match input.decks with | .constructed ds => ds | _ => []
  let reuseFields := if reuse then
    (completed.back?.map (·.summary.battlefields)).getD [] else []
  LiveGame.begin {
    s, seen := {}, i := 0, rng := Rng.ofSeed seed, humans, seed,
    kind := if base.ruleSet.isLimited then .sealed else .constructed,
    match_ := some state, teamSetup := some setup, input := some input, completed, reuseFields,
    timeAfterGames, queuedGameLoss, decks := registrations.map (·.deck),
    sides := registrations.map (·.sideboard) }

/-- Set up a game with real cards and keep its starting registration available for export. -/
def liveNewConfigured (setup : LiveSetup) (decks : ReplayDecks) (seed : Nat)
    (humans : List PlayerId) (first : PlayerId) (chooser : Option PlayerId) (m : MatchState)
    (completed : Array RecordedGame := #[]) (reuseFields : List (PlayerId × CardId) := [])
    (timeAfterGames : Option Nat := none) (afterTime : Bool := false)
    (queuedGameLoss : Option (List PlayerId) := none) :
    Except String (LiveGame × List String) := do
  let config := replayGameConfig setup.config m (setup.singleElimination?.getD false) afterTime
  let kind := match setup.config.ruleSet.tournamentFormat with
    | none => LiveKind.core
    | some format => match format with
      | .constructed => .constructed | .sealed => .sealed | .draft => .draft
  let registrations := match decks with | .constructed ds => ds | _ => []
  let bo1Setup? := if m.games == 0 && setup.bo1Sideboarding?.getD false then some registrations else none
  let input : GameInputs := { decks, answers := #[], chooser, bo1Setup? }
  let s ← input.initial RiftboundCards.db config
  LiveGame.begin {
    s, seen := {}, i := 0, rng := Rng.ofSeed seed, humans, kind, seed,
    order := some (MatchState.turnOrderOf first), match_ := some m, setup := some setup,
    input := some input, completed, reuseFields, timeAfterGames, queuedGameLoss,
    decks := registrations.map (·.deck), sides := registrations.map (·.sideboard) }

/-- The fixed part of the reply to the start of a game. -/
def LiveGame.startInfo (g : LiveGame) : List (String × String) :=
  [("seed", toString g.seed), ("players", toString g.s.playerCount),
    ("cards", jobj (g.s.cards.cards.map (fun c => (c.id.code, cardJson c))))] ++
      if g.teamSetup.isSome then [("teams", "[[0,1],[2,3]]")] else []

/-- Start a game of the kind, with `seed` for the chance decisions. A person controls the players in
`humans`. With `matchTarget` (1 or 2 wins), the game is the first of a match. -/
def liveStart (seed : Nat) (humans : List PlayerId) (kind : LiveKind := .core)
    (matchTarget : Option Nat := none) : Except String (LiveGame × String) :=
  match liveNew kind seed humans none (matchTarget.map MatchState.start) with
  | .error e => .error e
  | .ok (g, js) => .ok (g, g.reply js g.startInfo)

/-- Start a match using the real card registry, preserving every answer for replay. -/
def liveStartConfigured (seed : Nat) (humans : List PlayerId) (setup : LiveSetup) :
    Except String (LiveGame × String) := do
  if setup.config.mode != Mode.duel || setup.firstChooser.n >= 2 || setup.first.n >= 2 ||
      !(humans.all (fun p => p.n < 2)) || (setup.winsRequired != 1 && setup.winsRequired != 2) then
    throw "invalid live match configuration"
  if let .tournamentElimination .. := setup.config.ruleSet then
    throw "choose single elimination on the match, rather than setting a per-game procedure"
  if setup.singleElimination?.getD false && !setup.config.ruleSet.isTournament then
    throw "single elimination uses Tournament Rules"
  if setup.bo1Sideboarding?.getD false &&
      (setup.winsRequired != 1 || setup.config.ruleSet.tournamentFormat != some .constructed) then
    throw "initial sideboarding requires a Constructed Best of 1 match"
  checkReplayEvent setup.config setup.tournament
  let (g, steps) ← liveNewConfigured setup setup.decks seed humans setup.first
    (some setup.firstChooser) (MatchState.start setup.winsRequired)
  return (g, g.reply steps g.startInfo)

/-- Start a real Constructed or Sealed 2v2 tournament match with its observed opening order. -/
def liveStartTeam (seed : Nat) (humans : List PlayerId) (setup : LiveTeamSetup) :
    Except String (LiveGame × String) := do
  unless humans.all (fun p => p.n < 4) && setup.firstChooser.n < 2 &&
      (setup.winsRequired == 1 || setup.winsRequired == 2) do
    throw "invalid live team match configuration"
  if let some pools := setup.sealed? then pools.check RiftboundCards.db
  let input : GameInputs :=
    { decks := setup.decks, answers := #[], chooser := some setup.firstChooser, openingOrder := some setup.order }
  let (g, steps) ← liveNewTeam setup seed humans (MatchState.start setup.winsRequired) input
  return (g, g.reply steps g.startInfo)

/-- Export the entire recorded live match for independent replay. -/
def LiveGame.archive (g : LiveGame) : Except String RecordedMatch := do
  let some setup := g.setup | throw "no real decks were registered for this match"
  let some ending := g.ending | throw "the match is not over"
  let some input := g.input | throw "the game's inputs are missing"
  let games := g.completed.push (g.gameRecord input)
  MatchInputs.recordPlayed {
    config := setup.config, tournament := setup.tournament,
    elimination? := if g.singleElimination then some { timeAfterGames? := g.timeAfterGames } else none,
    winsRequired := setup.winsRequired, fuel := setup.fuel, games := games.map (·.input), ending }
    games g.s.cards

/-- Package the four-seat match in the same format consumed by `verify-team`. -/
def LiveGame.teamArchive (g : LiveGame) : Except String RecordedTeamMatch := do
  let some setup := g.teamSetup | throw "no team match was started"
  let some ending := g.ending | throw "the match is not over"
  let some input := g.input | throw "the game's inputs are missing"
  let games := g.completed.push (g.gameRecord input)
  let observations ← games.mapM RecordedGame.teamObservation
  (setup.matchRecord observations ending g.timeAfterGames).recordPlayed games

/-- End a live match by an external match decision. -/
def liveEnd (g : LiveGame) (ending : ReplayMatchEnd) : Except String (LiveGame × String) := do
  let some m := g.match_ | throw "this is not a match"
  if g.ending.isSome then throw "the match is over"
  match ending with
  | .finalGame => throw "the engine records game results"
  | .timeBetweenGames =>
    if g.s.result.isNone || !g.s.config.ruleSet.isTournament || g.s.clock.isSome ||
        g.timeAfterGames.isSome then
      throw "time between games requires a completed tournament game"
  | .concede seat =>
    if !g.humans.contains seat then throw "the concession must come from a controlled seat"
  | .matchLoss seat | .disqualification seat =>
    unless g.input.isSome && g.s.config.ruleSet.isTournament && g.s.players.contains seat do
      throw "a match penalty requires a registered tournament seat"
  | .agreedDraw => pure ()
  if ending == .timeBetweenGames && needsTimedTiebreaker m g.singleElimination then
    let next := { g with timeAfterGames := some m.games }
    return (next, next.reply [])
  let _ ← concludeReplayMatch m (g.s.result.isSome && g.s.clock.isSome) (g.matchEnding ending)
    g.singleElimination
  let next := { g with ending := some ending }
  return (next, next.reply [])

/-- Follow a manual answer with automatic answers and package the steps in one reply. -/
def LiveGame.runAfterAnswer (answer : Except String (LiveGame × String)) :
    Except String (LiveGame × String) := do
  let (g, json) ← answer
  let (next, steps) ← g.autoRun 100000 []
  return (next, next.reply (json :: steps))

/-- Give the answer of the person, number `k` of the answers listed, and let the game go on. -/
def liveAct (g : LiveGame) (k : Nat) : Except String (LiveGame × String) := do
  let some a := g.legal[k]? | throw s!"there is no answer number {k}"
  LiveGame.runAfterAnswer (g.apply a)

/-- The clock calls time, or the judge declares a draw (TR 408.2, 505.6): an answer that is not a
player's. The engine refuses it when it is not legal. -/
def liveExternal (g : LiveGame) (a : Action) : Except String (LiveGame × String) :=
  LiveGame.runAfterAnswer (g.apply a)

/-- Log a rewind or remedy shuffle in the record of the active game. -/
def liveJudgeCorrection (g : LiveGame) (answer : ReplayAnswer) :
    Except String (LiveGame × String) :=
  match answer with
  | .judgeRewind _ | .judgeShuffle _ | .judgePrivateRewind _ => LiveGame.runAfterAnswer (g.applyReplay answer)
  | _ => .error "expected a judge correction"

/-- Apply an in-game Game Loss or schedule one for the next game (TR 701.2.b.1). -/
def liveJudgeGameLoss (g : LiveGame) (seats : List PlayerId) : Except String (LiveGame × String) := do
  unless g.input.isSome && g.s.config.ruleSet.isTournament && g.ending.isNone do
    throw "a Game Loss requires an open recorded tournament match"
  let _ ← judgeGameLossResult g.s.players g.s.config.mode.sameSide seats
  if g.s.result.isSome then
    let queued := (g.queuedGameLoss.getD [] ++ seats).eraseDups
    let next := { g with queuedGameLoss := some queued }
    return (next, next.reply [])
  LiveGame.runAfterAnswer (g.applyReplay (.gameLoss seats))

/-- The controlled chooser selects first or second after the Battlefield draws (TR 406.1.h.3). -/
def liveBo1First (g : LiveGame) (first : Bool) : Except String (LiveGame × String) := do
  let some chooser := g.bo1Chooser | throw "there is no Best of 1 initiative choice now"
  let starter := if first then chooser else MatchState.other chooser
  let order := MatchState.turnOrderOf starter
  LiveGame.runAfterAnswer ({ g with order := some order }.apply ⟨.chance, .arrangePlayers order⟩)

/-- Close the initial sideboard window before setting out the chosen champions and shuffling. -/
def liveBo1Sideboard (g : LiveGame) : Except String (LiveGame × String) := do
  unless g.bo1SideboardOpen && !g.humans.isEmpty do
    throw "there is no Best of 1 sideboard window now"
  LiveGame.runAfterAnswer (g.applyReplay .bo1Sideboard)

/-- The player who chooses who goes first in the next game, when a person is that player and has not
chosen yet (TR 407). -/
def LiveGame.chooser (g : LiveGame) : Option PlayerId :=
  match g.match_ with
  | none => none
  | some m =>
    match m.nextOrder with
    | .same _ => none
    | o =>
      let c := o.chooser ⟨(g.seed + m.games) % 2⟩
      if g.humans.contains c then some c else none

/-- The next game of the match. A person who chooses says whether they go first (`choice`); when
they have not said it, the reply asks (`choice` is the chooser). Otherwise the chooser goes first
(TR 407). The seed of a game is the seed of the match plus the games played. -/
def liveNext (g : LiveGame) (choice : Option Bool) : Except String (LiveGame × String) :=
  if g.teamSetup.isSome then .error "use team-next for a team match" else
  match g.match_ with
  | none => .error "this is not a match"
  | some m =>
    if g.ending.isSome then .error "the match is over"
    else if g.s.result.isNone then .error "the game is not over"
    else
      match g.chooser, choice with
      | some c, none => .ok (g, jobj [("choice", toString c.n)])
      | _, _ =>
        let how := m.nextOrder
        let random : PlayerId := ⟨(g.seed + m.games) % 2⟩
        let first := how.first random (choice.getD true)
        let seed := g.seed + m.games
        let fields := if reuseReplayBattlefields m g.endedByGameLoss then g.fields else []
        let replayChooser := match how with | .same _ => none | _ => some (how.chooser random)
        let next := match g.setup, g.input with
          | some setup, some input =>
            let decks := match input.decks with
              | .constructed _ => ReplayDecks.constructed g.registrations
              | other => other
            liveNewConfigured setup decks seed g.humans first replayChooser m
              (g.completed.push (g.gameRecord input)) fields g.timeAfterGames
              (g.s.clock.isSome || g.timeAfterGames.isSome) g.queuedGameLoss
          | _, _ =>
            liveNew g.kind seed g.humans (some (MatchState.turnOrderOf first))
              (some m) g.decks g.sides fields
        next.map (fun (g', steps) => (g', g'.reply steps g'.startInfo))

/-- Start the next team game. The losing team makes the choice; after a draw the complete
order and Battlefields are reused. Sealed registrations can be submitted together so that
teammates can reallocate cards within their shared pool. -/
def liveTeamNext (g : LiveGame) (requested : Option (List PlayerId) := none)
    (sealedDecks : Option (List LimitedDeck) := none) : Except String (LiveGame × String) := do
  let some setup := g.teamSetup | throw "this is not a team match"
  let some state := g.match_ | throw "this is not a match"
  let some oldInput := g.input | throw "the game's inputs are missing"
  if g.ending.isSome then throw "the match is over"
  if g.s.result.isNone then throw "the game is not over"
  if sealedDecks.isSome && setup.sealed?.isNone then throw "this is not a Sealed match"
  let seats := TeamSeats.standard
  let orders := Mode.teamTurnOrderChoices seats.team0 seats.team1
  let chooser ← match state.nextOrder with
    | .loserChooses team => pure (some team)
    | .same _ => pure none
    | .chance => throw "the previous game did not establish the next initiative choice"
  if let some team := chooser then
    if requested.isNone && g.humans.any (fun p => g.matchSide p == team) then
      let choices := jarr (orders.map (fun order => jarr (order.map (fun p => toString p.n))))
      return (g, jobj [("teamChoice", jobj [("team", toString team.n), ("orders", choices)])])
  let order ← match requested, chooser with
    | none, none => pure g.s.turnOrder
    | some chosen, none =>
      if chosen == g.s.turnOrder then pure chosen else throw "a draw preserves the same turn order"
    | some chosen, some _ =>
      if orders.contains chosen then pure chosen else throw "invalid alternating A/B turn order"
    | none, some team =>
      let some chosen := orders.find? (fun o => o.head?.any (fun p => g.matchSide p == team))
        | throw "no starting order for the losing team"
      pure chosen
  let decks := match oldInput.decks with
    | .constructed _ => ReplayDecks.constructed g.registrations
    | .limited existing => .limited (sealedDecks.getD existing)
    | other => other
  checkReplayDeckChange state oldInput.decks decks setup.sealed?.isSome
  let input : GameInputs := { decks, answers := #[], chooser, openingOrder := some order }
  let completed := g.completed.push (g.gameRecord oldInput)
  let (next, steps) ← liveNewTeam setup (g.seed + state.games) g.humans state input completed g.timeAfterGames
    g.queuedGameLoss
  return (next, next.reply steps next.startInfo)

/-- Apply a seat's complete post-sideboard registration through the same checks as replay. -/
def liveRegister (g : LiveGame) (p : PlayerId) (registration : ConstructedDeck) :
    Except String (LiveGame × String) := do
  let some m := g.match_ | throw "this is not a match"
  if g.ending.isSome then throw "the match is over"
  let initial := g.bo1SideboardOpen
  unless initial || (g.s.result.isSome && m.sideboardAllowed) do
    throw "the sideboard cannot be used now"
  if !g.humans.contains p then throw "this seat is not controlled"
  let some env := g.s.config.formatLegality | throw "the sideboard requires format legality"
  let some old := g.registrations[p.n]? | throw "there is no Constructed registration for this seat"
  if !sameRegisteredPool old registration then throw "the registered pool or fixed slots changed"
  if !decide (ConstructedDeckValid g.s.cards env registration) then
    throw "the deck would not be a legal Constructed deck"
  let next := { g with
    decks := g.decks.set p.n registration.deck,
    sides := g.sides.set p.n registration.sideboard }
  let next := if initial then
    { next with input := next.input.map (fun input => { input with decks := .constructed next.registrations }) }
    else next
  return (next, next.reply [])

/-- Exchange one Main Deck card for one sideboard card during a permitted sideboard window
(TR 403.4, 403.5, 403.10, 406.1.h). The engine rechecks Constructed deck legality. -/
def liveSwap (g : LiveGame) (out inn : String) (seat : Option PlayerId := none) :
    Except String (LiveGame × String) :=
  do
    let some p := seat <|> g.sideSeat | throw "there is no controlled seat"
    let some r := g.registrations[p.n]? | throw "there is no Constructed registration for this seat"
    let outgoing : CardId := ⟨out⟩
    let incoming : CardId := ⟨inn⟩
    if !r.deck.main.contains outgoing then throw s!"{out} is not in the Main Deck"
    if !r.sideboard.contains incoming then throw s!"{inn} is not in the sideboard"
    liveRegister g p {
      deck := { r.deck with main := r.deck.main.erase outgoing ++ [incoming] },
      sideboard := r.sideboard.erase incoming ++ [outgoing] }

end RiftboundDriver

end
