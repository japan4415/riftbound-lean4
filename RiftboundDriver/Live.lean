module

public import RiftboundDriver.Trace
public import RiftboundDriver.MatchReplay

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
  /-- This game's starting registration and initiative, separate from edits for the next game. -/
  input : Option GameInputs := none
  /-- Answers already given, newest first so undo snapshots share the earlier entries. -/
  answersRev : List ReplayAnswer := []
  /-- Evidence for setup and each answer, newest first. -/
  checkpointsRev : List ReplayCheckpoint := []
  /-- Completed games in chronological order, up to the start of this game. -/
  completed : Array RecordedGame := #[]
  /-- Battlefield cards selected for this game, keyed by the seat that brought them. -/
  fields : List (PlayerId × CardId) := []
  /-- When replaying a draw, require the same Battlefield selections. -/
  reuseFields : List (PlayerId × CardId) := []
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

/-- The game waits for a person. -/
def LiveGame.needsHuman (g : LiveGame) : Bool :=
  g.s.result.isNone && (match g.waiting with | some p => g.humans.contains p | none => false)

/-- Give an answer: the step as JSON, and the game after it. -/
def LiveGame.apply (g : LiveGame) (a : Action) : Except String (LiveGame × String) :=
  if g.ending.isSome then .error "the match is over" else
  match step (g.setup.map (·.fuel) |>.getD 100) g.s a with
  | .error e => .error s!"the engine refused the answer: {repr e}"
  | .ok (s', es) =>
    let (j, seen') := stepJson g.i (some a) es s' g.seen g.s.pending.head?
    .ok ({ g with
      s := s', seen := seen', i := g.i + 1,
      answersRev := if g.input.isSome then .observed a :: g.answersRev else g.answersRev,
      checkpointsRev := if g.input.isSome then ReplayCheckpoint.capture s' es :: g.checkpointsRev
        else g.checkpointsRev,
      fields := (pickedBattlefield g.s a).toList ++ g.fields }, j)

/-- When the game is over, its result goes to the match, once (TR 404). -/
def LiveGame.settle (g : LiveGame) : LiveGame :=
  match g.match_, g.s.result with
  | some m, some r =>
    if g.recorded then g
    else
      let first := g.s.turnOrder.head?
      let next := { m.record r (first.getD ⟨0⟩) with lastFirst := first }
      { g with
        match_ := some next, recorded := true,
        ending := if next.finished || g.s.clock.isSome then some .finalGame else none }
  | _, _ => g

/-- A forced answer during setup, when match decisions already determine the choice. -/
def LiveGame.setupAnswer (g : LiveGame) : Except String (Option Action) := do
  match g.s.pending with
  | .chanceTurnOrder :: _ => return g.order.map (fun order => ⟨.chance, .arrangePlayers order⟩)
  | .chanceBattlefield seat :: _ =>
    let some card := g.reuseFields.lookup seat | return none
    let some index := (g.s.zone (.player seat .outOfGame)).findIdx?
        (fun id => (g.s.cardDef? id).any (·.id == card))
      | throw s!"seat {seat.n} cannot reuse Battlefield {card.code}"
    return some ⟨.chance, .pick index⟩
  | _ => return none

/-- Answer for the seats nobody controls until the game is over or a person is to answer. The steps
that were made, in order. -/
def LiveGame.autoRun : Nat → LiveGame → List String → Except String (LiveGame × List String)
  | 0, g, acc =>
    if g.s.result.isSome || g.needsHuman then .ok (g.settle, acc.reverse)
    else .error "the automatic player reached its action limit"
  | n + 1, g, acc => do
    if g.s.result.isSome || g.needsHuman then return (g.settle, acc.reverse)
    let planned ← g.setupAnswer
    let answer := match planned with
      | some a => some (a, g.rng)
      | none => demoAnswer g.rng g.s
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
      (concludeReplayMatch m (g.s.result.isSome && g.s.clock.isSome) ending).toOption)
    jobj [("target", toString m.target), ("wins", jarr [toString m.wins0, toString m.wins1]),
      ("games", toString m.games), ("finished", toString g.ending.isSome),
      ("winner", match result with | some (.won p) => toString p.n | _ => "null"),
      ("sideboard", if m.sideboardAllowed then "true" else "false"),
      ("sameBattlefields", if m.reuseBattlefields then "true" else "false"),
      ("order", jstr (match m.nextOrder with
        | .chance => "chance" | .loserChooses p => s!"loser{p.n}" | .same f => s!"same{f.n}"))]

/-- Whether the clock may call time and the judge declare a draw now (TR 408.2, 410.1, 505.6). -/
def LiveGame.externalJson (g : LiveGame) : String :=
  let ok (a : Action) : String := toString (g.ending.isNone && decide (Legal g.s a))
  jobj [("clock", ok ⟨.clock, .timeCalled⟩), ("judge", ok ⟨.judge, .declareDraw⟩),
    ("betweenGames", toString (g.ending.isNone && g.match_.isSome &&
      g.s.result.isSome && g.s.config.ruleSet.isTournament))]

/-- The cards of a list with how many of each, in the order they first appear. -/
def countIds (l : List CardId) : List (CardId × Nat) :=
  l.foldl (fun acc c =>
    if acc.any (fun x => x.1 == c) then acc.map (fun x => if x.1 == c then (x.1, x.2 + 1) else x)
    else acc ++ [(c, 1)]) []

/-- The player whose deck a person changes between games: the first player they control. -/
def LiveGame.sideSeat (g : LiveGame) : Option PlayerId := g.humans.head?

/-- The sideboard of the match as JSON, for a Constructed match: the Main Deck and the sideboard of
the player, and whether the players may use the sideboard now (TR 403.5, 403.10). `null`
otherwise. -/
def LiveGame.sideJson (g : LiveGame) : String :=
  match g.match_, g.sideSeat, g.kind with
  | some m, some p, .constructed =>
    match g.decks[p.n]?, g.sides[p.n]? with
    | some d, some side =>
      let group (l : List CardId) : String :=
        jarr ((countIds l).map (fun (c, n) =>
          jobj [("id", jstr c.code), ("name", jstr ((g.s.cards.find? c).map (·.name) |>.getD c.code)),
            ("n", toString n)]))
      jobj [("player", toString p.n),
        ("allowed", toString (m.sideboardAllowed && g.s.result.isSome && g.ending.isNone)),
        ("main", group d.main), ("side", group side),
        ("mainCount", toString d.main.length), ("sideCount", toString side.length)]
    | _, _ => "null"
  | _, _, _ => "null"

/-- What a request returns: the steps made, the answers a person can give, whether the game is
over, the match, and what the clock and the judge can do. -/
def LiveGame.reply (g : LiveGame) (steps : List String) (extra : List (String × String) := []) :
    String :=
  jobj (extra ++ [("steps", jarr steps), ("legal", g.legalJson),
    ("over", toString (g.s.result.isSome || g.ending.isSome)),
    ("archiveAvailable", toString (g.setup.isSome && g.ending.isSome)),
    ("match", g.matchJson), ("external", g.externalJson), ("sideboard", g.sideJson)])

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
  let (next, steps) ← { g with i := 1, seen, checkpointsRev }.autoRun 100000 []
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
    checkpoints := g.checkpointsRev.reverse.toArray
    summary := ReplayGameResult.fromState g.s input.decks g.fields.reverse true }

/-- Set up a game with real cards and keep its starting registration available for export. -/
def liveNewConfigured (setup : LiveSetup) (decks : ReplayDecks) (seed : Nat)
    (humans : List PlayerId) (first : PlayerId) (chooser : Option PlayerId) (m : MatchState)
    (completed : Array RecordedGame := #[]) (reuseFields : List (PlayerId × CardId) := []) :
    Except String (LiveGame × List String) := do
  let s ← decks.initial RiftboundCards.db setup.config
  let kind := match setup.config.ruleSet with
    | .coreOnly => LiveKind.core
    | .tournament format => match format with
      | .constructed => .constructed | .sealed => .sealed | .draft => .draft
  let registrations := match decks with | .constructed ds => ds | _ => []
  LiveGame.begin {
    s, seen := {}, i := 0, rng := Rng.ofSeed seed, humans, kind, seed,
    order := some (MatchState.turnOrderOf first), match_ := some m, setup := some setup,
    input := some { decks, answers := #[], chooser }, completed, reuseFields,
    decks := registrations.map (·.deck), sides := registrations.map (·.sideboard) }

/-- The fixed part of the reply to the start of a game. -/
def LiveGame.startInfo (g : LiveGame) : List (String × String) :=
  [("seed", toString g.seed), ("players", toString g.s.playerCount),
    ("cards", jobj (g.s.cards.cards.map (fun c => (c.id.code, cardJson c))))]

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
  checkReplayEvent setup.config setup.tournament
  let (g, steps) ← liveNewConfigured setup setup.decks seed humans setup.first
    (some setup.firstChooser) (MatchState.start setup.winsRequired)
  return (g, g.reply steps g.startInfo)

/-- Export the entire recorded live match for independent replay. -/
def LiveGame.archive (g : LiveGame) : Except String RecordedMatch := do
  let some setup := g.setup | throw "no real decks were registered for this match"
  let some ending := g.ending | throw "the match is not over"
  let some input := g.input | throw "the game's inputs are missing"
  let games := g.completed.push (g.gameRecord input)
  MatchInputs.recordPlayed {
    config := setup.config, tournament := setup.tournament,
    winsRequired := setup.winsRequired, fuel := setup.fuel, games := games.map (·.input), ending }
    games g.s.cards

/-- End a live match by an external match decision. -/
def liveEnd (g : LiveGame) (ending : ReplayMatchEnd) : Except String (LiveGame × String) := do
  let some m := g.match_ | throw "this is not a match"
  if g.ending.isSome then throw "the match is over"
  match ending with
  | .finalGame => throw "the engine records game results"
  | .timeBetweenGames =>
    if g.s.result.isNone || !g.s.config.ruleSet.isTournament then
      throw "time between games requires a completed tournament game"
  | .concede seat =>
    if !g.humans.contains seat then throw "the concession must come from a controlled seat"
  | .agreedDraw => pure ()
  let _ ← concludeReplayMatch m (g.s.result.isSome && g.s.clock.isSome) ending
  let next := { g with ending := some ending }
  return (next, next.reply [])

/-- Give the answer of the person, number `k` of the answers listed, and let the game go on. -/
def liveAct (g : LiveGame) (k : Nat) : Except String (LiveGame × String) :=
  match g.legal[k]? with
  | none => .error s!"there is no answer number {k}"
  | some a =>
    match g.apply a with
    | .error e => .error e
    | .ok (g1, j) =>
      match LiveGame.autoRun 100000 g1 [] with
      | .error e => .error e
      | .ok (g2, js) => .ok (g2, g2.reply (j :: js))

/-- The clock calls time, or the judge declares a draw (TR 408.2, 505.6): an answer that is not a
player's. The engine refuses it when it is not legal. -/
def liveExternal (g : LiveGame) (a : Action) : Except String (LiveGame × String) :=
  match g.apply a with
  | .error e => .error e
  | .ok (g1, j) =>
    match LiveGame.autoRun 100000 g1 [] with
    | .error e => .error e
    | .ok (g2, js) => .ok (g2, g2.reply (j :: js))

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
        let fields := if m.reuseBattlefields then g.fields else []
        let replayChooser := match how with | .same _ => none | _ => some (how.chooser random)
        let next := match g.setup, g.input with
          | some setup, some input =>
            let decks := match input.decks with
              | .constructed _ => ReplayDecks.constructed g.registrations
              | other => other
            liveNewConfigured setup decks seed g.humans first replayChooser m
              (g.completed.push (g.gameRecord input)) fields
          | _, _ =>
            liveNew g.kind seed g.humans (some (MatchState.turnOrderOf first))
              (some m) g.decks g.sides fields
        next.map (fun (g', steps) => (g', g'.reply steps g'.startInfo))

/-- Apply a seat's complete post-sideboard registration through the same checks as replay. -/
def liveRegister (g : LiveGame) (p : PlayerId) (registration : ConstructedDeck) :
    Except String (LiveGame × String) := do
  let some m := g.match_ | throw "this is not a match"
  if g.ending.isSome then throw "the match is over"
  if g.s.result.isNone then throw "the game is not over"
  if !m.sideboardAllowed then throw "the sideboard cannot be used now"
  if !g.humans.contains p then throw "this seat is not controlled"
  let some env := g.s.config.formatLegality | throw "the sideboard requires format legality"
  let some old := g.registrations[p.n]? | throw "there is no Constructed registration for this seat"
  if !sameRegisteredPool old registration then throw "the registered pool or fixed slots changed"
  if !decide (ConstructedDeckValid g.s.cards env registration) then
    throw "the deck would not be a legal Constructed deck"
  let next := { g with
    decks := g.decks.set p.n registration.deck,
    sides := g.sides.set p.n registration.sideboard }
  return (next, next.reply [])

/-- A person exchanges a card of their Main Deck for a card of their sideboard, between the games of
a Constructed match (TR 403.4): one for one, only when the match allows it (not before the first
game, not after a draw: TR 403.5, 403.10), and only if the deck stays a legal Constructed deck
(TR 403.4.c). The check is the engine's: `ConstructedDeckValid`. -/
def liveSwap (g : LiveGame) (out inn : String) : Except String (LiveGame × String) :=
  do
    let some p := g.sideSeat | throw "there is no controlled seat"
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
