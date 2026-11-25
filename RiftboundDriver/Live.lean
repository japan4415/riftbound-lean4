module

public import RiftboundDriver.Trace

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

open Riftbound

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

/-- The player whose answer the game waits for, if it is a player's. -/
def LiveGame.waiting (g : LiveGame) : Option PlayerId :=
  match (legalFrameActions g.s).head? with
  | some ⟨.player p, _⟩ => some p
  | _ => none

/-- The answers a person can give now: those of the players they control, a concession included.
-/
def LiveGame.legal (g : LiveGame) : List Action :=
  (legalActions g.s).filter (fun a =>
    match a.actor with
    | .player p => g.humans.contains p
    | _ => false)

/-- The game waits for a person. -/
def LiveGame.needsHuman (g : LiveGame) : Bool :=
  g.s.result.isNone && (match g.waiting with | some p => g.humans.contains p | none => false)

/-- Give an answer: the step as JSON, and the game after it. -/
def LiveGame.apply (g : LiveGame) (a : Action) : Except String (LiveGame × String) :=
  match step 100 g.s a with
  | .error e => .error s!"the engine refused the answer: {repr e}"
  | .ok (s', es) =>
    let (j, seen') := stepJson g.i (some a) es s' g.seen g.s.pending.head?
    .ok ({ g with s := s', seen := seen', i := g.i + 1 }, j)

/-- When the game is over, its result goes to the match, once (TR 404). -/
def LiveGame.settle (g : LiveGame) : LiveGame :=
  match g.match_, g.s.result with
  | some m, some r =>
    if g.recorded then g
    else { g with match_ := some (m.record r (g.s.turnOrder.headD ⟨0⟩)), recorded := true }
  | _, _ => g

/-- Answer for the seats nobody controls until the game is over or a person is to answer. The steps
that were made, in order. -/
def LiveGame.autoRun : Nat → LiveGame → List String → Except String (LiveGame × List String)
  | 0, g, acc => .ok (g.settle, acc.reverse)
  | n + 1, g, acc =>
    if g.s.result.isSome || g.needsHuman then .ok (g.settle, acc.reverse)
    else
      match g.s.pending, g.order with
      | .chanceTurnOrder :: _, some o =>
        match g.apply ⟨.chance, .arrangePlayers o⟩ with
        | .error e => .error e
        | .ok (g', j) => LiveGame.autoRun n g' (j :: acc)
      | _, _ =>
        match demoAnswer g.rng g.s with
        | none => .ok (g.settle, acc.reverse)
        | some (a, r') =>
          match { g with rng := r' }.apply a with
          | .error e => .error e
          | .ok (g', j) => LiveGame.autoRun n g' (j :: acc)

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
    jobj [("target", toString m.target), ("wins", jarr [toString m.wins0, toString m.wins1]),
      ("games", toString m.games), ("finished", if m.finished then "true" else "false"),
      ("winner", match m.winner with | some p => toString p.n | none => "null"),
      ("sideboard", if m.sideboardAllowed then "true" else "false"),
      ("sameBattlefields", if m.reuseBattlefields then "true" else "false"),
      ("order", jstr (match m.nextOrder with
        | .chance => "chance" | .loserChooses p => s!"loser{p.n}" | .same f => s!"same{f.n}"))]

/-- Whether the clock may call time and the judge declare a draw now (TR 408.2, 410.1, 505.6). -/
def LiveGame.externalJson (g : LiveGame) : String :=
  let ok (a : Action) : String := if decide (Legal g.s a) then "true" else "false"
  jobj [("clock", ok ⟨.clock, .timeCalled⟩), ("judge", ok ⟨.judge, .declareDraw⟩)]

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
          jobj [("id", jstr c.code), ("name", jstr ((demoDB.find? c).map (·.name) |>.getD c.code)),
            ("n", toString n)]))
      jobj [("player", toString p.n),
        ("allowed", if m.sideboardAllowed && g.s.result.isSome then "true" else "false"),
        ("main", group d.main), ("side", group side),
        ("mainCount", toString d.main.length), ("sideCount", toString side.length)]
    | _, _ => "null"
  | _, _, _ => "null"

/-- What a request returns: the steps made, the answers a person can give, whether the game is
over, the match, and what the clock and the judge can do. -/
def LiveGame.reply (g : LiveGame) (steps : List String) (extra : List (String × String) := []) :
    String :=
  jobj (extra ++ [("steps", jarr steps), ("legal", g.legalJson),
    ("over", if g.s.result.isSome then "true" else "false"),
    ("match", g.matchJson), ("external", g.externalJson), ("sideboard", g.sideJson)])

/-- What the reply to an undo says: the answers a person can give again, and how many steps the
viewer keeps (the steps made until then). -/
def LiveGame.undoReply (g : LiveGame) : String :=
  g.reply [] [("truncate", toString g.i)]

/-- The game before any answer, for the kind of game, from the decks of the players. -/
def LiveKind.initial (decks : List Deck) : LiveKind → Option GameState
  | .core => GameState.initial demoDB demoConfig decks
  | .constructed =>
    GameState.initial demoDB
      { ruleSet := .tournament .constructed, mode := Mode.duel, formatLegality := some demoEnv } decks
  | .sealed =>
    GameState.initialLimited demoDB { legalSets := [], banned := [] }
      { ruleSet := .tournament .sealed, mode := Mode.duel } [demoLimitedDeck, demoLimitedDeck]
  | .draft =>
    GameState.initialLimited demoDB { legalSets := [], banned := [] }
      { ruleSet := .tournament .draft, mode := Mode.duel } [demoLimitedDeck, demoLimitedDeck]

/-- A new game: the first step, and the game after the answers of the seats nobody controls. -/
def liveNew (kind : LiveKind) (seed : Nat) (humans : List PlayerId) (order : Option (List PlayerId))
    (m : Option MatchState) (decks : List Deck := [demoDeck, demoDeck])
    (sides : List (List CardId) := [demoSideboard, demoSideboard]) :
    Except String (LiveGame × List String) :=
  match kind.initial decks with
  | none => .error "the demo game cannot be set up"
  | some s0 =>
    let (j0, seen) := stepJson 0 none [] s0 {}
    let g0 : LiveGame := { s := s0, seen := seen, i := 1, rng := Rng.ofSeed seed, humans := humans }
    let g1 : LiveGame := { g0 with kind := kind, seed := seed, order := order, match_ := m }
    let g : LiveGame := { g1 with decks := decks, sides := sides }
    match LiveGame.autoRun 100000 g [] with
    | .error e => .error e
    | .ok (g', js) => .ok (g', j0 :: js)

/-- The fixed part of the reply to the start of a game. -/
def LiveGame.startInfo (g : LiveGame) : List (String × String) :=
  [("seed", toString g.seed), ("players", toString g.s.playerCount),
    ("cards", jobj (demoCards.map (fun c => (c.id.code, cardJson c))))]

/-- Start a game of the kind, with `seed` for the chance decisions. A person controls the players in
`humans`. With `matchTarget` (1 or 2 wins), the game is the first of a match. -/
def liveStart (seed : Nat) (humans : List PlayerId) (kind : LiveKind := .core)
    (matchTarget : Option Nat := none) : Except String (LiveGame × String) :=
  match liveNew kind seed humans none (matchTarget.map MatchState.start) with
  | .error e => .error e
  | .ok (g, js) => .ok (g, g.reply js g.startInfo)

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
    if m.finished then .error "the match is over"
    else if g.s.result.isNone then .error "the game is not over"
    else
      match g.chooser, choice with
      | some c, none => .ok (g, jobj [("choice", toString c.n)])
      | _, _ =>
        let how := m.nextOrder
        let random : PlayerId := ⟨(g.seed + m.games) % 2⟩
        let first := how.first random (choice.getD true)
        match liveNew g.kind (g.seed + m.games) g.humans (some (MatchState.turnOrderOf first))
            (some m) g.decks g.sides with
        | .error e => .error e
        | .ok (g', js) => .ok (g', g'.reply js g'.startInfo)

/-- A person exchanges a card of their Main Deck for a card of their sideboard, between the games of
a Constructed match (TR 403.4): one for one, only when the match allows it (not before the first
game, not after a draw: TR 403.5, 403.10), and only if the deck stays a legal Constructed deck
(TR 403.4.c). The check is the engine's: `ConstructedDeckValid`. -/
def liveSwap (g : LiveGame) (out inn : String) : Except String (LiveGame × String) :=
  match g.match_, g.sideSeat, g.kind with
  | some m, some p, .constructed =>
    if m.finished then .error "the match is over"
    else if g.s.result.isNone then .error "the game is not over"
    else if !m.sideboardAllowed then
      .error "the sideboard cannot be used now (not before the first game, nor after a draw)"
    else
      match g.decks[p.n]?, g.sides[p.n]? with
      | some d, some side =>
        let o : CardId := ⟨out⟩
        let i : CardId := ⟨inn⟩
        if !d.main.contains o then .error s!"{out} is not in the Main Deck"
        else if !side.contains i then .error s!"{inn} is not in the sideboard"
        else
          let d' := { d with main := d.main.erase o ++ [i] }
          let side' := side.erase i ++ [o]
          if decide (ConstructedDeckValid demoDB demoEnv { deck := d', sideboard := side' }) then
            let g' := { g with decks := g.decks.set p.n d', sides := g.sides.set p.n side' }
            .ok (g', g'.reply [])
          else .error "the deck would not be a legal Constructed deck"
      | _, _ => .error "there is no deck"
  | none, _, _ => .error "this is not a match"
  | _, _, _ => .error "the sideboard is for a Constructed match"

end RiftboundDriver

end
