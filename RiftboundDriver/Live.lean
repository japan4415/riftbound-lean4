module

public import RiftboundDriver.Trace

/-!
# Driver: live play

A game that a person plays through the viewer. The engine decides what can be answered
(`legalActions`) and what an answer does (`step`); this file only keeps the game between requests,
answers the questions of the seats that nobody controls (the chance decisions and the automatic
player, as `demoAnswer` does), and writes what happened as JSON. The viewer draws it and has no
rules. Like the trace, this library is not covered by the proofs (design.md §4).
-/

@[expose] public section

namespace RiftboundDriver

open Riftbound

/-- A game in progress: the state, the objects the viewer has seen, the number of steps written,
the generator for the chance decisions, and the seats a person controls. -/
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
    let (j, seen') := stepJson g.i (some a) es s' g.seen
    .ok ({ g with s := s', seen := seen', i := g.i + 1 }, j)

/-- Answer for the seats nobody controls until the game is over or a person is to answer. The steps
that were made, in order. -/
def LiveGame.autoRun : Nat → LiveGame → List String → Except String (LiveGame × List String)
  | 0, g, acc => .ok (g, acc.reverse)
  | n + 1, g, acc =>
    if g.s.result.isSome || g.needsHuman then .ok (g, acc.reverse)
    else
      match demoAnswer g.rng g.s with
      | none => .ok (g, acc.reverse)
      | some (a, r') =>
        match { g with rng := r' }.apply a with
        | .error e => .error e
        | .ok (g', j) => LiveGame.autoRun n g' (j :: acc)

/-- The answers a person can give, as JSON: the number to send back, and the answer. -/
def LiveGame.legalJson (g : LiveGame) : String :=
  jarr ((g.legal.zipIdx).map (fun (a, k) => jobj [("k", toString k), ("a", actionJson a)]))

/-- What a request returns: the steps made, the answers a person can give, and whether the game is
over. -/
def LiveGame.reply (g : LiveGame) (steps : List String) (extra : List (String × String) := []) :
    String :=
  jobj (extra ++ [("steps", jarr steps), ("legal", g.legalJson),
    ("over", if g.s.result.isSome then "true" else "false")])

/-- Start a game: the demo decks under the Core Rules, `seed` for the chance decisions. A person
controls the players in `humans`. -/
def liveStart (seed : Nat) (humans : List PlayerId) : Except String (LiveGame × String) :=
  match GameState.initial demoDB demoConfig [demoDeck, demoDeck] with
  | none => .error "the demo game cannot be set up"
  | some s0 =>
    let (j0, seen) := stepJson 0 none [] s0 {}
    let g : LiveGame := { s := s0, seen, i := 1, rng := Rng.ofSeed seed, humans }
    match LiveGame.autoRun 100000 g [] with
    | .error e => .error e
    | .ok (g', js) =>
      .ok (g', g'.reply (j0 :: js) [("seed", toString seed), ("players", toString s0.playerCount),
        ("cards", jobj (demoCards.map (fun c => (c.id.code, cardJson c))))])

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

end RiftboundDriver

end
