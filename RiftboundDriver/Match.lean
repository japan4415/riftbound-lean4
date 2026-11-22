module

public import RiftboundDriver.Trace
public import Riftbound.Tournament.Match

/-!
# Driver: a match of demo games

Plays games with the engine one after the other and feeds each result to `MatchState` (TR 404). A
game that is not over when `cap` turns have begun is stopped by the time, and its result is decided
by the points (TR 408.2). This library is not part of the verified core; the match logic it calls
is (`Riftbound/Tournament/Match.lean`).
-/

@[expose] public section

namespace RiftboundDriver

open Riftbound

/-- What came of one game. -/
structure GameLog where
  /-- The seed of the game. -/
  seed : Nat
  /-- Who went first. -/
  first : PlayerId
  /-- The turns that had begun when the game ended. -/
  turns : Nat
  /-- The points of the two players at the end. -/
  points : Nat × Nat
  /-- Whether the time was up (TR 408.2). -/
  timeUp : Bool
  /-- How it ended. -/
  result : GameResult
deriving Repr

/-- Play the game until it ends. When `cap` turns have begun, the clock calls time (TR 408.2): the
turn that is going on is played to its end, and 3 turns more, and the engine ends the game. -/
def playUntilEnd (cap : Nat) : Nat → Rng → GameState → Except RuleError GameState
  | 0, _, s => .ok s
  | n + 1, r, s =>
    if s.result.isSome then .ok s
    else if s.clock.isNone && cap ≤ s.turn && s.active.isSome then
      match step 100 s ⟨.clock, .timeCalled⟩ with
      | .ok (s', _) => playUntilEnd cap n r s'
      | .error e => .error e
    else
      match demoAnswer r s with
      | none => .ok s
      | some (a, r') =>
        match step 100 s a with
        | .ok (s', _) => playUntilEnd cap n r' s'
        | .error e => .error e

/-- The rules of the matches: a Duel under the Tournament Rules, Constructed. -/
def matchConfig : GameConfig := { ruleSet := .tournament .constructed, mode := Mode.duel }

/-- One demo game from the seed. The clock calls time when `cap` turns have begun. -/
def playGameLog (seed cap : Nat) : Except String GameLog :=
  match GameState.initial demoDB matchConfig [demoDeck, demoDeck] with
  | none => .error "the demo game cannot be set up"
  | some s0 =>
    match playUntilEnd cap 100000 (Rng.ofSeed seed) s0 with
    | .error e => .error s!"the engine refused an answer: {repr e}"
    | .ok s =>
      let pts := (s.pointsOf ⟨0⟩, s.pointsOf ⟨1⟩)
      let first := s.turnOrder.headD ⟨0⟩
      match s.result with
      | some r => .ok ⟨seed, first, s.turn, pts, s.clock.isSome, r⟩
      | none => .error "the game did not end"

/-- A match of at most `limit` games (a Best of 3 by default), with the seeds `seed`, `seed + 1`,
and so on. Each game's result goes through `MatchState.record`. The games and the match at the
end. -/
def playMatch (seed cap : Nat) (target : Nat := 2) (limit : Nat := 8) :
    Except String (List GameLog × MatchState) :=
  let rec go : Nat → MatchState → List GameLog → Except String (List GameLog × MatchState)
    | 0, m, acc => .ok (acc.reverse, m)
    | n + 1, m, acc =>
      if m.finished then .ok (acc.reverse, m)
      else
        match playGameLog (seed + acc.length) cap with
        | .error e => .error e
        | .ok g => go n (m.record g.result g.first) (g :: acc)
  go limit (MatchState.start target) []

end RiftboundDriver

end
