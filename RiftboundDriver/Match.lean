module

public import RiftboundDriver.Trace
public import Riftbound.Tournament.Match
public import Riftbound.Tournament.LoopDetect

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
  /-- Who decided who goes first (TR 407). -/
  how : MatchState.Order
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

/-- A certified forced loop in tournament play is answered with the ordinary judge ruling
(TR 505.6). -/
def forcedLoopRuling (fuel : Nat) (s : GameState) (history : List (GameState × Action)) :
    Option Action :=
  if s.config.ruleSet.isTournament then
    (detectExactForcedLoop fuel s history).map (fun _ => ⟨.judge, .declareDraw⟩)
  else none

/-- Whenever the driver proposes the ruling, it carries a nonempty forced sequence that can be
repeated arbitrarily many times. -/
theorem forcedLoopRuling_sound {fuel : Nat} {s : GameState}
    {history : List (GameState × Action)} {ruling : Action}
    (reported : forcedLoopRuling fuel s history = some ruling) :
    ruling = ⟨.judge, .declareDraw⟩ ∧
      ∃ cycle, cycle ≠ [] ∧ ∀ rounds,
        runForcedAnswers fuel s (List.replicate rounds cycle).flatten = some s := by
  unfold forcedLoopRuling at reported
  split at reported
  · cases found : detectExactForcedLoop fuel s history with
    | none => simp [found] at reported
    | some cycle =>
      simp only [found, Option.map_some, Option.some.injEq] at reported
      exact ⟨reported.symm, cycle, (detectExactForcedLoop_sound found 0).1,
        fun rounds => (detectExactForcedLoop_sound found rounds).2⟩
  · simp at reported

/-- Play until the game ends, calling time after `cap` turns have begun (TR 408.2) or applying
the judge's ruling when a forced cycle is certified (TR 505.6). -/
def playUntilEnd (cap : Nat) (order : List PlayerId) (steps : Nat) (r : Rng) (s : GameState) :
    Except RuleError GameState :=
  go steps r s []
where
  go : Nat → Rng → GameState → List (GameState × Action) → Except RuleError GameState
    | 0, _, s, _ => .ok s
    | n + 1, r, s, history =>
      if s.result.isSome then .ok s
      else if (match s.pending with | .chanceTurnOrder :: _ => true | _ => false) then
        match step 100 s ⟨.chance, .arrangePlayers order⟩ with
        | .ok (s', _) => go n r s' []
        | .error e => .error e
      else if s.clock.isNone && cap ≤ s.turn && s.active.isSome then
        match step 100 s ⟨.clock, .timeCalled⟩ with
        | .ok (s', _) => go n r s' []
        | .error e => .error e
      else
        match ((forcedLoopRuling 100 s history).map (fun action => (action, r))).orElse
          (fun _ => demoAnswer r s) with
        | none => .ok s
        | some (a, r') =>
          match step 100 s a with
          | .ok (s', _) =>
            let history' := if s.config.ruleSet.isTournament && forcedAnswer s == some a then
              (s, a) :: history else []
            go n r' s' history'
          | .error e => .error e

/-- The rules of the matches: a Duel under the Tournament Rules, Constructed. -/
def matchConfig : GameConfig :=
  { ruleSet := .tournament .constructed, mode := Mode.duel, formatLegality := some demoEnv }

/-- One demo game from the seed, with the turn order the match decided (TR 407). The clock calls
time when `cap` turns have begun. -/
def playGameLog (seed cap : Nat) (how : MatchState.Order) (order : List PlayerId) :
    Except String GameLog :=
  match GameState.initial demoDB matchConfig [demoDeck, demoDeck] with
  | none => .error "the demo game cannot be set up"
  | some s0 =>
    match playUntilEnd cap order 100000 (Rng.ofSeed seed) s0 with
    | .error e => .error s!"the engine refused an answer: {repr e}"
    | .ok s =>
      let pts := (s.pointsOf ⟨0⟩, s.pointsOf ⟨1⟩)
      let first := s.turnOrder.headD ⟨0⟩
      match s.result with
      | some r => .ok ⟨seed, how, first, s.turn, pts, s.clock.isSome, r⟩
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
        -- the draw picks a player, and the player who chooses goes first (TR 407)
        let how := m.nextOrder
        let random : PlayerId := ⟨(seed + acc.length) % 2⟩
        let first := how.first random true
        match playGameLog (seed + acc.length) cap how (MatchState.turnOrderOf first) with
        | .error e => .error e
        | .ok g => go n (m.record g.result g.first) (g :: acc)
  go limit (MatchState.start target) []

end RiftboundDriver

end
