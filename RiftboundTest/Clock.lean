module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: the clock (TR 408.2)

The clock calls time; the turn that is going on is played to its end and 3 turns more; then the game
is over and the points decide.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- The game in the Main Phase of the turn `n`, under the given rules. -/
meta def atTurn (rules : RuleSet) (n : Nat) : Option GameState :=
  match GameState.initial db { ruleSet := rules, mode := Mode.duel } [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 n 4000 (Rng.ofSeed 1) s with
      | .ok s => some s
      | .error _ => none

meta def callTime : Action := ⟨.clock, .timeCalled⟩

/-- Let both players pass until the game is over. -/
meta def passToEnd : Nat → GameState → GameState
  | 0, s => s
  | n + 1, s =>
    if s.result.isSome then s
    else
      match playAnswer (Rng.ofSeed 1) s with
      | none => s
      | some (a, _) =>
        match step 100 s a with
        | .ok (s', _) => passToEnd n s'
        | .error _ => s

-- only the clock calls time, under the Tournament Rules, once the first turn has begun, and once
#guard match atTurn (.tournament .constructed) 2 with
  | some s =>
    (step 100 s callTime).toOption.isSome &&
    (step 100 s ⟨.player ⟨0⟩, .timeCalled⟩).toOption.isNone &&
    (step 100 s ⟨.judge, .timeCalled⟩).toOption.isNone &&
    (match step 100 s callTime with
      | .ok (s1, _) => (step 100 s1 callTime).toOption.isNone && s1.clock == some (s.turn + 3)
      | .error _ => false)
  | none => false

-- under the Core Rules there is no clock
#guard match atTurn .coreOnly 2 with
  | some s => (step 100 s callTime).toOption.isNone
  | none => false

-- time is called in turn 2: turns 3, 4 and 5 are played, and the game is over when turn 6 would
-- begin; with no points on either side it is a draw (TR 408.2)
#guard match atTurn (.tournament .constructed) 2 with
  | some s =>
    match step 100 s callTime with
    | .ok (s1, _) =>
      let e := passToEnd 2000 s1
      s.turn == 2 && e.turn == 5 && e.result == some .draw && e.pending.isEmpty
    | .error _ => false
  | none => false

-- 2 points ahead wins by the clock; the game ends when the clock has run out, nothing sooner
#guard match atTurn (.tournament .constructed) 2 with
  | some s =>
    match step 100 s callTime with
    | .ok (s1, _) =>
      let s2 := (s1.gainPoints ⟨0⟩ 2)
      let e := passToEnd 2000 s2
      let f := passToEnd 2000 (s1.gainPoints ⟨1⟩ 1)
      e.result == some (.won [⟨0⟩]) && f.result == some .draw &&
      (passToEnd 20 s2).turn ≤ 5
    | .error _ => false
  | none => false

end RiftboundTest
