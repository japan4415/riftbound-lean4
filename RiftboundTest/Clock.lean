module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: the clock (TR 408.2, 408.4)

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
      | .ok (s1, _) => (step 100 s1 callTime).toOption.isNone && s1.clock == some (.swiss (s.turn + 3))
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

-- Single elimination settles on a one-point lead, or leaves an even game to the match leader.
#guard (do
  let tied ← atTurn (.tournamentElimination .constructed (.regular true)) 2
  let leading ← atTurn (.tournamentElimination .constructed (.regular false)) 2
  let (tied, _) ← (step 100 tied callTime).toOption
  let (leading, _) ← (step 100 leading callTime).toOption
  let pointWins := passToEnd 30 (tied.gainPoints ⟨1⟩ 1)
  let matchWins := passToEnd 30 leading
  return pointWins.turn == 5 && pointWins.result == some (GameResult.won [⟨1⟩]) &&
    matchWins.turn == 5 && matchWins.result == some GameResult.draw).getD false

-- A tiebreaker starts with its clock already set. Tied points allow turn 7, whose first actual
-- point (here awarded through Burn Out) completes the game before any further decision.
#guard (do
  let s ← atTurn (.tournamentElimination .constructed .tiebreaker) 6
  let (overtime, _) ← (step 100 s ⟨.player (s.active.getD ⟨0⟩), .pass⟩).toOption
  let p ← overtime.active
  let recipient := otherPlayer p
  let main := Zone.player p .mainDeck
  let trash := Zone.player p .trash
  let emptyDeck ← (overtime.zone main).foldlM
    (fun board card => (moveObj board card trash).map Prod.fst) overtime
  let drawing := { emptyDeck with pending := [.draw p 1, .priority p] }
  let (shuffling, _) ← (advance 10 drawing []).toOption
  let order := (shuffling.zone trash).reverse
  let (waiting, _) ← (step 10 shuffling ⟨.chance, .arrange order⟩).toOption
  let ((scored, es), seen) ←
    (stepWithDisclosures 0 waiting ⟨.player p, .burnOutTarget recipient⟩).toOption
  return s.clock == some (RoundClock.elimination 6 true) && overtime.turn == 7 && overtime.result.isNone &&
    shuffling.pending.head? == some (Frame.chanceBurnOut p) &&
    waiting.pending == [Frame.chooseBurnOut p, Frame.draw p 1, Frame.priority p] &&
    scored.result == some (GameResult.won [recipient]) && scored.pending.isEmpty &&
    scored.pointsOf recipient == waiting.pointsOf recipient + 1 &&
    scored.zone main == waiting.zone main && scored.zone (.player p .hand) == waiting.zone (.player p .hand) &&
    es == [Event.pointsGained recipient 1] && seen.isEmpty).getD false

-- Sudden death respects the Final Point restriction on Conquer, including the replacement draw.
#guard (do
  let s ← atTurn (.tournamentElimination .constructed .tiebreaker) 7
  let [first, second] := s.battlefields | none
  let p := s.active.getD ⟨0⟩
  let s := (s.gainPoints ⟨0⟩ (s.victoryScore - 1)).gainPoints ⟨1⟩ (s.victoryScore - 1)
  let (conquered, work, events) := scoreBf s p first true
  let (held, _, points) := scoreBf conquered p second false
  return work == [Frame.draw p 1] && (conquered.withTriggers events).result.isNone &&
    (held.withTriggers points).result == some (GameResult.won [p])).getD false

end RiftboundTest
