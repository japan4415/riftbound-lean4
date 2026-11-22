module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: the judge's draw (TR 410.1, 505.6) and the match concession (TR 410.2)
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def atTurnJ (rules : RuleSet) (n : Nat) : Option GameState :=
  match GameState.initial db { ruleSet := rules, mode := Mode.duel } [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 n 4000 (Rng.ofSeed 1) s with
      | .ok s => some s
      | .error _ => none

meta def callTimeJ : Action := ⟨.clock, .timeCalled⟩

meta def declare : Action := ⟨.judge, .declareDraw⟩

-- the judge declares a draw under the Tournament Rules: the game is over, with nothing left, even
-- when a player is ahead
#guard match atTurnJ (.tournament .constructed) 2 with
  | some s =>
    match step 100 (s.gainPoints ⟨0⟩ 3) declare with
    | .ok (s1, _) =>
      s1.result == some .draw && s1.pending.isEmpty && s1.turn == s.turn &&
      (step 100 s1 declare).toOption.isNone && (step 100 s1 callTimeJ).toOption.isNone &&
      (legalActions s1).isEmpty
    | .error _ => false
  | none => false

-- neither a player nor the clock declares a draw, and the Core Rules have no judge
#guard match atTurnJ (.tournament .constructed) 2 with
  | some s =>
    (step 100 s ⟨.player ⟨0⟩, .declareDraw⟩).toOption.isNone &&
    (step 100 s ⟨.clock, .declareDraw⟩).toOption.isNone
  | none => false
#guard match atTurnJ .coreOnly 2 with
  | some s => (step 100 s declare).toOption.isNone
  | none => false

-- a draw can be declared in any open question, here before the first turn begins
#guard match GameState.initial db { ruleSet := .tournament .constructed, mode := Mode.duel }
    [goodDeck, goodDeck] with
  | some s => (step 100 s declare).toOption.any (fun r => r.1.result == some .draw)
  | none => false

-- a conceded match goes to the other player; an agreed draw of the match is a draw (TR 410.2)
#guard MatchState.concedeMatch ⟨0⟩ == .won ⟨1⟩
#guard MatchState.concedeMatch ⟨1⟩ == .won ⟨0⟩
#guard MatchState.agreedDrawMatch == .draw

end RiftboundTest
