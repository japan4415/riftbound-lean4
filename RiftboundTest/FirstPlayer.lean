module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: who goes first (TR 407)
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def q0 : PlayerId := ⟨0⟩
meta def q1 : PlayerId := ⟨1⟩

-- the player who chooses, and who goes first (TR 407.1, 407.2, 407.4)
#guard (MatchState.Order.chance.first q0 true) == q0
#guard (MatchState.Order.chance.first q0 false) == q1
#guard (MatchState.Order.chance.first q1 false) == q0
#guard (MatchState.Order.loserChooses q1).first q0 true == q1
#guard (MatchState.Order.loserChooses q1).first q0 false == q0
#guard (MatchState.Order.same q1).first q0 true == q1
#guard (MatchState.Order.same q1).first q0 false == q1
#guard MatchState.turnOrderOf q1 == [q1, q0]

/-- The game up to the question about the turn order. -/
meta def toTurnOrder : Nat → Rng → GameState → Option GameState
  | 0, _, _ => none
  | n + 1, r, s =>
    match s.pending with
    | .chanceTurnOrder :: _ => some s
    | _ =>
      match autoAnswer r s with
      | none => none
      | some (a, r') =>
        match step 100 s a with
        | .ok (s', _) => toTurnOrder n r' s'
        | .error _ => none

/-- Answer the question with the order, and play to the first turn. -/
meta def firstTurn (order : List PlayerId) : Option GameState :=
  match GameState.initial db { ruleSet := .tournament .constructed, mode := Mode.duel }
      [goodDeck, goodDeck] with
  | none => none
  | some s0 =>
    match toTurnOrder 1000 (Rng.ofSeed 1) s0 with
    | none => none
    | some s =>
      match step 100 s ⟨.chance, .arrangePlayers order⟩ with
      | .error _ => none
      | .ok (s1, _) =>
        match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s1 with
        | .ok s2 => some s2
        | .error _ => none

-- the player the match chose goes first, and the other player second (TR 407)
#guard match firstTurn (MatchState.turnOrderOf q1) with
  | some s => s.turnOrder == [q1, q0] && s.active == some q1 && s.turn == 1
  | none => false
#guard match firstTurn (MatchState.turnOrderOf q0) with
  | some s => s.turnOrder == [q0, q1] && s.active == some q0 && s.turn == 1
  | none => false

-- an order that is not an arrangement of the two players is refused
#guard match GameState.initial db { ruleSet := .tournament .constructed, mode := Mode.duel }
    [goodDeck, goodDeck] with
  | some s0 =>
    match toTurnOrder 1000 (Rng.ofSeed 1) s0 with
    | some s => (step 100 s ⟨.chance, .arrangePlayers [q0, q0]⟩).toOption.isNone &&
        (step 100 s ⟨.player q0, .arrangePlayers [q0, q1]⟩).toOption.isNone
    | none => false
  | none => false

end RiftboundTest
