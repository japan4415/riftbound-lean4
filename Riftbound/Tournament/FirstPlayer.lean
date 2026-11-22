module

public import Riftbound.Spec.Legal
public import Riftbound.Tournament.Match

/-!
# Who goes first (TR 407)

The match decides who goes first in a game (`MatchState.nextOrder`, `Order.first`). The engine takes
the order from the answer to the question `chanceTurnOrder`, which comes from outside the game
(CR 115): any arrangement of the players is legal. So the choice of the player who chooses (TR 407)
reaches the game as that answer. These are the facts that tie the two: the answer for a chosen
first player is legal, it is the turn order of the game, and the first turn is the chosen player's.

Model decision: the answer is given by the chance actor, like a draw would be, not by the player who
chooses. The player's choice is made outside the engine, in the match.
-/

@[expose] public section

namespace Riftbound

/-- **The answer for a chosen first player is legal** (TR 407): the arrangement that puts a player
of a 1v1 game first is an answer to the turn-order question (CR 115). -/
theorem turnOrder_answer_legal {s : GameState} {rest : List Frame}
    (hp : s.pending = .chanceTurnOrder :: rest) (h2 : s.playerCount = 2) {f : PlayerId}
    (hf : f.n < 2) :
    LegalFrame s ⟨.chance, .arrangePlayers (MatchState.turnOrderOf f)⟩ := by
  unfold LegalFrame
  rw [hp]
  refine ⟨rfl, ?_⟩
  rw [h2]
  exact MatchState.turnOrderOf_perm hf

/-- The answer is the turn order of the game. -/
theorem turnOrder_answer_sets {s s' : GameState} {rest : List Frame} {es : List Event}
    {l : List PlayerId} (hp : s.pending = .chanceTurnOrder :: rest)
    (h : applyFrame0 s ⟨.chance, .arrangePlayers l⟩ = some (s', es)) : s'.turnOrder = l := by
  unfold applyFrame0 at h
  rw [hp] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rfl

/-- **The first turn is the chosen player's, and the second turn the other player's** (TR 407):
with the turn order of the chosen first player, in a 1v1 game (CR 301). -/
theorem first_turns {s : GameState} {f : PlayerId}
    (ho : s.turnOrder = MatchState.turnOrderOf f) (h2 : s.playerCount = 2) :
    (s.turn = 0 → s.nextTurnPlayer = f) ∧
      (s.turn = 1 → s.nextTurnPlayer = MatchState.other f) := by
  unfold GameState.nextTurnPlayer
  rw [ho, h2]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp [h, MatchState.turnOrderOf]

end Riftbound

end
