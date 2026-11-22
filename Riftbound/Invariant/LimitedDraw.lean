module

public import Riftbound.Invariant.Draw

/-!
# The extra draw of Limited (TR 602.4.a.5.b)

In a Limited format a deck may go without a Legend or a Chosen Champion. A player whose deck has
no Legend or no Chosen Champion draws 1 card at the start of their first Beginning Phase, and 1
only, even when the deck has neither. This is the first rule in which the format changes the course
of the game: the engine reads the rules of the game (`GameConfig.ruleSet`) and the zones of the
player.

Reading chosen: the first Beginning Phase is the player's own, so every player of such a deck draws
once, in the first round of turns. The wording of the rule (the first Beginning Phase of each game)
could also mean the first player only; the Tournament Rules' text is not in the repository.
-/

@[expose] public section

namespace Riftbound

/-- **Only Limited formats give the draw** (TR 602.4.a.5.b): under the Core Rules, and in
Constructed, nobody draws more. -/
theorem extraDraws_zero_of_not_limited {s : GameState} (h : s.config.ruleSet.isLimited = false)
    (p : PlayerId) : s.extraDraws p = 0 := by
  unfold GameState.extraDraws
  simp [h]

/-- **At most 1 card** (TR 602.4.a.5.b): a deck with neither a Legend nor a Chosen Champion draws 1
too. -/
theorem extraDraws_le_one (s : GameState) (p : PlayerId) : s.extraDraws p ≤ 1 := by
  unfold GameState.extraDraws
  split <;> omega

/-- **Who draws, and when** (TR 602.4.a.5.b): the draw is 1 exactly in a Limited format, in the
first round of turns, for a player whose zone of Legend or of Chosen Champion is empty. -/
theorem extraDraws_eq_one_iff (s : GameState) (p : PlayerId) :
    s.extraDraws p = 1 ↔ s.config.ruleSet.isLimited = true ∧ s.turn ≤ s.playerCount ∧
      ((s.zone (.player p .legendZone)).isEmpty = true ∨
        (s.zone (.player p .championZone)).isEmpty = true) := by
  unfold GameState.extraDraws
  by_cases h1 : s.config.ruleSet.isLimited = true <;> by_cases h2 : s.turn ≤ s.playerCount <;>
    by_cases h3 : (s.zone (.player p .legendZone)).isEmpty = true <;>
    by_cases h4 : (s.zone (.player p .championZone)).isEmpty = true <;> simp_all

/-- **No draw after the first round** (TR 602.4.a.5.b): from the turn after the last first turn, the
draw is 0. -/
theorem extraDraws_zero_late {s : GameState} (h : s.playerCount < s.turn) (p : PlayerId) :
    s.extraDraws p = 0 := by
  unfold GameState.extraDraws
  simp only [Nat.not_le.mpr h]
  simp

end Riftbound

end
