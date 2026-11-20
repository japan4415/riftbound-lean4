module

public import Riftbound.Core.Mode
public import Riftbound.Tournament.Format

/-!
# The rules of a game

Which rules a game is played under. It is stored in the initial state and never changes during
the game (design.md §6.1).
-/

@[expose] public section

namespace Riftbound

/-- Which rules apply. -/
inductive RuleSet where
  /-- The Core Rules only. -/
  | coreOnly
  /-- The Tournament Rules, which win over the Core Rules (TR 104.1). -/
  | tournament (format : Format)
deriving DecidableEq, Repr

/-- The rules of a game. -/
structure GameConfig where
  /-- Core Rules only, or a tournament format. -/
  ruleSet : RuleSet
  /-- The game mode (CR 483-491). -/
  mode : Mode
deriving DecidableEq, Repr

/-- A configuration that can be played. For now: at least two players. Which pairs of mode and
format the Tournament Rules provide procedures for is to be checked against TR 600
(tournament-model.md §7). -/
def GameConfig.Valid (c : GameConfig) : Prop := 2 ≤ c.mode.players

instance GameConfig.decidableValid (c : GameConfig) : Decidable c.Valid := by unfold GameConfig.Valid; infer_instance

end Riftbound

end
