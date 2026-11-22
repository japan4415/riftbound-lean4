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

/-- The Tournament Rules are in use. -/
def RuleSet.isTournament : RuleSet → Bool
  | .coreOnly => false
  | .tournament _ => true

/-- The Tournament Rules are in use, with a Limited format (TR 602). -/
def RuleSet.isLimited : RuleSet → Bool
  | .coreOnly => false
  | .tournament f => f.isLimited

/-- The smallest Main Deck of the Limited format in use (TR 602.4): `none` when no Limited format
is in use. -/
def RuleSet.limitedMinMain : RuleSet → Option Nat
  | .coreOnly => none
  | .tournament f => f.limitedMinMain

/-- The rules of a game. -/
structure GameConfig where
  /-- Core Rules only, or a tournament format. -/
  ruleSet : RuleSet
  /-- The game mode (CR 483-491). -/
  mode : Mode
deriving DecidableEq, Repr

/-- A configuration that can be played. For now: at least two players, and a deck holds at least
one Battlefield, since one is picked at random from each (CR 487.5). Which pairs of mode and
format the Tournament Rules provide procedures for is still to be checked
in the 600 series of the Tournament Rules (tournament-model.md §7). -/
def GameConfig.Valid (c : GameConfig) : Prop :=
  2 ≤ c.mode.players ∧ 1 ≤ c.mode.deckBattlefields

instance GameConfig.decidableValid (c : GameConfig) : Decidable c.Valid := by
  unfold GameConfig.Valid; infer_instance

end Riftbound

end
