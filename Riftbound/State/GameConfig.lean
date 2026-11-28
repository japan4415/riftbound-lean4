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

/-- The situation when a timed single-elimination game starts (TR 408.4). -/
inductive EliminationGame where
  /-- A game that may receive a time call. The match score before this game determines whether
  tied points can lead to sudden death after the three additional turns. -/
  | regular (tiedWins : Bool)
  /-- A new game is required after time has been called with tied game wins. -/
  | tiebreaker
deriving DecidableEq, Repr

/-- Which rules apply. -/
inductive RuleSet where
  /-- The Core Rules only. -/
  | coreOnly
  /-- The Tournament Rules, which win over the Core Rules (TR 104.1). -/
  | tournament (format : Format)
  /-- The Tournament Rules with the single-elimination end-of-match procedure (TR 408.4). -/
  | tournamentElimination (format : Format) (game : EliminationGame)
deriving DecidableEq, Repr

/-- The tournament format, shared by Swiss and single-elimination matches. -/
def RuleSet.tournamentFormat : RuleSet → Option Format
  | .coreOnly => none
  | .tournament f | .tournamentElimination f _ => some f

/-- The Tournament Rules are in use. -/
def RuleSet.isTournament : RuleSet → Bool
  | .coreOnly => false
  | .tournament _ | .tournamentElimination .. => true

/-- The Tournament Rules are in use, with a Limited format (TR 602). -/
def RuleSet.isLimited : RuleSet → Bool
  | .coreOnly => false
  | .tournament f | .tournamentElimination f _ => f.isLimited

/-- The smallest Main Deck of the Limited format in use (TR 602.4): `none` when no Limited format
is in use. -/
def RuleSet.limitedMinMain : RuleSet → Option Nat
  | .coreOnly => none
  | .tournament f | .tournamentElimination f _ => f.limitedMinMain

/-- A called clock remembers the last scheduled turn and the procedure at that deadline. -/
inductive RoundClock where
  /-- The Swiss result is determined at the end of the additional turns (TR 408.2). -/
  | swiss (lastTurn : Nat)
  /-- One point of lead is sufficient. If game wins were tied, tied points lead to sudden death
  (TR 408.4.c). -/
  | elimination (lastTurn : Nat) (tiedWins : Bool)
deriving DecidableEq

/-- The last scheduled turn, before any sudden-death turns. -/
def RoundClock.lastTurn : RoundClock → Nat
  | .swiss n | .elimination n _ => n

/-- Whether tied points can require play beyond the scheduled turns. -/
def RoundClock.allowsSuddenDeath : RoundClock → Bool
  | .swiss _ => false
  | .elimination _ tiedWins => tiedWins

/-- Swiss clocks retain the original numeric representation used by replay checkpoints. -/
instance : Repr RoundClock where
  reprPrec
    | .swiss n, prec => reprPrec n prec
    | .elimination n tiedWins, prec =>
      Repr.addAppParen (Std.Format.group ("RoundClock.elimination" ++ Std.Format.line ++
        repr n ++ Std.Format.line ++ repr tiedWins)) prec

/-- The time call made during a game leaves its current turn and three further turns
(TR 408.2, 408.4.c). -/
def RuleSet.callClock (rules : RuleSet) (turn : Nat) : RoundClock :=
  match rules with
  | .tournamentElimination _ (.regular tied) => .elimination (turn + 3) tied
  | .tournamentElimination _ .tiebreaker => .elimination (turn + 3) true
  | _ => .swiss (turn + 3)

/-- A time call always names the third turn after the current turn. -/
@[simp] theorem RuleSet.callClock_lastTurn (rules : RuleSet) (turn : Nat) :
    (rules.callClock turn).lastTurn = turn + 3 := by
  cases rules with
  | tournamentElimination _ game => cases game <;> rfl
  | _ => rfl

/-- A new game started after time is called gets the first turn plus five additional turns
(TR 408.4.d). -/
def RuleSet.openingClock : RuleSet → Option RoundClock
  | .tournamentElimination _ .tiebreaker => some (.elimination 6 true)
  | _ => none

/-- The rules of a game. -/
structure GameConfig where
  /-- Core Rules only, or a tournament format. -/
  ruleSet : RuleSet
  /-- The game mode (CR 483-491). -/
  mode : Mode
  /-- Tournament card eligibility, when provided with the game (CR 762) (TR 601.2-3, 602.1). -/
  formatLegality : Option LegalityEnv := none
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
