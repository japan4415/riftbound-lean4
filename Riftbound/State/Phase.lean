module

public import Riftbound.Core.Ids

/-!
# Phases and the result of a game

The phases of a turn (CR 314-317) and how a game ends (CR 193-196, 649-651).
-/

@[expose] public section

namespace Riftbound

/-- The phase the game is in. `setup` is before the first turn; the others are the phases of a
turn in order (CR 314-317). The Beginning Step and Scoring Step (CR 315.2), and the Ending Step
and Expiration Step (CR 317), are not told apart yet. -/
inductive Phase where
  /-- Before the first turn (CR 110-118). -/
  | setup
  /-- Awaken Phase (CR 315.1). -/
  | awaken
  /-- Beginning Phase (CR 315.2). -/
  | beginning
  /-- Channel Phase (CR 315.3). -/
  | channel
  /-- Draw Phase (CR 315.4). -/
  | draw
  /-- Main Phase (CR 316). -/
  | main
  /-- Ending Phase (CR 317). -/
  | ending
deriving DecidableEq, Repr

/-- The phase after this one; the Ending Phase is followed by the next turn's Awaken Phase. -/
def Phase.next : Phase → Phase
  | .setup => .awaken
  | .awaken => .beginning
  | .beginning => .channel
  | .channel => .draw
  | .draw => .main
  | .main => .ending
  | .ending => .awaken

/-- How a game ended. Core Rules only have wins; draws come from the Tournament Rules
(design.md §6.1). -/
inductive GameResult where
  /-- The winners: one player, or a team in 2v2 (CR 491.6.a). -/
  | won (winners : List PlayerId)
  /-- A draw (TR 408.2.b, 410.1, 505.6). -/
  | draw
deriving DecidableEq, Repr

end Riftbound

end
