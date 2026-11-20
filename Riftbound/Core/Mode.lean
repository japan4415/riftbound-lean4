module

/-!
# Game modes

The data part of a game mode (CR 483-491): what deck building and the setup need.
Only 1v1 Duel is defined for now (design.md §12, Q2); other modes arrive in milestone M9.
-/

@[expose] public section

namespace Riftbound

/-- The data of a game mode (CR 483-491). -/
structure Mode where
  /-- Number of players. -/
  players : Nat
  /-- Points needed to win (CR 194.3). -/
  victoryScore : Nat
  /-- Number of Battlefields in play. -/
  battlefieldsInPlay : Nat
  /-- Number of Battlefields each deck holds (CR 103.5). -/
  deckBattlefields : Nat
deriving DecidableEq, Repr

/-- 1v1 Duel (CR 487): two players, Victory Score 8, two Battlefields in play; each player
brings three Battlefields and one is chosen at random (CR 487.5). -/
def Mode.duel : Mode :=
  { players := 2, victoryScore := 8, battlefieldsInPlay := 2, deckBattlefields := 3 }

end Riftbound

end
