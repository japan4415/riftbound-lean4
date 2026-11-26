module

public import Riftbound.Core.Ids

/-!
# Game modes

The data part of a game mode (CR 483-491): what deck building and the setup need.
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

/-- Four seats in two teams (CR 491). A and B of the first team have seats 0 and 1,
and A and B of the second team have seats 2 and 3 (TR 603.7). -/
def Mode.teamDuel : Mode :=
  { players := 4, victoryScore := 11, battlefieldsInPlay := 3, deckBattlefields := 3 }

/-- The mode uses shared team scores and joint wins and losses. -/
def Mode.isTeamDuel (mode : Mode) : Bool := mode == Mode.teamDuel

/-- The seat under which a player's points are stored. Both teammates look up the same entry. -/
def Mode.scoringSeat (mode : Mode) (p : PlayerId) : PlayerId :=
  if mode.isTeamDuel && p.n < 4 then ⟨p.n / 2 * 2⟩ else p

/-- Whether two seats have the same side. A solo player constitutes a side. -/
def Mode.sameSide (mode : Mode) (p q : PlayerId) : Bool :=
  mode.scoringSeat p == mode.scoringSeat q

/-- The seats winning or losing together with `p`, in seat order. -/
def Mode.sideSeats (mode : Mode) (p : PlayerId) : List PlayerId :=
  if mode.isTeamDuel && p.n < 4 then
    let first := mode.scoringSeat p
    [first, ⟨first.n + 1⟩]
  else [p]

/-- The teams alternate and A of each team precedes its B (TR 603.7). -/
def Mode.teamTurnOrder (team0First : Bool) : List PlayerId :=
  if team0First then [⟨0⟩, ⟨2⟩, ⟨1⟩, ⟨3⟩] else [⟨2⟩, ⟨0⟩, ⟨3⟩, ⟨1⟩]

/-- The number of sides whose players can all be eliminated together supports a direct finish. -/
def Mode.hasTwoSides (mode : Mode) : Bool := mode.players == 2 || mode.isTeamDuel

/-- Solo modes keep an individual score for every seat. -/
@[simp] theorem Mode.scoringSeat_eq_of_not_team {mode : Mode} (h : mode.isTeamDuel = false)
    (p : PlayerId) : mode.scoringSeat p = p := by simp [Mode.scoringSeat, h]

/-- The seat relation is reflexive, including modes with a one-seat side. -/
@[simp] theorem Mode.sameSide_self (mode : Mode) (p : PlayerId) : mode.sameSide p p = true := by
  simp [Mode.sameSide]

end Riftbound

end
