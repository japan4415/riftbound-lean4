module

public import Riftbound.Rules.Frames

/-!
# Legality

The specification of which answers are legal, written decision by decision from the Core Rules
(design.md §6.3). `Legal` reads the state and the frame on top of the stack; it does not use `step`
or `applyAction`. The question is the frame; the candidates are computed here from the board.

Chance answers are legal when they are an arrangement of what the rules shuffle, as a
permutation (`List.Perm`): they are not enumerated (design.md §6.4).
-/

@[expose] public section

namespace Riftbound

/-- The players of a game with `n` players, in seat order. -/
def allPlayers (n : Nat) : List PlayerId := (List.range n).map (fun i => ⟨i⟩)

/-- A player is among the players of the game exactly when the seat number is below the count. -/
@[simp] theorem mem_allPlayers (n : Nat) (p : PlayerId) : p ∈ allPlayers n ↔ p.n < n := by
  simp only [allPlayers, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro h; exact ⟨p.n, h, by cases p; rfl⟩

/-- `a` is a legal answer to the frame on top of the stack. -/
def Legal (s : GameState) (a : Action) : Prop :=
  match s.pending, a.kind with
  -- the shuffle of a zone (CR 114): an arrangement of its contents
  | .chanceShuffle z :: _, .arrange l =>
    a.actor = .chance ∧ z.Valid s.playerCount ∧ l.Perm (s.zone z)
  -- the random Battlefield of a player (CR 487.5): one of the player's Battlefields
  | .chanceBattlefield p :: _, .pick i =>
    a.actor = .chance ∧ i < (s.zone (.player p .outOfGame)).length
  -- the turn order (CR 115): an arrangement of the players
  | .chanceTurnOrder :: _, .arrangePlayers l =>
    a.actor = .chance ∧ l.Perm (allPlayers s.playerCount)
  -- the mulligan (CR 117): set aside up to two cards of the hand, or finish
  | .mulligan p n :: _, .mulliganPick c =>
    a.actor = .player p ∧ c ∈ s.zone (.player p .hand) ∧ n < 2
  | .mulligan p _ :: _, .mulliganDone => a.actor = .player p
  -- the order of a Recycle to the Main Deck (CR 417.5): an arrangement of the cards set aside
  | .chanceRecycle p :: _, .arrange l =>
    a.actor = .chance ∧ l.Perm (s.zone (.player p .setAside))
  -- the order of the Trash in a Burn Out (CR 432.2.b): an arrangement of the Trash
  | .chanceBurnOut p :: _, .arrange l =>
    a.actor = .chance ∧ l.Perm (s.zone (.player p .trash))
  -- the opponent of a Burn Out (CR 432.2.c): a player other than the one who burned out
  | .chooseBurnOut p :: _, .burnOutTarget opp =>
    a.actor = .player p ∧ opp ≠ p ∧ opp.n < s.playerCount
  | _, _ => False

instance Legal.decidable (s : GameState) (a : Action) : Decidable (Legal s a) := by
  unfold Legal
  split <;> infer_instance

end Riftbound

end
