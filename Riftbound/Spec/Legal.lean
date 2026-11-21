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
def LegalFrame (s : GameState) (a : Action) : Prop :=
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
  -- the turn player has priority in the Main Phase (CR 312, 316): passing ends the phase (CR 305)
  | .priority p :: _, .pass => a.actor = .player p
  -- a Basic Rune of the player's on the Base adds a resource (CR 164.2, 430)
  | .priority p :: _, .runeAbility c ab =>
    a.actor = .player p ∧ c ∈ s.zone (.player p .base) ∧ runeUsable s p c ab = true
  -- a Unit or a Gear of the player's hand, or a Spell with its targets, paid for from the Rune
  -- Pool, in the Main Phase (CR 349-359)
  | .priority p :: _, .playCard c pay ts =>
    a.actor = .player p ∧ c ∈ s.zone (.player p .hand) ∧ PlayOk s p c pay ts
  -- a Standard Move of a Unit of the player's, in the Main Phase (CR 144)
  | .priority p :: _, .standardMove u d => a.actor = .player p ∧ moveOk s p u d = true
  -- the player with priority passes while the Chain holds a Spell (CR 311-313)
  | .chainPass p _ :: _, .pass => a.actor = .player p
  -- the player with Focus passes in a Showdown (CR 347-348)
  | .showdown _ q _ :: _, .pass => a.actor = .player q
  -- the next Unit to be given lethal damage, Tank Units first (CR 467.2.c, 815)
  | .assign bf _ side acc _ :: _, .assignPick u =>
    a.actor = .player side ∧ s.pickOk bf side acc u = true
  -- every Unit of the other side is named (CR 467.2.c)
  | .assign bf _ side acc _ :: _, .assignDone =>
    a.actor = .player side ∧ s.doneOk bf side acc = true
  | _, _ => False

instance LegalFrame.decidable (s : GameState) (a : Action) : Decidable (LegalFrame s a) := by
  unfold LegalFrame
  split <;> infer_instance

/-- A player concedes (CR 649-650): at any time, whatever question is open. In a 1v1 game the
other player wins (CR 651.1); with more players a concession removes the player from the game
(CR 651.2, 652), which comes with the multiplayer rules (roadmap.md, M9). -/
def LegalConcede (s : GameState) (a : Action) : Prop :=
  a.kind = .concede ∧
    match a.actor with
    | .player p => p.n < s.playerCount ∧ s.playerCount = 2
    | _ => False

instance LegalConcede.decidable (s : GameState) (a : Action) : Decidable (LegalConcede s a) := by
  unfold LegalConcede
  split <;> infer_instance

/-- A legal concession is made by a player of the game, in a 1v1 game. -/
theorem LegalConcede.actor {s : GameState} {a : Action} (h : LegalConcede s a) :
    ∃ p, a.actor = .player p ∧ p.n < s.playerCount ∧ s.playerCount = 2 := by
  obtain ⟨-, h2⟩ := h
  cases hac : a.actor with
  | player p =>
    rw [hac] at h2
    exact ⟨p, rfl, h2⟩
  | chance => rw [hac] at h2; exact h2.elim
  | clock => rw [hac] at h2; exact h2.elim
  | judge => rw [hac] at h2; exact h2.elim

/-- `a` is a legal answer: the game is not over, and the answer is to the open question or a
concession. -/
def Legal (s : GameState) (a : Action) : Prop :=
  s.result = none ∧ (LegalFrame s a ∨ LegalConcede s a)

instance Legal.decidable (s : GameState) (a : Action) : Decidable (Legal s a) := by
  unfold Legal
  infer_instance

/-- A legal answer that is not a concession answers the open question. -/
theorem Legal.frame {s : GameState} {a : Action} (h : Legal s a) (hk : a.kind ≠ .concede) :
    LegalFrame s a := by
  rcases h.2 with h2 | h2
  · exact h2
  · exact absurd h2.1 hk

/-- A legal concession. -/
theorem Legal.of_concede {s : GameState} {a : Action} (h : Legal s a) (hk : a.kind = .concede) :
    LegalConcede s a := by
  rcases h.2 with h2 | h2
  · -- a frame answer never concedes
    exfalso
    unfold LegalFrame at h2
    rw [hk] at h2
    split at h2 <;> first | exact h2.elim | simp_all
  · exact h2

end Riftbound

end
