module

public import Riftbound.Invariant.Hands

/-!
# The turn structure

The phases of a turn come in a fixed order (invariant I9, roadmap.md), the turn player alternates in
a 1v1 game, and a concession ends the game with the other player winning (CR 651.1).
-/

@[expose] public section

namespace Riftbound

/-- The phases of a turn up to the Main Phase, in the order `beginTurn` lays them out. -/
def turnPhases : List Phase := [.awaken, .beginning, .channel, .draw, .main]

/-- The frames of a turn are its phases in order, then the turn player's priority (CR 315-316). -/
theorem turnFrames_eq (tp : PlayerId) :
    turnFrames tp = turnPhases.map Frame.phase ++ [Frame.priority tp] := rfl

/-- **I9 (phase order).** Each phase of a turn is followed by the next one (CR 314-317). -/
theorem turnPhases_chain : List.Pairwise (fun a b => a.next = b) [Phase.awaken, .beginning] ∧
    Phase.awaken.next = .beginning ∧ Phase.beginning.next = .channel ∧
    Phase.channel.next = .draw ∧ Phase.draw.next = .main ∧ Phase.main.next = .ending ∧
    Phase.ending.next = .awaken := by
  decide

/-- A phase frame sets the phase of the game unless the Draw Phase is skipped (CR 314-317). -/
theorem microStep_phase0 {s s' : GameState} {es : List Event} {ph : Phase} {rest : List Frame}
    (hp : s.pending = .phase ph :: rest) (hne : ph ≠ .setup)
    (h : microStep0 s = some (s', es)) :
    s'.phase = if ph == .draw && s.hasControlledMod (s.active.getD ⟨0⟩) .skipDrawPhase
      then s.phase else ph := by
  unfold microStep0 at h
  rw [hp] at h
  cases ph with
  | setup => exact absurd rfl hne
  | awaken => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | beginning =>
    dsimp only at h
    split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl)
  | channel => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | draw => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | main => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | ending => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl

/-- Detecting triggers preserves the phase set by the phase frame. -/
theorem microStep_phase {s s' : GameState} {es : List Event} {ph : Phase} {rest : List Frame}
    (hp : s.pending = .phase ph :: rest) (hne : ph ≠ .setup)
    (h : microStep s = some (s', es)) :
    s'.phase = if ph == .draw && s.hasControlledMod (s.active.getD ⟨0⟩) .skipDrawPhase
      then s.phase else ph := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  obtain ⟨q, result, hq⟩ := withTriggers_pending s2 (es ++ s.workTransitionEvents s2)
  have h2 := microStep_phase0 hp hne h0
  rw [hq]
  exact h2

/-- A game that is over accepts no answer (CR 193-196). -/
theorem step_over {fuel : Nat} {s : GameState} {a : Action} (h : s.result ≠ none) :
    step fuel s a = .error .illegal :=
  step_illegal (fun hl => h hl.1)

/-- **Concession** (CR 649-651). A legal concession ends the game immediately. -/
theorem step_concede {fuel : Nat} {s : GameState} {a : Action} {p : PlayerId}
    (hl : Legal s a) (hk : a.kind = .concede) (hp : a.actor = .player p) :
    step fuel s a = .ok ({ s with result := some (.won (s.concessionWinners p)), pending := [] }, []) := by
  have hc := hl.of_concede hk
  have noCost : s.actionDeathCostChoice a = none := by
    cases h : s.pending with
    | nil => simp [GameState.actionDeathCostChoice, h]
    | cons frame rest =>
      cases frame <;> simp [GameState.actionDeathCostChoice, GameState.actionKillCosts, h, hk]
  simp only [step, hl, ite_true, applyDeclaredAction, noCost, applyAction_concede hk hp]
  unfold advance
  cases fuel <;> simp

/-- Taking turns in turn order: the turn player at turn `k` (CR 118, 301). -/
def GameState.turnPlayerAt (s : GameState) (k : Nat) : PlayerId :=
  s.turnOrder.getD (k % s.playerCount) ⟨0⟩

/-- **The turn player alternates in a 1v1 game** (no extra turns yet): the player of one turn is not
the player of the next, once the turn order is an arrangement of the two players (CR 118, 301). -/
theorem turnPlayerAt_alternates {s : GameState} (hc : s.playerCount = 2)
    (hto : s.turnOrder.Perm (allPlayers s.playerCount)) (k : Nat) :
    s.turnPlayerAt k ≠ s.turnPlayerAt (k + 1) := by
  rw [hc] at hto
  have hlen : s.turnOrder.length = 2 := by
    have := hto.length_eq
    simpa [allPlayers] using this
  have hnd : s.turnOrder.Nodup := hto.nodup_iff.mpr (allPlayers_nodup 2)
  obtain ⟨a, b, hab⟩ : ∃ a b, s.turnOrder = [a, b] := by
    rcases h : s.turnOrder with _ | ⟨a, _ | ⟨b, _ | ⟨c, u⟩⟩⟩
    · rw [h] at hlen; simp at hlen
    · rw [h] at hlen; simp at hlen
    · exact ⟨a, b, rfl⟩
    · rw [h] at hlen; simp at hlen
  rw [hab] at hnd
  have hne : a ≠ b := by
    intro e
    subst e
    simp at hnd
  unfold GameState.turnPlayerAt
  rw [hc, hab]
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have h2 : (k + 1) % 2 = 1 := by omega
    rw [h, h2]
    simpa using hne
  · have h2 : (k + 1) % 2 = 0 := by omega
    rw [h, h2]
    simpa using hne.symm

/-- Seats that each lead all their opponents belong to the same winning side (CR 323.1, 491.6). -/
theorem win_side_unique {s : GameState} {p q : PlayerId}
    (pSeat : p ∈ s.participatingSeats) (qSeat : q ∈ s.participatingSeats)
    (pLeads : ∀ other ∈ s.participatingSeats, s.config.mode.sameSide p other = false →
      s.pointsOf other < s.pointsOf p)
    (qLeads : ∀ other ∈ s.participatingSeats, s.config.mode.sameSide q other = false →
      s.pointsOf other < s.pointsOf q) :
    s.config.mode.sameSide p q = true := by
  cases side : s.config.mode.sameSide p q
  · have reverse : s.config.mode.sameSide q p = false := by
      cases reverse : s.config.mode.sameSide q p
      · rfl
      · have seats : s.config.mode.scoringSeat q = s.config.mode.scoringSeat p :=
          of_decide_eq_true reverse
        simp [Mode.sameSide, seats] at side
    have hp := pLeads q qSeat side
    have hq := qLeads p pSeat reverse
    omega
  · rfl

/-- A seat that leads all its opponents belongs to the side the engine declares the winner. -/
theorem GameState.winner_sameSide {s : GameState} {p winner : PlayerId}
    (result : s.winner = some winner) (seat : p ∈ s.participatingSeats)
    (leads : ∀ other ∈ s.participatingSeats, s.config.mode.sameSide p other = false →
      s.pointsOf other < s.pointsOf p) : s.config.mode.sameSide p winner = true := by
  have member : winner ∈ s.participatingSeats := List.mem_of_find?_eq_some result
  exact win_side_unique seat member leads (winner_spec result).2

end Riftbound

end
