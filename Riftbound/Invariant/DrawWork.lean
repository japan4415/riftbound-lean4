module

public import Riftbound.Invariant.WorkPrefix

/-!
# Finite draw batches (I12)

A draw frame consumes one count for each available card. An exhausted deck asks for a Burn Out
answer. The final frame emits the event for the whole batch.
-/

@[expose] public section

namespace Riftbound

/-- The draw finishes its batch or pauses for Burn Out within the requested count plus one
work step, through the rule dispatcher. -/
theorem rawDraw_bound (s : GameState) (p : PlayerId) (count : Nat)
    (startingHand : Option Nat) (rest : List Frame)
    (pending : s.pending = .draw p count startingHand :: rest) :
    ∃ t used events, used ≤ count + 1 ∧ RawWorkPrefix s t used events ∧
      (t.pending = rest ∨
        ∃ remaining hand, t.pending = .chanceBurnOut p :: .draw p (remaining + 1) hand :: rest) := by
  induction count generalizing s startingHand with
  | zero =>
    let next := { s with pending := rest }
    have rule : microStep0 s = some (next, startingHand.toList.map (.drewGroup p)) := by
      simp only [microStep0, pending, next]
    exact ⟨next, 1, _, Nat.le_refl _, .single pending rfl rule, Or.inl rfl⟩
  | succ count ih =>
    cases drawn : drawOne s p with
    | none =>
      let next := { s with pending := .chanceBurnOut p :: .draw p (count + 1) startingHand :: rest }
      have rule : microStep0 s = some (next, []) := by
        simp only [microStep0, pending, drawn, next]
      exact ⟨next, 1, [], by omega, .single pending rfl rule, Or.inr ⟨count, startingHand, rfl⟩⟩
    | some result =>
      obtain ⟨board, effects⟩ := result
      let initial := startingHand <|> some ((s.zone (.player p .hand)).length)
      let next := { board.noteDraw p with pending := .draw p count initial :: rest }
      have rule : microStep0 s = some (next, effects ++ [.drew p]) := by
        simp only [microStep0, pending, drawn, next, initial]
      obtain ⟨t, used, events, bound, work, done⟩ := ih next initial rfl
      exact ⟨t, used + 1, (effects ++ [.drew p]) ++ events, by omega,
        .next pending rfl rule work, done⟩

/-- In any phase, the engine consumes at most the requested number of draws plus one work
step before reaching the rest of the stack, asking for Burn Out or applying an observer
that changes a transition. After an observer change its new stack needs its own bound. -/
theorem advance_draw_bound (s : GameState) (p : PlayerId) (count : Nat)
    (startingHand : Option Nat) (rest : List Frame)
    (pending : s.pending = .draw p count startingHand :: rest) :
    ∃ t used events, used ≤ count + 1 ∧ AdvancePrefix s t used events ∧
      (t.pending = rest ∨
        (∃ remaining hand, t.pending = .chanceBurnOut p :: .draw p (remaining + 1) hand :: rest) ∨
        ∃ before expected, WorkObserverChange before expected t) := by
  obtain ⟨t, used, events, bound, work, done⟩ := rawDraw_bound s p count startingHand rest pending
  rcases work.observe with reached | ⟨before, expected, actual, steps, emitted, changed, _, cut, reached, _⟩
  · exact ⟨t, used, events, bound, reached, done.imp_right Or.inl⟩
  · exact ⟨actual, steps, emitted, Nat.le_trans cut bound, reached, Or.inr (Or.inr ⟨before, expected, changed⟩)⟩

end Riftbound

end
