module

public import Riftbound.Invariant.ObservedWork

/-!
# Cleanup across immediate Adds (I12)

The rule's board measure decreases for each repeated Cleanup, even with immediate Adds
between iterations. A settled Cleanup leaves its continuation or stages a decision.
-/

@[expose] public section

namespace Riftbound

private theorem cleanupFrame_route (s : GameState) (rest : List Frame) (wf : s.WF)
    (pending : s.pending = .cleanup :: rest) :
    let raw := (cleanupFrame s rest).1
    raw.pending.head?.all (fun f => !f.isWork) = true ∨ raw.pending = rest ∨
      (raw.pending = .cleanup :: rest ∧ MeasLt raw.cleanupMeasure s.cleanupMeasure) := by
  have reinstall (t : GameState) (safe : Safe s t) : { t with pending := .cleanup :: rest } = t := by
    rw [← safe.same.pending.trans pending]
  unfold cleanupFrame
  cases winner : s.winner with
  | some p => exact Or.inl rfl
  | none =>
    cases choice : cleanupDeathBanishChoice s with
    | some r =>
      obtain ⟨src, player, first, other⟩ := r
      exact Or.inl rfl
    | none =>
      cases group : cleanupResolveDeathGroup s with
      | some r =>
        refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        dsimp only
        rw [reinstall _ (cleanupResolveDeathGroup_safe group)]
        exact cleanupResolveDeathGroup_decreases wf group
      | none =>
        cases one : cleanupStep s with
        | some r =>
          obtain ⟨board, events⟩ := r
          refine Or.inr (Or.inr ⟨rfl, ?_⟩)
          dsimp only
          rw [reinstall _ (cleanupStep_safe (s' := board) (es := events) one)]
          exact cleanupStep_lt wf one
        | none =>
          cases staged : s.stagedShowdowns rest with
          | nil => exact Or.inr (Or.inl rfl)
          | cons entry more =>
            obtain ⟨bf, player⟩ := entry
            dsimp only
            split <;> exact Or.inl rfl

/-- Resolve Cleanup and every immediate Add it detects, including when it opens a decision.
Ordinary triggers waiting behind Cleanup stay in the continuation tracked by `keeps`. -/
theorem advance_cleanup_with_adds {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = .cleanup :: rest)
    (keeps : List Frame → Prop) (base : keeps rest)
    (insertion : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun f => !f.isWork) = true ∨
        (keeps t.pending ∧ t.WF ∧ t.cards = s.cards)) := by
  revert wf reads rest
  apply (InvImage.wf GameState.cleanupMeasure MeasLt.wf).induction s
  intro state ih rest wellFormed reads pending base
  let raw := cleanupFrame state rest
  let notices := raw.2 ++ state.workTransitionEvents raw.1
  let observed := raw.1.withTriggers notices
  have work : workStep state = some (observed, raw.2) := by
    simp only [workStep, pending, microStep, microStep0, raw, Option.map_some, observed, notices]
  have known : raw.1.cards = state.cards := cleanupFrame_cards state rest
  have rawWF : raw.1.WF := (cleanupFrame_preservesBoard state rest wellFormed).1
  obtain ⟨mid, used, events, observedPath, midWF, observedCards, observedStack, measured⟩ :=
    advance_observed_work_measured raw.1 notices rawWF (known ▸ reads)
  have path := observedPath.prepend pending rfl work
  have cards : mid.cards = state.cards := observedCards.trans known
  have positive : 0 < used + 1 := by omega
  rcases cleanupFrame_route state rest wellFormed pending with decision | resume | ⟨repeatStack, decreases⟩
  · obtain ⟨t, later, finished, stopped⟩ :=
      advance_observed_decision mid raw.1.pending midWF (cards ▸ reads) observedStack decision
    exact ⟨t, used + 1 + later, raw.2 ++ events, by omega,
      by simpa only [List.append_nil] using path.append finished, Or.inl stopped⟩
  · change raw.1.pending = rest at resume
    rw [resume] at observedStack
    generalize stack : mid.pending = frames at observedStack
    cases observedStack with
    | empty => exact ⟨mid, _, _, positive, path, Or.inl (by rw [stack]; rfl)⟩
    | resume => exact ⟨mid, _, _, positive, path, Or.inr ⟨stack.symm ▸ base, midWF, cards⟩⟩
    | queue q nonempty =>
      exact ⟨mid, _, _, positive, path, Or.inr ⟨stack.symm ▸ insertion rest base q nonempty, midWF, cards⟩⟩
  · change raw.1.pending = .cleanup :: rest at repeatStack
    rw [repeatStack] at observedStack
    have again (tail : List Frame) (stack : mid.pending = .cleanup :: tail) (track : keeps tail) :
        ∃ t used events, 0 < used ∧ AdvancePrefix state t used events ∧
          (t.pending.head?.all (fun f => !f.isWork) = true ∨
            (keeps t.pending ∧ t.WF ∧ t.cards = state.cards)) := by
      have same := measured (by rw [stack]; simp)
      have smaller : InvImage MeasLt GameState.cleanupMeasure mid state := by
        change MeasLt mid.cleanupMeasure state.cleanupMeasure
        rw [same]
        exact decreases
      obtain ⟨t, later, emitted, _, finished, stopped | ⟨lastStack, lastWF, lastCards⟩⟩ :=
        ih mid smaller midWF (cards ▸ reads) stack track
      · exact ⟨t, used + 1 + later, (raw.2 ++ events) ++ emitted, by omega, path.append finished,
          Or.inl stopped⟩
      · exact ⟨t, used + 1 + later, (raw.2 ++ events) ++ emitted, by omega, path.append finished,
          Or.inr ⟨lastStack, lastWF, lastCards.trans cards⟩⟩
    generalize stack : mid.pending = frames at observedStack
    cases observedStack with
    | empty => exact ⟨mid, _, _, positive, path, Or.inl (by rw [stack]; rfl)⟩
    | resume => exact again rest stack base
    | queue q nonempty => exact again (insertTriggers q rest) stack (insertion rest base q nonempty)

end Riftbound

end
