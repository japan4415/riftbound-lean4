module

public import Riftbound.Invariant.ExpirationWork
public import RiftboundCards.MightObservation

/-!
# Checks of the Might-related passive expressions in the registered cards
-/

public section

namespace RiftboundCards

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- The registered cards' Might-related passive abilities use the supported read expressions. -/
theorem db_mightReads : Riftbound.MightRead.database db := by decide

/-- Ordinary trigger processing with the registered cards reaches a decision or its previous
continuation within the queue length plus one work step. -/
theorem advance_triggers (s : Riftbound.GameState) (wf : s.WF) (cards : s.cards = db)
    (queue : List Riftbound.PendTrigger) (rest : List Riftbound.Frame)
    (pending : s.pending = .triggers queue :: rest) :
    ∃ t used, used ≤ queue.length + 1 ∧ Riftbound.AdvancePrefix s t used [] ∧
      Riftbound.TriggerWorkStop rest t.pending :=
  Riftbound.advance_triggers_checkedMight s wf queue rest pending (cards ▸ db_mightReads)

private theorem mightReads_of_registered {cards : Riftbound.CardDB}
    (registered : cards = db ∨ cards = db.withConcessionBattlefield) :
    Riftbound.MightRead.database cards := by
  rcases registered with h | h
  · exact h ▸ db_mightReads
  · exact h ▸ Riftbound.MightRead.database_withConcessionBattlefield db_mightReads

/-- The registered cards, including the Battlefield token used after a free-for-all concession,
support the proof from a legal ordinary Pass through the Ending Phase and its ordinary triggers. -/
theorem step_priority_pass_ending {s : Riftbound.GameState} {p : Riftbound.PlayerId} (wf : s.WF)
    (cards : s.cards = db ∨ s.cards = db.withConcessionBattlefield) (pending : s.pending = [.priority p])
    (legal : Riftbound.Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ Riftbound.EndingWorkStop t.pending.head? ∧
      (∀ fuel, Riftbound.step (used + fuel) s ⟨.player p, .pass⟩ = Riftbound.advance fuel t events) ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true →
        Riftbound.step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  exact Riftbound.step_priority_pass_ending wf (mightReads_of_registered cards) pending legal

/-- A legal ordinary Pass reaches Awaken, an earlier decision or immediate Add, or the end of
the stack, with the registered cards and the Battlefield token used after a concession. -/
theorem step_priority_pass_to_awaken {s : Riftbound.GameState} {p : Riftbound.PlayerId} (wf : s.WF)
    (cards : s.cards = db ∨ s.cards = db.withConcessionBattlefield) (pending : s.pending = [.priority p])
    (legal : Riftbound.Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ Riftbound.TurnBoundaryStop t ∧
      (∀ fuel, Riftbound.step (used + fuel) s ⟨.player p, .pass⟩ = Riftbound.advance fuel t events) ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true →
        Riftbound.step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  have ordinaryMight : s.cards.mightTriggersAreOrdinary := by
    rcases cards with h | h
    · exact h ▸ db_mightTriggersAreOrdinary
    · exact h ▸ Riftbound.CardDB.mightTriggersAreOrdinary_withConcessionBattlefield db_mightTriggersAreOrdinary
  exact Riftbound.step_priority_pass_to_awaken wf (mightReads_of_registered cards) ordinaryMight pending legal

end RiftboundCards

end
