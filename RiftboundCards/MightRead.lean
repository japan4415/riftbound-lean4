module

public import Riftbound.Invariant.ExpirationWork
public import Riftbound.Invariant.ObservedAddWork
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

private theorem ordinaryMight_of_registered {cards : Riftbound.CardDB}
    (registered : cards = db ∨ cards = db.withConcessionBattlefield) : cards.mightTriggersAreOrdinary := by
  rcases registered with h | h
  · exact h ▸ db_mightTriggersAreOrdinary
  · exact h ▸ Riftbound.CardDB.mightTriggersAreOrdinary_withConcessionBattlefield db_mightTriggersAreOrdinary

private theorem ordinaryAwaken_of_registered {cards : Riftbound.CardDB}
    (registered : cards = db ∨ cards = db.withConcessionBattlefield) : cards.awakenTriggersAreOrdinary := by
  rcases registered with h | h
  · exact h ▸ db_awakenTriggersAreOrdinary
  · exact h ▸ Riftbound.CardDB.awakenTriggersAreOrdinary_withConcessionBattlefield db_awakenTriggersAreOrdinary

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

/-- A legal ordinary Pass with the registered cards resolves all immediate Adds during
Ending and reaches a player decision, the end of the stack, or Begin Turn. -/
theorem step_priority_pass_ending_with_adds {s : Riftbound.GameState} {p : Riftbound.PlayerId} (wf : s.WF)
    (cards : s.cards = db ∨ s.cards = db.withConcessionBattlefield) (pending : s.pending = [.priority p])
    (legal : Riftbound.Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true ∨ t.pending = [.beginTurn]) ∧
      (∀ fuel, Riftbound.step (used + fuel) s ⟨.player p, .pass⟩ = Riftbound.advance fuel t events) ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true →
        Riftbound.step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  exact Riftbound.step_priority_pass_ending_with_adds wf (mightReads_of_registered cards)
    (ordinaryMight_of_registered cards) pending legal

/-- A legal ordinary Pass resolves Ending's immediate Adds and reaches Awaken, an earlier
decision, or the end of the stack, including after a free-for-all concession. -/
theorem step_priority_pass_to_awaken {s : Riftbound.GameState} {p : Riftbound.PlayerId} (wf : s.WF)
    (cards : s.cards = db ∨ s.cards = db.withConcessionBattlefield) (pending : s.pending = [.priority p])
    (legal : Riftbound.Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ Riftbound.TurnBoundaryStop t ∧
      (∀ fuel, Riftbound.step (used + fuel) s ⟨.player p, .pass⟩ = Riftbound.advance fuel t events) ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true →
        Riftbound.step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  exact Riftbound.step_priority_pass_to_awaken wf (mightReads_of_registered cards)
    (ordinaryMight_of_registered cards) pending legal

/-- With the registered cards, a legal ordinary Pass resolves Ending's immediate Adds and
proceeds through Awaken to Beginning, an earlier decision, or the end of the stack. -/
theorem step_priority_pass_through_awaken {s : Riftbound.GameState} {p : Riftbound.PlayerId} (wf : s.WF)
    (cards : s.cards = db ∨ s.cards = db.withConcessionBattlefield) (pending : s.pending = [.priority p])
    (legal : Riftbound.Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ Riftbound.AwakenWorkStop s.cards t ∧
      (∀ fuel, Riftbound.step (used + fuel) s ⟨.player p, .pass⟩ = Riftbound.advance fuel t events) ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true →
        Riftbound.step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  exact Riftbound.step_priority_pass_through_awaken wf (mightReads_of_registered cards)
    (ordinaryMight_of_registered cards) (ordinaryAwaken_of_registered cards) pending legal

/-- With the registered cards, a legal ordinary Pass reaches the next decision or game end
with some finite fuel. Extra fuel produces the same state and events. -/
theorem step_priority_pass_to_decision {s : Riftbound.GameState} {p : Riftbound.PlayerId} (wf : s.WF)
    (cards : s.cards = db ∨ s.cards = db.withConcessionBattlefield) (pending : s.pending = [.priority p])
    (legal : Riftbound.Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, Riftbound.step (used + extra) s ⟨.player p, .pass⟩ = .ok (t, events) := by
  exact Riftbound.step_priority_pass_to_decision wf (mightReads_of_registered cards)
    (ordinaryMight_of_registered cards) (ordinaryAwaken_of_registered cards) pending legal

/-- A detected batch of immediate and ordinary triggers runs through the engine with the registered
cards, including the Battlefield entry used after a concession. -/
theorem advance_detectedTriggers (s : Riftbound.GameState) (triggers : List Riftbound.PendTrigger)
    (rest : List Riftbound.Frame) (wf : s.WF) (cards : s.cards = db ∨ s.cards = db.withConcessionBattlefield) :
    ∃ t used events, Riftbound.AdvancePrefix
      { s with pending := Riftbound.insertDetectedTriggers s triggers rest } t used events ∧
      Riftbound.TriggerWorkStop (Riftbound.afterLeadingTriggers (Riftbound.ordinaryTriggerContinuation s triggers rest))
        t.pending :=
  Riftbound.advance_detectedTriggers_checkedMight s triggers rest wf (mightReads_of_registered cards)

end RiftboundCards

end
