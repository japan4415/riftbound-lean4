module

public import Riftbound.Invariant.TriggerWork
public import RiftboundCards.Registry

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

end RiftboundCards

end
