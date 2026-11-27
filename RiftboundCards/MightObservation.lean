module

public import Riftbound.Invariant.MightObservation
public import RiftboundCards.Registry

/-!
# Might observations in the registered cards
-/

public section

namespace RiftboundCards

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- No registered Might threshold schedules an immediate Add through the ability it queues. -/
theorem db_mightTriggersAreOrdinary : db.mightTriggersAreOrdinary := by decide

end RiftboundCards

end
