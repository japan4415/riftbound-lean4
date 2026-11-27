module

public import Riftbound.Invariant.MightObservation
public import RiftboundCards.Registry

/-!
# Might and Awaken observations in the registered cards
-/

public section

namespace RiftboundCards

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- No registered Might threshold schedules an immediate Add through the ability it queues. -/
theorem db_mightTriggersAreOrdinary : db.mightTriggersAreOrdinary := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- No registered Awaken or ready ability can schedule an immediate Add through its queued index. -/
theorem db_awakenTriggersAreOrdinary : db.awakenTriggersAreOrdinary := by decide

end RiftboundCards

end
