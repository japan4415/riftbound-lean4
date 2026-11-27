module

public import Riftbound.Invariant.MightReadSyntax
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

end RiftboundCards

end
