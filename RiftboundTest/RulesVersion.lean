module

import Riftbound.Basic.RulesVersion
meta import Riftbound.Basic.RulesVersion

/-!
# Tests: rules version
-/

open Riftbound

#guard coreRulesVersion == ⟨2026, 10, 9⟩
#guard tournamentRulesVersion == ⟨2026, 10, 9⟩
#guard decide coreRulesVersion.WellFormed
#guard !decide (RulesDate.WellFormed ⟨2026, 13, 1⟩)
