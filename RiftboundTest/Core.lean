module

import Riftbound.Core.Keyword
meta import Riftbound.Core.Keyword
import Riftbound.Core.Might
meta import Riftbound.Core.Might
import Riftbound.Rules.Deck
meta import Riftbound.Rules.Deck

/-!
# Tests: costs, Might, keywords, domains
-/

namespace RiftboundTest

open Riftbound

-- Cost arithmetic (CR 356)
#guard (Cost.addEnergy ⟨3, []⟩ (-1)).energy == 2
#guard (Cost.addEnergy ⟨3, []⟩ (-5)).energy == 0
#guard (Cost.addEnergy ⟨3, []⟩ 2).energy == 5
#guard (Cost.dropPower ⟨2, [.domain .fury, .any, .own]⟩ 2).power == [.own]
#guard (Cost.dropPower ⟨2, [.any]⟩ 5).power == []
#guard Cost.total ⟨2, [.any, .own]⟩ == 4

-- Might (CR 143.2.c, 708)
#guard Might.eff (-3) == 0
#guard Might.eff 4 == 4
#guard decide (Might.Mighty 5)
#guard !decide (Might.Mighty 4)
#guard !decide (Might.Mighty (-7))

-- 28 keywords, 6 domains
#guard Keyword.all.length == 28
#guard Domain.all.length == 6

-- copy limit (CR 103.3.b, 825)
#guard (CardDef.copyLimit { id := ⟨"a"⟩, name := "a", types := [] }) == 3
#guard (CardDef.copyLimit { id := ⟨"a"⟩, name := "a", types := [],
                            keywords := [{ keyword := .unique }] }) == 1

end RiftboundTest
