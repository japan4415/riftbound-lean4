module

import Riftbound.Tournament.Sideboard
meta import Riftbound.Tournament.Sideboard
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: sideboarding (TR 403)

Exchanges between the Main Deck and the sideboard: one for one, and the deck stays legal when the
parts that an exchange can change are in order.
-/

namespace RiftboundTest

open Riftbound

meta def okSb (d : Deck) (side : List CardId) : Bool :=
  decide (ConstructedDeckValid db env { deck := d, sideboard := side })

meta def vs (n k : Nat) : List CardId := List.replicate k (cid s!"V{n}")

/-- The registered sideboard: three copies of V13, V14 and V15, and one of V16. -/
meta def side0 : List CardId := vs 13 3 ++ vs 14 3 ++ vs 15 3 ++ vs 16 1

/-- Two copies of V0 leave the Main Deck; V13 and V14 come in. -/
meta def mainAfter : List CardId :=
  cid "C1" :: (vs 0 1 ++ (List.range 13).tail!.flatMap (fun n => vs n 3)) ++ [cid "V13", cid "V14"]
meta def sideAfter : List CardId :=
  (vs 13 2 ++ vs 14 2 ++ vs 15 3 ++ vs 16 1) ++ vs 0 2

-- the registered deck is legal, and so is the deck after a one-for-one exchange
#guard okSb goodDeck side0
#guard okSb { goodDeck with main := mainAfter } sideAfter
-- the cards of the Main Deck and the sideboard together are the same (TR 601.1.c)
#guard (mainAfter ++ sideAfter).length == (goodDeck.main ++ side0).length
#guard (mainAfter.length == goodDeck.main.length) && (sideAfter.length == side0.length)

-- an exchange that is not one for one breaks the size of the Main Deck (TR 402.1)
#guard !okSb { goodDeck with main := mainAfter.tail } sideAfter

-- the limit on the copies of a name counts the Main Deck and the sideboard together
-- (TR 601.1.c): a sideboard with 3 copies of V0 next to the 1 left in the Main Deck makes 4
#guard !okSb { goodDeck with main := mainAfter } (vs 0 3 ++ vs 13 2 ++ vs 14 2 ++ vs 15 3)
#guard okSb { goodDeck with main := mainAfter } (vs 0 2 ++ vs 13 2 ++ vs 14 2 ++ vs 15 3 ++ vs 16 1)

-- the Runes, the Legend and the Battlefields are as they were registered (TR 403.4.b): changing one
-- is not an exchange of the sideboard, and here makes the deck illegal
#guard !okSb { goodDeck with battlefields := [cid "B0", cid "B1", cid "B1"] } side0

-- no exchange before the first game, none after a draw (TR 403.5, 403.10)
#guard !(MatchState.start 2).sideboardAllowed
#guard !(MatchState.ofGames 2 [(.won [⟨0⟩], ⟨0⟩), (.draw, ⟨1⟩)]).sideboardAllowed
#guard (MatchState.ofGames 2 [(.won [⟨0⟩], ⟨0⟩)]).sideboardAllowed

end RiftboundTest
