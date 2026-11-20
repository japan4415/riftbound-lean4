module

import Riftbound.Tournament.DeckLegality
meta import Riftbound.Tournament.DeckLegality
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: deck legality in the tournament formats (TR 402, 601, 602)
-/

namespace RiftboundTest

open Riftbound

meta def okC (d : Deck) (side : List CardId := []) (e : LegalityEnv := env) : Bool :=
  decide (ConstructedDeckValid db e { deck := d, sideboard := side })

meta def okCore (d : Deck) : Bool := decide (DeckValid db Mode.duel d)

meta def ids (n : Nat) (k : Nat) : List CardId := List.replicate k (cid s!"V{n}")

-- Constructed: the legal deck, and I13 on it
#guard okC goodDeck
#guard okCore goodDeck

-- exactly 40 cards (TR 402.1): 41 is legal in the Core Rules, not in Constructed
#guard okCore { goodDeck with main := goodDeck.main ++ [cid "V13"] }
#guard !okC { goodDeck with main := goodDeck.main ++ [cid "V13"] }
#guard !okC { goodDeck with main := goodDeck.main.tail }

-- Battlefields: exactly three, different names (TR 402.1, 601.1.b)
#guard !okC { goodDeck with battlefields := [cid "B0", cid "B1"] }
#guard !okC { goodDeck with battlefields := [cid "B0", cid "B1", cid "B1"] }
#guard !okC { goodDeck with battlefields := [cid "B0", cid "B1", cid "B2", cid "B3"] }

-- sideboard: at most 10 cards (TR 601.1.c)
#guard okC goodDeck (ids 13 3 ++ ids 14 3 ++ ids 15 3 ++ ids 16 1)
#guard !okC goodDeck (ids 13 3 ++ ids 14 3 ++ ids 15 3 ++ ids 16 3)
-- name limit counts the Main Deck and the sideboard together
#guard okCore goodDeck
#guard !okC goodDeck [cid "V0"]
-- the sideboard must fit the Domain Identity
#guard !okC goodDeck [cid "X1"]
-- an unknown card in the sideboard
#guard !okC goodDeck [cid "nope"]

-- card legality (TR 601.2-3)
#guard !okC goodDeck [] { env with banned := [cid "V0"] }
#guard !okC goodDeck [] { env with legalSets := [] }
#guard okC goodDeck [] { env with banned := [cid "V19"] }

-- Limited
meta def limited : LimitedDeck :=
  { identity := [.fury, .calm, .mind], legend := none, chosenChampion := none,
    main := ids 0 25, runes := List.replicate 12 (cid "R1"), battlefields := [cid "B0"] }

meta def okS (d : LimitedDeck) (e : LegalityEnv := env) : Bool :=
  decide (SealedDeckValid db e d)
meta def okD (d : LimitedDeck) (e : LegalityEnv := env) : Bool :=
  decide (DraftDeckValid db e d)

-- no copy limit, no Legend, no Chosen Champion (TR 602.4.a.5-6)
#guard okS limited
#guard okD limited
-- sizes: 25 for Sealed, 20 for Draft
#guard !okS { limited with main := ids 0 24 }
#guard okD { limited with main := ids 0 20 }
#guard !okD { limited with main := ids 0 19 }
-- identity: three different domains
#guard !okS { limited with identity := [.fury, .calm] }
#guard !okS { limited with identity := [.fury, .fury, .calm] }
-- cards must fit the identity
#guard !okS { limited with main := ids 0 24 ++ [cid "X1"] }
-- Legend and Chosen Champion, when present
#guard okS { limited with legend := some (cid "L1"), chosenChampion := some (cid "C1"),
                          main := cid "C1" :: ids 0 24 }
#guard !okS { limited with chosenChampion := some (cid "C1") }
#guard !okS { limited with legend := some (cid "V0") }
-- banned cards stay banned in Limited unless the format un-bans them (TR 602.1.b)
#guard !okS limited { env with banned := [cid "V0"] }
-- Rune Deck of 12
#guard !okS { limited with runes := List.replicate 11 (cid "R1") }

end RiftboundTest
