module

import Riftbound.Rules.Deck
meta import Riftbound.Rules.Deck
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: deck building (CR 101-103)

Each rule has a deck that breaks that rule alone, and the legal deck is accepted.
-/

namespace RiftboundTest

open Riftbound

meta def ok (d : Deck) : Bool := decide (DeckValid db Mode.duel d)

-- fixtures themselves
#guard decide db.WF
#guard goodDeck.main.length == 40

-- the legal deck
#guard ok goodDeck

-- unknown card
#guard !ok { goodDeck with legend := cid "nope" }
#guard !ok { goodDeck with runes := cid "nope" :: goodDeck.runes.tail }

-- Legend must be a Legend (CR 103.2)
#guard !ok { goodDeck with legend := cid "V0" }

-- Main Deck size (CR 103.3)
#guard !ok { goodDeck with main := goodDeck.main.tail }
#guard ok { goodDeck with main := goodDeck.main ++ [cid "V13"] }

-- Chosen Champion (CR 103.3.a)
#guard !ok { goodDeck with chosenChampion := cid "V0" }
#guard !ok { goodDeck with main := goodDeck.main.tail ++ [cid "V13"] }

-- copy limit (CR 103.3.b) and Unique (CR 825)
#guard !ok { goodDeck with main := goodDeck.main ++ [cid "V0"] }
#guard ok { goodDeck with main := goodDeck.main ++ [cid "U1"] }
#guard !ok { goodDeck with main := goodDeck.main ++ [cid "U1", cid "U1"] }

-- Signature cards (CR 103.3.d)
#guard ok { goodDeck with main := goodDeck.main ++ [cid "S0", cid "S1", cid "S2"] }
#guard !ok { goodDeck with main := goodDeck.main ++ [cid "S0", cid "S1", cid "S2", cid "S3"] }

-- Domain Identity (CR 103.2.b)
#guard !ok { goodDeck with main := goodDeck.main ++ [cid "X1"] }

-- Rune Deck (CR 103.4)
#guard !ok { goodDeck with runes := goodDeck.runes.tail }
#guard !ok { goodDeck with runes := cid "V0" :: goodDeck.runes.tail }

-- Battlefields (CR 103.5)
#guard !ok { goodDeck with battlefields := [cid "B0", cid "B1"] }
#guard !ok { goodDeck with battlefields := [cid "B0", cid "B1", cid "B1"] }
#guard !ok { goodDeck with battlefields := [cid "B0", cid "B1", cid "V0"] }

-- database well-formedness (duplicate identifiers)
#guard !decide (CardDB.WF { cards := [legend, legend] })

end RiftboundTest
