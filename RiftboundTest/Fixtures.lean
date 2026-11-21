module

public import Riftbound.Tournament.DeckLegality
meta import Riftbound.Tournament.DeckLegality
meta import Riftbound.Rules.Deck

/-!
# Test fixtures

A small card database and a legal Duel deck, used by the deck tests.
-/

public section

namespace RiftboundTest

open Riftbound

/-- Shorthand for a card identifier. -/
meta def cid (s : String) : CardId := ⟨s⟩

/-- The test Legend (Fury, Calm). -/
meta def legend : CardDef :=
  { id := cid "L1", name := "Test Legend", types := [.legend], tags := [⟨"Hero"⟩],
    domains := [.fury, .calm] }

/-- The test Chosen Champion. -/
meta def champion : CardDef :=
  { id := cid "C1", name := "Hero", subtitle := some "Champion", types := [.unit],
    supertypes := [.champion], tags := [⟨"Hero"⟩], domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩, might := some 4 }

/-- The `n`-th vanilla Unit of the test database. -/
meta def vanilla (n : Nat) : CardDef :=
  { id := cid s!"V{n}", name := s!"Vanilla {n}", types := [.unit], domains := [.fury],
    cost := some ⟨1, []⟩, might := some 2 }

/-- A Signature spell of the test Legend. -/
meta def signature (n : Nat) : CardDef :=
  { id := cid s!"S{n}", name := s!"Signature {n}", types := [.spell],
    supertypes := [.signature], tags := [⟨"Hero"⟩], domains := [.fury] }

/-- A Unique Unit. -/
meta def unique : CardDef :=
  { id := cid "U1", name := "Only One", types := [.unit], domains := [.calm],
    keywords := [{ keyword := .unique }] }

/-- A card of a domain outside the Legend's identity. -/
meta def offDomain : CardDef :=
  { id := cid "X1", name := "Off Domain", types := [.unit], domains := [.chaos] }

/-- The Fury Rune. -/
meta def furyRune : CardDef :=
  { id := cid "R1", name := "Fury Rune", types := [.rune], domains := [.fury] }

/-- The `n`-th Battlefield. -/
meta def battlefield (n : Nat) : CardDef :=
  { id := cid s!"B{n}", name := s!"Battlefield {n}", types := [.battlefield] }

/-- A Spell that draws a card. -/
meta def drawSpell : CardDef :=
  { id := cid "SP0", name := "Quick Study", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of [] (.prim (.draw .you (.const 1)))) }

/-- A Spell that deals 2 damage to an enemy Unit on a Base. -/
meta def spark : CardDef :=
  { id := cid "SP1", name := "Spark", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of
      [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
      (.prim (.deal (.slot 0) (.const 2)))) }

/-- The set every fixture card is printed in. -/
meta def testSet : SetCode := ⟨"TST"⟩

/-- The database of all fixtures. -/
meta def db : CardDB :=
  { cards := ([legend, champion, unique, offDomain, furyRune, drawSpell, spark] ++
      (List.range 20).map vanilla ++
      (List.range 4).map signature ++ (List.range 4).map battlefield).map
        (fun c => { c with sets := [testSet] }) }

/-- The legality environment of the fixtures: the test set is legal, nothing is banned. -/
meta def env : LegalityEnv := { legalSets := [testSet], banned := [] }

/-- A legal Duel deck: the champion and three copies of each of 13 vanilla Units
(40 cards), 12 Runes and 3 Battlefields. -/
meta def goodDeck : Deck :=
  { legend := cid "L1", chosenChampion := cid "C1",
    main := cid "C1" :: (List.range 13).flatMap (fun n => List.replicate 3 (cid s!"V{n}")),
    runes := List.replicate 12 (cid "R1"),
    battlefields := [cid "B0", cid "B1", cid "B2"] }

end RiftboundTest

end
