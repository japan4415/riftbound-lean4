module

import RiftboundCards
meta import RiftboundCards

/-!
# Tests: the generated card database (docs/card-data.md §4)

The cards come from `data/cards/logical.json` through `scripts/gen_lean.py`. These checks keep the
generator and the Lean types in step: the numbers, the identifiers and a few cards read by hand.
-/

namespace RiftboundTest

open Riftbound RiftboundCards

-- every logical card is there, and the identifiers are unique (`CardDB.WF`)
#guard allCards.length == 1103
#guard decide db.WF

-- the cards of each set (first printings)
#guard Origins.cards.length == 298
#guard ProvingGrounds.cards.length == 24
#guard Spiritforged.cards.length == 222
#guard Unleashed.cards.length == 225
#guard Vendetta.cards.length == 167
#guard Radiance.cards.length == 167

-- Falling Star (OGN-029): a Spell of Fury, 2 Energy and 2 Fury Power
#guard match db.find? ⟨"OGN-029"⟩ with
  | some c => c.name == "Falling Star" && c.types == [.spell] && c.domains == [.fury] &&
      c.cost == some ⟨2, [.domain .fury, .domain .fury]⟩ && c.might == none
  | none => false

-- Blazing Scorcher (OGN-001): a Unit with Accelerate and 5 Might
#guard match db.find? ⟨"OGN-001"⟩ with
  | some c => c.types == [.unit] && c.might == some 5 &&
      c.keywords == [{ keyword := .accelerate }] && c.sets == [⟨"OGN"⟩]
  | none => false

-- a card with a subtitle keeps both parts of its name (CR 132)
#guard match db.find? ⟨"OGN-119"⟩ with
  | some c => c.name == "Ahri" && c.subtitle == some "Inquisitive" &&
      c.sets == [⟨"OGN"⟩, ⟨"SFD"⟩, ⟨"VEN"⟩]
  | none => false

-- a parameter that is a number, and a parameter that is a cost
#guard match db.find? ⟨"OGN-003"⟩ with
  | some c => c.keywords.any (·.arg == .amount 2)
  | none => false
#guard match db.find? ⟨"SFD-003"⟩ with
  | some c => c.keywords ==
      [{ keyword := .action }, { keyword := .repeat_, arg := .cost ⟨1, []⟩ }]
  | none => false

end RiftboundTest
