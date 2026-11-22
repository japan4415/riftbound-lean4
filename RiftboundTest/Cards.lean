module

import RiftboundCards
meta import RiftboundCards
import Riftbound.Rules.Understood
meta import Riftbound.Rules.Understood

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

-- the cards of Origins that do everything their text says (`CardDef.runs`): the measure of the
-- goal "every card of the first set works" (298)
#guard (allCards.filter (fun c => c.id.code.startsWith "OGN-" && c.runs)).length == 274
#guard (allCards.filter (fun c => c.id.code.startsWith "OGN-")).length == 298

-- the cards written down as IR values (docs/coverage.md): 239 by hand, 169 by `transcribe.py`
#guard (allCards.filter (·.status == .drafted)).length == 408
-- an Equipment's effect text is kept apart, and such a card is not written down yet
#guard match db.find? ⟨"UNL-019"⟩ with
  | some c => c.status == .todo
  | none => false

-- Firestorm: one choice (the Battlefield), a spell effect and no abilities
#guard match db.find? ⟨"OGS-002"⟩ with
  | some c => c.spellEffect.isSome && c.abilities.isEmpty && c.status == .drafted &&
      (match c.spellEffect with | some e => e.choices.length == 1 | none => false)
  | none => false

-- Karthus, Eternal: a passive ability that makes triggers fire once more
#guard match db.find? ⟨"OGN-236"⟩ with
  | some c => c.abilities == [.passive .always [.triggersExtra .die .anywhere]]
  | none => false

-- Recruit the Vanguard cannot be written yet: the tokens go to a place chosen then
#guard match db.find? ⟨"OGS-015"⟩ with
  | some c => c.status == .todo && c.spellEffect.isNone
  | none => false

-- the drafted Spells: how many the interpreter runs from start to end (roadmap.md, M4d). The rest
-- use something it does not know yet: a mode, a choice of several objects, a place such as a chosen
-- Battlefield, a delayed or replaced event, taking control, an extra turn. A lasting change of
-- Might that ends with the turn (`grant`) runs since M6d.
#guard (allCards.filter (fun c => c.status == .drafted && c.spellEffect.isSome)).length == 104
#guard (allCards.filter (fun c => c.status == .drafted && c.spellRuns)).length == 98

end RiftboundTest
