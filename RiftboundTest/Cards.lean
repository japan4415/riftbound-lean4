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

-- Lee Sin, Centered and Leona, Determined were Chosen Champions at RQ Houston.
#guard ["OGN-151", "OGN-238"].all fun code =>
  (db.find? ⟨code⟩).any (fun c => decide c.IsChosenChampionCandidate)

-- a parameter that is a number, and a parameter that is a cost
#guard match db.find? ⟨"OGN-003"⟩ with
  | some c => c.keywords.any (·.arg == .amount 2)
  | none => false
#guard match db.find? ⟨"SFD-003"⟩ with
  | some c => c.keywords ==
      [{ keyword := .action }, { keyword := .repeat_, arg := .cost ⟨1, []⟩ }]
  | none => false

-- Hourglass has IR, with competing death replacements still partially covered.
#guard (Origins.cards.filter (fun c => !c.runs)).map (·.id.code) == ["OGN-077"]
#guard (allCards.filter (fun c => c.id.code.startsWith "OGN-")).length == 298
-- Spiritforged (222): the measure of the goal "every card of the second set works"
#guard (allCards.filter (fun c => c.id.code.startsWith "SFD-" && c.runs)).length == 222
#guard (allCards.filter (fun c => c.id.code.startsWith "SFD-")).length == 222
-- Unleashed (225): the measure of the goal "every card of the third set works"
#guard (allCards.filter (fun c => c.id.code.startsWith "UNL-" && c.runs)).length == 225
#guard (allCards.filter (fun c => c.id.code.startsWith "UNL-")).length == 225

-- The set is present as IR throughout scenario verification (docs/coverage.md).
#guard Vendetta.cards.all (fun c => c.status == .drafted || c.status == .full)
#guard (Vendetta.cards.filter CardDef.runs).length == 167
#guard Radiance.cards.all (fun c => c.status == .full && c.runs)
#guard allCards.all (fun c => c.status != .todo)

-- The official image of Bilgewater Tracker shows Fury and the Bilgewater tag.
#guard match db.find? ⟨"RAD-003"⟩ with
  | some c => c.domains == [.fury] && c.tags == [⟨"Bilgewater"⟩]
  | none => false
-- an Equipment's effect text is kept apart: the abilities it gives the Unit it is attached to are
-- `grants`, not the abilities of the card
#guard match db.find? ⟨"UNL-019"⟩ with
  | some c => c.status == .drafted && c.grants.length == 2 && c.abilities.isEmpty
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

-- Recruit the Vanguard runs the four placement choices when the spell resolves.
#guard match db.find? ⟨"OGS-015"⟩ with
  | some c => c.status == .full && c.spellRuns
  | none => false

-- the Spells with written effects: how many the interpreter runs from start to end (roadmap.md, M4d). The rest
-- use something it does not know yet: a mode, a choice of several objects, a place such as a chosen
-- Battlefield, a delayed or replaced event, taking control, an extra turn. A lasting change of
-- Might that ends with the turn (`grant`) runs since M6d.
#guard (allCards.filter (fun c => (c.status == .drafted || c.status == .full) && c.spellEffect.isSome)).length == 271
#guard (allCards.filter (fun c => (c.status == .drafted || c.status == .full) && c.spellRuns)).length == 270

end RiftboundTest
