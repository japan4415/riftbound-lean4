module

import Riftbound.Card.CardDef
meta import Riftbound.Card.CardDef

/-!
# Tests: the effect IR (design.md §7.2)

The types derive equality and printing; the environment finds what it binds; and two cards are
written down as IR values, as a check that the shapes fit real card text (the transcription of the
cards comes in milestone M3b, card-data.md §6).
-/

namespace RiftboundTest

open Riftbound

/-- "a unit" as a target (CR 355). -/
meta def aUnit : Choice := .target .one .any .anywhere (.cons (.ofType .unit) .nil)

/-- Falling Star (OGN-029): "Deal 3 to a unit. Deal 3 to a unit." -/
meta def fallingStarEffect : EffectDef :=
  { choices := [aUnit, aUnit],
    body := .seq (.cons (.prim (.deal (.slot 0) (.const 3)))
      (.cons (.prim (.deal (.slot 1) (.const 3))) .nil)) }

/-- "When you play me, draw 1." -/
meta def drawOnPlay : Ability :=
  .triggered { event := .play } { body := .prim (.draw .you (.const 1)) } .unlimited

-- equality is decided, and distinguishes what differs
#guard decide (fallingStarEffect = fallingStarEffect)
#guard decide (fallingStarEffect ≠ { fallingStarEffect with choices := [aUnit] })
#guard decide (drawOnPlay ≠ .triggered { event := .attack } { body := .nop } .unlimited)
#guard decide (Amount.add (.const 1) (.count .self) ≠ .add (.const 1) (.count (.slot 0)))

-- a selector with filters: "an enemy unit here with Might 3 or less"
#guard decide (Selector.pick .one .enemy .here
    (.cons (.ofType .unit) (.cons (.might .le (.const 3)) .nil)) ≠ .self)

-- the environment finds a variable it binds, newest first
#guard (Env.empty.bind ⟨"n"⟩ (.int 2)).lookup ⟨"n"⟩ == some (.int 2)
#guard ((Env.empty.bind ⟨"n"⟩ (.int 2)).bind ⟨"n"⟩ (.int 5)).lookup ⟨"n"⟩ ==
  some (.int 5)
#guard (Env.empty.bind ⟨"n"⟩ (.int 2)).lookup ⟨"m"⟩ == none

-- a card carries effects; the generated cards have none yet
meta def sampleCard : CardDef :=
  { id := ⟨"T1"⟩, name := "T", types := [.spell], spellEffect := some fallingStarEffect,
    abilities := [drawOnPlay] }

#guard sampleCard.spellEffect.isSome
#guard sampleCard.abilities.length == 1

end RiftboundTest
