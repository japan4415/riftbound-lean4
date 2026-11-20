module

import Riftbound.Card.CardDB
meta import Riftbound.Card.CardDB

/-!
# Tests: the static check of the effect IR (design.md §7.1, `CardDB.WF`)

Each mistake a card can make has an effect that makes it alone, and the check refuses it; the
right ways of using a slot, a variable, `it` and a mode are accepted.
-/

namespace RiftboundTest

open Riftbound

/-- A spell card with the given effect. -/
meta def spell (d : EffectDef) : CardDef :=
  { id := ⟨"T"⟩, name := "T", types := [.spell], spellEffect := some d }

/-- A unit card with the given abilities. -/
meta def unitWith (as : List Ability) : CardDef :=
  { id := ⟨"T"⟩, name := "T", types := [.unit], abilities := as }

meta def aUnit : Choice := .targetOf .one .any .anywhere [.ofType .unit]

meta def ok (c : CardDef) : Bool := decide c.StaticOk

-- a slot that was declared is accepted, one that was not is refused (CR 355)
#guard ok (spell (.of [aUnit] (.prim (.kill (.slot 0)))))
#guard !ok (spell (.of [aUnit] (.prim (.kill (.slot 1)))))
#guard !ok (spell (.of [] (.prim (.kill (.slot 0)))))
-- only targets fill slots: a mode and an X do not
#guard !ok (spell (.of [.mode 2, .xValue] (.prim (.kill (.slot 0)))))

-- a variable can be used inside the effect it is bound for, and not outside it
#guard ok (spell (.of [] (.bind ⟨"n"⟩ (.const 2) (.prim (.draw .you (.var ⟨"n"⟩))))))
#guard !ok (spell (.of [] (.prim (.draw .you (.var ⟨"n"⟩)))))
#guard !ok (spell (.of []
  (.seqOf [.bind ⟨"n"⟩ (.const 2) .nop, .prim (.draw .you (.var ⟨"n"⟩))])))

-- an X is used only where one was chosen
#guard ok (spell (.of [.xValue] (.prim (.draw .you .x))))
#guard !ok (spell (.of [] (.prim (.draw .you .x))))

-- a choice of a mode needs the same number of modes (CR 355)
#guard ok (spell (.of [.mode 2] (.modes [.nop, .nop])))
#guard !ok (spell (.of [.mode 3] (.modes [.nop, .nop])))
#guard !ok (spell (.of [] (.modes [.nop, .nop])))

-- `it` means something in a loop, a grant and a trigger, and nowhere else
#guard ok (spell (.of [] (.forEach (.all .friendly .anywhere [.ofType .unit])
  (.prim (.heal .it (.const 1))))))
#guard !ok (spell (.of [] (.prim (.heal .it (.const 1)))))
#guard ok (spell (.of [] (.grant .self (.mightPlus .it (.const 1)) .thisTurn)))
#guard ok (spell (.of [] (.grant .self (.mightPlus .self (.const 1)) .thisTurn)))
#guard ok (unitWith [.triggered { event := .attack, subject := .it } (.of [] .nop) .unlimited])
#guard !ok (unitWith [.passive .always [.mightPlus .it (.const 1)]])

-- the amount of a replaced event is known only in a replacement
#guard ok (unitWith [.replacement .draw .always (.of [] (.prim (.draw .you .eventAmount)))])
#guard !ok (unitWith [.triggered { event := .play } (.of [] (.prim (.draw .you .eventAmount)))
  .unlimited])

-- a database with a card that fails the check is not well formed
#guard decide (CardDB.WF { cards := [spell (.of [aUnit] (.prim (.kill (.slot 0))))] })
#guard !decide (CardDB.WF { cards := [spell (.of [] (.prim (.kill (.slot 0))))] })

end RiftboundTest
