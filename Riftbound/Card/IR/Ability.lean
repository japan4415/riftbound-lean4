module

public import Riftbound.Card.IR.Effect

/-!
# The effect IR: choices, effect definitions and abilities

What a card carries (design.md §7.2): the choices made when it is played, the effect with them, and
its abilities. Choices are declared apart from the body of the effect, so what has to be chosen
at play time (CR 355) is known without running the effect; the body reaches a chosen object by its
slot number (`Selector.slot`).
-/

@[expose] public section

namespace Riftbound

/-- Something chosen when a card is played or an ability is used (CR 355). The slot of a target is
its place among the targets of the declaration, counted from 0. -/
inductive Choice where
  /-- Choose objects. -/
  | target (q : Quantity) (side : Side) (place : Place) (fs : FilterList)
  /-- Choose one of `count` modes. -/
  | mode (count : Nat)
  /-- Choose a number X. -/
  | xValue
  /-- An additional cost; the player pays it only if they choose to when `optional` is true. -/
  | extraCost (cs : List AbilityCost) (optional : Bool)
deriving DecidableEq, Repr, Hashable

/-- An effect with the choices made when it starts: a Spell, or an ability. -/
structure EffectDef where
  /-- The choices, in the order they are made. -/
  choices : List Choice := []
  /-- What happens when it resolves. -/
  body : Effect
deriving DecidableEq, Repr, Hashable

/-- How often an ability can be used. -/
inductive Limit where
  /-- As often as the player wants and can pay. -/
  | unlimited
  /-- At most `n` times each turn (CR 371, 386). -/
  | perTurn (n : Nat)
deriving DecidableEq, Repr, Hashable

/-- An ability of a card (CR 361). -/
inductive Ability where
  /-- A passive ability: it changes the game as long as the card is in play and the condition
  holds. -/
  | passive (cond : Condition) (mods : List StaticMod)
  /-- A replacement ability: when the event would happen, the effect happens instead. -/
  | replacement (ev : ReplaceEvent) (cond : Condition) (instead : EffectDef)
  /-- An activated ability: pay the costs to use it, at the given speed. -/
  | activated (costs : List AbilityCost) (speed : Speed) (body : EffectDef) (limit : Limit)
  /-- A triggered ability: it fires when the trigger does. -/
  | triggered (t : Trigger) (body : EffectDef) (limit : Limit)
deriving DecidableEq, Repr, Hashable

end Riftbound

end
