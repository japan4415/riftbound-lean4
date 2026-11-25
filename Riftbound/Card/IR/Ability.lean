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

/-- A mode with its own targets and instructions (CR 355.3). -/
structure SpellMode where
  /-- The label shown with the legal action. -/
  label : String
  /-- The targets required by this mode. -/
  choices : List Choice
  /-- What this mode does on resolution. -/
  body : Effect
deriving DecidableEq, Repr, Hashable

/-- A destination chosen for a Unit named by a Spell's targets (CR 355.4). -/
structure MoveChoice where
  /-- The target slot of the Unit to move. -/
  slot : Nat
  /-- Allow the Unit's Base. -/
  allowBase : Bool
  /-- Additional requirements on destination Battlefields. -/
  filters : FilterList := .nil
deriving DecidableEq, Repr, Hashable

/-- An effect with the choices made when it starts: a Spell, or an ability. -/
structure EffectDef where
  /-- The choices, in the order they are made. -/
  choices : List Choice := []
  /-- What happens when it resolves. -/
  body : Effect
  /-- Modes with their own choices and instructions. -/
  modes : List SpellMode := []
  /-- The declared destination choice, if any. -/
  moveChoice : Option MoveChoice := none
deriving DecidableEq, Repr, Hashable

/-- Get the instructions and target requirements for the choice on the Chain. -/
def EffectDef.forPick (e : EffectDef) : SpellPick → Option EffectDef
  | .mode i => e.modes[i]?.map (fun mode => { choices := mode.choices, body := mode.body })
  | .plain => if e.modes.isEmpty && e.moveChoice.isNone then some e else none
  | .destination _ => if e.modes.isEmpty && e.moveChoice.isSome then some e else none

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
