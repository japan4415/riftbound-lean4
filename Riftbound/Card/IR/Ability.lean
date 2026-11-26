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

/-- A destination chosen for an object named by a Spell's targets (CR 355.4). -/
structure MoveChoice where
  /-- The target slot of the object to move. -/
  slot : Nat
  /-- Allow the object's Base. -/
  allowBase : Bool
  /-- Additional requirements on destination Battlefields. -/
  filters : FilterList := .nil
deriving DecidableEq, Repr, Hashable

/-- A mode with its own targets and instructions (CR 355.3). -/
structure SpellMode where
  /-- The label shown with the legal action. -/
  label : String
  /-- The targets required by this mode. -/
  choices : List Choice
  /-- What this mode does on resolution. -/
  body : Effect
  /-- The destination required by this mode. -/
  moveChoice : Option MoveChoice := none
deriving DecidableEq, Repr, Hashable

/-- An effect with the choices made when it starts: a Spell, or an ability. -/
structure EffectDef where
  /-- The choices, in the order they are made. -/
  choices : List Choice := []
  /-- Extra targets chosen at finalization only when the player shows off (CR 355, 832). -/
  showOffChoices : List Choice := []
  /-- What happens when it resolves. -/
  body : Effect
  /-- Modes with their own choices and instructions. -/
  modes : List SpellMode := []
  /-- The declared destination choice, if any. -/
  moveChoice : Option MoveChoice := none
  /-- The side from which this spell or ability chooses a player during finalization (CR 355.7). -/
  playerTarget : Option Side := none
  /-- Recheck the declared object targets separately at resolution (CR 355.11, 359.3.e.2). -/
  recheckTargets : Bool := false
  /-- The unbounded target group requires exactly the declared additional Power (CR 355.5). -/
  variablePowerTargets : Bool := false
deriving DecidableEq, Repr, Hashable

/-- The selected mode's instructions and choices, with the declaration's shared rules. -/
def EffectDef.modeAt (e : EffectDef) (i : Nat) : Option EffectDef :=
  e.modes[i]?.map (fun mode =>
    { choices := mode.choices, body := mode.body, playerTarget := e.playerTarget,
      recheckTargets := e.recheckTargets, moveChoice := mode.moveChoice,
      variablePowerTargets := e.variablePowerTargets })

/-- Get the instructions and target requirements for the choice on the Chain. -/
def EffectDef.forPick (e : EffectDef) : SpellPick → Option EffectDef
  | .mode i => (e.modeAt i).filter (·.moveChoice.isNone)
  | .modeDestination i _ => (e.modeAt i).filter (·.moveChoice.isSome)
  | .plain => if e.modes.isEmpty && e.moveChoice.isNone then some e else none
  | .destination _ => if e.modes.isEmpty && e.moveChoice.isSome then some e else none
  | .payForBattlefield .. | .withPermanentCosts .. | .withGearDiscounts .. => none
  | .withPlayer pick _ => e.forPick pick
  | .withShowOff pick _ => (e.forPick pick).map (fun branch =>
    { branch with choices := branch.choices ++ e.showOffChoices, showOffChoices := [] })
  | .withCosts pick _ _ | .thenRepeat pick _ _ | .withExtraObject pick _ |
      .withSpellExhausts pick _ | .withXP pick => e.forPick pick
  | .withVariablePower pick n => (e.forPick pick).map (fun branch =>
    if branch.variablePowerTargets then
      { branch with choices := branch.choices.map (fun
        | .target .anyNumber side place fs => .target (.exactly n) side place fs
        | choice => choice) }
    else branch)

/-- Whether the Spell can have distinct modes, targets or destinations in a Repeat (CR 820.2). -/
def EffectDef.hasFinalizationChoice (e : EffectDef) : Bool :=
  (e.choices ++ e.showOffChoices).any (fun
    | .target .. => true
    | _ => false) || !e.modes.isEmpty || e.moveChoice.isSome || e.playerTarget.isSome

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
