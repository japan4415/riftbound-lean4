module

public import Riftbound.Card.IR.Value

/-!
# The effect IR: amounts, selectors and conditions

The expressions an effect reads the game with (design.md §7.2). They are one family of types
that refer to each other: an amount can count what a selector picks, a selector can ask for objects
whose Might is compared to an amount, and a condition compares amounts and asks about selectors.

A recursive type here never holds a `List` or an `Option` of itself: v4.36.0 cannot derive
`DecidableEq` for a nested inductive type (lean-guidelines.md §5.4). The one list that is needed,
the filters of a selector, is a list type of its own, in the same `mutual` block.
-/

@[expose] public section

namespace Riftbound

mutual

/-- A number an effect computes. -/
inductive Amount where
  /-- A constant. -/
  | const (n : Nat)
  /-- The X chosen when the card is played (CR 355). -/
  | x
  /-- A bound variable. -/
  | var (v : VarId)
  /-- How many objects the selector matches. -/
  | count (s : Selector)
  /-- The Might of an object. -/
  | mightOf (s : Selector)
  /-- The Energy cost of an object. -/
  | costOf (s : Selector)
  /-- The XP of the player the effect belongs to. -/
  | xp
  /-- How many points the player still needs to win. -/
  | pointsLeft
  /-- The number of cards in a player's hand. -/
  | handSize (p : PlayerSel)
  /-- The sum. -/
  | add (a b : Amount)
  /-- The difference. It is never negative: a subtraction below zero is zero. -/
  | sub (a b : Amount)
  /-- The product. -/
  | mul (a b : Amount)
  /-- The smaller of two amounts. -/
  | min (a b : Amount)
  /-- The larger of two amounts. -/
  | max (a b : Amount)
deriving DecidableEq, Repr, Hashable

/-- A property an object can have, used to pick objects. -/
inductive Filter where
  /-- Has the card type. -/
  | ofType (t : CardType)
  /-- Has the supertype. -/
  | ofSupertype (s : Supertype)
  /-- Has the tag. -/
  | tag (t : Tag)
  /-- Has the name. -/
  | named (name : String)
  /-- Has the keyword. -/
  | hasKeyword (k : Keyword)
  /-- Has the domain. -/
  | domain (d : Domain)
  /-- Its Might compares to the amount. -/
  | might (op : Cmp) (a : Amount)
  /-- Its Energy cost compares to the amount. -/
  | cost (op : Cmp) (a : Amount)
  /-- Is exhausted. -/
  | exhausted
  /-- Is ready. -/
  | ready
  /-- Has damage. -/
  | damaged
  /-- Is stunned. -/
  | stunned
  /-- Has a buff. -/
  | buffed
  /-- Is Mighty (its Might is at least 5). -/
  | mighty
  /-- Has an object attached. -/
  | attached
  /-- Is an attacker in the combat. -/
  | attacker
  /-- Is a defender in the combat. -/
  | defender
  /-- Is not the object the effect belongs to ("another"). -/
  | notSelf
deriving DecidableEq, Repr, Hashable

/-- A list of filters. -/
inductive FilterList where
  /-- No filter. -/
  | nil
  /-- A filter, then the rest. -/
  | cons (f : Filter) (rest : FilterList)
deriving DecidableEq, Repr, Hashable

/-- Some objects of the game. -/
inductive Selector where
  /-- The object the effect belongs to ("me", "this"). -/
  | self
  /-- The object chosen into a slot when the card was played (Choose) (CR 355). -/
  | slot (i : Nat)
  /-- The object a `forEach` or a trigger is about. -/
  | it
  /-- A bound variable. -/
  | var (v : VarId)
  /-- Objects picked while the effect resolves, or all that match (Pick) (CR 355). -/
  | pick (q : Quantity) (side : Side) (place : Place) (fs : FilterList)
  /-- The object another one is attached to. -/
  | attachedTo (s : Selector)
  /-- The objects attached to another one. -/
  | attachments (s : Selector)
deriving DecidableEq, Repr, Hashable

/-- A question about the game. -/
inductive Condition where
  /-- Always true. -/
  | always
  /-- Not. -/
  | not (c : Condition)
  /-- Both. -/
  | and (a b : Condition)
  /-- Either. -/
  | or (a b : Condition)
  /-- Two amounts compare. -/
  | cmp (op : Cmp) (a b : Amount)
  /-- At least one object matches the selector. -/
  | exists (s : Selector)
  /-- The object matches the filter. -/
  | matches (s : Selector) (f : Filter)
  /-- The unit is Empowered (CR 828). -/
  | empowered (s : Selector)
  /-- Legion: another card was played this turn (CR 812). -/
  | legion
  /-- It is the turn of the player the effect belongs to. -/
  | yourTurn
  /-- A combat is going on. -/
  | inCombat
  /-- A showdown is going on. -/
  | inShowdown
deriving DecidableEq, Repr, Hashable

end

end Riftbound

end
