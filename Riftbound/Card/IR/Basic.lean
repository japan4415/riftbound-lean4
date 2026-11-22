module

public import Riftbound.Core.Ids
public import Riftbound.Core.CardType
public import Riftbound.Core.Domain
public import Riftbound.Core.Keyword

/-!
# The effect IR: the small parts

The vocabulary the pieces of the effect IR are built from (design.md §7.2): sides, places,
quantities, comparisons, the points of a turn, and the names of variables, choice slots and
custom handlers. Nothing here is recursive.
-/

@[expose] public section

namespace Riftbound

/-- Whose side an object is on, seen from the player the effect belongs to (CR 740.1). -/
inductive Side where
  /-- Friendly: controlled by the player. -/
  | friendly
  /-- Enemy: controlled by an opponent. -/
  | enemy
  /-- Either side. -/
  | any
deriving DecidableEq, Repr, Hashable

/-- Where an object is. -/
inductive Place where
  /-- Anywhere in play. -/
  | anywhere
  /-- At the Battlefield the effect is about: "here" (a Battlefield's own text, or a Unit's). -/
  | here
  /-- At a Battlefield (any). -/
  | atBattlefield
  /-- At a Base. -/
  | atBase
  /-- In the player's hand. -/
  | inHand
  /-- In the player's Trash. -/
  | inTrash
  /-- In the player's Main Deck. -/
  | inMainDeck
  /-- In the player's Rune Deck. -/
  | inRuneDeck
  /-- In the combat the effect is about. -/
  | inCombat
  /-- Hidden face down (CR 811). -/
  | inHidden
deriving DecidableEq, Repr, Hashable

/-- How many objects an effect takes (CR 355): "a", "up to N", "N", "each" or "all". -/
inductive Quantity where
  /-- Exactly one. -/
  | one
  /-- Up to `n`. -/
  | upTo (n : Nat)
  /-- Exactly `n`. -/
  | exactly (n : Nat)
  /-- Every one that matches. -/
  | all
deriving DecidableEq, Repr, Hashable

/-- A comparison. -/
inductive Cmp where
  /-- Equal. -/
  | eq
  /-- Less than. -/
  | lt
  /-- At most. -/
  | le
  /-- Greater than. -/
  | gt
  /-- At least. -/
  | ge
deriving DecidableEq, Repr, Hashable

/-- Which players an effect is about. -/
inductive PlayerSel where
  /-- The player the effect belongs to. -/
  | you
  /-- An opponent (in a 1v1 game, the one opponent). -/
  | opponent
  /-- Every player. -/
  | eachPlayer
  /-- Every opponent. -/
  | eachOpponent
  /-- The player who chose a slot of the effect. -/
  | chosen (slot : Nat)
  /-- The player the replaced event is about ("they draw 1 instead"). -/
  | eventPlayer
deriving DecidableEq, Repr, Hashable

/-- What a spell or an ability makes true for the rest of the turn (CR 389-393). -/
inductive TurnEffect where
  /-- The next spell the player plays this turn costs `n` Energy less. -/
  | nextSpellCostMinus (n : Nat)
  /-- The next unit the player plays this turn enters ready. -/
  | nextUnitReady
  /-- The units the player plays this turn enter ready. -/
  | unitsReady
  /-- Spells and abilities deal no damage this turn. -/
  | preventEffectDamage
deriving DecidableEq, Repr, Hashable

/-- The kind of card whose plays a turn effect watches: "the next spell", "the next unit". -/
def TurnEffect.playType : TurnEffect → CardType
  | .nextSpellCostMinus _ => .spell
  | _ => .unit

/-- A point of the turn a delayed effect or a trigger waits for (CR 314-317). -/
inductive Timing where
  /-- The start of the turn. -/
  | startOfTurn
  /-- The start of the Beginning Phase. -/
  | beginning
  /-- The end of the turn (the Ending Step). -/
  | endOfTurn
  /-- The start of the Main Phase. -/
  | startOfMain
  /-- The start of a combat. -/
  | startOfCombat
  /-- The end of a combat. -/
  | endOfCombat
  /-- The start of a showdown. -/
  | startOfShowdown
  /-- The end of a showdown. -/
  | endOfShowdown
deriving DecidableEq, Repr, Hashable

/-- Something a player or an object can do, for restrictions ("can't ...") and permissions
("may ...") (design.md §7.3). -/
inductive Act where
  /-- Attack. -/
  | attack
  /-- Move. -/
  | move
  /-- Be played. -/
  | play
  /-- Score. -/
  | score
  /-- Be chosen by a spell or ability. -/
  | beChosen
  /-- Be the target of a Reaction. -/
  | react
  /-- Ready. -/
  | ready
  /-- Draw. -/
  | draw
  /-- Be recalled. -/
  | recall
deriving DecidableEq, Repr, Hashable

/-- How fast an ability can be used (CR 806, 813). -/
inductive Speed where
  /-- Only when the player has priority on their own turn, with an empty Chain. -/
  | normal
  /-- Like an Action (CR 806). -/
  | action
  /-- Like a Reaction (CR 813). -/
  | reaction
deriving DecidableEq, Repr, Hashable

/-- How many times a trigger or a delayed effect fires. -/
inductive Occurrence where
  /-- Every time. -/
  | every
  /-- On the `n`-th time only. -/
  | nth (n : Nat)
  /-- On the next `n` times, then no more. -/
  | next (n : Nat)
deriving DecidableEq, Repr, Hashable

/-- Where a point comes from when a player scores. -/
inductive ScoreSource where
  /-- Conquering a Battlefield. -/
  | conquer
  /-- Holding a Battlefield. -/
  | hold
deriving DecidableEq, Repr, Hashable

/-- The name of a variable bound in an effect (design.md §7.2). -/
structure VarId where
  /-- The name. -/
  name : String
deriving DecidableEq, Repr, Hashable

/-- The name of a handler in the table of custom handlers (design.md §7.1). -/
structure CustomId where
  /-- The name. -/
  name : String
deriving DecidableEq, Repr, Hashable

end Riftbound

end
