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
  /-- The amount of the event a replacement ability changes (draw N, channel N, score N). -/
  | eventAmount
  /-- How many turns the players have taken so far. -/
  | turnsTaken (p : PlayerSel)
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
  /-- The points of the players. -/
  | points (p : PlayerSel)
  /-- The Victory Score of the game (CR 194). -/
  | victoryScore
  /-- The highest Might among the objects (0 if there are none). -/
  | highestMight (s : Selector)
  /-- The number the keyword carries, summed over the objects ("my [Assault]"). -/
  | kwAmount (s : Selector) (k : Keyword)
  /-- How many cards the player has played this turn. -/
  | cardsPlayed
  /-- How many Standard Moves the object made this turn. -/
  | movesThisTurn
  /-- How many notes of the effect the object has this turn (for the player who made them). -/
  | notes (e : TurnEffect)
  /-- The Energy that was paid to play the object (0 if it was played for nothing). -/
  | energyPaid
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
  /-- Its Power cost (the number of Power it asks for) compares to the amount. -/
  | powerCost (op : Cmp) (a : Amount)
  /-- Is a Battlefield an opponent of the object's controller controls. -/
  | controlledByOpponent
  /-- Made its last move this turn from the Battlefield the object the effect belongs to is. -/
  | movedFromHere
  /-- Is exhausted. -/
  | exhausted
  /-- The object is at a Battlefield (not at a Base). -/
  | onBattlefield
  /-- A Spell whose effect has no choice to make when it is played. -/
  | noChoices
  /-- The Energy cost is less than the points of the player the effect belongs to. -/
  | costBelowPoints
  /-- A Battlefield with room for one more hidden card (CR 811). -/
  | hideRoom
  /-- The card has a passive ability that lets the Units of its player be played to an open
  Battlefield. -/
  | permitsOpenPlay
  /-- Is ready. -/
  | ready
  /-- Has damage. -/
  | damaged
  /-- Has lethal damage: damage that is not 0 and at least its Might (CR 142.4.b). -/
  | lethal
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
  /-- Does not have the property. -/
  | not (f : Filter)
  /-- Is a card hidden face down (CR 811). -/
  | hidden
  /-- Is among the first `n` cards of the Main Deck or of the Rune Deck of its owner. -/
  | top (n : Nat)
  /-- Is a Battlefield nobody controls: an open Battlefield. -/
  | openBf
  /-- The Battlefield the player of `self` scored this turn. -/
  | scoredByMine
  /-- The card is in its owner's hand. -/
  | inHandZone
  /-- The Battlefield where the player of `self` is attacking. -/
  | attackedByMine
  /-- Is a Battlefield where a unit of another player than the one the effect belongs to is. -/
  | enemyOccupied
  /-- Is a Battlefield its controller of the object the effect belongs to controls. -/
  | controlled
  /-- Is the object a selector names (`self`, a chosen object or a variable). -/
  | sameAs (s : Selector)
  /-- Is at the place the selector gives (a Battlefield, for example the one that was chosen). -/
  | at_ (s : Selector)
  /-- Is the only unit of its side in the combat ("alone"). -/
  | alone
  /-- Is attached to the object the selector names (`self`, a chosen object or a variable). -/
  | attachedTo (s : Selector)
  /-- Is attached to a unit: an Equipment that is not detached. -/
  | isAttached
  /-- Is a token. -/
  | token
  /-- Is a spell that chooses a unit or a gear of the player the effect belongs to. -/
  | choosesMine
  /-- Made its last move from a Battlefield. -/
  | fromBattlefield
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
  /-- The Battlefields the objects are at (a Unit in a Base is at none). -/
  | locationOf (s : Selector)
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
  /-- An additional cost was paid when the object was played (CR 357.2). -/
  | paid
  /-- The controller has played another card this turn, as the ability is used (CR 812). -/
  | playedAnother
  /-- The player's Rune Pool can pay the cost. -/
  | canPay (c : Cost)
  /-- A unit of an opponent has died this turn. -/
  | enemyUnitDied
  /-- The object has been noted this turn for the player with the effect. -/
  | marked (e : TurnEffect)
  /-- The object came into play from Hidden. -/
  | fromHidden
  /-- The player assigned at least `n` excess damage to enemy Units in the last Combat this turn. -/
  | excessAtLeast (n : Nat)
  /-- The player has the effect noted this turn. -/
  | noted (e : TurnEffect)
  /-- The player has a passive ability that lets them hide a card for one Energy (Swift Scout). -/
  | hidesWithEnergy
  /-- The player has a card in play, or a Legend, that is the card (Heimerdinger). -/
  | hasFriendlyCard (id : CardId)
  /-- The object an ability watches (its first slot) was noted with the effect for its player when
  it died, this turn. -/
  | diedWith (e : TurnEffect)
  /-- The player has discarded a card this turn. -/
  | discardedThisTurn
  /-- It is the turn of the player the effect belongs to. -/
  | yourTurn
  /-- A combat is going on. -/
  | inCombat
  /-- A showdown is going on. -/
  | inShowdown
  /-- The point being scored comes from this source. -/
  | scoreFrom (src : ScoreSource)
deriving DecidableEq, Repr, Hashable

end

end Riftbound

end
