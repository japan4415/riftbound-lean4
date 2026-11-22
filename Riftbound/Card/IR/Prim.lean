module

public import Riftbound.Card.IR.Expr
public import Riftbound.Core.Cost

/-!
# The effect IR: primitives, durations, arguments and static modifications

The parts of an effect that do not contain another effect (design.md §7.2): the primitives, which
follow the game actions of the Core Rules (CR 408-446), how long an effect lasts, the arguments of
a custom handler, and the modifications a static ability makes.
-/

@[expose] public section

namespace Riftbound

/-- Where objects are moved to. -/
inductive Dest where
  /-- The Base of the player the effect belongs to. -/
  | base
  /-- The place the selector gives: a Battlefield. -/
  | at_ (s : Selector)
deriving DecidableEq, Repr, Hashable

/-- A game action: one thing an effect does (CR 408-446). -/
inductive Prim where
  /-- The players draw cards (CR 414). -/
  | draw (p : PlayerSel) (n : Amount)
  /-- The players discard cards (CR 415). -/
  | discard (p : PlayerSel) (n : Amount)
  /-- Deal damage to objects. -/
  | deal (s : Selector) (n : Amount)
  /-- Heal damage from objects. -/
  | heal (s : Selector) (n : Amount)
  /-- Kill objects. -/
  | kill (s : Selector)
  /-- Banish objects. -/
  | banish (s : Selector)
  /-- Recall objects to their Base, exhausted if `exhausted` (a recall is not a move). -/
  | recall (s : Selector) (exhausted : Bool)
  /-- Return objects to their owners' hands. -/
  | returnToHand (s : Selector)
  /-- Move objects to a Battlefield or a Base. -/
  | move (s : Selector) (dest : Dest)
  /-- Ready objects. -/
  | ready (s : Selector)
  /-- Exhaust objects. -/
  | exhaust (s : Selector)
  /-- Stun objects. -/
  | stun (s : Selector)
  /-- Buff objects. -/
  | buff (s : Selector)
  /-- Spend the buff of units: they lose it (CR 704). -/
  | spendBuff (s : Selector)
  /-- Recycle objects to the bottom of their decks. -/
  | recycle (s : Selector)
  /-- The players recycle the top card of their Main Deck: it goes to the bottom (CR 417). -/
  | recycleTop (p : PlayerSel)
  /-- The players channel `n` Runes, and `extraExhausted` more that enter exhausted. -/
  | channel (p : PlayerSel) (n : Amount) (extraExhausted : Amount)
  /-- Add Energy to a Rune Pool; it can be spent on `only` if that is given. -/
  | addEnergy (p : PlayerSel) (n : Amount) (only : Option Act)
  /-- Add Power to a Rune Pool, of a domain or of any; it can be spent on `only` if given. -/
  | addPower (p : PlayerSel) (n : Amount) (d : Option Domain) (only : Option Act)
  /-- Counter a spell. -/
  | counter (s : Selector)
  /-- Play a card. -/
  | play (s : Selector)
  /-- Hide cards face down at a Battlefield (CR 811). -/
  | hideAt (s : Selector) (bf : Selector)
  /-- Reveal cards from the top of the Main Deck until one with the properties is revealed, play it
  without paying its cost, and recycle the others (all of them if none matches). Only a Unit or a
  Gear can be played this way. -/
  | playFirst (fs : FilterList)
  /-- Play cards without paying their cost, to a Battlefield. -/
  | playTo (s : Selector) (bf : Selector)
  /-- Put cards in their owner's Trash: not killed, so nothing that waits for a death fires. -/
  | bin (s : Selector)
  /-- Discard cards of a hand: the player of the cards discards them (CR 423). -/
  | discardCard (s : Selector)
  /-- Hide a card. -/
  | hide (s : Selector)
  /-- Reveal cards. -/
  | reveal (s : Selector)
  /-- Play tokens, by name, in a place: `n` of them, ready or exhausted (CR 179-187, 359). -/
  | create (token : String) (n : Amount) (at_ : Place) (ready : Bool)
  /-- Attach objects to an object. -/
  | attach (s : Selector) (to : Selector)
  /-- Detach objects. -/
  | detach (s : Selector)
  /-- The players gain XP. -/
  | gainXP (p : PlayerSel) (n : Amount)
  /-- The players score points. -/
  | score (p : PlayerSel) (n : Amount)
  /-- The players Burn Out `n` times in a row (CR 432). -/
  | burn (p : PlayerSel) (n : Amount)
  /-- Look at the top cards of the Main Deck and recycle some. -/
  | predict (n : Amount)
  /-- Copy an object. -/
  | copy (s : Selector)
  /-- Double the Might of an object. -/
  | double (s : Selector)
  /-- Swap two objects. -/
  | swap (a b : Selector)
  /-- Empower units. -/
  | empower (s : Selector)
  /-- Disempower units. -/
  | disempower (s : Selector)
  /-- Take control of objects. -/
  | takeControl (s : Selector)
  /-- The players take an extra turn (CR 734-738). -/
  | extraTurn (p : PlayerSel)
  /-- The players win the game. -/
  | win (p : PlayerSel)
  /-- Make something true for the rest of the turn. -/
  | turnEffect (e : TurnEffect)
  /-- Activate the conquer effects of the units. -/
  | activateConquer (s : Selector)
  /-- Make something true for the rest of the turn about the objects. -/
  | markOn (s : Selector) (e : TurnEffect)
  /-- Pay Energy and Power from the Rune Pool, as an effect resolves (CR 357). -/
  | pay (c : Cost)
deriving DecidableEq, Repr, Hashable

/-- How long an effect lasts. -/
inductive Duration where
  /-- Until the end of this turn. -/
  | thisTurn
  /-- Until the end of this combat. -/
  | thisCombat
  /-- Until the end of this showdown. -/
  | thisShowdown
  /-- Until the end of the next turn. -/
  | nextTurn
  /-- As long as the condition holds. -/
  | whileCond (c : Condition)
  /-- For the rest of the game. -/
  | permanent
deriving DecidableEq, Repr, Hashable

/-- An argument of a custom handler: an expression the interpreter evaluates (design.md §7.1). -/
inductive Arg where
  /-- An amount. -/
  | amount (a : Amount)
  /-- Some objects. -/
  | selector (s : Selector)
  /-- A condition. -/
  | condition (c : Condition)
deriving DecidableEq, Repr, Hashable

/-- The arguments of a custom handler. -/
inductive ArgList where
  /-- No argument. -/
  | nil
  /-- An argument, then the rest. -/
  | cons (a : Arg) (rest : ArgList)
deriving DecidableEq, Repr, Hashable

/-- What a trigger waits for (CR 389, 390-393). -/
inductive TriggerEvent where
  /-- The object is played. -/
  | play
  /-- The object enters play. -/
  | enter
  /-- The object attacks. -/
  | attack
  /-- The object defends. -/
  | defend
  /-- The object conquers a Battlefield. -/
  | conquer
  /-- The object holds a Battlefield. -/
  | hold
  /-- The object moves. -/
  | move
  /-- The object dies. -/
  | die
  /-- The object leaves play. -/
  | leave
  /-- A card is drawn. -/
  | draw
  /-- A card is discarded. -/
  | discard
  /-- The object is stunned. -/
  | stun
  /-- The object is readied (it was exhausted). -/
  | ready
  /-- The object gets a buff. -/
  | buff
  /-- The player plays a card from Hidden (CR 811). -/
  | playHidden
  /-- A combat the object was in ends. -/
  | combatEnd
  /-- The unit becomes Mighty. -/
  | becomeMighty
  /-- The unit becomes Empowered. -/
  | becomeEmpowered
  /-- Points are scored. -/
  | scored
  /-- The player conquers a Battlefield (a Legend or a Battlefield watches the player). -/
  | youConquer
  /-- The player holds a Battlefield. -/
  | youHold
  /-- The unit's Might becomes `n` or more. -/
  | mightAtLeast (n : Nat)
  /-- A point of the turn comes. -/
  | at_ (t : Timing)
deriving DecidableEq, Repr, Hashable

/-- Something that happens in the game that a replacement ability can change (CR 367-375). -/
inductive ReplaceEvent where
  /-- The object would die. -/
  | die
  /-- The object would be dealt damage. -/
  | takeDamage
  /-- The player would draw. -/
  | draw
  /-- The player would score. -/
  | score
  /-- The player would channel. -/
  | channel
  /-- The object would enter play exhausted. -/
  | enterExhausted
deriving DecidableEq, Repr, Hashable

/-- What a static ability changes in the game (design.md §7.3). -/
inductive StaticMod where
  /-- Objects get more Might. -/
  | mightPlus (s : Selector) (a : Amount)
  /-- Objects get less Might. -/
  | mightMinus (s : Selector) (a : Amount)
  /-- Objects get less Might, to a minimum: the change never takes their Might below `floor`
  ("to a minimum of 1"). -/
  | mightMinusMin (s : Selector) (a : Amount) (floor : Nat)
  /-- Objects get a keyword (CR 479.3). -/
  | keyword (s : Selector) (k : KeywordInst)
  /-- The object takes no damage from anything (CR 142). -/
  | noDamage
  /-- The Units at this Battlefield cannot make a Standard Move to the Base (CR 144). -/
  | noMoveToBase
  /-- The Hidden cards of the opponents of the Units at this place cannot be revealed here
  (CR 811). -/
  | noHiddenReveal
  /-- Spells and abilities that affect the units at this Battlefield each deal `n` Bonus Damage
  more (CR 142). -/
  | bonusDamageHere (n : Nat)
  /-- Objects cost less Energy, to a minimum: never below `floor` (CR 356). -/
  | costMinusMin (s : Selector) (a : Amount) (floor : Nat)
  /-- Objects cost more Energy (CR 356). -/
  | costPlus (s : Selector) (a : Amount)
  /-- Objects cost less Energy (CR 356). -/
  | costMinus (s : Selector) (a : Amount)
  /-- Objects can't do something ("can't" beats "can") (CR 054). -/
  | cant (s : Selector) (act : Act)
  /-- Objects may do something they could not. -/
  | may (s : Selector) (act : Act)
  /-- The Victory Score goes up. -/
  | victoryScorePlus (a : Amount)
  /-- The Victory Score goes down. -/
  | victoryScoreMinus (a : Amount)
  /-- The player ignores a keyword of the opponents' objects at a place ("you ignore Tank
  here"). -/
  | ignoreKeyword (k : Keyword) (where_ : Place)
  /-- The objects enter ready. -/
  | entersReady (s : Selector)
  /-- The player's spells and abilities deal more damage (Bonus Damage). -/
  | bonusDamage (a : Amount)
  /-- The player's triggered abilities for the event fire one more time, at the place. -/
  | triggersExtra (ev : TriggerEvent) (where_ : Place)
  /-- The players can't do something at a place until their `untilTurn`-th turn. -/
  | cantPlayer (p : PlayerSel) (act : Act) (where_ : Place) (untilTurn : Nat)
  /-- A modification the IR cannot express: a handler of the table of custom handlers. -/
  | custom (id : CustomId) (args : ArgList)
deriving DecidableEq, Repr, Hashable

/-- A cost of an ability or an additional cost of a card (CR 356, 408-446). The Energy and Power of
a card are a `Cost` (`Riftbound.Core.Cost`); these are the others. -/
inductive AbilityCost where
  /-- Exhaust the object the ability belongs to. -/
  | exhaustSelf
  /-- Pay Energy and Power. -/
  | pay (c : Cost)
  /-- Recycle cards from the Trash. -/
  | recycleFromTrash (n : Nat)
  /-- Discard cards. -/
  | discard (n : Nat)
  /-- Kill friendly objects that match. -/
  | killFriendly (q : Quantity) (fs : FilterList)
  /-- Spend XP. -/
  | spendXP (n : Nat)
  /-- Spend a buff. -/
  | spendBuff
  /-- The ability can be used only while its card is in the hand: Hide (CR 811). -/
  | fromHand
  /-- The ability can be used only while its card is hidden, from the turn after (CR 811). -/
  | fromHidden
  /-- Disempower the unit. -/
  | disempowerSelf
  /-- Recycle the object itself. -/
  | recycleSelf
  /-- Kill the object the ability belongs to ("Kill this"). -/
  | killSelf
deriving DecidableEq, Repr, Hashable

/-- When a triggered ability or a delayed effect fires. -/
structure Trigger where
  /-- What happens. -/
  event : TriggerEvent
  /-- To which objects it happens. -/
  subject : Selector := .self
  /-- A condition that has to hold ("if ..."). -/
  condition : Condition := .always
  /-- How many times it fires. -/
  occurrence : Occurrence := .every
deriving DecidableEq, Repr, Hashable

end Riftbound

end
