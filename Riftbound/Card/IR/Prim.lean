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

/-- Who replays a banished Unit and where the effect requires it to enter. -/
inductive BanishReplay where
  /-- Its owner plays it to a legal location. -/
  | byOwner
  /-- Its owner plays it to the location it left. -/
  | sameLocation
  /-- The effect's controller plays it to their Base. -/
  | toBase
deriving DecidableEq, Repr, Hashable

/-- A game action: one thing an effect does (CR 408-446). -/
inductive Prim where
  /-- The players draw cards (CR 414). -/
  | draw (p : PlayerSel) (n : Amount)
  /-- The players discard cards (CR 415). -/
  | discard (p : PlayerSel) (n : Amount)
  /-- Deal damage to objects. -/
  | deal (s : Selector) (n : Amount)
  /-- Two units deal damage equal to their current Mights to each other (CR 418.6.b.3). -/
  | exchangeDamage (a b : Selector)
  /-- Set a Unit's base Might for the rest of the turn (CR 143.2.a, 479.2). -/
  | setBaseMight (s : Selector) (n : Amount)
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
  /-- The players swap the top two cards of their Main Deck (Predict puts the cards back in any
  order). -/
  | swapTop (p : PlayerSel)
  /-- The players channel `n` Runes, and `extraExhausted` more that enter exhausted. -/
  | channel (p : PlayerSel) (n : Amount) (extraExhausted : Amount)
  /-- Add Energy to a Rune Pool; it can be spent on `only` if that is given. -/
  | addEnergy (p : PlayerSel) (n : Amount) (only : Option Act)
  /-- Add Energy that pays only for Units and their activated abilities. -/
  | addUnitEnergy (p : PlayerSel) (n : Amount)
  /-- Add Power to a Rune Pool, of a domain or of any; it can be spent on `only` if given. -/
  | addPower (p : PlayerSel) (n : Amount) (d : Option Domain) (only : Option Act)
  /-- Counter a spell. -/
  | counter (s : Selector)
  /-- Counter a spell: it returns to its owner's hand, not the Trash (Abandon). -/
  | counterToHand (s : Selector)
  /-- Play a card. -/
  | play (s : Selector)
  /-- Play a card ignoring its printed cost, with a requirement to play it to Base (CR 355.17). -/
  | playAtBase (s : Selector)
  /-- Banish the Units, then play them according to the effect's instructions (CR 420.3, 428).
  A banished token ceases to exist. -/
  | banishReplay (s : Selector) (replay : BanishReplay := .byOwner)
  /-- The Unit attached to this Equipment snapshots the chosen Unit's copyable traits (CR 479.1). -/
  | copyAttachedFrom (s : Selector)
  /-- Play the cards, ignoring their Energy cost: their Power cost is paid (Promising Future). -/
  | playPaying (s : Selector)
  /-- Play the cards, paying their cost less `less` Energy (and all their Power), to a Battlefield
  if one is given. Spells are cast on the Chain (Void Rush). -/
  | playReduced (s : Selector) (less : Amount) (to : Option Selector)
  /-- Give the objects all the keywords the object has now, for the turn (Kato the Arm). -/
  | giveKeywords (to : Selector) (from_ : Selector)
  /-- Queue the Trash spell, ignoring its base Energy cost, and Recycle it after it resolves
  (Kai'Sa, Evolutionary and Fizz, Trickster). -/
  | castInline (s : Selector)
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
  /-- Discard a card, with a linked reflexive trigger for each matching type (CR 387.1.b). -/
  | discardWithTypeTriggers (s : Selector) (links : List (CardType × Nat))
  /-- Hide a card. -/
  | hide (s : Selector)
  /-- Reveal cards. -/
  | reveal (s : Selector)
  /-- Reveal the top `n` cards of the player's Main Deck. -/
  | revealTop (n : Nat)
  /-- The same, with nothing done first (what `revealTop` does once a passive ability has had its
  say). -/
  | revealTopNow (n : Nat)
  /-- Reveal, with nothing done first (what `reveal` does once a passive ability has had its say). -/
  | revealNow (s : Selector)
  /-- Play tokens, by name, in a place: `n` of them, ready or exhausted (CR 179-187, 359). -/
  | create (token : String) (n : Amount) (at_ : Place) (ready : Bool)
  /-- Play all the tokens at the single selected Battlefield (CR 184.2, 355.2). -/
  | createAt (token : String) (n : Amount) (battlefield : Selector) (ready : Bool)
  /-- Play a Unit token, choosing its location as it is played (CR 185.2.a, 355.2). -/
  | playUnitToken (token : String)
  /-- Play a Unit token at the chosen Battlefield, or at its Base (CR 185.2.a). -/
  | playUnitTokenAt (token : String) (dest : Option ObjId)
  /-- Attach objects to an object. -/
  | attach (s : Selector) (to : Selector)
  /-- Attach Equipment to an object, paying the Equip cost of each, less `less` Power
  (Weaponmaster). Nothing happens if the cost cannot be paid. -/
  | attachPaying (s : Selector) (to : Selector) (less : Nat)
  /-- Detach objects. -/
  | detach (s : Selector)
  /-- The players gain XP. -/
  | gainXP (p : PlayerSel) (n : Amount)
  /-- The player spends XP (it goes down by the amount, to 0 at the least). -/
  | spendXP (p : PlayerSel) (n : Amount)
  /-- The players score points. -/
  | score (p : PlayerSel) (n : Amount)
  /-- Put the top `n` cards of the players' Main Decks into their Trash (CR 441). -/
  | burn (p : PlayerSel) (n : Amount)
  /-- Burn from your Main Deck and fire the linked reflexive ability for each Unit burned
  (CR 388-389, 441). -/
  | burnWithUnitTrigger (n : Amount) (idx : Nat)
  /-- Look at the top cards of the Main Deck and recycle some. -/
  | predict (n : Amount)
  /-- Copy an object. -/
  | copy (s : Selector)
  /-- Double the Might of an object. -/
  | double (s : Selector)
  /-- Give the selected objects an activated ability on the Chain until the end of the turn
  (CR 317.2, 376-381, 479.3). -/
  | grantActivation (s : Selector) (ability : AbilityGrant)
  /-- Swap two objects. -/
  | swap (a b : Selector)
  /-- Empower Units, Gear, or Legends (CR 442). -/
  | empower (s : Selector)
  /-- Disempower Units, Gear, or Legends (CR 443). -/
  | disempower (s : Selector)
  /-- Take control of objects. -/
  | takeControl (s : Selector)
  /-- The tokens the first selector names become copies of the object the second names: they have
  its card (Reflection). -/
  | becomeCopy (s src : Selector)
  /-- Add the Battlefield token to the board, if it is not there already (Baron Pit). -/
  | addBattlefield (token : String)
  /-- Play `n` tokens at the place the object came from by its last move: the Battlefield it left,
  else the Base (Lillia). -/
  | createAtPrev (token : String) (n : Amount) (ready : Bool)
  /-- Play an additional copy of each token the selector names, where it is (Zilean). -/
  | cloneToken (s : Selector)
  /-- Banish the objects, and remember that this object banished them (Cursed Sarcophagus,
  Virtuoso). -/
  | banishWith (s : Selector)
  /-- Move every card of a side in a zone off the board that has the properties to another zone:
  to the Banishment, noting that this object banished them if asked (Cursed Sarcophagus). -/
  | moveAll (side : Side) (place : Place) (fs : FilterList) (dest : Place) (mark : Bool)
  /-- The objects gain the tag (for good): Ivern is a Bird, a Cat, a Dog or a Poro; The List names
  a tag. -/
  | gainTag (s : Selector) (name : String)
  /-- Replace the Battlefield with the Battlefield token: it is set aside, and the units there stay
  at the token (Green Father). -/
  | replaceBattlefield (old : Selector) (token : String)
  /-- Put the Battlefield the token replaced back, in place of the token (Brush). -/
  | restoreBattlefield (cur : Selector)
  /-- Play, for free, every Unit in the player's Banishment that this object (an Equipment)
  banished when its Unit died (The Zero Drive). -/
  | playBanishedWith
  /-- The objects go back to their owners' control (Hostile Takeover). -/
  | returnControl (s : Selector)
  /-- Take control of objects until the source (a Unit) leaves the board: the objects remember the
  card of the source (Akshan). -/
  | takeControlUntilLeaves (s : Selector)
  /-- The players take an extra turn (CR 734-738). -/
  | extraTurn (p : PlayerSel)
  /-- The players win the game. -/
  | win (p : PlayerSel)
  /-- Make something true for the rest of the turn. -/
  | turnEffect (e : TurnEffect)
  /-- The player returns their Chosen Champion from their Trash to their Champion Zone, if it is
  empty. -/
  | returnChampion
  /-- Two Units swap places: each goes to where the other is (a Battlefield or a Base). -/
  | swapPlaces (a b : Selector)
  /-- Look at the top `n` cards of the Main Deck of the player. -/
  | lookTop (n : Nat)
  /-- The player chooses the objects while the effect resolves: nothing changes but the events
  ("when you choose"). -/
  | choose (s : Selector)
  /-- Activate the conquer effects of the units. -/
  | activateConquer (s : Selector)
  /-- Make something true for the rest of the turn about the objects. -/
  | markOn (s : Selector) (e : TurnEffect)
  /-- Create the source's delayed trigger for when a selected Unit dies this turn (CR 391-393). -/
  | delayUntilDeath (s : Selector) (idx : Nat)
  /-- Pay Energy and Power from the Rune Pool, as an effect resolves (CR 357). -/
  | pay (c : Cost)
  /-- Put cards on the top of their owners' Main Decks. -/
  | topdeck (s : Selector)
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
  /-- The player completes their first play of a card this turn (CR 420.4.a). -/
  | firstCardResolved
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
  /-- A Deathknell that is explicitly represented as a triggered ability (CR 808). -/
  | deathknell
  /-- The object leaves play. -/
  | leave
  /-- A card is drawn. -/
  | draw
  /-- The player banishes a card they own. -/
  | banishOwn
  /-- A card is discarded. -/
  | discard
  /-- The object is stunned. -/
  | stun
  /-- The object becomes exhausted while on the Board (CR 415). -/
  | exhaust
  /-- This ability's controller exhausts at least this many friendly Units at once (CR 415). -/
  | youExhaustUnits (minimum : Nat)
  /-- The object is readied (it was exhausted). -/
  | ready
  /-- The object gets a buff. -/
  | buff
  /-- The player plays a card from Hidden (CR 811). -/
  | playHidden
  /-- The player looks at this card on the top of their Main Deck (and does not draw it). -/
  | seenOnTop
  /-- A player chooses a unit of theirs that is at this Battlefield with a spell: the choice made
  when the spell is played (not the choices made as it resolves, nor those of abilities). -/
  | chosenHere
  /-- The player uses an activated ability of a gear of theirs (a unit of theirs watches). -/
  | useGearAbility
  /-- The player plays a Unit, Gear, or activated ability whose base Energy cost is at least this
  much (CR 206-206.1). -/
  | playAtBaseEnergy (minimum : Nat)
  /-- An Equipment is attached to the unit (the unit itself waits for it). -/
  | attachedTo
  /-- The player defends at a Battlefield (their units elsewhere wait for it; the ability reaches
  the Battlefield as its first slot). -/
  | youDefend
  /-- The player spends a buff of one of their units (their units wait for it). -/
  | spendBuff
  /-- The unit is chosen by a spell of its player ("when you choose me with a spell"); a Legend,
  a Gear or a Unit that watches the units chosen has a subject that is a selector. -/
  | chosen
  /-- The unit is chosen by a spell or an ability of its player ("when you choose me"). -/
  | chosenAny
  /-- The player kills a unit with a spell, and the card is in their Trash. -/
  | killBySpell
  /-- The player conquers a Battlefield, and the card is in their Trash. -/
  | conquerFromTrash
  /-- The player recycles one or more cards (CR 417). -/
  | recycle
  /-- The player recycled a Rune (to the Rune Deck). -/
  | recycleRune
  /-- The player hid a card (it went face down at a Battlefield). -/
  | hide
  /-- An opponent of the player scores (a Battlefield is conquered or held). -/
  | opponentScores
  /-- An opponent of the player holds a Battlefield. -/
  | opponentHolds
  /-- An opponent holds the Battlefield where the source is located (CR 830). -/
  | opponentHoldsHere
  /-- The player moves a unit with an effect (Blast Cone). -/
  | movedByYou
  /-- The card is revealed from its owner's deck. -/
  | revealedFromDeck
  /-- A Unit token is played (the watcher is told the token). -/
  | playToken
  /-- A Combat starts at the Battlefield (CR 466.2.b). -/
  | combatStart
  /-- A combat the object was in ends. -/
  | combatEnd
  /-- The object's side wins a combat: only its units are left at the Battlefield (a Unit says "I
  win", a Legend "you win"). -/
  | winCombat
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
  /-- The linked Burn instruction burned a Unit card (CR 388-389). -/
  | linkedBurnUnit
  /-- The linked Discard instruction discarded a card of the corresponding type. -/
  | linkedDiscardType
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
  /-- This Equipment attaches, then runs an instruction with its new Unit in slot 0 (CR 370.1.b.1). -/
  | attach
deriving DecidableEq, Repr, Hashable

/-- What a static ability changes in the game (design.md §7.3). -/
inductive StaticMod where
  /-- Objects get more Might. -/
  | mightPlus (s : Selector) (a : Amount)
  /-- Objects that have the keyword after the keyword layer get more Might (CR 479.3-479.4). -/
  | mightPlusWithKeyword (s : Selector) (k : Keyword) (a : Amount)
  /-- Objects get less Might. -/
  | mightMinus (s : Selector) (a : Amount)
  /-- Objects get less Might, to a minimum: the change never takes their Might below `floor`
  ("to a minimum of 1"). -/
  | mightMinusMin (s : Selector) (a : Amount) (floor : Nat)
  /-- Objects get a keyword (CR 479.3). -/
  | keyword (s : Selector) (k : KeywordInst)
  /-- A granted Flow instance whose cost is the affected Spell's base cost (CR 829). -/
  | flowAtBaseCost
  /-- Each Equipment of the player gives the Unit it is attached to the keyword (Purifier: one more
  time for each Equipment). -/
  | equipEach (k : KeywordInst)
  /-- The object takes no damage from anything (CR 142). -/
  | noDamage
  /-- Prevent damage from enemy spells and abilities. -/
  | noEnemyEffectDamage
  /-- Enemy spells and abilities cannot move this Unit. -/
  | noEnemyEffectMove
  /-- The Units at this Battlefield cannot make a Standard Move to the Base (CR 144). -/
  | noMoveToBase
  /-- The opponents of the player play Units only to their Base (not to a Battlefield). -/
  | oppsPlayToBaseOnly
  /-- Opponents cannot play a card with the name this source chose (CR 054, 759-762). -/
  | oppsCantPlayNamed
  /-- The controller skips their Draw Phase (CR 315.4). -/
  | skipDrawPhase
  /-- The controller can play cards from their Trash at their regular costs (CR 420.1). -/
  | playFromTrash
  /-- A card entering the controller's Trash from outside their Main Deck is banished instead
  (CR 367-370). -/
  | banishInsteadOfTrash
  /-- (Of an Equipment's grants) if the Unit it is attached to would die, the Equipment dies instead,
  and the Unit is healed, exhausted and recalled (Guardian Angel). -/
  | diesInsteadGear
  /-- If another Unit of the player at the same Battlefield with less Might would die, it is healed,
  exhausted and recalled instead (Soraka). -/
  | rescueWeakerHere
  /-- The objects the selector gives add this much more Energy when they Add (Chem-Baroness). -/
  | manaExtraEnergy (s : Selector) (n : Amount)
  /-- The optional additional costs the player pays cost this much less (Ezreal, Prodigy). -/
  | extraCostLess (n : Nat)
  /-- The Repeat costs the player pays cost this much less (Marai Spire). -/
  | repeatCostLess (n : Nat)
  /-- The first activated ability of a Gear its controller plays each turn costs less Energy. -/
  | firstGearAbilityLess (n : Nat)
  /-- The controller's Units here pay less for Empower, in Energy or Power per reduction. -/
  | empowerHereLess (n : Nat)
  /-- (Of an Equipment) the Unit it is attached to has the triggered abilities of its own card once
  more (Svellsongur copies the text of the Unit). -/
  | copiesUnitText
  /-- (Of an Equipment's grants) the Unit it is attached to is banished when it dies, not put in the
  Trash (The Zero Drive: Deathknell, banish me). -/
  | banishOnDeath
  /-- If the player would reveal cards from a deck, they look at the top card first and may recycle
  it (Void Hatchling). -/
  | lookBeforeReveal
  /-- Spells of the player that choose this object cost this much less (1 Energy or 1 Power of
  any domain: the player's choice) (Irelia). -/
  | chosenSpellsCostLess (n : Nat)
  /-- Spells that choose a friendly Unit here cost less Power (CR 355-356). -/
  | friendlyTargetPowerCut (n : Nat)
  /-- Cards with Reaction cost more Power during the Showdown here (CR 341, 356, 813). -/
  | showdownReactionTax (n : Nat)
  /-- Legends of the controller of this Battlefield can: Exhaust, attach an Equipment they control to
  a unit they control (Forge of the Fluft). -/
  | legendsAttach
  /-- The object has Assault equal to the number of objects the selector gives (Ancient Warmonger). -/
  | assaultCount (s : Selector)
  /-- Units cannot move to a Base from anywhere (Minotaur Reckoner). -/
  | noMoveToBaseAny
  /-- The card can be played from the hand to a Battlefield with the properties (Rengar: one it is
  attacking), as an ability. -/
  | playToBf (fs : List Filter)
  /-- The card is not played to the Base from the hand: only where `playToBf` says. -/
  | noPlayToBase
  /-- Spells and abilities cannot ready the Units and Gear of the opponents of the player. -/
  | noReadyOfOpps
  /-- Units can move here from anywhere: from another Battlefield, too (Baron Pit). -/
  | movesHereFromAnywhere
  /-- The Spells of the player have Repeat, for the cost (Syndra, in a showdown). -/
  | grantRepeat (k : Cost)
  /-- A card with Hidden can be hidden for one Energy instead of one Power. -/
  | hideWithEnergy
  /-- The Unit must be assigned combat damage last (after the others, but not before a Tank). -/
  | assignedLast
  /-- Any amount of the damage of the player's side is enough to kill the enemy units (Elder
  Dragon). -/
  | anyDamageKills
  /-- The card enters play exhausted (a Gear: Honeyfruit, Scryer's Bloom). -/
  | entersExhausted
  /-- The Unit can have any number of buffs. -/
  | anyBuffs
  /-- The friendly Units can be played to an open Battlefield. -/
  | playToOpenBf
  /-- The units of the player can be played to the Battlefields that have the properties (Arachnoid
  Horror: to an occupied one with an enemy unit alone there). -/
  | playToBfAll (fs : List Filter)
  /-- Any player may pay this additional cost to play a Unit with the given tag here (CR 355.17). -/
  | playHereFor (tag : Tag) (cost : Cost)
  /-- One more card can be hidden at this Battlefield. -/
  | extraHide
  /-- A Combat where the player attacks that ends in a tie recalls all Units, not only theirs. -/
  | recallAllOnTie
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
  /-- Objects cost `a` Power symbols more (an `[A]` each: `more`), or less (the symbols of the
  domain, or any if none is named). -/
  | costPower (s : Selector) (a : Amount) (dom : Option Domain) (more : Bool)
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
  /-- The player's abilities from sources of this type deal more damage (CR 142). -/
  | bonusAbilityDamage (sourceType : CardType) (a : Amount)
  /-- The player's triggered abilities for the event fire one more time, at the place. -/
  | triggersExtra (ev : TriggerEvent) (where_ : Place)
  /-- The players can't do something at a place until their `untilTurn`-th turn. -/
  | cantPlayer (p : PlayerSel) (act : Act) (where_ : Place) (untilTurn : Nat)
  /-- Replace a point from scoring a Battlefield on one's first `turns` turns with a draw. -/
  | earlyScoreDraw (turns : Nat)
  /-- The Unit deals no combat damage (Ezreal, Dashing). -/
  | noCombatDamage
  /-- Limit the number of runes normally channeled at the start of the Channel Phase. -/
  | channelLimit (n : Nat)
  /-- This spell can't be countered (CR 426). -/
  | uncounterable
  /-- Spells and abilities controlled by this object's controller can't be countered (CR 426). -/
  | controlledItemsUncounterable
  /-- This Unit gains the activated abilities of friendly objects that exhaust their source. -/
  | friendlyExhaustAbilities
  /-- The controller's spells and abilities give this much extra negative Might to Units
  they choose (CR 370). -/
  | targetMightPenalty (n : Nat)
  /-- If a spell or ability that chooses this Unit would stun, reduce its Might, or return it
  to hand, give it this much Might this turn instead (CR 370). -/
  | chosenHarmToMight (n : Nat)
  /-- Ignore Deflect when paying the cost of this spell (CR 809). -/
  | ignoreDeflectSpell
  /-- Ignore Deflect on objects chosen at this Battlefield (CR 809). -/
  | ignoreDeflectHere
  /-- The objects the selector names deal no combat damage (Vilemaw). -/
  | noCombatDamageFor (s : Selector)
  /-- Each Equipment attached to the Unit gives double its Might bonus (Gearhead). -/
  | doubleEquip
  /-- (Of an Equipment) the Unit it is attached to has `n` more Might if it was attached this
  turn (Brutalizer). -/
  | mightIfFresh (n : Nat)
  /-- (Of an Equipment) the Unit it is attached to also has the tag (Experimental Hexplate). -/
  | gainsTag (t : Tag)
  /-- (Of an Equipment) the Units of the player of the Unit it is attached to, at the place of that
  Unit, have the keyword (Shurelya's Requiem). -/
  | keywordHere (k : KeywordInst)
  /-- (Of an Equipment) the hold effects of the Unit are also conquer effects, and the other way
  round (Skyfall of Areion). -/
  | holdIsConquer
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
  /-- Discard this many cards with the given properties from the player's hand (CR 423.3). -/
  | discardMatching (n : Nat) (fs : FilterList)
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
  /-- The ability can be used only while its card is in the Champion Zone: the Chosen Champion is
  played from there. -/
  | fromChampionZone
  /-- The ability can be used only while its card is in the Trash (Undying Legion). -/
  | fromTrash
  /-- Disempower the unit. -/
  | disempowerSelf
  /-- Reduce the activated ability's Energy cost when the condition holds (CR 827.1.c.3). -/
  | energyDiscount (cond : Condition) (amount : Amount)
  /-- Recycle the object itself. -/
  | recycleSelf
  /-- Kill the object the ability belongs to ("Kill this"). -/
  | killSelf
deriving DecidableEq, Repr, Hashable

/-- A cost paid before a triggered ability becomes a finalized Chain item (CR 383.3.b). -/
inductive TriggerCost where
  /-- The ability requires no payment. -/
  | free
  /-- Spend the specified amount of Energy. -/
  | energy (amount : Nat)
  /-- Exhaust the source during finalization (CR 383.3.b, 415.4). -/
  | exhaustSelf
  /-- Burn exactly this many cards from the controller's Main Deck (CR 441.3.a). -/
  | burn (count : Nat)
  /-- Kill exactly this many friendly permanents that match the filters. -/
  | killFriendly (count : Nat) (filters : FilterList)
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
  /-- A leading "you may" is a choice whether to finalize the ability (CR 383.3.a). -/
  optional : Bool := false
  /-- Each mode may be chosen only once this turn (Riven, Broken Blade). -/
  separateModesPerTurn : Bool := false
  /-- The cost in an instruction that precedes its effect. -/
  cost : TriggerCost := .free
deriving DecidableEq, Repr, Hashable

end Riftbound

end
