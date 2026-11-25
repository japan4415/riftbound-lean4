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
  /-- On the Board or in a Legend Zone. -/
  | boardOrLegend
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
  /-- In the player's Champion Zone. -/
  | inChampionZone
  /-- In the player's Legend Zone. -/
  | inLegendZone
  /-- In the combat the effect is about. -/
  | inCombat
  /-- Hidden face down (CR 811). -/
  | inHidden
  /-- In the player's Banishment. -/
  | inBanishment
  /-- On the Chain: the spells waiting to resolve (CR 330). -/
  | onChain
  /-- On the Chain: the spells and the abilities waiting to resolve. -/
  | onChainAll
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
  /-- The attacker and defender of the ongoing Combat (CR 466.2.c). -/
  | combatSides
  /-- The player who chose a slot of the effect. -/
  | chosen (slot : Nat)
  /-- The player the replaced event is about ("they draw 1 instead"). -/
  | eventPlayer
  /-- The controller of the object chosen at a slot of the effect ("its controller"). -/
  | controllerOf (slot : Nat)
deriving DecidableEq, Repr, Hashable

/-- What a spell or an ability makes true for the rest of the turn (CR 389-393). -/
inductive TurnEffect where
  /-- The unit can't be chosen by enemy spells and abilities this turn. -/
  | unchoosableEnemy
  /-- The next spell the player plays this turn costs `n` Energy less. -/
  | nextSpellCostMinus (n : Nat)
  /-- The next spell the player plays this turn deals `n` Bonus Damage with each instance of
  damage it deals (CR 142). -/
  | nextSpellBonus (n : Nat)
  /-- The next unit the player plays this turn enters ready. -/
  | nextUnitReady
  /-- The units the player plays this turn enter ready. -/
  | unitsReady
  /-- The units the player plays this turn are buffed (Rally the Troops). -/
  | unitsBuffed
  /-- The next unit the player plays this turn is buffed (Nami). -/
  | nextUnitBuffed
  /-- The units the player plays this turn cost `n` Energy more (Vaults of Helia). -/
  | unitsCostMore (n : Nat)
  /-- The Battlefield was open (nobody controlled it) when the player conquered it this turn. -/
  | openConquest
  /-- This turn the object (a Unit) has the triggered ability of the card at the place (Relentless
  Pursuit: "When I conquer, you may move me to my base"). -/
  | grantsAbility (card : String) (idx : Nat)
  /-- A spell or ability created a delayed trigger for when the marked Unit dies this turn
  (CR 391-393). -/
  | triggerOnDeath (source : ObjId) (card : CardId) (idx : Nat)
  /-- At the end of this turn, the ability of the card at the place fires, with the object as its
  source (Hostile Takeover: the unit goes back). -/
  | endTrigger (card : String) (idx : Nat)
  /-- The next Spell the player plays this turn has Repeat, for its own cost (Temporal Portal). -/
  | nextSpellRepeat
  /-- The next damage the object (a Unit) would be dealt this turn is prevented (Counter Strike). -/
  | damagePrevented
  /-- Spells and abilities deal no damage this turn. -/
  | preventEffectDamage
  /-- Buffs give the player's units an additional +1 Might this turn. -/
  | buffsExtraMight
  /-- The opponents of the player cannot play cards this turn. -/
  | opponentsCantPlay
  /-- The opponents of the player cannot play Spells this turn (Lilting Lullaby). -/
  | opponentsNoSpells
  /-- A note for the turn that the object (a Battlefield) was conquered by the player. -/
  | conqueredHere
  /-- The unit is to be recalled the next time it dies this turn (Unlicensed Armory). -/
  | recallOnDeath
  /-- The dead card was marked to be recalled when it died: the note is about the dead card. -/
  | recallDied
  /-- The player had a unit at the Battlefield chosen with a spell this turn (a Battlefield of
  theirs waits for the first time). -/
  | chosenHere
  /-- Hiding costs nothing this turn. -/
  | hideFree
  /-- The object has been paid one unit for ("pay any amount"): one note for each unit paid. -/
  | unitPaid
  /-- The player assigned `n` excess damage (damage beyond what is lethal) to enemy Units in the
  Combat Damage of this turn's last Combat. -/
  | excessDamage (n : Nat)
  /-- The object has chosen mode `n` of an ability this turn ("choose one you have not chosen"). -/
  | modeUsed (n : Nat)
  /-- A card is played from Hidden: the event it makes is what matters. -/
  | hiddenPlayed
  /-- A buffed unit died: the note is about the dead card. -/
  | buffedUnitDied
  /-- A unit died with no other unit of its player where it was: the note is about the dead
  card (Lonely Poro). -/
  | diedAlone
  /-- A stunned unit died: the note is about the dead card. -/
  | stunnedUnitDied
  /-- A Mighty unit died (its Might was 5 or more as it died): the note is about the dead card. -/
  | mightyUnitDied
  /-- A unit that takes damage this turn is killed (all units, or the one it is put on). -/
  | killOnDamage
  /-- A unit the player controlled died during a Beginning Phase (a note of the turn). -/
  | diedInBeginning
  /-- The player gained XP (a note of the turn). -/
  | gainedXP
  /-- The unit is banished instead of dying this turn (Smite): a note on the unit. -/
  | banishInstead
  /-- The next time the unit would die this turn, it is healed, exhausted and recalled instead
  (Tactical Retreat): a note on the unit. -/
  | saveOnce
  /-- The unit was saved from dying (a note of the turn, not an effect): `saveOnce` is used up. -/
  | saveUsed
  /-- All damage that would be dealt to the unit this turn is doubled (Lotus Trap). -/
  | doubleDamage
  /-- A unit the player controlled was killed (a note of the turn, not an effect). -/
  | unitDied
  /-- A card of the player was discarded (a note of the turn, not an effect). -/
  | cardDiscarded
  /-- The player chose an enemy Unit this turn (CR 355.7). -/
  | choseEnemyUnit
  /-- One unit of the Power in the player's Pool is of Fire Below the Mountain: it can only pay for
  playing a Gear or using an ability of a Gear this turn. -/
  | gearMana
  /-- The next Gear the player plays from their hand this turn, with an Energy cost of no more than
  `n`, costs no Energy (Jayce). -/
  | nextGearFree (n : Nat)
  /-- A note of the turn on an object: an ability of the card waits for it ("at the start of your
  next Main Phase, ..."); `n` tells the notes apart. -/
  | armed (n : Nat)
deriving DecidableEq, Repr, Hashable

/-- The kind of card whose plays a turn effect watches: "the next spell", "the next unit". -/
def TurnEffect.playType : TurnEffect → CardType
  | .nextSpellCostMinus _ => .spell
  | .nextSpellRepeat => .spell
  | .nextGearFree _ => .gear
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
