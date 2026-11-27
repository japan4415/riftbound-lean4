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

/-- A reusable ability described in a card definition's grants (CR 479.3). -/
structure AbilityGrant where
  /-- The definition that describes the ability being granted. -/
  card : CardId
  /-- The index within the definition's grants, or within the copied rules text. -/
  index : Nat
  /-- The distinct instance of copied Effect Text for an attachment, if any. -/
  copyStamp : Option Timestamp := none
  /-- The source index is in the full definition of a friendly object whose ability was gained. -/
  borrowed : Bool := false
  /-- The object supplying a continuous grant, identified by its unique entry timestamp. -/
  sourceStamp : Option Timestamp := none
deriving DecidableEq, Repr, Hashable

/-- Distinguish different instances of the same granted text. -/
def AbilityGrant.instanceStamp (g : AbilityGrant) : Option Timestamp := g.copyStamp <|> g.sourceStamp

/-- An additional selection recorded when a card is finalized (CR 355). -/
inductive SpellPick where
  /-- The Spell only has its ordinary target and payment choices. -/
  | plain
  /-- The index of the chosen mode. -/
  | mode (index : Nat)
  /-- The chosen Battlefield, or the moved object's Base. -/
  | destination (battlefield : Option ObjId)
  /-- The chosen mode and its required Move destination. -/
  | modeDestination (index : Nat) (battlefield : Option ObjId)
  /-- Pay the elected Battlefields' fees and the listed optional costs of the Unit itself. -/
  | payForBattlefield (battlefields : List ObjId) (ownCosts : List Nat := [])
  /-- A Unit or Gear's elected optional costs without any Battlefield fees. -/
  | withPermanentCosts (ownCosts : List Nat)
  /-- The optional discounts declared for this permanent play (CR 355, 356.4). -/
  | withGearDiscounts (pick : SpellPick) (sources : List ObjId)
  /-- A player targeted during finalization, alongside the other effect choices (CR 355.7). -/
  | withPlayer (pick : SpellPick) (player : PlayerId)
  /-- The object revealed from hand or picked from the Board for Show Off (CR 832). -/
  | withShowOff (pick : SpellPick) (object : ObjId)
  /-- The choices before resolution, with the printed optional cost and the number of Repeats
  chosen for this play (CR 355.1, 356.4.f.1). -/
  | withCosts (pick : SpellPick) (printed : Bool) (repeats : Nat)
  /-- A permanent used to pay an additional play cost, separate from targets and destination. -/
  | withExtraObject (pick : SpellPick) (object : ObjId)
  /-- The amount of a variable additional Power cost declared for this play. -/
  | withVariablePower (pick : SpellPick) (amount : Nat)
  /-- Additional Spell costs that exhaust each named source and its chosen Units (CR 357.2). -/
  | withSpellExhausts (pick : SpellPick) (groups : List (ObjId × List ObjId))
  /-- This execution uses the first `targetCount` targets. Its Repeat has separate choices (CR 820.2). -/
  | thenRepeat (pick : SpellPick) (targetCount : Nat) (next : SpellPick)
  /-- Elect the card's printed additional XP cost. This choice names no object. -/
  | withXP (pick : SpellPick)
  /-- The object used to pay a Kill cost and its base costs at payment (CR 359.3.e.13).
  Recorded by the engine after paying the cost. -/
  | withPaidKill (pick : SpellPick) (object : ObjId) (energy power : Nat)
deriving DecidableEq, Repr, Hashable

/-- The source and base costs recorded when the Spell paid its Kill cost. -/
def SpellPick.paidKill : SpellPick → Option (ObjId × Nat × Nat)
  | .withPaidKill _ object energy power => some (object, energy, power)
  | .withCosts pick _ _ => pick.paidKill
  | _ => none

/-- Keep the previously paid Kill cost when assigning new effect choices. -/
def SpellPick.addPaidKill (pick : SpellPick) (payment : Option (ObjId × Nat × Nat)) : SpellPick :=
  payment.elim pick (fun (object, energy, power) => .withPaidKill pick object energy power)

/-- Whether the play elects the printed XP cost. -/
def SpellPick.paysXP : SpellPick → Bool
  | .withXP _ => true
  | .withCosts pick _ _ | .thenRepeat pick _ _ | .withExtraObject pick _ |
      .withSpellExhausts pick _ | .withPaidKill pick .. => pick.paysXP
  | _ => false

/-- Remove the XP payment before inspecting the remaining finalization choices. -/
def SpellPick.withoutXP : SpellPick → SpellPick
  | .withXP pick => pick
  | pick => pick

/-- The choices of costs, when declared explicitly. -/
def SpellPick.optionalCosts : SpellPick → Option (Bool × Nat)
  | .withCosts _ printed repeats => some (printed, repeats)
  | .withPlayer pick _ | .withShowOff pick _ | .withExtraObject pick _ |
      .withVariablePower pick _ | .withSpellExhausts pick _ | .withXP pick |
      .withPaidKill pick .. => pick.optionalCosts
  | _ => none

/-- The explicitly elected optional costs of a Unit or Gear. -/
def SpellPick.permanentCosts : SpellPick → Option (List Nat)
  | .payForBattlefield _ costs | .withPermanentCosts costs => some costs
  | .withShowOff pick _ | .withGearDiscounts pick _ | .withExtraObject pick _ |
      .withXP pick => pick.permanentCosts
  | _ => none

/-- The player targeted during finalization. -/
def SpellPick.playerTarget : SpellPick → Option PlayerId
  | .withPlayer _ player => some player
  | .withCosts pick _ _ | .thenRepeat pick _ _ | .withShowOff pick _ |
      .withExtraObject pick _ | .withVariablePower pick _ | .withSpellExhausts pick _ |
      .withXP pick | .withPaidKill pick .. => pick.playerTarget
  | _ => none

/-- The mode or destination selected for the effect, independently of its optional costs. -/
def SpellPick.effectChoice : SpellPick → SpellPick
  | .withPlayer pick _ | .withShowOff pick _ | .withVariablePower pick _ => pick.effectChoice
  | .withCosts pick _ _ | .thenRepeat pick _ _ | .withExtraObject pick _ |
      .withSpellExhausts pick _ | .withXP pick | .withPaidKill pick .. => pick.effectChoice
  | pick => pick

/-- The location selected at finalization, with an inner `none` for Base. -/
def SpellPick.moveDestination? (pick : SpellPick) : Option (Option ObjId) :=
  match pick.effectChoice with
  | .destination location | .modeDestination _ location => some location
  | _ => none

/-- Whether this play has distinct recorded choices for each execution. -/
def SpellPick.hasExecutionChoices : SpellPick → Bool
  | .thenRepeat .. => true
  | .withCosts pick _ _ | .withShowOff pick _ | .withExtraObject pick _ |
      .withVariablePower pick _ | .withSpellExhausts pick _ | .withXP pick |
      .withPaidKill pick .. => pick.hasExecutionChoices
  | _ => false

/-- Read the ordered finalization choices with the targets belonging to each execution. -/
def SpellPick.executions (targets : List ObjId) : SpellPick → List (SpellPick × List ObjId)
  | .withCosts pick _ _ => pick.executions targets
  | .withExtraObject pick _ | .withSpellExhausts pick _ => pick.executions targets
  | .withVariablePower pick n => (pick.executions targets).map (fun (k, ts) => (.withVariablePower k n, ts))
  | .thenRepeat pick count next => (pick, targets.take count) :: next.executions (targets.drop count)
  | .withXP pick => (pick.executions targets).map (fun (k, ts) => (.withXP k, ts))
  | .withPaidKill pick object energy power =>
    (pick.executions targets).map (fun (k, ts) => (.withPaidKill k object energy power, ts))
  | pick => [(pick, targets)]

/-- The object shown off for this play. -/
def SpellPick.showOffObject : SpellPick → Option ObjId
  | .withShowOff _ object => some object
  | .withCosts pick _ _ | .withPlayer pick _ | .thenRepeat pick _ _ |
      .withExtraObject pick _ | .withVariablePower pick _ | .withGearDiscounts pick _ |
      .withSpellExhausts pick _ | .withXP pick | .withPaidKill pick .. => pick.showOffObject
  | _ => none

/-- The declared amount of a variable Power cost for this play. -/
def SpellPick.variablePower : SpellPick → Option Nat
  | .withVariablePower _ n => some n
  | .withCosts pick _ _ | .withPlayer pick _ | .withShowOff pick _ |
      .withExtraObject pick _ | .withSpellExhausts pick _ | .thenRepeat pick _ _ |
      .withXP pick | .withPaidKill pick .. => pick.variablePower
  | _ => none

/-- Decorate a finalization when its additional Power amount is declared. -/
def SpellPick.addVariablePower (pick : SpellPick) (amount : Option Nat) : SpellPick :=
  amount.elim pick (.withVariablePower pick)

/-- Passive sources whose optional Gear discount was elected. -/
def SpellPick.gearDiscounts : SpellPick → List ObjId
  | .withGearDiscounts _ sources => sources
  | .withExtraObject pick _ | .withXP pick => pick.gearDiscounts
  | _ => []

/-- Remove the Gear discount declaration before inspecting other costs. -/
def SpellPick.withoutGearDiscounts : SpellPick → SpellPick
  | .withGearDiscounts pick _ => pick
  | pick => pick

/-- The permanent selected separately to pay this play's cost. -/
def SpellPick.extraObject : SpellPick → Option ObjId
  | .withExtraObject _ object => some object
  | .withPaidKill _ object .. => some object
  | .withSpellExhausts pick _ | .withXP pick => pick.extraObject
  | _ => none

/-- Every source and group of Units elected to exhaust together during the Spell's play. -/
def SpellPick.spellExhausts : SpellPick → List (ObjId × List ObjId)
  | .withSpellExhausts _ groups => groups
  | .withXP pick => pick.spellExhausts
  | _ => []

/-- Strip the extra Exhaust cost while preserving any separate object cost. -/
def SpellPick.withoutSpellExhausts : SpellPick → SpellPick
  | .withSpellExhausts pick _ => pick
  | pick => pick

/-- Strip the payment choice from the rest of the Spell's finalization. -/
def SpellPick.withoutExtraObject : SpellPick → SpellPick
  | .withExtraObject pick _ => pick
  | pick => pick

/-- Add the optional Show Off selection to an otherwise complete finalization. -/
def SpellPick.addShowOff (pick : SpellPick) (object : Option ObjId) : SpellPick :=
  object.elim pick (.withShowOff pick)

/-- Remove the permanent's Show Off choice before determining its costs. -/
def SpellPick.withoutShowOff : SpellPick → SpellPick
  | .withShowOff pick _ => pick
  | pick => pick

/-- Characteristics of an object shown off, as they were during finalization (CR 832). -/
structure ShownOff where
  /-- The effective Might on the Board or the printed Might in hand. -/
  might : Option Int
  /-- The number of Power symbols in its cost. -/
  power : Nat
deriving DecidableEq, Repr, Hashable

/-- Whose side an object is on, seen from the player the effect belongs to (CR 740.1). -/
inductive Side where
  /-- Friendly: controlled by the player or their teammate. -/
  | friendly
  /-- Enemy: controlled by an opponent. -/
  | enemy
  /-- Either side. -/
  | any
  /-- Controlled by the player making the choice (CR 491.8). -/
  | you
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

/-- A specific physical location on the Board (CR 197). -/
inductive BoardLocation where
  /-- A specific seat's Base. -/
  | base (seat : PlayerId)
  /-- A specific Battlefield on the Board. -/
  | battlefield (id : ObjId)
deriving DecidableEq, Repr, Hashable

/-- How many objects an effect takes (CR 355): "a", "up to N", "N", "each" or "all". -/
inductive Quantity where
  /-- Exactly one. -/
  | one
  /-- Up to `n`. -/
  | upTo (n : Nat)
  /-- Any subset, including the empty one (CR 355.13). -/
  | anyNumber
  /-- Any subset whose total Might is at most the limit (CR 355.11). -/
  | combinedMightAtMost (limit : Nat)
  /-- Any subset controlled by one seat whose total Might is at most the limit (CR 355.11). -/
  | combinedMightFromOneController (limit : Nat)
  /-- From one to `limit` targets together at a Battlefield (CR 355.11, 355.14). -/
  | atOneBattlefield (limit : Nat)
  /-- Up to one target in each specific Base or Battlefield. -/
  | onePerLocation
  /-- From one target up to the current Might of the Unit at an earlier slot (CR 355.14). -/
  | splitByMight (slot : Nat)
  /-- Exactly `n`. -/
  | exactly (n : Nat)
  /-- Every one that matches. -/
  | all
  /-- Up to `limit` targets together at one specific Base or Battlefield (CR 355.11). -/
  | atOneLocation (limit : Nat)
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
  /-- The player chosen at a player target slot when the item was finalized (CR 355.7). -/
  | chosen (slot : Nat)
  /-- The player the replaced event is about ("they draw 1 instead"). -/
  | eventPlayer
  /-- The controller of the object chosen at a slot of the effect ("its controller"). -/
  | controllerOf (slot : Nat)
  /-- Every player in turn order, starting after the current turn player. -/
  | eachPlayerFromNext
  /-- The owner of the object held in an effect's slot. -/
  | ownerOf (slot : Nat)
  /-- The player who played the unit held in an effect's slot this turn. -/
  | playedBy (slot : Nat)
  /-- Every player except the player the effect belongs to, including any teammate. -/
  | eachOtherPlayer
deriving DecidableEq, Repr, Hashable

/-- A replacement still available for one damage event. Turn notes use their positions in
the original damage batch, so individual effects can be spent independently. -/
inductive DamageReplacement where
  /-- One instance of doubling the incoming damage. -/
  | double
  /-- A remaining finite Prevent Value. -/
  | prevent (note remaining : Nat)
  /-- One effect that prevents the next hit in full. -/
  | shield (note : Nat)
deriving DecidableEq, Repr, Hashable

/-- Which requirement applies to a Unit with conflicting combat priorities (CR 467.2.c.8). -/
inductive CombatAssignmentPriority where
  /-- Assign damage before the controller's Units without Tank. -/
  | tank
  /-- Assign damage after the controller's Units without Backline. -/
  | backline
deriving DecidableEq, Repr, Hashable

/-- One answer to a death replacement decision (CR 372). -/
inductive DeathDecision where
  /-- Banish the dying permanent with this player's replacement. -/
  | banish (player : PlayerId)
  /-- Kill this Gear in place of the dying Unit. -/
  | gear (source : ObjId)
  /-- Apply a rescuer on the Board, or Tactical Retreat when the source is absent. -/
  | free (source : Option ObjId)
  /-- Sacrifice a Unit, or decline the optional replacement. -/
  | sacrifice (cost : Option ObjId)
deriving DecidableEq, Repr, Hashable

/-- A Board source that can replace more than one death in a simultaneous group (CR 373.2). -/
inductive DeathSequenceSource where
  /-- The Gear whose own Kill replaces the original death. -/
  | gear (source : ObjId)
  /-- The Unit that directly heals, exhausts, and recalls the dying Unit. -/
  | rescuer (source : ObjId)
deriving DecidableEq, Repr, Hashable

/-- What a spell or an ability makes true for the rest of the turn (CR 389-393). -/
inductive TurnEffect where
  /-- Original locations specified for a finalized Chain item's targets (CR 359.3.e). -/
  | declaredTargetLocations (locations : List (ObjId × BoardLocation))
  /-- The Base seats declared for the grouped moves of a finalized Spell (CR 355.4). -/
  | declaredMoveBases (bases : List (ObjId × PlayerId))
  /-- The unit can't be chosen by enemy spells and abilities this turn. -/
  | unchoosableEnemy
  /-- No standard or instructed Move can move this Unit this turn (CR 447). -/
  | cannotMove
  /-- The player recorded by this note cannot move the Unit this turn (CR 447). -/
  | cannotMoveByPlayer
  /-- The next spell the player plays this turn costs `n` Energy less. -/
  | nextSpellCostMinus (n : Nat)
  /-- The next card the player plays this turn costs less Energy and Power (CR 420.5). -/
  | nextCardCostMinus (energy power : Nat)
  /-- Discount the next Unit play and give that Unit the indicated Ending Step trigger. -/
  | nextUnitCostMinusThenEnd (energy power : Nat) (card : CardId) (idx : Nat)
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
  /-- The next unit the player plays this turn has Accelerate (CR 805). -/
  | nextUnitAccelerate
  /-- The player's next Unit can be played to any legal Battlefield and enters buffed. -/
  | nextUnitAnywhereBuffed
  /-- The units the player plays this turn cost `n` Energy more (Vaults of Helia). -/
  | unitsCostMore (n : Nat)
  /-- The Battlefield was open (nobody controlled it) when the player conquered it this turn. -/
  | openConquest
  /-- The Turn Player's teammate controlled this Battlefield at the scoring step (CR 491.8.b.1). -/
  | teamHeldAtScoring
  /-- This player occupied the Battlefield at their side's scoring step (CR 491.8.g.1). -/
  | teamOccupiedAtScoring
  /-- This turn the object (a Unit) has the triggered ability of the card at the place (Relentless
  Pursuit: "When I conquer, you may move me to my base"). -/
  | grantsAbility (card : String) (idx : Nat)
  /-- This source chose the indicated mode of a triggered ability this turn (CR 355.3). -/
  | chosenTriggerMode (card : CardId) (idx mode : Nat) (copy : Option Timestamp)
  /-- A spell or ability created a delayed trigger for when the marked Unit dies this turn
  (CR 391-393). -/
  | triggerOnDeath (source : ObjId) (card : CardId) (idx : Nat)
  /-- Positive damage from the referenced instruction can fire a reflexive ability
  if the Unit dies during that Chain item's Cleanup (CR 389, 429.5.c). -/
  | linkedDamageDeath (source : ObjId) (card : CardId) (idx : Nat)
  /-- A delayed ability fires for the next plays of the type by this player this turn
  (CR 391-393). Its source is the object named by the note. -/
  | triggerOnPlays (card : CardId) (idx : Nat) (kind : CardType) (remaining : Nat)
  /-- The player played a Unit or Gear to the Battlefield named by the note this turn. -/
  | playedToBattlefield
  /-- At the end of this turn, the ability of the card at the place fires, with the object as its
  source (Hostile Takeover: the unit goes back). -/
  | endTrigger (card : String) (idx : Nat)
  /-- At this turn's end, run the remembered ability with the amount captured by its instruction. -/
  | endTriggerWithAmount (card : CardId) (idx amount : Nat)
  /-- The next Spell the player plays this turn has Repeat, for its own cost (Temporal Portal). -/
  | nextSpellRepeat
  /-- The next damage the object (a Unit) would be dealt this turn is prevented (Counter Strike). -/
  | damagePrevented
  /-- Prevent this much of the next damage to the marked Unit this turn (CR 438). -/
  | preventDamage (remaining : Nat)
  /-- The replacement order chosen for the Unit's current combat damage (CR 467.2.c.5). -/
  | combatDamageOrder (order : List DamageReplacement)
  /-- The assigning player's choice between a Unit's conflicting requirements this combat. -/
  | combatAssignmentPriority (priority : CombatAssignmentPriority)
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
  /-- The player assigned `n` excess damage to enemy Units in the Combat at the noted Battlefield. -/
  | excessDamage (n : Nat)
  /-- The object has chosen mode `n` of an ability this turn ("choose one you have not chosen"). -/
  | modeUsed (n : Nat)
  /-- A copied ability has chosen mode `n` in this instance of its rules text (CR 479.1). -/
  | copiedModeUsed (copy : Timestamp) (n : Nat)
  /-- A card is played from Hidden: the event it makes is what matters. -/
  | hiddenPlayed
  /-- A buffed unit died: the note is about the dead card. -/
  | buffedUnitDied
  /-- A unit died with no other unit of its player where it was: the note is about the dead
  card (Lonely Poro). -/
  | diedAlone
  /-- The actual company at death when it differs from the historical replay note. -/
  | deathCompany (alone : Bool)
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
  /-- The affected Unit's controller selected the Banish replacement whose player this note names. -/
  | chosenDeathBanisher
  /-- The affected Unit's controller selected the permanent that will die in its place. -/
  | chosenDeathGear (gear : ObjId)
  /-- The affected Unit's controller selected a free rescue. None selects Tactical Retreat. -/
  | chosenDeathFree (source : Option ObjId)
  /-- The choice for the death currently being processed. None declines just this event. -/
  | deathSacrificeChoice (unit : Option ObjId)
  /-- The controller put this Unit's replacement next in one simultaneous group (CR 373). -/
  | deathOrder (group : List ObjId)
  /-- Transient context for a root death: these effects already completed their sequences. -/
  | closedDeathSequences (sources : List DeathSequenceSource)
  /-- Apply the revised choice only after the earlier events in this group have been resolved. -/
  | deathReselection (group earlier : List ObjId) (choice : DeathDecision)
  /-- A choice for a Kill created by an earlier replacement in the same chain (CR 370.2). -/
  | nestedDeathDecision (root : ObjId) (used : List (ObjId × Bool)) (choice : DeathDecision)
      (groupScope : Option (List ObjId × List ObjId))
  /-- This permanent has used its optional death replacement this turn (CR 371). -/
  | deathSacrificeUsed
  /-- The next time the unit would die this turn, it is healed, exhausted and recalled instead
  (Tactical Retreat): a note on the unit. -/
  | saveOnce
  /-- A rescue was recorded. It spends a preceding Tactical Retreat if one is available. -/
  | saveUsed
  /-- All damage that would be dealt to the unit this turn is doubled (Lotus Trap). -/
  | doubleDamage
  /-- A unit the player controlled was killed (a note of the turn, not an effect). -/
  | unitDied
  /-- At least one Unit or Gear the player controlled died this turn. -/
  | permanentDied
  /-- A Battlefield's first non-token Unit death this turn for this player.
  The note's timestamp identifies the dead object. -/
  | firstUnitDeathHere
  /-- A card of the player was discarded (a note of the turn, not an effect). -/
  | cardDiscarded
  /-- The player chose an enemy Unit this turn (CR 355.7). -/
  | choseEnemyUnit
  /-- The player already played an activated ability of a Gear this turn. -/
  | usedGearAbility
  /-- This passive source supplied its optional Gear play discount this turn. -/
  | usedGearPlayDiscount
  /-- One unit of the Power in the player's Pool is of Fire Below the Mountain: it can only pay for
  playing a Gear or using an ability of a Gear this turn. -/
  | gearMana
  /-- One flexible Power reserved for playing a Unit or Gear (CR 135, 357). -/
  | permanentMana
  /-- The next Gear the player plays from their hand this turn, with an Energy cost of no more than
  `n`, costs no Energy (Jayce). -/
  | nextGearFree (n : Nat)
  /-- A note of the turn on an object: an ability of the card waits for it ("at the start of your
  next Main Phase, ..."); `n` tells the notes apart. -/
  | armed (n : Nat)
  /-- A source used its Unit token duplication this turn (CR 371). -/
  | duplicatedUnitToken (copy : Option Timestamp)
  /-- Friendly Units enter ready for the rest of the turn. -/
  | friendlyUnitsReady
  /-- The player may inspect facedown cards this seat controls for the rest of the turn. -/
  | inspectFacedown (controller : PlayerId)
deriving DecidableEq, Repr, Hashable

/-- Choices limited by an ability's rules text belong to that instance. -/
def TurnEffect.forCopy (effect : TurnEffect) (copy : Option Timestamp) : TurnEffect :=
  match effect, copy with
  | .modeUsed mode, some stamp => .copiedModeUsed stamp mode
  | _, _ => effect

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
  /-- Once when one or more subjects die together. -/
  | deathGroup
  /-- Once when the controller Stuns one or more subjects in one instruction (CR 370, 412.4). -/
  | stunGroup
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
