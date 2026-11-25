module

public import Riftbound.Card.IR.Prim

/-!
# The effect IR: effects

An effect is built from primitives with combinators: a sequence, a choice of one mode, a condition,
a loop over objects, an optional step, a follow-up that needs the first step done, a bound
variable, a lasting modification, a delayed effect (design.md §7.1, §7.2). The only recursive
types of the IR are `Effect` and the list of effects, in one `mutual` block, so that they derive
`DecidableEq` (lean-guidelines.md §5.4).
-/

@[expose] public section

namespace Riftbound

/-- How an effect changes the cost of a card it lets its player play (CR 356.1). -/
inductive EffectPlayPrice where
  /-- Reduce Energy by the specified amount, including optional costs. -/
  | reduceEnergy (amount : Nat)
  /-- Ignore the base Energy cost. -/
  | ignoreEnergy
  /-- Ignore the entire base cost. -/
  | ignoreBase
deriving DecidableEq, Repr, Hashable

/-- An effect play's cost and mandatory destination requirements (CR 355.17). Each requirement
lists all the locations satisfying it, with `none` meaning the player's Base. -/
structure EffectPlayTerms where
  /-- The effect's adjustment to the price of playing the card. -/
  price : EffectPlayPrice
  /-- The sets of locations required by the effects already in force. -/
  requirements : List (List (Option ObjId)) := []
deriving DecidableEq, Repr, Hashable

/-- A finalization choice for a Unit or Gear played by an effect (CR 355-357, 420.3). -/
structure ReducedPermanentPlay where
  /-- The adjusted price, with the Power domains chosen. -/
  cost : Cost
  /-- The Battlefield destination, or the Base when empty. -/
  battlefield : Option ObjId
  /-- The object selected for an additional cost. -/
  extraObject : Option ObjId
  /-- The card selected for an optional discard cost. -/
  discard : Option ObjId
  /-- Whether the card's optional resource cost is paid. -/
  additionalPaid : Bool
  /-- Whether the Unit is played with Accelerate. -/
  accelerated : Bool
  /-- The Battlefields whose additional costs the player elected to pay. -/
  battlefieldFees : List ObjId := []
deriving DecidableEq, Repr, Hashable

/-- One activation that provides resources for an effect's play (CR 357.1.a). -/
inductive EffectAdd where
  /-- Exhaust or Recycle a Basic Rune. -/
  | rune (source : ObjId) (recycle : Bool)
  /-- Use a card's Add ability with its own selected resource cost. -/
  | ability (source : ObjId) (index energy : Nat) (power : List Domain)
deriving DecidableEq, Repr, Hashable

/-- Choices and resource price of a Spell under a limited play effect. -/
structure EffectSpellPlay where
  /-- The objects chosen by the Spell. -/
  targets : List ObjId
  /-- The resources due for the selected choices. -/
  cost : Cost
  /-- Its mode, player target, destination or optional cost choices. -/
  pick : SpellPick
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

/-- A damage event while its controller is ordering the applicable replacements. -/
structure EffectDamageHit where
  /-- The object that will take the damage. -/
  target : ObjId
  /-- The damage after the replacements chosen so far. -/
  amount : Nat
  /-- The replacements that have not yet applied to this event. -/
  replacements : List DamageReplacement
deriving DecidableEq, Repr, Hashable

/-- Damage from one instruction. Keep replacements and damage tentative until the whole
instruction is ready, so simultaneous events are still observed together. -/
structure EffectDamageBatch where
  /-- Who controls damage from a Spell or Ability, or none for an exchange between Units. -/
  controller : Option PlayerId
  /-- Events waiting to have their replacements ordered. -/
  incoming : List (ObjId × Nat)
  /-- Final damage events, in reverse input order. -/
  resolved : List (ObjId × Nat) := []
  /-- The amount consumed from each numbered turn note. -/
  spent : List (Nat × Nat) := []
deriving DecidableEq, Repr, Hashable

mutual

/-- An effect: what happens when a spell resolves or an ability fires. -/
inductive Effect where
  /-- Nothing happens. -/
  | nop
  /-- Do the effects in order. -/
  | seq (es : EffectList)
  /-- Do the mode that was chosen when the card was played (CR 355). -/
  | chooseOne (modes : EffectList)
  /-- The player chooses one of the effects while the effect resolves, and does it. -/
  | eitherOf (modes : EffectList)
  /-- Pay a resource cost from the Rune Pool, then continue with the effect (CR 445.2). -/
  | payThen (cost : Cost) (body : Effect)
  /-- Spend the specific resources selected from the Pool for this payment. -/
  | paySelected (resources : Cost) (body : Effect)
  /-- Do the first effect if the condition holds, the second otherwise. -/
  | ifThen (c : Condition) (t e : Effect)
  /-- Do the effect for each of the objects, with `it` the object. -/
  | forEach (s : Selector) (body : Effect)
  /-- Each of the players does the effect: the effect is done for them, so that what they choose
  is theirs ("each player kills one of their units"). -/
  | eachPlayer (who : PlayerSel) (body : Effect)
  /-- Reveal the specified hands for the following instructions (CR 425). -/
  | revealHand (who : PlayerSel) (body : Effect)
  /-- Name a format-legal card of this type and remember it on the source (CR 759-762). -/
  | nameCard (kind : CardType)
  /-- Record the answer to a naming choice on the original source. -/
  | rememberNamedCard (card : CardId)
  /-- Look at up to `n` cards from the top of the Main Deck for the following instructions. -/
  | lookAtTop (n : Nat) (body : Effect)
  /-- The player may banish a matching looked-at card and play it with an Energy reduction.
  The object that entered play replaces the pick in `pickVar` (CR 420.3). -/
  | banishAndPlayLooked (less : Nat) (filters : FilterList)
  /-- Recycle the looked-at cards still in the Main Deck in a random order (CR 417.5). -/
  | recycleLooked
  /-- Continue after offering a choice of eligible cards from a look. -/
  | chooseLookedToPlay (less : Nat) (first : ObjId) (more : List ObjId)
  /-- Banish the card picked from the looked-at cards and finalize the play. -/
  | banishLookedForPlay (less : Nat)
  /-- Continue an effect's play, offering the Unit or Gear's legal finalizations. -/
  | planPermanentPlay (card : ObjId) (terms : EffectPlayTerms)
  /-- Banish one Unit before its owner finalizes the new play. -/
  | banishForReplay (card : ObjId) (sameLocation : Bool)
  /-- Apply the selected finalization of a Unit or Gear played by the effect. -/
  | finishReducedPermanent (card : ObjId) (terms : EffectPlayTerms) (plan : ReducedPermanentPlay)
  /-- Continue choosing resource activations for the selected finalization. -/
  | fundLookedPermanent (card : ObjId) (terms : EffectPlayTerms) (plan : ReducedPermanentPlay)
      (adds : List EffectAdd)
  /-- Use the chosen Add abilities and pay for the effect's permanent as one finalization. -/
  | finishFundedPermanent (card : ObjId) (terms : EffectPlayTerms) (plan : ReducedPermanentPlay)
      (adds : List EffectAdd)
  /-- Finalize the Spell queued by an effect that plays and then recycles it. -/
  | finalizeTrashSpell (card : ObjId)
  /-- Continue choosing the individual Add abilities for the queued Spell's payment. -/
  | fundTrashSpell (card : ObjId) (plan : EffectSpellPlay) (adds : List EffectAdd)
  /-- Pay for the queued Spell and make its chosen targets and other finalization choices public. -/
  | finishTrashSpell (card : ObjId) (plan : EffectSpellPlay) (adds : List EffectAdd)
  /-- Put the queued Spell back in its owner's Trash without finalizing it. -/
  | cancelTrashSpell (card : ObjId)
  /-- Continue working through the events of a single damage instruction. -/
  | resolveEffectDamage (batch : EffectDamageBatch) (hit : Option EffectDamageHit)
  /-- Apply one selected replacement and continue with the rest. -/
  | chooseDamageReplacement (batch : EffectDamageBatch) (hit : EffectDamageHit)
      (replacement : DamageReplacement)
  /-- Choose one object during resolution and bind it to `pickVar` for the following
  instructions (CR 355.18). -/
  | chooseObject (side : Side) (place : Place) (filters : FilterList) (body : Effect)
  /-- Each player chooses one of their own objects. Append the picks to the slots, then run the
  body for the original controller. The picks are not targets (CR 355.10.e). -/
  | pickOwn (place : Place) (filters : FilterList) (body : Effect)
  /-- Move the Unit in the given slot to the location chosen during finalization (CR 355.4).
  If the move happens, run the follow-up with a chosen Battlefield available as the latest pick. -/
  | moveChoosing (slot : Nat) (allowBase : Bool) (battlefields : FilterList) (afterMove : Effect)
  /-- Continue gathering each player's own pick. `capture` records the latest answer first. -/
  | collectOwnPicks (controller : PlayerId) (remaining : List PlayerId)
      (place : Place) (filters : FilterList) (body : Effect) (capture : Bool)
  /-- The player may do the effect. -/
  | may (e : Effect)
  /-- Do the first effect, and if it was done, the second ("if you do") (CR 387). -/
  | doThen (first rest : Effect)
  /-- Do the effect a number of times. -/
  | repeatN (n : Amount) (e : Effect)
  /-- Bind a variable to an amount, then do the effect. -/
  | bind (v : VarId) (a : Amount) (e : Effect)
  /-- A game action. -/
  | prim (p : Prim)
  /-- Change objects for a while. The modification is made to each of the objects, which the
  modification calls `it`. -/
  | grant (s : Selector) (m : StaticMod) (d : Duration)
  /-- Do the effect later, when the trigger fires (CR 390-393). -/
  | delayed (t : Trigger) (e : Effect) (d : Duration)
  /-- Prevent the next `n` damage that would be dealt to the objects, for a while (CR 438). -/
  | preventNext (s : Selector) (n : Amount) (d : Duration)
  /-- The next time the event would happen to the objects, do the effect instead (CR 367-375). -/
  | replaceNext (ev : ReplaceEvent) (s : Selector) (instead : Effect) (d : Duration)
  /-- Choose an object again while the effect resolves, and make it slot `i` (the targets of a spell
  that is repeated are chosen again) (CR 820). -/
  | fillSlot (i : Nat) (s : Selector)
  /-- Make the object just chosen (`pickVar`) slot `i`. -/
  | fillFromPick (i : Nat)
  /-- At resolution, keep one of the remaining legal groups of original targets (CR 355.11.b). -/
  | retainTargetSet (groups : List (List ObjId))
  /-- The controller may remake all the Spell's finalization choices (CR 750-755). -/
  | remakeSpellChoices (spell : Selector)
  /-- Record the answer to a Spell's choice-remaking decision. -/
  | setSpellChoices (spell : ObjId) (pick : SpellPick) (targets : List ObjId)
  /-- An effect the IR cannot express: a handler of the table of custom handlers. -/
  | custom (id : CustomId) (args : ArgList)
deriving DecidableEq, Repr, Hashable

/-- A list of effects. -/
inductive EffectList where
  /-- No effect. -/
  | nil
  /-- An effect, then the rest. -/
  | cons (e : Effect) (rest : EffectList)
deriving DecidableEq, Repr, Hashable

end

end Riftbound

end
