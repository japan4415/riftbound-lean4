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
  /-- Replace the base cost before modifiers and additional costs (CR 356.1). -/
  | alternateBase (cost : Cost)
deriving DecidableEq, Repr, Hashable

/-- A limited play can change where the finalized Spell goes when it leaves the Chain (CR 391.3.a). -/
inductive LimitedSpellExit where
  /-- Use the normal Chain destination. -/
  | normal
  /-- Recycle the Spell after it resolves. -/
  | recycle
  /-- Banish it in place of the regular exit from the Chain. -/
  | banish
deriving DecidableEq, Repr, Hashable

/-- An effect play's cost and mandatory destination requirements (CR 355.17). Each requirement
lists all the locations satisfying it, with `none` meaning the player's Base. -/
structure EffectPlayTerms where
  /-- The effect's adjustment to the price of playing the card. -/
  price : EffectPlayPrice
  /-- The sets of locations required by the effects already in force. -/
  requirements : List (List (Option ObjId)) := []
  /-- Banish a card from the look as part of finalizing its play (CR 420.3.c). -/
  banishBeforeFunding : Bool := false
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
  /-- The passive sources whose Gear play reductions were elected. -/
  gearDiscounts : List ObjId := []
  /-- The card revealed or friendly object picked for Show Off (CR 832). -/
  showOff : Option ObjId := none
  /-- Whether the player elects the card's additional XP cost. -/
  spendXP : Bool := false
deriving DecidableEq, Hashable

/-- Preserve the fingerprints of old plans that did not elect XP without an object. -/
instance : Repr ReducedPermanentPlay where
  reprPrec p _ :=
    let field (name : String) (value : Std.Format) :=
      Std.Format.text name ++ " := " ++ (Std.Format.nest (name.length + 4) value).group
    let fields := [field "cost" (repr p.cost), field "battlefield" (repr p.battlefield),
      field "extraObject" (repr p.extraObject), field "discard" (repr p.discard),
      field "additionalPaid" (repr p.additionalPaid), field "accelerated" (repr p.accelerated),
      field "battlefieldFees" (repr p.battlefieldFees), field "gearDiscounts" (repr p.gearDiscounts),
      field "showOff" (repr p.showOff)]
    let fields := if p.spendXP then fields ++ [field "spendXP" (repr true)] else fields
    Std.Format.bracket "{ " (Std.Format.joinSep fields (Std.Format.text "," ++ Std.Format.line)) " }"

/-- One activation that provides resources for an effect's play (CR 357.1.a). -/
inductive EffectAdd where
  /-- Exhaust or Recycle a Basic Rune. -/
  | rune (source : ObjId) (recycle : Bool)
  /-- Use a card's Add ability with its own selected resource cost. -/
  | ability (source : ObjId) (index energy : Nat) (power : List Domain) (banish : Option ObjId := none)
deriving DecidableEq, Repr, Hashable

/-- Choices and resource price of a Spell under a limited play effect. -/
structure EffectSpellPlay where
  /-- The objects chosen by the Spell. -/
  targets : List ObjId
  /-- The resources due for the selected choices. -/
  cost : Cost
  /-- Its mode, player target, destination or optional cost choices. -/
  pick : SpellPick
  /-- The hand card selected to pay an optional additional cost. -/
  discard : Option ObjId := none
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

/-- The parameters and tentative results of a simultaneous damage instruction. -/
structure EffectDamageProgress where
  /-- Who controls damage from a Spell or Ability, or none for an exchange between Units. -/
  controller : Option PlayerId
  /-- Events waiting to have their replacements ordered. -/
  incoming : List (ObjId × Nat)
  /-- Final damage events, in reverse input order. -/
  resolved : List (ObjId × Nat) := []
  /-- The amount consumed from each numbered turn note. -/
  spent : List (Nat × Nat) := []
deriving DecidableEq, Repr, Hashable

/-- The reflexive ability created by a death caused by this instruction. -/
structure DamageKillLink where
  /-- Original Chain item. -/
  source : ObjId
  /-- Unit dealing the damage. -/
  dealer : ObjId
  /-- Controller of the reflexive ability. -/
  player : PlayerId
  /-- Card containing the reflexive ability. -/
  card : CardId
  /-- Reflexive ability index. -/
  index : Nat
deriving DecidableEq, Repr, Hashable

/-- Damage from one instruction. Damage and replacements remain tentative until the
whole simultaneous instruction is ready. -/
structure EffectDamageBatch extends EffectDamageProgress where
  /-- An optional reflexive ability tied to actual deaths from the damage. -/
  onKill : Option DamageKillLink := none
deriving DecidableEq, Hashable

/-- Keep the established checkpoint representation for damage without a linked ability. -/
instance : Repr EffectDamageBatch where
  reprPrec batch prec := match batch.onKill with
    | none => reprPrec batch.toEffectDamageProgress prec
    | some link => reprPrec (batch.toEffectDamageProgress, link) prec

/-- The reflexive ability attached to a Unit token instruction (CR 375, 388-389). -/
structure UnitTokenFollowup where
  /-- The object from which the linked instruction originated. -/
  source : ObjId
  /-- The definition containing the follow-up ability. -/
  card : CardId
  /-- The index of the ability in that definition. -/
  index : Nat
  /-- The object chosen earlier, if the linked ability refers to it. -/
  target : Option ObjId
deriving DecidableEq, Repr, Hashable

/-- A simultaneous group of Unit token plays at the specified location. Each entry records
its card and any instruction to enter ready (CR 184.2, 375-376). -/
structure UnitTokenBatch where
  /-- The shared Battlefield, or the controller's Base. -/
  destination : Option ObjId
  /-- Whether the original instruction explicitly contests its destination. -/
  contest : Bool
  /-- The token definitions and their explicit entry-ready flags. -/
  entries : List (CardId × Bool)
  /-- The ability to queue with the objects that actually enter. -/
  followup : Option UnitTokenFollowup := none
  /-- Sources whose optional duplication was elected for this play. -/
  duplicatedBy : List (ObjId × Option Timestamp) := []
deriving DecidableEq, Repr, Hashable

/-- An available replacement sequence for simultaneous Unit token plays (CR 370-375). -/
inductive UnitTokenReplacement where
  /-- Offer substitutions from the available token definitions, one for each entry. -/
  | substitute (cards : List CardId)
  /-- Offer one extra copy of a token, from this unused ability instance. -/
  | duplicate (source : ObjId) (copy : Option Timestamp)
deriving DecidableEq, Repr, Hashable

/-- The decisions still to complete before finalizing a group of Unit token plays. -/
inductive UnitTokenPlan where
  /-- Choose each token's substitution, then continue with the remaining replacements. -/
  | substitute (cards : List CardId) (remaining chosen : List (CardId × Bool))
      (after : List UnitTokenReplacement)
  /-- Apply the next replacement in the elected order. -/
  | apply (replacement : UnitTokenReplacement) (after : List UnitTokenReplacement)
  /-- Duplicate the selected entry or decline this use. -/
  | duplicate (source : ObjId) (copy : Option Timestamp) (entry : Option Nat)
      (after : List UnitTokenReplacement)
deriving DecidableEq, Repr, Hashable

mutual

/-- An effect: what happens when a spell resolves or an ability fires. -/
inductive Effect where
  /-- Choose a previously registered additional Legend to add while the source is on the Board. -/
  | addReservedLegend
  /-- Capture the answer to the registered Legend choice. -/
  | addReservedLegendPicked
  /-- Add one available registered Legend. -/
  | addReservedLegendChosen (legend : ObjId)
  /-- Choose the replacements for the tokens before the group is placed. -/
  | planUnitTokenEntries (batch : UnitTokenBatch) (plan : UnitTokenPlan)
  /-- Choose resources and add funding for the token's optional Accelerate. -/
  | fundTokenAccelerate (batch : UnitTokenBatch) (payment : Nat × List Domain) (adds : List EffectAdd)
  /-- Place the group with the selected additional cost, if any. -/
  | finishUnitTokens (batch : UnitTokenBatch) (accelerate : Option (Nat × List Domain))
      (adds : List EffectAdd)
  /-- Nothing happens. -/
  | nop
  /-- Turn the chosen Gear into a Unit Gear until this ability chooses another (CR 143.5, 479). -/
  | animateGear
  /-- Record a triggered Add's use before its resource effects resolve (CR 430.2). -/
  | markTriggeredAdd (idx : Nat)
  /-- Do the effects in order. -/
  | seq (es : EffectList)
  /-- Do the mode that was chosen when the card was played (CR 355). -/
  | chooseOne (modes : EffectList)
  /-- Attach the Equipment to the Unit after paying a discounted Equip cost (CR 821). -/
  | equipWithCost (gear recipient : Selector) (powerDiscount : Nat)
  /-- The player chooses one of the effects while the effect resolves, and does it. -/
  | eitherOf (modes : EffectList)
  /-- Pay a resource cost from the Rune Pool, then continue with the effect (CR 445.2). -/
  | payThen (cost : Cost) (body : Effect) (gearPower : Bool := true)
  /-- Spend the specific resources selected from the Pool for this payment. -/
  | paySelected (resources : Cost) (body : Effect) (gearPower : Bool := true)
  /-- Do the first effect if the condition holds, the second otherwise. -/
  | ifThen (c : Condition) (t e : Effect)
  /-- Do the effect for each of the objects, with `it` the object. -/
  | forEach (s : Selector) (body : Effect)
  /-- Each of the players does the effect: the effect is done for them, so that what they choose
  is theirs ("each player kills one of their units"). -/
  | eachPlayer (who : PlayerSel) (body : Effect)
  /-- Reveal the specified hands for the following instructions (CR 425). -/
  | revealHand (who : PlayerSel) (body : Effect)
  /-- Reveal one top Main Deck card from each listed player and keep those cards for the body. -/
  | revealDeckTops (who : PlayerSel) (body : Effect)
  /-- The chosen player guesses a Main Deck card type, then the controller runs that branch. -/
  | guessCardType (who : PlayerSel) (onUnit onGear onSpell : Effect)
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
  /-- Recycle the cards targeted in Trashes together (CR 417.5). -/
  | recycleTrashTargets
  /-- Choose cards in the specified Trashes as this resolves, then Recycle them together (CR 417.4-6). -/
  | recycleFromTrash (side : Side) (count : Nat) (upTo : Bool) (picked : List ObjId := [])
  /-- Offer the next object choice after agreeing to Recycle one more card. -/
  | chooseTrashRecycle (side : Side) (count : Nat) (picked : List ObjId)
  /-- Continue a group Recycle with the chosen card still in its Trash. -/
  | recordTrashRecycle (side : Side) (count : Nat) (upTo : Bool) (picked : List ObjId)
  /-- Report activation after paying its Recycle cost. Until then, the declared targets and
  filters constrain which Trash cards may pay that cost (CR 357.3, 401.1). -/
  | completeActivation (source : ObjId) (index : Nat) (baseEnergy : Option Nat)
      (targets : List ObjId) (filters : FilterList)
  /-- Recycle an exact group selected during resolution. -/
  | finishTrashRecycle (picked : List ObjId)
  /-- Recycle the player's Runes together after their owners choose the order (CR 417.5.a). -/
  | recycleRunes
  /-- Continue collecting the order of each owner's Runes before any are Recycled. -/
  | orderRuneRecycle (groups : List (PlayerId × List ObjId)) (picked : List ObjId)
  /-- Record the Rune chosen next in an owner's order. -/
  | recordRuneRecycle (remaining : List ObjId) (later : List (PlayerId × List ObjId))
      (picked : List ObjId)
  /-- Continue after offering a choice of eligible cards from a look. -/
  | chooseLookedToPlay (less : Nat) (first : ObjId) (more : List ObjId)
  /-- Banish the card picked from the looked-at cards and finalize the play. -/
  | banishLookedForPlay (less : Nat)
  /-- Optionally play a card selected while resolving the effect (CR 355.16, 420.3). -/
  | mayPlayCard (selector : Selector) (price : EffectPlayPrice)
  /-- Play one of the matching physical cards, if it has a legal finalization (CR 420.3). -/
  | playCard (selector : Selector) (price : EffectPlayPrice) (baseOnly : Bool := false)
  /-- Banish the selected card and play that physical card from Banishment (CR 420.3). -/
  | banishAndPlayCard (selector : Selector) (price : EffectPlayPrice)
  /-- Banish the top Main Deck card and permit its play until the player's next Ending Phase. -/
  | banishTopForPlay
  /-- Kill the targets and register the end-of-turn ability with their actual death count. -/
  | killThenAtEnd (targets : Selector) (triggerIndex : Nat)
  /-- Play the source card if it is still in this player's Trash. -/
  | playSelfFromTrash (cost : Cost) (exit : LimitedSpellExit)
  /-- Optionally play up to this many distinct Units or Gear selected during resolution. -/
  | mayPlayPermanents (selector : Selector) (maximum : Nat) (price : EffectPlayPrice)
  /-- Offer another play from the candidates identified when the instruction began. -/
  | offerNextCardPlay (cards : List ObjId) (remaining : Nat) (price : EffectPlayPrice)
  /-- Ask which of the available cards to play. -/
  | chooseOfferedPlay (cards : List ObjId) (remaining : Nat) (price : EffectPlayPrice)
      (first : ObjId) (others : List ObjId)
  /-- Continue to the selected card's finalization. -/
  | playOfferedCard (cards : List ObjId) (remaining : Nat) (price : EffectPlayPrice)
      (baseOnly : Bool := false)
  /-- Count a successful finalization before offering another play. -/
  | afterOfferedPlay (card : ObjId) (cards : List ObjId) (remaining : Nat) (price : EffectPlayPrice)
  /-- Continue an effect's play, offering the Unit or Gear's legal finalizations. -/
  | planPermanentPlay (card : ObjId) (terms : EffectPlayTerms)
  /-- Banish one Unit before its owner finalizes the new play. -/
  | banishForReplay (card : ObjId) (replay : BanishReplay)
  /-- Banish the chosen group of Units together, then replay each owner's cards. -/
  | banishAndReplayGroup
  /-- The owners order their pending plays in turn order before finalization (CR 303.2.a). -/
  | orderBanishReplays (remaining ordered : List (PlayerId × ObjId × Option ObjId))
  /-- Record one owner's next play and return to ordering the rest of the group. -/
  | recordBanishReplay (controller : PlayerId)
      (remaining ordered : List (PlayerId × ObjId × Option ObjId))
  /-- Finalize an ordered replay from Banishment once the group is ready. -/
  | planBanishReplay (card : ObjId) (location : Option ObjId)
  /-- Return a pending replay to Banishment if it could not finalize. -/
  | cancelBanishReplay (card : ObjId)
  /-- Apply the selected finalization of a Unit or Gear played by the effect. -/
  | finishReducedPermanent (card : ObjId) (terms : EffectPlayTerms) (plan : ReducedPermanentPlay)
  /-- Continue choosing resource activations for the selected finalization. -/
  | fundPermanentFromEffect (card : ObjId) (terms : EffectPlayTerms) (plan : ReducedPermanentPlay)
      (adds : List EffectAdd)
  /-- Use the chosen Add abilities and pay for the effect's permanent as one finalization. -/
  | finishFundedPermanent (card : ObjId) (terms : EffectPlayTerms) (plan : ReducedPermanentPlay)
      (adds : List EffectAdd)
  /-- Finalize a Spell queued by a limited play effect. -/
  | finalizeLimitedSpell (card : ObjId)
  /-- Continue choosing the individual Add abilities for the queued Spell's payment. -/
  | fundLimitedSpell (card : ObjId) (plan : EffectSpellPlay) (adds : List EffectAdd)
  /-- Pay for the queued Spell and make its chosen targets and other finalization choices public. -/
  | finishLimitedSpell (card : ObjId) (plan : EffectSpellPlay) (adds : List EffectAdd)
  /-- Return the queued Spell to its original zone without finalizing it. -/
  | cancelLimitedSpell (card : ObjId)
  /-- Resolve one of a Spell's independently finalized executions (CR 820.2). -/
  | resolveSpellExecution (pick : SpellPick) (targets : List ObjId)
  /-- Continue working through the events of a single damage instruction. -/
  | resolveEffectDamage (batch : EffectDamageBatch) (hit : Option EffectDamageHit)
  /-- Divide damage among the remaining targets at resolution (CR 355.14). -/
  | splitDamage (targets : Selector) (total : Nat)
  /-- A Unit deals its current Might in divided damage, with a reflexive ability per kill. -/
  | splitUnitDamage (dealer targets : Selector) (onKill : Nat)
  /-- Apply a selected division whose damage comes from a Unit (CR 418.6.b.3). -/
  | applyUnitSplitDamage (hits : List (ObjId × Nat)) (link : DamageKillLink)
  /-- Deal the chosen damage simultaneously after replacements have been applied. -/
  | applySplitDamage (hits : List (ObjId × Nat))
  /-- Apply one selected replacement and continue with the rest. -/
  | chooseDamageReplacement (batch : EffectDamageBatch) (hit : EffectDamageHit)
      (replacement : DamageReplacement)
  /-- Choose which replacements apply first to a combat assignment. `chosen` is in reverse order. -/
  | orderCombatDamage (target : ObjId) (chosen remaining : List DamageReplacement)
  /-- Record which player's Banish replaces the pending death (CR 372). -/
  | chooseDeathBanisher (unit : ObjId) (banisher : PlayerId)
  /-- Record which mandatory Gear replacement the affected Unit's controller selected. -/
  | chooseDeathGear (unit gear : ObjId)
  /-- Record the selected free rescue, with None for a Tactical Retreat on the Unit. -/
  | chooseDeathFree (unit : ObjId) (source : Option ObjId)
  /-- Declare the friendly Unit paying for this death replacement, or decline it. -/
  | recordDeathSacrifice (unit : ObjId) (cost : Option ObjId)
  /-- Record a controller's next replacement among simultaneous deaths (CR 373). -/
  | recordDeathOrder (group : List ObjId) (unit : ObjId)
  /-- Record a revised replacement after an earlier event consumed or moved its source. -/
  | recordDeathReselection (group earlier : List ObjId) (unit : ObjId) (choice : DeathDecision)
  /-- Record an answer for one distinct nested Kill event. -/
  | recordNestedDeathDecision (root : ObjId) (used : List (ObjId × Bool))
      (unit : ObjId) (choice : DeathDecision) (groupScope : Option (List ObjId × List ObjId))
  /-- Expire the assignment choices and record excess damage once Combat Damage is dealt. -/
  | endCombatDamage (excess : Nat)
  /-- Choose one object during resolution and bind it to `pickVar` for the following
  instructions (CR 355.18). -/
  | chooseObject (side : Side) (place : Place) (filters : FilterList) (body : Effect)
  /-- Each player chooses one of their own objects. Append the picks to the slots, then run the
  body for the original controller. The picks are not targets (CR 355.10.e). -/
  | pickOwn (place : Place) (filters : FilterList) (body : Effect)
  /-- The controller must pick one of their own objects during resolution. Append it to the
  slots without making it a target (CR 355.10.f). -/
  | pickRequired (place : Place) (filters : FilterList) (body : Effect)
  /-- Move the Unit in the given slot to the location chosen during finalization (CR 355.4).
  If the move happens, run the follow-up with a chosen Battlefield available as the latest pick. -/
  | moveChoosing (slot : Nat) (allowBase : Bool) (battlefields : FilterList) (afterMove : Effect)
      (afterNegatedMove : Bool := false)
  /-- During resolution the named player chooses and moves one of their Units to the Battlefield
  when the move is possible. The choice is not a target (CR 355.10.e). -/
  | forceMoveToBattlefield (who : PlayerSel) (destination : Selector)
  /-- Carry out the Move after its fee was paid. Its follow-up runs only if a Unit moved. -/
  | moveAfterFee (move : Prim) (afterMove : Effect)
  /-- Plan or commit Add activations for a fee on an instructed Move (CR 204.4.b.1). -/
  | fundMoveFee (move : Prim) (afterMove : Effect) (adds : List EffectAdd) (commit : Bool)
  /-- Grant a numbered keyword whose amount is determined as the effect resolves. -/
  | grantNumericKeyword (objects : Selector) (keyword : Keyword) (amount : Amount)
      (duration : Duration)
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
  /-- Play a group of Unit tokens, then queue the linked ability with the resulting objects.
  The linked ability can inherit one previously chosen object without choosing it again. -/
  | playUnitTokensThen (name : String) (count : Nat) (place : Place) (ready : Bool)
      (index : Nat) (target : Option Selector := none)
  /-- Kill the chosen permanent, then resolve the linked instruction for its controller
  (CR 359.3.e.14). -/
  | killThenForController (slot : Nat) (body : Effect)
  /-- Kill the chosen permanent, then perform the linked instruction only if this action killed
  that permanent (CR 359.3.e, 370.1.a.1). -/
  | killThenIfKilled (slot : Nat) (body : Effect)
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
