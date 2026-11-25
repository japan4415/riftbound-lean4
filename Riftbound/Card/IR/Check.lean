module

public import Riftbound.Card.IR.Build

/-!
# The effect IR: the static check

A card can be written down as an IR value that no game could run: a variable that is not bound, a
chosen object that was never declared, a mode to choose in an effect with no modes. These checks
decide, from the shape of an effect alone, whether such a mistake is there (design.md §7.1,
`CardDB.WF`). They are Boolean functions, so that `decide` and `#guard` can run them.

The context of a check (`Ctx`) says what an effect may refer to at that point: the variables bound
so far, how many objects were chosen when the card was played, whether an X and a mode were
chosen, whether `it` (the object of a loop or a trigger) means something, and whether the amount and
the player of a replaced event do.
-/

@[expose] public section

namespace Riftbound

/-- What an effect may refer to at a point. -/
structure Ctx where
  /-- The variables bound so far. -/
  vars : List VarId := []
  /-- The number of objects chosen when the card was played: the slots `0` to `slots - 1`. -/
  slots : Nat := 0
  /-- The number of declared player target slots. -/
  playerSlots : Nat := 0
  /-- An X was chosen when the card was played. -/
  hasX : Bool := false
  /-- The number of modes the card asks to choose from, if it does. -/
  modes : Option Nat := none
  /-- `it` means the object of a loop or of a trigger. -/
  itOk : Bool := false
  /-- The amount and the player of a replaced event are known. -/
  eventOk : Bool := false
  /-- An amount was captured by a reflexive trigger. -/
  eventAmountOk : Bool := false
deriving DecidableEq, Repr

/-- The players an effect names can be found. -/
def PlayerSel.ok (c : Ctx) : PlayerSel → Bool
  | .chosen i => decide (i < c.playerSlots)
  | .eventPlayer => c.eventOk
  | _ => true

mutual

/-- An amount refers only to what is there. -/
def Amount.ok (c : Ctx) : Amount → Bool
  | .const _ => true
  | .x => c.hasX
  | .var v => c.vars.contains v || v == pickVar
  | .points p => PlayerSel.ok c p
  | .eventAmount => c.eventOk || c.eventAmountOk
  | .shownOffMight | .shownOffPower => true
  | .turnsTaken p => p.ok c
  | .count s => Selector.ok c s
  | .mightOf s => Selector.ok c s
  | .mightIncreaseTo unit reference => Selector.ok c unit && Selector.ok c reference
  | .damageOn s => Selector.ok c s
  | .costOf s => Selector.ok c s
  | .powerCostOf s => Selector.ok c s
  | .xp => true
  | .pointsLeft => true
  | .victoryScore => true
  | .highestMight s => Selector.ok c s
  | .kwAmount s _ => Selector.ok c s
  | .cardsPlayed => true
  | .spellsChoseEnemy => true
  | .powerSpent => true
  | .gearsPlayed => true
  | .equipmentPlayed => true
  | .excess => true
  | .heldPoints => true
  | .movesThisTurn => true
  | .notes _ => true
  | .energyPaid | .returnedGearEnergy => true
  | .empowerCount => true
  | .handSize p => p.ok c
  | .add a b => Amount.ok c a && Amount.ok c b
  | .sub a b => Amount.ok c a && Amount.ok c b
  | .mul a b => Amount.ok c a && Amount.ok c b
  | .min a b => Amount.ok c a && Amount.ok c b
  | .max a b => Amount.ok c a && Amount.ok c b

/-- A filter refers only to what is there. -/
def Filter.ok (c : Ctx) : Filter → Bool
  | .might _ a => Amount.ok c a
  | .cost _ a => Amount.ok c a
  | .powerCost _ a => Amount.ok c a
  | .at_ s => Selector.ok c s
  | .attachedTo s => Selector.ok c s
  | .not f => Filter.ok c f
  | .either a b => Filter.ok c a && Filter.ok c b
  | .both a b => Filter.ok c a && Filter.ok c b
  | .sameAs s => Selector.ok c s
  | .sameController s => Selector.ok c s
  | .ownedByPlayerTarget i => decide (i < c.playerSlots)
  | _ => true

/-- Every filter of a list refers only to what is there. -/
def FilterList.ok (c : Ctx) : FilterList → Bool
  | .nil => true
  | .cons f rest => Filter.ok c f && FilterList.ok c rest

/-- A selector refers only to what is there. -/
def Selector.ok (c : Ctx) : Selector → Bool
  | .self => true
  | .slot i => decide (i < c.slots)
  | .it => c.itOk
  | .var v => c.vars.contains v || v == pickVar
  | .pick _ _ _ fs => FilterList.ok c fs
  | .revealedDeck _ => true
  | .attachedTo s => Selector.ok c s
  | .attachments s => Selector.ok c s
  | .locationOf s => Selector.ok c s
  | .slotsFrom i => decide (i < c.slots)

/-- A condition refers only to what is there. -/
def Condition.ok (c : Ctx) : Condition → Bool
  | .always => true
  | .not d => Condition.ok c d
  | .and a b => Condition.ok c a && Condition.ok c b
  | .or a b => Condition.ok c a && Condition.ok c b
  | .cmp _ a b => Amount.ok c a && Amount.ok c b
  | .exists s => Selector.ok c s
  | .matches s f => Selector.ok c s && Filter.ok c f
  | .empowered s => Selector.ok c s
  | .opponentFinalizedOtherSpell s | .firstResolvedType _ s => Selector.ok c s
  | _ => true

end

/-- A destination refers only to what is there. -/
def Dest.ok (c : Ctx) : Dest → Bool
  | .base => true
  | .at_ s => Selector.ok c s

/-- A game action refers only to what is there. -/
def Prim.ok (c : Ctx) : Prim → Bool
  | .draw p n => p.ok c && Amount.ok c n
  | .drawLooked s => Selector.ok c s
  | .discard p n => p.ok c && Amount.ok c n
  | .deal s n => Selector.ok c s && Amount.ok c n
  | .exchangeDamage a b => Selector.ok c a && Selector.ok c b
  | .setBaseMight s n => Selector.ok c s && Amount.ok c n
  | .heal s n => Selector.ok c s && Amount.ok c n
  | .kill s => Selector.ok c s
  | .banish s => Selector.ok c s
  | .recall s _ => Selector.ok c s
  | .returnToHand s => Selector.ok c s
  | .move s d => Selector.ok c s && d.ok c
  | .ready s => Selector.ok c s
  | .exhaust s => Selector.ok c s
  | .stun s => Selector.ok c s
  | .buff s => Selector.ok c s
  | .recycle s => Selector.ok c s
  | .spendBuff s => Selector.ok c s
  | .recycleTop p => PlayerSel.ok c p
  | .swapTop p => PlayerSel.ok c p
  | .channel p n e => p.ok c && Amount.ok c n && Amount.ok c e
  | .addEnergy p n _ | .addUnitEnergy p n => p.ok c && Amount.ok c n
  | .addPower p n _ _ => p.ok c && Amount.ok c n
  | .counter s => Selector.ok c s
  | .counterToHand s => Selector.ok c s
  | .play s | .playAtBase s => Selector.ok c s
  | .banishReplay s _ => Selector.ok c s
  | .copyAttachedFrom s => Selector.ok c s
  | .playPaying s => Selector.ok c s
  | .giveKeywords t f => Selector.ok c t && Selector.ok c f
  | .playReduced s a t => Selector.ok c s && Amount.ok c a && (match t with
    | some b => Selector.ok c b
    | none => true)
  | .castInline s => Selector.ok c s
  | .hideAt s b => Selector.ok c s && Selector.ok c b
  | .playTo s b => Selector.ok c s && Selector.ok c b
  | .bin s => Selector.ok c s
  | .discardCard s | .discardWithTypeTriggers s _ => Selector.ok c s
  | .hide s => Selector.ok c s
  | .reveal s => Selector.ok c s
  | .revealNow s => Selector.ok c s
  | .revealTop _ => true
  | .revealTopNow _ => true
  | .create _ n _ _ => Amount.ok c n
  | .createAt _ n bf _ => Amount.ok c n && Selector.ok c bf
  | .playUnitToken _ | .playUnitTokenAt _ _ => true
  | .attach s t => Selector.ok c s && Selector.ok c t
  | .attachPaying s t _ => Selector.ok c s && Selector.ok c t
  | .detach s => Selector.ok c s
  | .gainXP p n => p.ok c && Amount.ok c n
  | .becomeCopy s src => Selector.ok c s && Selector.ok c src
  | .addBattlefield _ => true
  | .createAtPrev _ n _ => Amount.ok c n
  | .cloneToken s => Selector.ok c s
  | .banishWith s => Selector.ok c s
  | .gainTag s _ => Selector.ok c s
  | .replaceBattlefield s _ => Selector.ok c s
  | .restoreBattlefield s => Selector.ok c s
  | .moveAll _ _ fs _ _ => FilterList.ok c fs
  | .spendXP p n => p.ok c && Amount.ok c n
  | .score p n => p.ok c && Amount.ok c n
  | .burn p n => p.ok c && Amount.ok c n
  | .burnWithUnitTrigger n _ => Amount.ok c n
  | .predict n => Amount.ok c n
  | .copy s => Selector.ok c s
  | .double s | .grantActivation s _ => Selector.ok c s
  | .swap a b => Selector.ok c a && Selector.ok c b
  | .empower s => Selector.ok c s
  | .disempower s => Selector.ok c s
  | .takeControl s => Selector.ok c s
  | .playBanishedWith => true
  | .returnControl s => Selector.ok c s
  | .takeControlUntilLeaves s => Selector.ok c s
  | .extraTurn p => p.ok c
  | .win p => p.ok c
  | .turnEffect _ => true
  | .playFirst fs => FilterList.ok c fs
  | .markOn s _ => Selector.ok c s
  | .delayUntilDeath s _ => Selector.ok c s
  | .activateConquer s => Selector.ok c s
  | .choose s => Selector.ok c s
  | .lookTop _ => true
  | .swapPlaces a b => Selector.ok c a && Selector.ok c b
  | .returnChampion => true
  | .pay _ => true
  | .topdeck s => Selector.ok c s

/-- A duration refers only to what is there. -/
def Duration.ok (c : Ctx) : Duration → Bool
  | .whileCond d => Condition.ok c d
  | _ => true

/-- An argument of a custom handler refers only to what is there. -/
def Arg.ok (c : Ctx) : Arg → Bool
  | .amount a => Amount.ok c a
  | .selector s => Selector.ok c s
  | .condition d => Condition.ok c d

/-- The arguments of a custom handler refer only to what is there. -/
def ArgList.ok (c : Ctx) : ArgList → Bool
  | .nil => true
  | .cons a rest => a.ok c && ArgList.ok c rest

/-- A static modification refers only to what is there. -/
def StaticMod.ok (c : Ctx) : StaticMod → Bool
  | .mightPlus s a | .mightPlusWithKeyword s _ a => Selector.ok c s && Amount.ok c a
  | .mightMinus s a => Selector.ok c s && Amount.ok c a
  | .mightMinusMin s a _ => Selector.ok c s && Amount.ok c a
  | .keyword s _ => Selector.ok c s
  | .flowAtBaseCost => c.itOk
  | .costPlus s a => Selector.ok c s && Amount.ok c a
  | .costMinus s a => Selector.ok c s && Amount.ok c a
  | .costPower s a _ _ => Selector.ok c s && Amount.ok c a
  | .costMinusMin s a _ => Selector.ok c s && Amount.ok c a
  | .noDamage | .noEnemyEffectDamage | .noEnemyEffectMove => true
  | .noMoveToBase => true
  | .recallAllOnTie => true
  | .extraHide => true
  | .playToOpenBf => true
  | .anyBuffs => true
  | .hideWithEnergy => true
  | .assignedLast => true
  | .anyDamageKills => true
  | .movesHereFromAnywhere => true
  | .grantRepeat _ | .spellsHaveReaction | .deployGearHaveAction => true
  | .entersExhausted => true
  | .oppsPlayToBaseOnly | .oppsCantPlayNamed => true
  | .skipDrawPhase | .playFromTrash | .banishInsteadOfTrash => true
  | .allUnitsEnterReady | .skipUnitAwaken | .unitsEnterReadyAtControlledBattlefields => true
  | .sharedBattlefieldActivation | .grantFriendlyLegendsActivations
  | .additionalExhaustedRunes _ => true
  | .assaultCount s => Selector.ok c s
  | .legendsAttach => true
  | .chosenSpellsCostLess _ => true
  | .friendlyTargetPowerCut _ | .showdownReactionTax _ => true
  | .lookBeforeReveal => true
  | .banishOnDeath => true
  | .copiesUnitText => true
  | .extraCostLess _ => true
  | .repeatCostLess _ => true
  | .firstGearAbilityLess _ | .firstPermanentHereLess _ | .empowerHereLess _ => true
  | .equipEach _ => true
  | .manaExtraEnergy s n => Selector.ok c s && Amount.ok c n
  | .diesInsteadGear => true
  | .rescueWeakerHere => true
  | .noMoveToBaseAny => true
  | .moveFeeHere _ => true
  | .playToBf fs => FilterList.ok c (FilterList.ofList fs)
  | .playToBfAll fs => FilterList.ok c (FilterList.ofList fs)
  | .playHereFor _ _ => true
  | .noPlayToBase => true
  | .noReadyOfOpps => true
  | .noHiddenReveal => true
  | .bonusDamageHere _ => true
  | .cant s _ => Selector.ok c s
  | .may s _ => Selector.ok c s
  | .victoryScorePlus a => Amount.ok c a
  | .victoryScoreMinus a => Amount.ok c a
  | .ignoreKeyword _ _ => true
  | .entersReady s => Selector.ok c s
  | .bonusDamage a | .bonusAbilityDamage _ a => Amount.ok c a
  | .noCombatDamage => true
  | .channelLimit _ => true
  | .uncounterable | .controlledItemsUncounterable | .friendlyExhaustAbilities
  | .targetMightPenalty _ | .chosenHarmToMight _ => true
  | .ignoreDeflectSpell => true
  | .ignoreDeflectHere => true
  | .noCombatDamageFor _ => true
  | .doubleEquip => true
  | .mightIfFresh _ => true
  | .gainsTag _ => true
  | .keywordHere _ => true
  | .holdIsConquer => true
  | .triggersExtra _ _ => true
  | .cantPlayer p _ _ _ => p.ok c
  | .earlyScoreDraw _ => true
  | .custom _ args => args.ok c

/-- A cost of an ability refers only to what is there. -/
def AbilityCost.ok (c : Ctx) : AbilityCost → Bool
  | .killFriendly _ fs | .discardMatching _ fs | .exhaustFriendly fs
  | .killFriendlyPermanent fs => FilterList.ok c fs
  | .energyDiscount cond amount => Condition.ok c cond && Amount.ok c amount
  | _ => true

/-- How many objects the ability of a trigger gets from what it watches: one if it watches another
object, and for the player's units elsewhere when they defend (the Battlefield). -/
def Trigger.watched (t : Trigger) : Nat :=
  match t.event with
  | .youDefend => 1
  | _ => if t.subject == .self then 0 else 1

/-- A trigger refers only to what is there. -/
def Trigger.ok (c : Ctx) (t : Trigger) : Bool :=
  -- the condition may use the object the ability watches (slot 0); the subject may not
  Selector.ok c t.subject &&
    Condition.ok { c with slots := t.watched } t.condition &&
    (match t.cost with
     | .killFriendly _ fs => FilterList.ok c fs
     | _ => true)

/-- How many effects a list holds. -/
def EffectList.length : EffectList → Nat
  | .nil => 0
  | .cons _ rest => rest.length + 1

mutual

/-- An effect refers only to what is there, and a mode is chosen only where modes were declared. -/
def Effect.ok (c : Ctx) : Effect → Bool
  | .nop => true
  | .markTriggeredAdd _ => false
  | .seq es => EffectList.ok c es
  | .chooseOne modes => decide (c.modes = some modes.length) && EffectList.ok c modes
  | .eitherOf modes => EffectList.ok c modes
  | .payThen _ body _ => Effect.ok c body
  | .paySelected .. | .moveAfterFee .. => false
  | .ifThen d t e => Condition.ok c d && Effect.ok c t && Effect.ok c e
  | .forEach s body => Selector.ok c s && Effect.ok { c with itOk := true } body
  | .fillSlot _ s => Selector.ok c s
  | .fillFromPick _ => true
  | .retainTargetSet _ | .applySplitDamage _ => false
  | .splitDamage targets _ => Selector.ok c targets
  | .remakeSpellChoices spell => Selector.ok c spell
  | .setSpellChoices .. => false
  | .eachPlayer w e => PlayerSel.ok c w && Effect.ok c e
  | .revealHand w e | .revealDeckTops w e => PlayerSel.ok c w && Effect.ok c e
  | .guessCardType who unit gear spell =>
    PlayerSel.ok c who && Effect.ok c unit && Effect.ok c gear && Effect.ok c spell
  | .nameCard _ | .rememberNamedCard _ => true
  | .lookAtTop _ body => Effect.ok c body
  | .banishAndPlayLooked _ fs => FilterList.ok c fs
  | .recycleLooked | .recycleRunes | .banishTopForPlay | .playSelfFromTrash .. => true
  | .playCard sel _ | .banishAndPlayCard sel _ | .mayPlayCard sel _ |
      .mayPlayPermanents sel _ _ => Selector.ok c sel
  | .orderRuneRecycle .. | .recordRuneRecycle .. | .offerNextCardPlay .. |
      .chooseOfferedPlay .. | .playOfferedCard .. | .afterOfferedPlay .. => false
  | .chooseLookedToPlay .. | .banishLookedForPlay _ | .planPermanentPlay .. |
      .banishForReplay .. | .finishReducedPermanent .. | .fundPermanentFromEffect .. |
      .finishFundedPermanent .. | .finalizeLimitedSpell .. | .fundLimitedSpell .. |
      .finishLimitedSpell .. | .cancelLimitedSpell .. | .resolveSpellExecution .. |
      .resolveEffectDamage .. |
      .chooseDamageReplacement .. | .orderCombatDamage .. | .chooseDeathBanisher .. |
      .endCombatDamage .. => false
  | .chooseObject _ _ fs e => FilterList.ok c fs && Effect.ok c e
  | .pickOwn _ fs e => FilterList.ok c fs && Effect.ok { c with slots := c.slots + 1 } e
  | .moveChoosing i _ fs e _ => Selector.ok c (.slot i) && FilterList.ok c fs && Effect.ok c e
  | .forceMoveToBattlefield who destination => PlayerSel.ok c who && Selector.ok c destination
  | .grantNumericKeyword objects _ amount duration =>
    Selector.ok c objects && Amount.ok c amount && Duration.ok c duration
  | .collectOwnPicks .. => false
  | .may e => Effect.ok c e
  | .doThen a b => Effect.ok c a && Effect.ok c b
  | .repeatN n e => Amount.ok c n && Effect.ok c e
  | .bind v a e => Amount.ok c a && Effect.ok { c with vars := v :: c.vars } e
  | .prim p => Prim.ok c p
  | .grant s m d => Selector.ok c s && StaticMod.ok { c with itOk := true } m && Duration.ok c d
  | .delayed t e d =>
    Trigger.ok { c with itOk := true } t && Effect.ok { c with itOk := true } e && Duration.ok c d
  | .preventNext s n d => Selector.ok c s && Amount.ok c n && Duration.ok c d
  | .replaceNext _ s instead d =>
    Selector.ok c s && Effect.ok { c with eventOk := true } instead && Duration.ok c d
  | .custom _ args => ArgList.ok c args

/-- Every effect of a list refers only to what is there. -/
def EffectList.ok (c : Ctx) : EffectList → Bool
  | .nil => true
  | .cons e rest => Effect.ok c e && EffectList.ok c rest

end

/-- Whether the choice is a target, which fills a slot. -/
def Choice.isTarget : Choice → Bool
  | .target .. => true
  | _ => false

/-- A choice refers only to what is there. A target is chosen before anything else is known. -/
def Choice.ok (earlier : Nat) : Choice → Bool
  | .target _ _ _ fs => FilterList.ok { slots := earlier } fs
  | .mode _ => true
  | .xValue => true
  | .extraCost cs _ => cs.all (AbilityCost.ok {})

/-- Every choice of a list refers only to what is there: a choice may name the targets chosen
before it (`slot i`). `earlier` is the number of targets chosen before the list. -/
def Choice.allOk (earlier : Nat) : List Choice → Bool
  | [] => true
  | c :: cs =>
    Choice.ok earlier c && Choice.allOk (earlier + (if c.isTarget then 1 else 0)) cs

/-- The number of the mode choice, if the declaration has one. -/
def Choice.modeCount : Choice → Option Nat
  | .mode n => some n
  | _ => none

/-- What the body of an effect may refer to, given the choices declared for it. -/
def EffectDef.ctx (base : Ctx) (d : EffectDef) : Ctx :=
  { base with
    slots := (d.choices.filter Choice.isTarget).length + base.slots,
    playerSlots := if d.playerTarget.isSome then base.playerSlots + 1 else base.playerSlots,
    hasX := d.choices.any (· == .xValue),
    modes := (d.choices.filterMap Choice.modeCount).head? }

/-- An effect with its choices refers only to what is there. -/
def EffectDef.ok (base : Ctx) (d : EffectDef) : Bool :=
  let d := { d with choices := d.choices ++ d.showOffChoices }
  let ctx := d.ctx base
  Choice.allOk 0 d.choices && Effect.ok ctx d.body &&
    (d.moveChoice.all (fun move => decide (move.slot < ctx.slots) && FilterList.ok ctx move.filters)) &&
    d.modes.all (fun mode =>
      let branch : EffectDef :=
        { choices := mode.choices ++ d.showOffChoices, body := mode.body, playerTarget := d.playerTarget }
      let context := branch.ctx base
      Choice.allOk 0 branch.choices && Effect.ok context branch.body &&
        mode.moveChoice.all (fun move =>
          decide (move.slot < context.slots) && FilterList.ok context move.filters))

/-- An ability refers only to what is there. -/
def Ability.ok : Ability → Bool
  | .passive cond mods => Condition.ok {} cond && mods.all (StaticMod.ok {})
  | .replacement event cond instead =>
    let ctx : Ctx := { eventOk := true, slots := if event == .attach then 1 else 0 }
    Condition.ok ctx cond && instead.ok ctx
  | .activated costs _ body _ => costs.all (AbilityCost.ok {}) && body.ok {}
  | .triggered t body _ =>
    -- an ability that watches another object gets it as the slot after its own choices
    Trigger.ok { itOk := true } t &&
      body.ok { itOk := true, slots := t.watched, eventAmountOk := t.event == .linkedBurnUnit }

/-- A chosen object is found exactly when its slot was declared. -/
theorem Selector.ok_slot (c : Ctx) (i : Nat) : Selector.ok c (.slot i) = true ↔ i < c.slots := by
  simp [Selector.ok]

/-- A variable is found exactly when it was bound, or it is the one that names the object chosen
while the effect resolves. -/
theorem Amount.ok_var (c : Ctx) (v : VarId) :
    Amount.ok c (.var v) = true ↔ v ∈ c.vars ∨ v = pickVar := by
  simp [Amount.ok]

/-- A bound variable can be used in the effect it is bound for, and in nothing else. -/
theorem Effect.ok_bind (c : Ctx) (v : VarId) (a : Amount) (e : Effect) :
    Effect.ok c (.bind v a e) = (Amount.ok c a && Effect.ok { c with vars := v :: c.vars } e) := by
  simp [Effect.ok]

/-- Inside an effect with choices, a slot is valid exactly when it is below the number of targets
declared (CR 355), and the slots the base has already (the object an ability watches). -/
theorem EffectDef.slot_ok_iff (base : Ctx) (d : EffectDef) (i : Nat) :
    Selector.ok (d.ctx base) (.slot i) = true ↔
      i < (d.choices.filter Choice.isTarget).length + base.slots := by
  simp [EffectDef.ctx, Selector.ok]

/-- The empty effect refers to nothing. -/
theorem Effect.ok_nop (c : Ctx) : Effect.ok c .nop = true := rfl

end Riftbound

end
