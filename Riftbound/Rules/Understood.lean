module

public import Riftbound.Rules.Effects
public import Riftbound.Rules.Chain
public import Riftbound.Rules.Mana

/-!
# What the interpreter understands

A static question about an effect: is it written entirely in the part of the IR that the
interpreter (`runEffect`) gives a meaning to? These functions mirror the arms of `runEffect`,
`Selector.eval`, `Amount.evalS`, `Condition.eval` and `Filter.holds`, so that the tests can count
the cards that run (roadmap.md, M4d) and the gaps are listed by name.

An effect that is understood can still be skipped at run time, for example when a selector names
an object that is not there; "understood" says that nothing in it is a construct the interpreter
does not know.
-/

@[expose] public section

namespace Riftbound

/-- The places that are understood. -/
def Place.understood : Place → Bool
  | .anywhere => true
  | .boardOrLegend => true
  | .atBase => true
  | .atBattlefield => true
  | .here => true
  | .inCombat => true
  | .onChain => true
  | .onChainAll => true
  | _ => false

/-- The players an effect names that are understood. -/
def PlayerSel.understood : PlayerSel → Bool
  | .you => true
  | .opponent => true
  | .eachPlayer => true
  | .eachPlayerFromNext => true
  | .eachOpponent => true
  | .combatSides => true
  | .chosen _ => true
  | .controllerOf _ => true
  | .ownerOf _ => true
  | _ => false

mutual

/-- An amount that is understood. -/
def Amount.understood : Amount → Bool
  | .const _ => true
  | .var _ => true
  | .eventAmount => true
  | .shownOffMight | .shownOffPower => true
  | .count (.pick .all _ place fs) =>
    (place.understood || place.zoneKind?.isSome) && FilterList.understood fs
  | .count s => Selector.understood s
  | .handSize p => p.understood
  | .xp => true
  | .turnsTaken p => p.understood
  | .points p => p.understood
  | .victoryScore => true
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
  | .costOf s => s.understood
  | .powerCostOf s => s.understood
  | .add a b => Amount.understood a && Amount.understood b
  | .sub a b => Amount.understood a && Amount.understood b
  | .mul a b => Amount.understood a && Amount.understood b
  | .min a b => Amount.understood a && Amount.understood b
  | .max a b => Amount.understood a && Amount.understood b
  | .mightOf s => Selector.understood s
  | .mightIncreaseTo unit reference => unit.understood && reference.understood
  | .damageOn s => Selector.understood s
  | .kwAmount s _ => Selector.understood s
  | _ => false

/-- An amount that is understood in a condition: the Might of objects is not (conditions read the
Might without the Layers, which they do not need yet). -/
def Amount.understoodC : Amount → Bool
  | .const _ => true
  | .var _ => true
  | .eventAmount => true
  | .shownOffMight | .shownOffPower => true
  | .count (.pick .all _ place fs) =>
    (place.understood || place.zoneKind?.isSome) && FilterList.understood fs
  | .count s => Selector.understood s
  | .handSize p => p.understood
  | .xp => true
  | .turnsTaken p => p.understood
  | .points p => p.understood
  | .victoryScore => true
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
  | .costOf s => s.understood
  | .powerCostOf s => s.understood
  | .mightOf s => Selector.understood s
  | .damageOn s => Selector.understood s
  | .add a b => Amount.understoodC a && Amount.understoodC b
  | .sub a b => Amount.understoodC a && Amount.understoodC b
  | .mul a b => Amount.understoodC a && Amount.understoodC b
  | .min a b => Amount.understoodC a && Amount.understoodC b
  | .max a b => Amount.understoodC a && Amount.understoodC b
  | _ => false

/-- An amount that is understood in the cost of a card: the highest Might is read as the cost is
worked out. -/
def Amount.understoodK : Amount → Bool
  | .highestMight s => s.understood
  | .kwAmount s _ => s.understood
  | a => a.understoodC

/-- A filter that is understood. -/
def Filter.understood : Filter → Bool
  | .physicalCard => true
  | .ofType _ => true
  | .ofSupertype _ => true
  | .tag _ => true
  | .named _ => true
  | .sameNameAsSource => true
  | .hasKeyword _ => true
  | .domain _ => true
  | .might _ a => Amount.understood a
  | .cost _ a => Amount.understood a
  | .powerCost _ a => Amount.understood a
  | .exhausted => true
  | .ready => true
  | .damaged => true
  | .damagedThisTurn => true
  | .notSelf => true
  | .stunned => true
  | .buffed => true
  | .not f => Filter.understood f
  | .either a b => Filter.understood a && Filter.understood b
  | .both a b => Filter.understood a && Filter.understood b
  | .controlled => true
  | .controlledByOpponent => true
  | .unitsHere _ _ => true
  | .movedFromHere | .movedThisTurn | .notedOn _ => true
  | .hidden => true
  | .top _ | .lookedAt => true
  | .openBf => true
  | .scoredByMine => true
  | .conqueredByMine => true
  | .sameController .self => true
  | .sameController (.slot _) => true
  | .sameController (.var _) => true
  | .ownedByPlayerTarget _ => true
  | .revealedByEffect => true
  | .givesLegendsAttach => true
  | .copiesText => true
  | .takenByMyCard => true
  | .wasTakenByMyCard => true
  | .banishedWithMe => true
  | .playedFromElsewhere => true
  | .playedThisTurn => true
  | .playedLast => true
  | .inHandZone => true
  | .inTrashZone => true
  | .empowered => true
  | .unitsPlayable => true
  | .attackedByMine => true
  | .myUnitsHere => true
  | .enemyAlone => true
  | .enemyOccupied => true
  | .sameAs .self => true
  | .sameAs (.slot _) => true
  | .sameAs (.slotsFrom _) => true
  | .sameAs (.var _) => true
  | .mighty => true
  | .attacker => true
  | .defender => true
  | .alone => true
  | .isAttached => true
  | .attached => true
  | .token => true
  | .choosesMine => true
  | .sharesGainedTag => true
  | .xpAtLeast _ => true
  | .mightLtOf .self => true
  | .mightLtOf (.slot _) => true
  | .mightLtOf (.var _) => true
  | .choosesOnly .self => true
  | .choosesOnly (.slot _) => true
  | .choosesOnly (.var _) => true
  | .fromBattlefield => true
  | .attachedTo .self => true
  | .attachedTo (.slot _) => true
  | .attachedTo (.var _) => true
  | .onBattlefield => true
  | .atEventBattlefield _ | .inTriggerGroup _ => true
  | .atShowdown => true
  | .combatsEnemyOfDomain _ | .chosenByEnemySpellOfDomain _ => true
  | .noChoices => true
  | .costBelowPoints => true
  | .hideRoom => true
  | .permitsOpenPlay => true
  | .lethal => true
  | .at_ .self => true
  | .at_ .it => true
  | .at_ (.slot _) => true
  | .at_ (.var _) => true
  | _ => false

/-- Every filter of a list is understood. -/
def FilterList.understood : FilterList → Bool
  | .nil => true
  | .cons f rest => Filter.understood f && FilterList.understood rest

/-- A selector that is understood. -/
def Selector.understood : Selector → Bool
  | .self => true
  | .slot _ => true
  | .it => true
  | .var _ => true
  | .pick .all _ place fs => place.understood && FilterList.understood fs
  | .locationOf sel => Selector.understood sel
  | .slotsFrom _ | .revealedDeck _ | .eventObjects => true
  | _ => false

end

/-- A condition that is understood. -/
def Condition.understood : Condition → Bool
  | .always => true
  | .not c => Condition.understood c
  | .and a b => Condition.understood a && Condition.understood b
  | .or a b => Condition.understood a && Condition.understood b
  | .cmp _ a b => a.understoodC && b.understoodC
  | .exists s => s.understood
  | .matches s f => s.understood && f.understood
  | .yourTurn => true
  | .inCombat => true
  | .inCombatHere => true
  | .legendReady => true
  | .openConquered => true
  | .legion => true
  | .paid => true
  | .discardPaid => true
  | .showedOff => true
  | .playedAnother => true
  | .finalizedType _ => true
  | .opponentFinalizedOtherSpell s | .firstResolvedType _ s => s.understood
  | .empowered s => s.understood
  | .leftEmpowered => true
  | .fewerRunesThanOpponent | .canPay _ => true
  | .enemyUnitDied => true
  | .marked _ => true
  | .fromHidden => true
  | .excessAtLeast _ => true
  | .noted _ | .friendlyNoted _ => true
  | .hidesWithEnergy => true
  | .hasFriendlyCard _ => true
  | .diedWith _ => true
  | .discardedThisTurn => true
  | .hasHidden | .hasHiddenHere => true
  | .spentOnSpell _ => true
  | .beginningPhase => true
  | .inShowdown => true
  | .showdownNow => true
  | .drewCards _ => true
  | .iControlHere => true
  | _ => false

/-- A selector of a primitive that returns objects to a hand: it may name one object to choose
while the effect resolves (`runEffect` asks the player), also a card off the board. -/
def Selector.understoodPickAny : Selector → Bool
  | .pick .one _ place fs =>
    (place.understood || place.zoneKind?.isSome) && FilterList.understood fs
  | s => s.understood

/-- A selector of a primitive that names one object to choose while the effect resolves, on the
board. -/
def Selector.understoodPick : Selector → Bool
  | .pick .one _ place fs => place.understood && FilterList.understood fs
  | s => s.understood

/-- A game action that is understood. -/
def Prim.understood : Prim → Bool
  | .draw p n => p.understood && n.understood
  | .drawLooked s => s.understoodPickAny
  | .burn p n => p.understood && n.understood
  | .burnWithUnitTrigger n _ => n.understood
  | .empower s => s.understoodPickAny
  | .disempower s => s.understoodPickAny
  | .score p n => p.understood && n.understood
  | .win p => p.understood
  | .turnEffect _ => true
  | .playFirst fs => FilterList.understood fs
  | .markOn s _ => s.understood
  | .delayUntilDeath s _ => s.understood
  | .activateConquer s => s.understood
  | .choose s => s.understood
  | .lookTop _ => true
  | .predict n => n.understood
  | .extraTurn ps => ps.understood
  | .swapPlaces a b => a.understood && b.understood
  | .returnChampion => true
  | .pay _ => true
  | .addEnergy ps n none | .addUnitEnergy ps n | .addSpellEnergy ps n => ps.understood && n.understoodC
  | .addPower ps n (some _) none => ps.understood && n.understoodC
  | .addPower ps n none none => ps.understood && n.understoodC
  | .recycleTop p => p.understood
  | .swapTop p => p.understood
  | .play s | .playAtBase s => s.understoodPickAny
  | .banishReplay s _ => s.understoodPickAny
  | .copyAttachedFrom s => s.understoodPick
  | .playPaying s => s.understoodPickAny
  | .giveKeywords t f => t.understood && f.understood
  | .playReduced s a t => s.understoodPickAny && a.understood && (match t with
    | some b => b.understood
    | none => true)
  | .castInline s => s.understoodPickAny
  | .counter s => s.understood
  | .counterToHand s => s.understood
  | .hideAt s b => s.understood && b.understood
  | .playTo s b => s.understoodPickAny && b.understood
  | .bin s => s.understoodPickAny
  | .discardCard s | .discardWithTypeTriggers s _ => s.understoodPickAny
  | .recycle s => s.understoodPickAny
  | .reveal s => s.understoodPickAny
  | .revealTop _ => true
  | .revealTopNow _ => true
  | .revealNow s => s.understoodPickAny
  | .spendBuff s => s.understoodPick
  | .takeControl s => s.understood
  | .playBanishedWith => true
  | .returnControl s => s.understood
  | .takeControlUntilLeaves s => s.understood
  | .recall s _ => s.understood
  | .discard p n => p.understood && n.understood
  | .channel p n m => p.understood && n.understood && m.understood
  | .deal s n => s.understoodPick && n.understood
  | .exchangeDamage a b => a.understood && b.understood
  | .setBaseMight s n => s.understoodPick && n.understood
  | .heal s n => s.understoodPick && n.understood
  | .kill s => s.understoodPick
  | .banish s => s.understoodPickAny
  | .returnToHand s => s.understoodPickAny
  | .ready s => s.understoodPickAny
  | .exhaust s => s.understoodPickAny
  | .create _ n pl _ => n.understood && (pl == .atBase || pl == .here)
  | .createAt _ n bf _ => n.understood && bf.understoodPick
  | .playUnitToken _ | .playUnitTokenAt _ _ => true
  | .attach g t => g.understood && t.understood
  | .attachPaying g t _ => g.understood && t.understood
  | .detach s => s.understoodPick
  | .topdeck s => s.understoodPickAny
  | .double s | .grantActivation s _ => s.understoodPick
  | .move s .base => s.understoodPick
  | .move s (.at_ d) =>
    -- one object is chosen while the effect resolves: the moved one or the destination, not both
    s.understoodPick && (match s with | .pick .one .. => d.understood | _ => d.understoodPick)
  | .stun s => s.understoodPick
  | .buff s => s.understoodPick
  | .gainXP p n => p.understood && n.understood
  | .becomeCopy s src => s.understood && src.understood
  | .addBattlefield _ => true
  | .createAtPrev _ n _ => n.understood
  | .cloneToken s => s.understood
  | .banishWith s => s.understoodPickAny
  | .gainTag s _ => s.understood
  | .replaceBattlefield s _ => s.understoodPick
  | .restoreBattlefield s => s.understood
  | .moveAll _ place fs dest _ =>
    place.zoneKind?.isSome && dest.zoneKind?.isSome && FilterList.understood fs
  | .spendXP p n => p.understood && n.understood
  | _ => false

mutual

/-- An effect that is understood. -/
def Effect.understood : Effect → Bool
  | .nop | .animateGear | .addReservedLegend => true
  | .playUnitTokensThen _ n place _ _ target =>
    decide (n > 0) && (place == .atBase || place == .here) && target.all Selector.understood
  | .addReservedLegendPicked | .addReservedLegendChosen _ => false
  | .seq es => EffectList.understood es
  | .ifThen c t e => c.understood && Effect.understood t && Effect.understood e
  | .forEach s body => s.understood && Effect.understood body
  | .fillSlot _ s => s.understoodPickAny
  | .remakeSpellChoices spell => spell.understood
  | .splitDamage targets _ => targets.understood
  | .fillFromPick _ => true
  | .repeatN n e => n.understood && Effect.understood e
  | .bind _ a e => a.understood && Effect.understood e
  | .prim p => p.understood
  | .may e => Effect.understood e
  | .doThen (.prim (.banish s)) e | .doThen (.prim (.disempower s)) e
  | .doThen (.prim (.spendBuff s)) e | .doThen (.prim (.exhaust s)) e =>
    s.understoodPickAny && Effect.understood e
  | .equipWithCost gear recipient _ => gear.understood && recipient.understood
  | .eitherOf es => EffectList.understood es
  | .payThen _ body _ => Effect.understood body
  | .eachPlayer w e => w.understood && Effect.understood e
  | .revealHand w e | .revealDeckTops w e => w.understood && Effect.understood e
  | .killThenAtEnd targets _ => targets.understood
  | .killThenForController _ body | .killThenIfKilled _ body => Effect.understood body
  | .lookAtTop _ body => Effect.understood body
  | .guessCardType who unit gear spell =>
    who.understood && unit.understood && gear.understood && spell.understood
  | .nameCard _ | .rememberNamedCard _ => true
  | .banishAndPlayLooked _ fs => FilterList.understood fs
  | .recycleLooked | .recycleRunes | .banishTopForPlay | .playSelfFromTrash .. |
      .banishAndReplayGroup => true
  | .banishAndPlayCard sel _ => sel.understood
  | .playCard sel _ _ | .mayPlayCard sel _ | .mayPlayPermanents sel _ _ => sel.understoodPickAny
  | .chooseObject _ place fs e =>
    (place.understood || place.zoneKind?.isSome) && FilterList.understood fs && Effect.understood e
  | .pickOwn place fs e => place.understood && FilterList.understood fs && Effect.understood e
  | .preventNext s n .thisTurn => s.understoodPick && n.understood
  | .moveChoosing _ _ fs e _ => FilterList.understood fs && Effect.understood e
  | .forceMoveToBattlefield who destination => who.understood && destination.understood
  | .grantNumericKeyword objects _ amount duration =>
    objects.understoodPick && amount.understood && duration.endPoint?.isSome
  | .grant s (.mightPlus .it a) d =>
    s.understoodPick && a.understood && d.endPoint?.isSome
  | .grant s (.mightMinus .it a) d =>
    s.understoodPick && a.understood && d.endPoint?.isSome
  | .grant s (.mightMinusMin .it a _) d =>
    s.understoodPick && a.understood && d.endPoint?.isSome
  | .grant s (.keyword .it _) d => s.understoodPick && d.endPoint?.isSome
  | .grant s .flowAtBaseCost d => s.understoodPick && d.endPoint?.isSome
  | _ => false

/-- Every effect of a list is understood. -/
def EffectList.understood : EffectList → Bool
  | .nil => true
  | .cons e rest => Effect.understood e && EffectList.understood rest

end

/-- All modes or the single effect can be played and interpreted. -/
def EffectDef.choicesRun (e : EffectDef) : Bool :=
  e.showOffChoices.all Choice.simple && if e.modes.isEmpty then
    e.choices.all Choice.simple && e.body.understood &&
      e.moveChoice.all (fun move => FilterList.understood move.filters)
  else e.modes.all (fun mode =>
    mode.choices.all Choice.simple && mode.body.understood &&
      mode.moveChoice.all (fun move => FilterList.understood move.filters))

/-- A Spell whose choices and effects can be played and interpreted. -/
def CardDef.spellRuns (c : CardDef) : Bool :=
  match c.spellEffect with
  | some e => e.choicesRun
  | none => false

/-! ### What a card does when it is played

The checks below say which cards do everything their text says in this model: every ability is one
the engine carries out, and every keyword is one it knows. They are the measure of "the card works"
(docs/coverage.md); a card whose text is written down but not run is not counted. -/

/-- A selector of the cards a cost change names that the engine reads: the card itself, or the cards
of a side with properties, wherever they are (the card is in the hand when it is played). -/
def costSel : Selector → Bool
  | .self => true
  | .pick .all _ .anywhere fs => FilterList.understood fs
  | _ => false

/-- A passive change the engine applies. -/
def StaticMod.runs : StaticMod → Bool
  | .mightPlus s a | .mightPlusWithKeyword s _ a => s.understood && a.understoodC
  | .mightMinus s a => s.understood && a.understoodC
  | .mightMinusMin s a _ => s.understood && a.understoodC
  | .keyword s _ => s.understood
  | .entersReady sel => costSel sel
  | .costMinus s a => costSel s && a.understoodK
  | .costMinusMin s a _ => costSel s && a.understoodK
  | .costPlus s a => costSel s && a.understoodK
  | .costPower s a _ _ => costSel s && a.understoodK
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
  | .assaultCount s => s.understood
  | .legendsAttach => true
  | .chosenSpellsCostLess _ => true
  | .friendlyTargetPowerCut _ | .showdownReactionTax _ => true
  | .lookBeforeReveal => true
  | .banishOnDeath => true
  | .copiesUnitText => true
  | .extraCostLess _ => true
  | .repeatCostLess _ => true
  | .firstGearAbilityLess _ | .firstPermanentHereLess _ | .empowerHereLess _ |
      .gearPlayDiscount .. | .spellExhaustDiscount .. => true
  | .equipEach _ => true
  | .manaExtraEnergy s n => costSel s && n.understoodK
  | .diesInsteadGear | .diesInsteadOfFriendly | .sacrificeToSaveSelf => true
  | .rescueWeakerHere | .replaceUnitTokenWith _ | .duplicateUnitTokenOnce => true
  | .noMoveToBaseAny => true
  | .moveFeeHere _ => true
  | .playToBf fs => FilterList.understood (FilterList.ofList fs)
  | .playToBfAll fs => FilterList.understood (FilterList.ofList fs)
  | .playHereFor _ _ => true
  | .noPlayToBase => true
  | .noReadyOfOpps => true
  | .ignoreKeyword .temporary .here | .ignoreKeyword .tank .here => true
  | .noHiddenReveal => true
  | .triggersExtra .die .anywhere => true
  | .triggersExtra .deathknell .here => true
  | .triggersExtra .conquer .here => true
  | .triggersExtra .hold .here => true
  | .cant .self .beChosen => true
  | .cant .self .play => true
  | .cant (.pick .all _ place fs) .beChosen => place.understood && FilterList.understood fs
  | .noCombatDamageFor (.pick .all _ place fs) => place.understood && FilterList.understood fs
  | .cantPlayer _ .score .here _ => true
  | .cantPlayer _ .score .anywhere _ => true
  | .cantPlayer _ .play .here _ => true
  | .earlyScoreDraw _ => true
  | .bonusDamageHere _ => true
  | .victoryScorePlus a => a.understoodC
  | .victoryScoreMinus a => a.understoodC
  | .bonusDamage a | .bonusAbilityDamage _ a => a.understoodC
  | .noCombatDamage => true
  | .channelLimit _ => true
  | .uncounterable | .controlledItemsUncounterable | .friendlyExhaustAbilities
  | .targetMightPenalty _ | .chosenHarmToMight _ => true
  | .ignoreDeflectSpell => true
  | .ignoreDeflectHere => true
  | .doubleEquip => true
  | .mightIfFresh _ => true
  | .gainsTag _ => true
  | .keywordHere _ => true
  | .holdIsConquer => true
  | _ => false

/-- The points of the turn that fire a triggered ability. -/
def Timing.runs : Timing → Bool
  | .startOfTurn => true
  | .beginning => true
  | .startOfMain => true
  | .endOfTurn => true
  | _ => false

/-- A trigger the engine detects: the event, whose subject it is about, and the condition. -/
def Trigger.runs (t : Trigger) : Bool :=
  (t.occurrence == .every || (t.occurrence == .deathGroup && t.event == .die &&
    t.subject != .self)) && t.condition.understood &&
    (match t.cost with
     | .killFriendly _ fs => FilterList.understood fs
     | _ => true) &&
    (match t.event with
      | .play => true | .die => true | .move => true | .attack => true | .defend => true
      | .friendlyAttackGroupHere => t.subject == .self
      | .firstUnitDeathHere => t.subject != .self
      | .deathknell => t.subject == .self
      | .firstCardResolved | .firstPermanentHere | .delayedPlay | .delayedEnd => t.subject == .self
      | .stun => true | .discard => true | .ready => true | .exhaust => true
      | .youExhaustUnits minimum => t.subject == .self && decide (0 < minimum)
      | .buff => true
      | .becomeMighty | .mightAtLeast _ => true
      | .mightReducedByYou => t.subject != .self
      | .linkedBurnUnit | .linkedDiscardType | .linkedUnitTokens _ => t.subject == .self
      | .becomeEmpowered => true
      | .winCombat => t.subject == .self
      | .combatStart => t.subject == .self
      | .combatEnd => t.subject == .self
      | .chosen => true
      | .chosenAny => true
      | .useGearAbility | .playAtBaseEnergy _ => t.subject == .self
      | .attachedTo => t.subject == .self
      | .youDefend => t.subject == .self
      | .spendBuff => t.subject == .self
      | .playHidden => t.subject == .self
      | .conquerFromTrash | .playCardFromTrashAtEnergy _ => t.subject == .self
      | .killBySpell => t.subject == .self
      | .chosenHere => t.subject == .self
      | .seenOnTop => t.subject == .self
      | .recycle => t.subject == .self
      | .recycleRune => t.subject == .self
      | .hide => t.subject == .self
      | .opponentScores => t.subject == .self
      | .opponentHolds | .opponentHoldsHere => t.subject == .self
      | .movedByYou => true
      | .draw => true
      | .drawGroupWithHand _ => t.subject == .self
      | .banishOwn => t.subject == .self
      | .leave => true
      | .revealedFromDeck => true
      | .playToken => true
      | .scored => t.subject == .self
      | .conquer => t.subject == .self | .hold => t.subject == .self
      | .youConquer => t.subject == .self | .youHold => t.subject == .self
      | .at_ tm => tm.runs && t.subject == .self
      | _ => false) &&
    (t.subject == .self ||
      (match t.subject with
        | .pick .all _ .anywhere fs => FilterList.understood fs
        | _ => false))

/-- The guard of an Add is a condition that is understood (`guardOk` lets what it cannot answer
pass). -/
def manaGuardUnderstood (body : EffectDef) : Bool :=
  match body.body with
  | .ifThen c _ .nop => c.understood
  | _ => true

/-- An ability the engine carries out. -/
def Ability.runs : Ability → Bool
  | .passive c mods => c.understood && mods.all StaticMod.runs &&
      (c == .always || !mods.contains .grantFriendlyLegendsActivations)
  | .activated costs _ body _ =>
    (body.playerTarget.isNone || (manaKind body).isNone) && ((costs.all (fun
      | .energyDiscount c a => c.understood && a.understoodK
      | .exhaustFriendly filters | .killFriendlyPermanent filters =>
        FilterList.understood filters && (manaKind body).isNone
      | _ => true) && (costPlan costs).isSome &&
      ((discardCost costs).all fun (_, fs) => FilterList.understood fs && (manaKind body).isNone) &&
      (((manaKind body).isSome && manaGuardUnderstood body) ||
        (body.choices.all Choice.simple && body.body.understood))) ||
    -- Some Adds pay another non-resource cost, such as killing their source or banishing a card.
    ((manaPlan costs).any (fun plan => plan.banish.all FilterList.understood) &&
      (manaKind body).isSome && manaGuardUnderstood body))
  | .triggered t body _ =>
    t.runs && body.moveChoice.isNone && body.modes.all (·.moveChoice.isNone) && body.choicesRun
  | .replacement .attach c body =>
    c.understood && body.choices.isEmpty && body.playerTarget.isNone && body.moveChoice.isNone &&
      body.modes.isEmpty && body.choicesRun
  | .replacement .. => false

/-- A keyword the engine knows. -/
def Keyword.runs : Keyword → Bool
  | .reaction => true | .action => true | .assault => true | .shield => true | .ganking => true
  | .tank => true | .temporary => true | .legion => true | .deflect => true
  | .deathknell => true | .hunt => true | .level => true | .equip => true
  | .accelerate => true | .vision => true | .hidden => true
  | .repeat_ => true | .unique => true | .quickDraw => true | .weaponmaster => true
  | .backline => true | .ambush => true | .deploy => true | .disarm => true
  | _ => false

/-- A card can model the printed Empower cost with an explicit activated ability (CR 827). -/
def CardDef.hasEmpowerAbility (c : CardDef) : Bool :=
  c.fullAbilities.any (fun a => a.isEmpower && a.runs)

/-- The card does everything its text says: it is written down, its abilities and its Spell are
carried out, and its keywords are known. -/
def CardDef.runs (c : CardDef) : Bool :=
  (c.status == .drafted || c.status == .full) &&
    c.abilities.all Ability.runs && c.grants.all Ability.runs &&
    c.keywords.all (fun k => k.keyword.runs || (k.keyword == .flow && c.types == [.spell] && k.flowCost?.isSome) ||
      (k.keyword == .empower && c.hasEmpowerAbility) ||
      (k.keyword == .showOff && c.showOffRequirement.any (·.filters.understood))) &&
    (match c.spellEffect with
      | some _ => c.spellRuns
      | none => !c.types.contains .spell)

end Riftbound

end
