module

public import Riftbound.Invariant.DamageWork
public import Riftbound.Invariant.RecyclePaymentWork
public import Riftbound.Invariant.DisclosureWork

/-!
# Checking Run programs for termination (I12)

The check follows the programs generated for the current resolution. Each accepted instruction
has a proof for the observed dispatcher, including any earlier player decision.
-/

@[expose] public section

namespace Riftbound

/-- Record the chosen player whose Banish replaces a death, then resume the effect. -/
theorem Effect.ObservedFinite.chooseDeathBanisher (unit : ObjId) (banisher : PlayerId) :
    (Effect.chooseDeathBanisher unit banisher).ObservedFinite :=
  Effect.SingleRun.observed (fun s _ _ _ _ =>
    ⟨s.addTurnFxOn banisher unit .chosenDeathBanisher, [], rfl⟩)

/-- Record the chosen Gear that saves the Unit. -/
theorem Effect.ObservedFinite.chooseDeathGear (unit gear : ObjId) :
    (Effect.chooseDeathGear unit gear).ObservedFinite :=
  Effect.SingleRun.observed (fun s p _ _ _ =>
    ⟨s.addTurnFxOn p unit (.chosenDeathGear gear), [], rfl⟩)

/-- Record the chosen free death replacement. -/
theorem Effect.ObservedFinite.chooseDeathFree (unit : ObjId) (source : Option ObjId) :
    (Effect.chooseDeathFree unit source).ObservedFinite :=
  Effect.SingleRun.observed (fun s p _ _ _ =>
    ⟨s.addTurnFxOn p unit (.chosenDeathFree source), [], rfl⟩)

/-- Record whether the selected sacrifice replaces the death. -/
theorem Effect.ObservedFinite.recordDeathSacrifice (unit : ObjId) (cost : Option ObjId) :
    (Effect.recordDeathSacrifice unit cost).ObservedFinite :=
  Effect.SingleRun.observed (fun s p _ _ _ =>
    ⟨s.addTurnFxOn p unit (.deathSacrificeChoice cost), [], rfl⟩)

/-- Record which Unit will be handled first in a group of deaths. -/
theorem Effect.ObservedFinite.recordDeathOrder (group : List ObjId) (unit : ObjId) :
    (Effect.recordDeathOrder group unit).ObservedFinite :=
  Effect.SingleRun.observed (fun s p _ _ _ => ⟨s.addTurnFxOn p unit (.deathOrder group), [], rfl⟩)

/-- Record a replacement chosen after an earlier death in the same group. -/
theorem Effect.ObservedFinite.recordDeathReselection (group earlier : List ObjId) (unit : ObjId)
    (choice : DeathDecision) : (Effect.recordDeathReselection group earlier unit choice).ObservedFinite :=
  Effect.SingleRun.observed (fun s p _ _ _ =>
    ⟨s.addTurnFxOn p unit (.deathReselection group earlier choice), [], rfl⟩)

/-- Record the choice made during the Kill required by another replacement. -/
theorem Effect.ObservedFinite.recordNestedDeathDecision (root : ObjId) (used : List (ObjId × Bool))
    (unit : ObjId) (choice : DeathDecision) (groupScope : Option (List ObjId × List ObjId)) :
    (Effect.recordNestedDeathDecision root used unit choice groupScope).ObservedFinite :=
  Effect.SingleRun.observed (fun s p _ _ _ =>
    ⟨s.addTurnFxOn p unit (.nestedDeathDecision root used choice groupScope), [], rfl⟩)

mutual

/-- Check the effect constructors for which the observed dispatcher has a termination proof. -/
def Effect.observedWorkSupported : Effect → Bool
  | .nop | .retainTargetSet _ | .prim (.gainXP ..) | .prim (.draw ..) | .prim (.discard ..)
  | .prim (.allowFacedownInspection _)
  | .prim (.recycle .self) | .prim (.recycle (.slot _)) | .may _ | .chooseObject ..
  | .prim (.lookTop _) | .prim (.recycleTop _) | .prim (.predict _)
  | .prim (.drawLooked (.revealedDeck _)) | .prim (.recycle (.revealedDeck _))
  | .nameCard _ | .rememberNamedCard _ | .guessCardType ..
  | .prim (.deal ..) | .prim (.exchangeDamage ..) | .prim (.markOn ..) | .grant ..
  | .splitDamage .. | .splitUnitDamage .. | .applySplitDamage .. | .applyUnitSplitDamage ..
  | .resolveEffectDamage .. | .chooseDamageReplacement .. | .orderCombatDamage .. | .endCombatDamage ..
  | .chooseDeathBanisher .. | .chooseDeathGear .. | .chooseDeathFree ..
  | .recordDeathSacrifice .. | .recordDeathOrder .. | .recordDeathReselection ..
  | .recordNestedDeathDecision .. | .orderRuneRecycle .. | .recordRuneRecycle ..
  | .finishTrashRecycle .. | .recycleTrashTargets .. | .recycleFromTrash ..
  | .chooseTrashRecycle .. | .recordTrashRecycle .. | .completeActivation .. => true
  | .seq program => program.observedWorkSupported
  | .eitherOf (.cons only .nil) => only.observedWorkSupported
  | .eitherOf _ => true
  | .ifThen _ yes no => yes.observedWorkSupported && no.observedWorkSupported
  | .lookAtTop _ body | .revealHand _ body | .revealDeckTops _ body => body.observedWorkSupported
  | .repeatN _ body | .bind _ _ body | .forEach _ body | .eachPlayer _ body => body.observedWorkSupported
  | .prim primitive => (Effect.prim primitive).isTriggerAdd
  | _ => false
termination_by structural effect => effect

/-- Check each instruction in a program individually. -/
def EffectList.observedWorkSupported : EffectList → Bool
  | .nil => true
  | .cons head tail => head.observedWorkSupported && tail.observedWorkSupported
termination_by structural program => program

end

private theorem Effect.ObservedFinite.addPrimitive (pr : Prim)
    (supported : (Effect.prim pr).isTriggerAdd = true) : (Effect.prim pr).ObservedFinite := by
  apply Effect.SingleRun.observed
  intro s p src env more
  rw [runEffect_triggerAdd_prim s p src env pr more supported]
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

mutual

/-- A supported instruction is finite through the real observer. -/
theorem Effect.observedFinite_of_supported (effect : Effect) (supported : effect.observedWorkSupported = true) :
    effect.ObservedFinite := by
  cases effect <;> try (simp [Effect.observedWorkSupported] at supported; done)
  case nop => exact Effect.SingleRun.nop.observed
  case prim pr =>
    cases pr <;> try (simp [Effect.observedWorkSupported, Effect.isTriggerAdd] at supported; done)
    case lookTop count => exact (Effect.SingleRun.lookTop count).observed
    case recycleTop who => exact (Effect.SingleRun.recycleTop who).observed
    case predict amount => exact Effect.ObservedFinite.predict amount
    case gainXP who amount => exact (Effect.SingleRun.gainXP who amount).observed
    case allowFacedownInspection whose => exact (Effect.SingleRun.allowFacedownInspection whose).observed
    case deal target amount => exact Effect.ObservedFinite.deal target amount
    case exchangeDamage a b => exact Effect.ObservedFinite.exchangeDamage a b
    case markOn target note => exact Effect.ObservedFinite.markOn target note
    case draw who amount => exact Effect.ObservedFinite.draw who amount
    case discard who amount => exact Effect.ObservedFinite.discard who amount
    case drawLooked selector =>
      cases selector <;> try (simp [Effect.observedWorkSupported, Effect.isTriggerAdd] at supported; done)
      exact (Effect.SingleRun.drawRevealed _).observed
    case recycle selector =>
      cases selector <;> try (simp [Effect.observedWorkSupported, Effect.isTriggerAdd] at supported; done)
      case self => exact Effect.SingleRun.recycleSelf.observed
      case slot => exact (Effect.SingleRun.recycleSlot _).observed
      case revealedDeck => exact (Effect.SingleRun.recycleRevealed _).observed
    all_goals apply Effect.ObservedFinite.addPrimitive <;> exact supported
  case nameCard kind => exact .nameCard kind
  case rememberNamedCard card => exact .rememberNamedCard card
  case guessCardType who unit gear spell => exact .guessCardType who unit gear spell
  case lookAtTop count body => exact .lookAtTop count (body.observedFinite_of_supported supported)
  case revealHand who body => exact .revealHand who (body.observedFinite_of_supported supported)
  case revealDeckTops who body => exact .revealDeckTops who (body.observedFinite_of_supported supported)
  case seq program => exact .seq (program.observedFinite_of_supported supported)
  case eitherOf options =>
    cases options with
    | nil => exact .eitherOf .nil
    | cons first rest =>
      cases rest with
      | nil => exact .eitherOf (.cons (first.observedFinite_of_supported supported) .nil)
      | cons second rest => exact .eitherChoice first second rest
  case ifThen test yes no =>
    obtain ⟨yesSupported, noSupported⟩ := Bool.and_eq_true_iff.mp supported
    exact .ifThen (yes.observedFinite_of_supported yesSupported) (no.observedFinite_of_supported noSupported)
  case repeatN count body => exact .repeatN (body.observedFinite_of_supported supported)
  case bind name amount body => exact .bind (body.observedFinite_of_supported supported)
  case forEach target body => exact .forEach (body.observedFinite_of_supported supported)
  case eachPlayer who body => exact .eachPlayer (body.observedFinite_of_supported supported)
  case may body => exact .may body
  case chooseObject side place filters body => exact .chooseObject side place filters body
  case retainTargetSet groups => exact .retainTargetSet groups
  case grant target modification duration => exact .grant target modification duration
  case splitDamage targets total => exact .splitDamage targets total
  case splitUnitDamage dealer targets index => exact .splitUnitDamage dealer targets index
  case applySplitDamage hits => exact .applySplitDamage hits
  case applyUnitSplitDamage hits link => exact .applyUnitSplitDamage hits link
  case resolveEffectDamage batch hit => exact .resolveDamage batch hit
  case chooseDamageReplacement batch hit replacement => exact .chooseDamage batch hit replacement
  case orderCombatDamage target chosen remaining => exact .orderCombatDamage target chosen remaining
  case endCombatDamage excess => exact .endCombatDamage excess
  case chooseDeathBanisher unit banisher => exact .chooseDeathBanisher unit banisher
  case chooseDeathGear unit gear => exact .chooseDeathGear unit gear
  case chooseDeathFree unit source => exact .chooseDeathFree unit source
  case recordDeathSacrifice unit cost => exact .recordDeathSacrifice unit cost
  case recordDeathOrder group unit => exact .recordDeathOrder group unit
  case recordDeathReselection group earlier unit choice => exact .recordDeathReselection group earlier unit choice
  case recordNestedDeathDecision root used unit choice scope =>
    exact .recordNestedDeathDecision root used unit choice scope
  case orderRuneRecycle remaining chosen => exact .orderRuneRecycle remaining chosen
  case recordRuneRecycle remaining chosen rune => exact .recordRuneRecycle remaining chosen rune
  case finishTrashRecycle picked => exact .finishTrashRecycle picked
  case recycleTrashTargets => exact .recycleTrashTargets
  case recycleFromTrash side count upTo picked => exact .recycleFromTrash side count upTo picked
  case chooseTrashRecycle side count picked => exact .chooseTrashRecycle side count picked
  case recordTrashRecycle side count upTo picked => exact .recordTrashRecycle side count upTo picked
  case completeActivation source index baseEnergy targets filters =>
    exact .completeActivation source index baseEnergy targets filters
termination_by structural effect

/-- A supported program is finite through the real observer. -/
theorem EffectList.observedFinite_of_supported (program : EffectList) (supported : program.observedWorkSupported = true) :
    program.ObservedFinite := by
  cases program with
  | nil => exact .nil
  | cons head tail =>
    obtain ⟨headSupported, tailSupported⟩ := Bool.and_eq_true_iff.mp supported
    exact .cons (head.observedFinite_of_supported headSupported) (tail.observedFinite_of_supported tailSupported)
termination_by structural program

end

end Riftbound

end
