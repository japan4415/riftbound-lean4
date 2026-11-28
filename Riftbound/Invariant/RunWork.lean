module

public import Riftbound.Invariant.DamageWork
public import Riftbound.Invariant.RecyclePaymentWork
public import Riftbound.Invariant.DisclosureWork
public import Riftbound.Invariant.ObservedCleanupWork
public import Riftbound.Invariant.UnitTokenWork

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
  | .prim (.score ..) | .prim (.win _)
  | .prim (.ready _) | .prim (.exhaust _) | .prim (.buff _) | .prim (.stun _)
  | .prim (.returnToHand _) | .prim (.banish _) | .prim (.topdeck _) | .prim (.bin _) | .prim (.castInline _)
  | .prim (.copyAttachedFrom _) | .prim (.detach _) | .prim (.becomeCopy ..)
  | .prim (.create ..) | .prim (.createAt ..) | .prim (.createAtPrev ..) | .prim (.cloneToken _)
  | .prim (.playUnitToken _) | .prim (.playReadyUnitToken _) | .prim (.playUnitTokenAt ..)
  | .prim (.playReadyUnitTokenAt ..)
  | .prim (.turnEffect _) | .prim (.hideAt ..) | .prim (.empower _) | .prim (.disempower _) | .prim (.spendBuff _)
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
  | .planUnitTokenEntries .. | .fundTokenAccelerate .. | .finishUnitTokens .. | .playUnitTokensThen .. => true
  | .planPermanentPlay .. | .finishReducedPermanent .. | .finishFundedPermanent .. | .fundPermanentFromEffect ..
  | .planBanishReplay .. | .prim (.playAtBase _) => true
  | .seq program => program.observedWorkSupported
  | .eitherOf (.cons only .nil) => only.observedWorkSupported
  | .eitherOf _ => true
  | .ifThen _ yes no => yes.observedWorkSupported && no.observedWorkSupported
  | .lookAtTop _ body | .revealHand _ body | .revealDeckTops _ body => body.observedWorkSupported
  | .repeatN _ body | .bind _ _ body | .forEach _ body | .eachPlayer _ body => body.observedWorkSupported
  | .doThen (.prim cost) body => cost.linkedCostSupported && body.observedWorkSupported
  | .payThen _ body _ | .paySelected _ body _ => body.observedWorkSupported
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
    case score who amount => exact (Effect.SingleRun.score who amount).observed
    case win who => exact (Effect.SingleRun.win who).observed
    case ready selector => exact Effect.ObservedFinite.ready selector
    case exhaust selector => exact Effect.ObservedFinite.exhaust selector
    case buff selector => exact Effect.ObservedFinite.buff selector
    case stun selector => exact Effect.ObservedFinite.stun selector
    case returnToHand selector => exact Effect.ObservedFinite.returnToHand selector
    case banish selector => exact Effect.ObservedFinite.banish selector
    case topdeck selector => exact Effect.ObservedFinite.topdeck selector
    case bin selector => exact Effect.ObservedFinite.bin selector
    case castInline selector => exact Effect.ObservedFinite.castInline selector
    case copyAttachedFrom selector => exact Effect.ObservedFinite.copyAttachedFrom selector
    case detach selector => exact Effect.ObservedFinite.detach selector
    case becomeCopy targets source => exact Effect.ObservedFinite.becomeCopy targets source
    case create name count place ready => exact Effect.ObservedFinite.create name count place ready
    case createAt name count dest ready => exact Effect.ObservedFinite.createAt name count dest ready
    case createAtPrev name count ready => exact Effect.ObservedFinite.createAtPrev name count ready
    case cloneToken target => exact Effect.ObservedFinite.cloneToken target
    case playUnitToken name => exact Effect.ObservedFinite.playUnitToken name false
    case playReadyUnitToken name => exact Effect.ObservedFinite.playUnitToken name true
    case playUnitTokenAt name dest => exact Effect.ObservedFinite.playUnitTokenAt name dest false
    case playReadyUnitTokenAt name dest => exact Effect.ObservedFinite.playUnitTokenAt name dest true
    case playAtBase selector => exact Effect.ObservedFinite.playAtBase selector
    case turnEffect effect => exact (Effect.SingleRun.turnEffect effect).observed
    case hideAt cards battlefields => exact (Effect.SingleRun.hideAt cards battlefields).observed
    case empower selector => exact Effect.ObservedFinite.empower selector
    case disempower selector => exact Effect.ObservedFinite.disempower selector
    case spendBuff selector => exact Effect.ObservedFinite.spendBuff selector
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
  case doThen first body =>
    cases first <;> try (simp [Effect.observedWorkSupported] at supported; done)
    case prim cost =>
      obtain ⟨checked, bodySupported⟩ := Bool.and_eq_true_iff.mp supported
      exact .linkedCost cost checked (body.observedFinite_of_supported bodySupported)
  case payThen cost body gearPower => exact .payThen cost gearPower (body.observedFinite_of_supported supported)
  case paySelected cost body gearPower => exact .paySelected cost gearPower (body.observedFinite_of_supported supported)
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
  case planUnitTokenEntries batch plan => exact .planUnitTokenEntries batch plan
  case fundTokenAccelerate batch payment adds => exact .fundTokenAccelerate batch payment adds
  case finishUnitTokens batch payment adds => exact .finishUnitTokens batch payment adds
  case playUnitTokensThen name count place ready index target => exact .playUnitTokensThen name count place ready index target
  case planPermanentPlay card terms => exact .planPermanentPlay card terms
  case finishReducedPermanent card terms plan => exact .finishReducedPermanent card terms plan
  case finishFundedPermanent card terms plan adds => exact .finishFundedPermanent card terms plan adds
  case fundPermanentFromEffect card terms plan adds => exact .fundPermanentFromEffect card terms plan adds
  case planBanishReplay card location => exact .planBanishReplay card location
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

/-- Whether the frame is a Run whose complete program is supported. -/
def runFrameSupported : Frame → Bool
  | .run _ _ _ program => program.observedWorkSupported
  | _ => false

/-- Every accepted Run frame carries the observed termination proof for its program. -/
theorem runFrameSupported_finite {f : Frame} (supported : runFrameSupported f = true) :
    f.FiniteRun := by
  cases f <;> try (simp [runFrameSupported] at supported; done)
  exact ⟨_, _, _, _, rfl, EffectList.observedFinite_of_supported _ supported⟩

/-- Check all of the Runs generated by the actual head instruction. This includes the
replacement effects produced by attaching Equipment, and the original continuation. -/
def generatedRunsSupported (s : GameState) : Bool :=
  match s.pending with
  | .run p src env (.cons effect more) :: _ =>
    (runEffect s p src (env.withMight s.mightTable) effect more effectAddPolicy).2.1.all runFrameSupported
  | _ => false

/-- Execute a live instruction and the list of supported Runs it actually generates.
The first transition observes its events and processes any immediate Adds. -/
theorem advance_generatedRuns_checked {s : GameState} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards) (checked : generatedRunsSupported s = true)
    (base : keeps s.pending.tail)
    (inserted : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    AdvanceTo s keeps := by
  cases pending : s.pending with
  | nil => simp [generatedRunsSupported, pending] at checked
  | cons frame rest =>
    cases frame <;> try (simp [generatedRunsSupported, pending] at checked; done)
    case run p src env program =>
      cases program with
      | nil => simp [generatedRunsSupported, pending] at checked
      | cons effect more =>
        let frames := (runEffect s p src (env.withMight s.mightTable) effect more effectAddPolicy).2.1
        have supported : frames.all runFrameSupported = true := by
          simpa only [generatedRunsSupported, pending] using checked
        have finite (f : Frame) (member : f ∈ frames) : f.FiniteRun :=
          runFrameSupported_finite (List.all_eq_true.mp supported f member)
        have entered : AdvanceTo s (ResolutionPrefix frames keeps) := by
          apply advance_run_rule wf reads pending ⟨rest, rfl, by simpa only [pending, List.tail_cons] using base⟩
          exact fun _ tracks q ne => tracks.insert (fun f member => (finite f member).isResolution) inserted q ne
        exact entered.then reads (fun _ safe known tracks => advance_run_frames safe known tracks finite inserted)

/-- Check the pending Play and the rest of its Run against the live checkpoint. -/
def permanentPlayRunSupported (s : GameState) : Bool :=
  match s.pending with
  | .run p src env (.cons (.prim (.play sel)) more) :: _ =>
    (Effect.prim (.play sel)).pickSel?.isNone &&
      (playSpellStep s p src (env.withMight s.mightTable) sel more effectAddPolicy).isNone &&
      more.observedWorkSupported
  | _ => false

/-- A checked Play in a live Run reaches a prepared decision or its retained continuation. -/
theorem advance_permanentPlayRun_checked {s : GameState} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards) (checked : permanentPlayRunSupported s = true)
    (base : keeps s.pending.tail)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  cases pending : s.pending with
  | nil => simp [permanentPlayRunSupported, pending] at checked
  | cons f rest =>
    cases f <;> try (simp [permanentPlayRunSupported, pending] at checked; done)
    case run p src env program =>
      cases program with
      | nil => simp [permanentPlayRunSupported, pending] at checked
      | cons effect more =>
        cases effect <;> try (simp [permanentPlayRunSupported, pending] at checked; done)
        case prim pr =>
          cases pr <;> try (simp [permanentPlayRunSupported, pending] at checked; done)
          case play sel =>
            simp only [permanentPlayRunSupported, pending, Bool.and_eq_true_iff] at checked
            obtain ⟨⟨direct, noSpell⟩, remaining⟩ := checked
            have hp : (Effect.prim (.play sel)).pickSel? = none := by
              cases found : (Effect.prim (.play sel)).pickSel? <;> simp_all
            have hs : playSpellStep s p src (env.withMight s.mightTable) sel more effectAddPolicy = none := by
              cases spell : playSpellStep s p src (env.withMight s.mightTable) sel more effectAddPolicy <;> simp_all
            have start := advance_run_playPermanent wf reads pending hp hs (by simpa [pending] using base) inserted
            apply start.then reads
            intro t safe known next
            obtain ⟨live, tail, stack, kept⟩ := next
            exact advance_run_program safe known stack (EffectList.observedFinite_of_supported more remaining)
              keeps kept inserted

/-- The inline Spell has a checked body and caller separated by Cleanup in the actual dispatch. -/
def inlineSpellFramesSupported : List Frame → Bool
  | [.run _ _ _ spell, .cleanup, .run _ _ _ caller] =>
    spell.observedWorkSupported && caller.observedWorkSupported
  | _ => false

/-- Inspect the actual Spell branch and test the continuation it schedules. -/
def spellPlayRunSupportedWith (accept : List Frame → Bool) (s : GameState) : Bool :=
  match s.pending with
  | .run p src env (.cons (.prim (.play sel)) more) :: _ =>
    (Effect.prim (.play sel)).pickSel?.isNone &&
      (playSpellStep s p src (env.withMight s.mightTable) sel more effectAddPolicy).any
        (fun result => accept result.2.1)
  | _ => false

/-- Check a Spell that resolves inline before resuming the originating effect. -/
def inlineSpellPlayRunSupported (s : GameState) : Bool := spellPlayRunSupportedWith inlineSpellFramesSupported s

/-- Queuing a Spell for later finalization leaves the caller's Run at the head of the stack. -/
def deferredSpellFramesSupported : List Frame → Bool
  | [.run _ _ _ caller] => caller.observedWorkSupported
  | _ => false

/-- Check either Spell route of an actual Play. -/
def spellPlayRunSupported (s : GameState) : Bool :=
  spellPlayRunSupportedWith (fun frames => inlineSpellFramesSupported frames || deferredSpellFramesSupported frames) s

private theorem advance_run_inlineSpell {s next : GameState} {p : PlayerId} {src : ObjId}
    {env : Env} {sel : Selector} {more : EffectList} {rest : List Frame} {events : List Event}
    {caster resume : PlayerId} {item resumeSource : ObjId} {spellEnv resumeEnv : Env} {body caller : EffectList}
    {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons (.prim (.play sel)) more) :: rest)
    (direct : (Effect.prim (.play sel)).pickSel? = none)
    (cast : playSpellStep s p src (env.withMight s.mightTable) sel more effectAddPolicy =
      some (next, [.run caster item spellEnv body, .cleanup, .run resume resumeSource resumeEnv caller], events))
    (spell : body.ObservedFinite) (remaining : caller.ObservedFinite)
    (base : keeps rest) (inserted : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    AdvanceTo s keeps := by
  let last := Frame.run resume resumeSource resumeEnv caller
  let first := Frame.run caster item spellEnv body
  let resumes := ResolutionPrefix [last] keeps
  let cleans := ResolutionPrefix [.cleanup] resumes
  let runs := ResolutionPrefix [first] cleans
  have insertLast (stack : List Frame) (held : resumes stack) (q : List PendTrigger) (ne : q ≠ []) :
      resumes (insertTriggers q stack) :=
    held.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) inserted q ne
  have insertCleanup (stack : List Frame) (held : cleans stack) (q : List PendTrigger) (ne : q ≠ []) :
      cleans (insertTriggers q stack) :=
    held.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) insertLast q ne
  have entered : AdvanceTo s runs := by
    apply advance_run_rule wf reads pending ?_ (fun _ held q ne =>
      held.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) insertCleanup q ne)
    simp only [runEffect, direct, runEffect1, runPrimEffect, cast]
    exact ⟨.cleanup :: last :: rest, rfl, ⟨last :: rest, rfl, ⟨rest, rfl, base⟩⟩⟩
  have afterSpell : AdvanceTo s cleans := entered.then reads (fun _ safe known held => by
    obtain ⟨_, stack, tail⟩ := held
    exact advance_run_program safe known stack spell cleans tail insertCleanup)
  have afterCleanup : AdvanceTo s resumes := afterSpell.then reads (fun _ safe known held => by
    obtain ⟨_, stack, tail⟩ := held
    obtain ⟨t, used, emitted, _, path, stop⟩ :=
      advance_cleanup_with_adds_prepared safe known stack resumes tail insertLast
    exact ⟨t, used, emitted, path, stop.imp_right (fun ⟨ready, wellFormed, cards, _⟩ =>
      ⟨ready, wellFormed, cards⟩)⟩)
  exact afterCleanup.then reads (fun _ safe known held => by
    obtain ⟨_, stack, tail⟩ := held
    exact advance_run_program safe known stack remaining keeps tail inserted)

private theorem advance_run_deferredSpell {s next : GameState} {p : PlayerId} {src : ObjId}
    {env : Env} {sel : Selector} {more : EffectList} {rest : List Frame} {events : List Event}
    {resume : PlayerId} {resumeSource : ObjId} {resumeEnv : Env} {caller : EffectList}
    {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons (.prim (.play sel)) more) :: rest)
    (direct : (Effect.prim (.play sel)).pickSel? = none)
    (cast : playSpellStep s p src (env.withMight s.mightTable) sel more effectAddPolicy =
      some (next, [.run resume resumeSource resumeEnv caller], events))
    (remaining : caller.ObservedFinite) (base : keeps rest)
    (inserted : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    AdvanceTo s keeps := by
  let resumes := ResolutionPrefix [.run resume resumeSource resumeEnv caller] keeps
  have insertRun (stack : List Frame) (held : resumes stack) (q : List PendTrigger) (ne : q ≠ []) :
      resumes (insertTriggers q stack) :=
    held.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) inserted q ne
  have queued : AdvanceTo s resumes := by
    apply advance_run_rule wf reads pending ?_ insertRun
    simp only [runEffect, direct, runEffect1, runPrimEffect, cast]
    exact ⟨rest, rfl, base⟩
  exact queued.then reads (fun _ safe known held => by
    obtain ⟨_, stack, tail⟩ := held
    exact advance_run_program safe known stack remaining keeps tail inserted)

/-- A checked Spell either executes inline or queues its declaration, then resumes the caller. -/
theorem advance_spellPlayRun_checked {s : GameState} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards) (checked : spellPlayRunSupported s = true)
    (base : keeps s.pending.tail)
    (inserted : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    AdvanceTo s keeps := by
  cases pending : s.pending with
  | nil => simp [spellPlayRunSupported, spellPlayRunSupportedWith, pending] at checked
  | cons f rest =>
    cases f <;> try (simp [spellPlayRunSupported, spellPlayRunSupportedWith, pending] at checked; done)
    case run p src env program =>
      cases program with
      | nil => simp [spellPlayRunSupported, spellPlayRunSupportedWith, pending] at checked
      | cons effect more =>
        cases effect <;> try (simp [spellPlayRunSupported, spellPlayRunSupportedWith, pending] at checked; done)
        case prim pr =>
          cases pr <;> try (simp [spellPlayRunSupported, spellPlayRunSupportedWith, pending] at checked; done)
          case play sel =>
            simp only [spellPlayRunSupported, spellPlayRunSupportedWith, pending, Bool.and_eq_true_iff] at checked
            obtain ⟨hasNoPick, supported⟩ := checked
            have noPick : (Effect.prim (.play sel)).pickSel? = none := by
              cases found : (Effect.prim (.play sel)).pickSel? <;> simp_all
            cases cast : playSpellStep s p src (env.withMight s.mightTable) sel more effectAddPolicy with
            | none => simp [cast] at supported
            | some result =>
              obtain ⟨next, frames, events⟩ := result
              simp only [cast, Option.any_some] at supported
              rcases Bool.or_eq_true_iff.mp supported with inline | deferred
              · unfold inlineSpellFramesSupported at inline
                split at inline
                · obtain ⟨body, caller⟩ := Bool.and_eq_true_iff.mp inline
                  exact advance_run_inlineSpell wf reads pending noPick cast
                    (EffectList.observedFinite_of_supported _ body) (EffectList.observedFinite_of_supported _ caller)
                    (by simpa [pending] using base) inserted
                · contradiction
              · unfold deferredSpellFramesSupported at deferred
                split at deferred
                · exact advance_run_deferredSpell wf reads pending noPick cast
                    (EffectList.observedFinite_of_supported _ deferred) (by simpa [pending] using base) inserted
                · contradiction

/-- Check Play when its selector no longer requires a resolution choice. -/
def directEffectPlayRunSupported (s : GameState) : Bool :=
  permanentPlayRunSupported s || spellPlayRunSupported s

private theorem advance_directEffectPlayRun_checked {s : GameState} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards) (checked : directEffectPlayRunSupported s = true)
    (base : keeps s.pending.tail)
    (inserted : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    AdvanceTo s keeps := by
  rcases Bool.or_eq_true_iff.mp checked with permanent | spell
  · exact advance_permanentPlayRun_checked wf reads permanent base inserted
  · exact advance_spellPlayRun_checked wf reads spell base inserted

/-- For a Play that selects its card during resolution, check the real decision or the
observed continuation of a singleton choice. -/
def pickedEffectPlayRunSupported (s : GameState) : Bool :=
  match s.pending with
  | .run p src env (.cons (.prim (.play (.pick .one side place filters))) more) :: _ =>
    match s.pickCandidates p src (env.withMight s.mightTable) side place filters true with
    | some [_] => (workStep s).any (fun result => directEffectPlayRunSupported result.1)
    | some (_ :: _ :: _) => true
    | _ => more.observedWorkSupported
  | _ => false

private theorem directEffectPlayRunSupported_front {s : GameState}
    (checked : directEffectPlayRunSupported s = true) :
    ∃ p src env sel more rest, s.pending = .run p src env (.cons (.prim (.play sel)) more) :: rest := by
  cases stack : s.pending with
  | nil => simp [directEffectPlayRunSupported, permanentPlayRunSupported, spellPlayRunSupported,
      spellPlayRunSupportedWith, stack] at checked
  | cons f rest =>
    cases f <;> try (simp [directEffectPlayRunSupported, permanentPlayRunSupported, spellPlayRunSupported,
      spellPlayRunSupportedWith, stack] at checked; done)
    case run p src env program =>
      cases program with
      | nil => simp [directEffectPlayRunSupported, permanentPlayRunSupported, spellPlayRunSupported,
          spellPlayRunSupportedWith, stack] at checked
      | cons effect more =>
        cases effect <;> try (simp [directEffectPlayRunSupported, permanentPlayRunSupported, spellPlayRunSupported,
          spellPlayRunSupportedWith, stack] at checked; done)
        case prim pr =>
          cases pr <;> try (simp [directEffectPlayRunSupported, permanentPlayRunSupported, spellPlayRunSupported,
            spellPlayRunSupportedWith, stack] at checked; done)
          case play sel => exact ⟨p, src, env, sel, more, rest, rfl⟩

private theorem immediateAddFrame_not_play {s : GameState} {trig : PendTrigger}
    {p : PlayerId} {src : ObjId} {env : Env} {sel : Selector} {more : EffectList} :
    trig.immediateAddFrame s ≠ some (.run p src env (.cons (.prim (.play sel)) more)) := by
  intro eq
  unfold PendTrigger.immediateAddFrame at eq
  split at eq
  · dsimp only at eq
    split at eq
    · injection eq with impossible
      cases impossible
    · contradiction
  · contradiction

/-- If observation leaves a checked Play at the front, its original tail was preserved
up to ordinary trigger insertion. Immediate Adds themselves start with a different instruction. -/
theorem playTail_after_observation {raw : GameState} {notices : List Event}
    {p : PlayerId} {src : ObjId} {env : Env} {sel : Selector} {more : EffectList} {rest : List Frame}
    {keeps : List Frame → Prop}
    (before : raw.pending = .run p src env (.cons (.prim (.play sel)) more) :: rest)
    (checked : directEffectPlayRunSupported (raw.withTriggers notices) = true)
    (base : keeps rest) (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    keeps (raw.withTriggers notices).pending.tail := by
  obtain ⟨p', src', env', sel', more', rest', layout⟩ := directEffectPlayRunSupported_front checked
  rcases withTriggers_cases raw notices with ⟨_, ended, _⟩ | recorded | ⟨queue, woven, _⟩
  · simp only [ended] at layout
    contradiction
  · rw [recorded]
    change keeps raw.pending.tail
    simpa only [before, List.tail_cons] using base
  · let ready := raw.recordTurnEvents notices
    let adds := (queue.map (fun t => (t, t.immediateAddFrame ready))).filterMap Prod.snd
    have noAdds : adds = [] := by
      have head := congrArg List.head? layout
      rw [woven] at head
      change (adds ++ _).head? = some (.run p' src' env' (.cons (.prim (.play sel')) more')) at head
      cases built : adds with
      | nil => rfl
      | cons first others =>
        simp only [built, List.cons_append, List.head?_cons, Option.some.injEq] at head
        have member : first ∈ adds := by simp [built]
        obtain ⟨⟨t, add⟩, mapped, result⟩ := List.mem_filterMap.mp member
        obtain ⟨trig, _, pair⟩ := List.mem_map.mp mapped
        have scheduled : trig.immediateAddFrame ready = some first := (Prod.mk.inj pair).2.trans result
        exact False.elim (immediateAddFrame_not_play (head ▸ scheduled))
    rw [woven]
    change keeps (adds ++ _).tail
    rw [noAdds, List.nil_append]
    split
    · simpa only [before, List.tail_cons] using base
    · rename_i nonempty
      rw [before]
      exact inserted rest base _ (fun eq => nonempty (by rw [eq]; rfl))

private theorem noRequiredPlayCandidates (candidates : Option (List ObjId)) : (none <|> candidates) = candidates := rfl

private theorem advance_pickedPlay_singleton {s : GameState} {p : PlayerId} {src obj : ObjId}
    {env : Env} {side : Side} {place : Place} {filters : FilterList} {more : EffectList}
    {rest : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons (.prim (.play (.pick .one side place filters))) more) :: rest)
    (found : s.pickCandidates p src (env.withMight s.mightTable) side place filters true = some [obj])
    (checked : (workStep s).any (fun result => directEffectPlayRunSupported result.1) = true)
    (base : keeps rest) (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  let live := env.withMight s.mightTable
  let play := Effect.prim (.play (.pick .one side place filters))
  let bound := Frame.run p src (live.bindPick obj (play.pickIsTarget s obj))
    (.cons (.prim (.play (.var pickVar))) more)
  let raw := { s with pending := bound :: rest }
  let events := play.pickEvents s p src obj
  let notices := events ++ s.workTransitionEvents raw
  let next := raw.withTriggers notices
  have actual : workStep s = some (next, events) := by
    simp only [workStep, pending, microStep, microStep0, runEffect, Effect.pickSel?, Prim.pickSel?,
      requiredPlayCandidates, noRequiredPlayCandidates, Effect.isLinkedCost, Bool.not_false, found,
      Effect.withPick, Prim.withSel, raw, bound, live, play, events, notices, next, Option.map_some, List.cons_append, List.nil_append]
  rw [actual, Option.any_some] at checked
  have tail := playTail_after_observation (raw := raw) (notices := notices) rfl checked base inserted
  have cards : next.cards = s.cards := by
    obtain ⟨_, _, updated⟩ := withTriggers_pending raw notices
    change (raw.withTriggers notices).cards = s.cards
    rw [updated]
    rfl
  obtain ⟨t, used, emitted, path, stop⟩ :=
    advance_directEffectPlayRun_checked (workStep_wf wf actual) (cards.symm ▸ reads) checked tail inserted
  exact ⟨t, used + 1, events ++ emitted, path.prepend pending rfl actual,
    stop.imp_right (fun ⟨kept, safe, known⟩ => ⟨kept, safe, known.trans cards⟩)⟩

private theorem advance_pickedPlay_cases {s : GameState} {p : PlayerId} {src : ObjId}
    {env : Env} {side : Side} {place : Place} {filters : FilterList} {more : EffectList}
    {rest : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons (.prim (.play (.pick .one side place filters))) more) :: rest)
    (checked : pickedEffectPlayRunSupported s = true)
    (base : keeps rest) (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  let live := env.withMight s.mightTable
  let play := Effect.prim (.play (.pick .one side place filters))
  let candidates := s.pickCandidates p src live side place filters true
  have route :
      (runEffect s p src live play more effectAddPolicy).2.1 =
        match candidates with
        | some [obj] => [.run p src (live.bindPick obj (play.pickIsTarget s obj)) (.cons play.withPick more)]
        | some (obj :: other :: rest) => [.pickDo p src live obj (other :: rest) play.withPick more]
        | _ => [.run p src live more] := by
    simp only [runEffect, play, Effect.pickSel?, Prim.pickSel?, requiredPlayCandidates,
      Effect.isLinkedCost, Bool.not_false, noRequiredPlayCandidates, candidates]
    generalize s.pickCandidates p src live side place filters true = choices
    cases choices with
    | none => rfl
    | some cards =>
      cases cards with
      | nil => rfl
      | cons first rest => cases rest <;> rfl
  have skips (empty : candidates = none ∨ candidates = some []) (supported : more.observedWorkSupported = true) :
      AdvanceTo s keeps := by
    have ran : AdvanceTo s (RunContinuation p src more keeps) := by
      apply advance_run_rule wf reads pending ?_ (fun _ held q ne => held.insert inserted q ne)
      change RunContinuation p src more keeps ((runEffect s p src live play more effectAddPolicy).2.1 ++ rest)
      rw [route]
      rcases empty with no | no <;> rw [no] <;> exact ⟨live, rest, rfl, base⟩
    exact ran.then reads (fun _ safe known ⟨_, _, stack, tail⟩ =>
      advance_run_program safe known stack (EffectList.observedFinite_of_supported more supported)
        keeps tail inserted)
  simp only [pickedEffectPlayRunSupported, pending, ← show live = env.withMight s.mightTable from rfl,
    ← show candidates = s.pickCandidates p src live side place filters true from rfl] at checked
  cases found : candidates with
  | none => exact skips (.inl found) (by simpa only [found] using checked)
  | some cards =>
    cases cards with
    | nil => exact skips (.inr found) (by simpa only [found] using checked)
    | cons first others =>
      cases others with
      | nil =>
        exact advance_pickedPlay_singleton wf reads pending found (by simpa only [found] using checked) base inserted
      | cons second later =>
        apply advance_run_decision wf reads pending
        change NonNeutralDecision ((runEffect s p src live play more effectAddPolicy).2.1 ++ rest)
        rw [route, found]
        rfl

/-- A checked resolution-time Play selection terminates at a decision or its retained continuation. -/
theorem advance_pickedEffectPlayRun_checked {s : GameState} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards) (checked : pickedEffectPlayRunSupported s = true)
    (base : keeps s.pending.tail)
    (inserted : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    AdvanceTo s keeps := by
  cases pending : s.pending with
  | nil => simp [pickedEffectPlayRunSupported, pending] at checked
  | cons f rest =>
    cases f <;> try (simp [pickedEffectPlayRunSupported, pending] at checked; done)
    case run p src env program =>
      cases program with
      | nil => simp [pickedEffectPlayRunSupported, pending] at checked
      | cons effect more =>
        cases effect <;> try (simp [pickedEffectPlayRunSupported, pending] at checked; done)
        case prim pr =>
          cases pr <;> try (simp [pickedEffectPlayRunSupported, pending] at checked; done)
          case play sel =>
            cases sel <;> try (simp [pickedEffectPlayRunSupported, pending] at checked; done)
            case pick quantity side place filters =>
              cases quantity <;> try (simp [pickedEffectPlayRunSupported, pending] at checked; done)
              case one => exact advance_pickedPlay_cases wf reads pending checked (by simpa [pending] using base) inserted

/-- Check live Play whether its card is known or chosen during resolution. -/
def effectPlayRunSupported (s : GameState) : Bool :=
  directEffectPlayRunSupported s || pickedEffectPlayRunSupported s

/-- Dispatch checked Play to the retained continuation or the next input. -/
theorem advance_effectPlayRun_checked {s : GameState} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards) (checked : effectPlayRunSupported s = true)
    (base : keeps s.pending.tail)
    (inserted : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    AdvanceTo s keeps := by
  rcases Bool.or_eq_true_iff.mp checked with direct | pick
  · exact advance_directEffectPlayRun_checked wf reads direct base inserted
  · exact advance_pickedEffectPlayRun_checked wf reads pick base inserted

end Riftbound

end
