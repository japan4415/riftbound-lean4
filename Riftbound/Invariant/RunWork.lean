module

public import Riftbound.Invariant.DamageWork
public import Riftbound.Invariant.RecyclePaymentWork
public import Riftbound.Invariant.DisclosureWork
public import Riftbound.Invariant.ObservedCleanupWork

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

/-- Check a live Play for a permanent or a Spell using either resolution route. -/
def effectPlayRunSupported (s : GameState) : Bool :=
  permanentPlayRunSupported s || spellPlayRunSupported s

/-- Dispatch either checked Play branch to the retained continuation or an input. -/
theorem advance_effectPlayRun_checked {s : GameState} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards) (checked : effectPlayRunSupported s = true)
    (base : keeps s.pending.tail)
    (inserted : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    AdvanceTo s keeps := by
  rcases Bool.or_eq_true_iff.mp checked with permanent | spell
  · exact advance_permanentPlayRun_checked wf reads permanent base inserted
  · exact advance_spellPlayRun_checked wf reads spell base inserted

end Riftbound

end
