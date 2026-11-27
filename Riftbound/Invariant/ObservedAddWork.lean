module

public import Riftbound.Invariant.AddObservation
public import Riftbound.Invariant.CleanupWork
public import Riftbound.Invariant.TriggerWork
public import Riftbound.Invariant.Step

/-!
# Immediate Adds through the observed engine

The supported resource additions cannot create another observer step. Their effects and use
markers therefore finish in the real engine, leaving the previously scheduled stack in place.
-/

@[expose] public section

namespace Riftbound

private theorem runStep_observed {s t : GameState} {p : PlayerId} {src : ObjId}
    {env : Env} {program : EffectList} {rest : List Frame} {events : List Event}
    (wf : s.WF) (checked : MightRead.database s.cards)
    (stack : s.pending = .run p src env program :: rest) (reads : SameMightReads s t)
    (raw : microStep0 s = some (t, events))
    (onlySkip : events = [] ∨ events = [.skipped src]) : workStep s = some (t, events) := by
  have none := workTransitionEvents_run_quiet wf checked reads stack
  simp only [workStep, stack, microStep, raw, Option.map_some, none, List.append_nil]
  rcases onlySkip with rfl | rfl
  · rw [withTriggers_nil]
  · rw [withTriggers_skipped]

private theorem runSingle_observed {s t : GameState} {p : PlayerId} {src : ObjId} {env refreshed : Env}
    {e : Effect} {more nextProgram : EffectList} {rest : List Frame} {events : List Event}
    (wf : s.WF) (checked : MightRead.database s.cards)
    (stack : s.pending = .run p src env (.cons e more) :: rest)
    (unchangedStack : t.pending = s.pending) (reads : SameMightReads s t)
    (rule : runEffect s p src (env.withMight s.mightTable) e more effectAddPolicy =
      (t, [.run p src refreshed nextProgram], events))
    (onlySkip : events = [] ∨ events = [.skipped src]) :
    workStep s = some ({ t with pending := .run p src refreshed nextProgram :: rest }, events) := by
  let next := { t with pending := .run p src refreshed nextProgram :: rest }
  have combat : next.combatNow = s.combatNow := by
    calc
      next.combatNow = t.combatNow := by
        unfold GameState.combatNow
        rw [unchangedStack, stack]
        rfl
      _ = s.combatNow := reads.combatNow
  have raw : microStep0 s = some (next, events) := by
    simp only [microStep0, stack, rule]
    rfl
  exact runStep_observed wf checked stack (reads.replacePending _ combat) raw onlySkip

private theorem runPrefix {s t : GameState} {p : PlayerId} {src : ObjId}
    {env : Env} {program : EffectList} {rest : List Frame} {events : List Event}
    (stack : s.pending = .run p src env program :: rest)
    (step : workStep s = some (t, events)) : AdvancePrefix s t 1 events := by
  have still : AdvancePrefix t t 0 [] := by intro fuel past; simp
  simpa only [List.append_nil] using still.prepend stack rfl step

private theorem popNil (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (rest : List Frame)
    (wf : s.WF) (checked : MightRead.database s.cards) :
    AdvancePrefix { s with pending := .run p src env .nil :: rest } { s with pending := rest } 1 [] := by
  let start := { s with pending := .run p src env .nil :: rest }
  have reads : SameMightReads start { s with pending := rest } :=
    (SameMightReads.refl start).replacePending rest rfl
  have step : workStep start = some ({ s with pending := rest }, []) :=
    runStep_observed (wf.congr rfl rfl rfl rfl) checked rfl reads rfl (Or.inl rfl)
  exact runPrefix rfl step

private theorem addPrimRule (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (pr : Prim) (more : EffectList) (allowed : (Effect.prim pr).isTriggerAdd = true) :
    runEffect s p src env (.prim pr) more effectAddPolicy =
      match applyPrim s p src env pr with
      | some (t, events) => (t, [.run p src env more], events)
      | none => (s, [.run p src env more], [.skipped src]) := by
  cases pr <;> try (simp [Effect.isTriggerAdd] at allowed; done)
  case' addEnergy who n only =>
    cases who <;> cases only <;> simp [Effect.isTriggerAdd] at allowed
  case' addUnitEnergy who n =>
    cases who <;> simp [Effect.isTriggerAdd] at allowed
  case' addSpellEnergy who n =>
    cases who <;> simp [Effect.isTriggerAdd] at allowed
  case' addPower who n domain only =>
    cases who <;> cases only <;> simp [Effect.isTriggerAdd] at allowed
    cases domain
  all_goals
    simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
      effectDamageBatch?, permanentPlayEffects, applyPrim]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;>
      cases PlayerSel.resolve s p .you env <;> cases n.evalS s p src env <;> rfl

/-- Two states contribute the same Cleanup measure under any shared continuation. -/
def SameCleanupMeasure (before after : GameState) : Prop :=
  ∀ stack, ({ after with pending := stack } : GameState).cleanupMeasure =
    ({ before with pending := stack } : GameState).cleanupMeasure

private theorem SameCleanupMeasure.refl (s : GameState) : SameCleanupMeasure s s := fun _ => rfl

private theorem SameCleanupMeasure.trans {s t u : GameState}
    (first : SameCleanupMeasure s t) (second : SameCleanupMeasure t u) :
    SameCleanupMeasure s u := fun stack => (second stack).trans (first stack)

private theorem sameCleanupMeasure_of_geometry {s t : GameState} (reads : SameMightReads s t)
    (cards : t.cards = s.cards) (objects : t.objects = s.objects) (zones : t.zones = s.zones) :
    SameCleanupMeasure s t := by
  intro stack
  apply cleanupMeasure_eq (s := { s with pending := stack }) (t := { t with pending := stack }) reads.config cards objects zones
  intro field
  have combat := reads.combat
  change (t.combat.any (·.battlefield == field) || _) = (s.combat.any (·.battlefield == field) || _)
  rw [combat]

private def AddEffectTerminates (e : Effect) : Prop :=
  ∀ (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (more : EffectList) (rest : List Frame),
    s.WF → MightRead.database s.cards →
    ∃ (t : GameState) (n : Nat) (events : List Event) (might : List (ObjId × Int)),
      AdvancePrefix { s with pending := .run p src env (.cons e more) :: rest }
        { t with pending := .run p src (env.withMight might) more :: rest } n events ∧
      t.WF ∧ t.cards = s.cards ∧ SameCleanupMeasure s t

private def AddSequenceTerminates (program : EffectList) : Prop :=
  ∀ (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (more : EffectList) (rest : List Frame),
    s.WF → MightRead.database s.cards →
    ∃ (t : GameState) (n : Nat) (events : List Event) (might : List (ObjId × Int)),
      AdvancePrefix { s with pending := .run p src env (program.append more) :: rest }
        { t with pending := .run p src (env.withMight might) more :: rest } n events ∧
      t.WF ∧ t.cards = s.cards ∧ SameCleanupMeasure s t

private theorem addSequence_nil : AddSequenceTerminates .nil := by
  intro s p src env more rest wf _
  refine ⟨s, 0, [], env.passMight, ?_, wf, rfl, .refl _⟩
  have same : env.withMight env.passMight = env := by cases env; rfl
  intro fuel events
  simp only [EffectList.append, same, Nat.zero_add, List.append_nil]

private theorem addSequence_cons {e : Effect} {later : EffectList}
    (first : AddEffectTerminates e) (remaining : AddSequenceTerminates later) :
    AddSequenceTerminates (.cons e later) := by
  intro s p src env more rest wf checked
  obtain ⟨t, n, events, might, ran, nextWF, cards, board⟩ := first s p src env (later.append more) rest wf checked
  obtain ⟨u, m, extra, refreshed, suffix, finalWF, finalCards, finalBoard⟩ :=
    remaining t p src (env.withMight might) more rest nextWF (cards ▸ checked)
  have refreshAgain : (env.withMight might).withMight refreshed = env.withMight refreshed := rfl
  exact ⟨u, n + m, events ++ extra, refreshed, by simpa only [EffectList.append, refreshAgain] using ran.append suffix,
    finalWF, finalCards.trans cards, board.trans finalBoard⟩

private theorem addEffect_single {e : Effect}
    (resolve : ∀ start p src env more, ∃ t events,
      runEffect start p src env e more effectAddPolicy = (t, [.run p src env more], events) ∧
      t.pending = start.pending ∧ SameMightReads start t ∧ t.cards = start.cards ∧ SameCleanupMeasure start t ∧
      (events = [] ∨ events = [.skipped src])) :
    AddEffectTerminates e := by
  intro s p src env more rest wf checked
  let start := { s with pending := .run p src env (.cons e more) :: rest }
  let refreshed := env.withMight start.mightTable
  obtain ⟨t, events, rule, stack, reads, cards, board, onlySkip⟩ := resolve start p src refreshed more
  have step := runSingle_observed (s := start) (wf.congr rfl rfl rfl rfl) checked rfl stack reads rule onlySkip
  exact ⟨t, 1, events, start.mightTable, runPrefix rfl step,
    (workStep_wf (s := start) (wf.congr rfl rfl rfl rfl) step).congr rfl rfl rfl rfl, cards, board⟩

private theorem addEffect_prim (pr : Prim) (allowed : (Effect.prim pr).isTriggerAdd = true) :
    AddEffectTerminates (.prim pr) := by
  apply addEffect_single
  intro s p src env more
  have rule := addPrimRule s p src env pr more allowed
  cases applied : applyPrim s p src env pr with
  | none =>
    exact ⟨s, [.skipped src], by simpa only [applied] using rule, rfl, .refl s, rfl, .refl _, Or.inr rfl⟩
  | some answer =>
    obtain ⟨t, events⟩ := answer
    obtain ⟨reads, cards, objects, zones, noEvents⟩ := applyPrim_add_geometry allowed applied
    exact ⟨t, events, by simpa only [applied] using rule, (applyPrim_safe applied).same.pending,
      reads, cards, sameCleanupMeasure_of_geometry reads cards objects zones, Or.inl noEvents⟩

private theorem addEffect_marker (index : Nat) : AddEffectTerminates (.markTriggeredAdd index) := by
  apply addEffect_single
  intro s p src env more
  refine ⟨s.modObj src (fun o => o.noteAbilityUse index env.abilityCopyStamp), [], rfl, rfl,
    noteAbilityUse_sameMightReads s src index env.abilityCopyStamp, rfl, ?_, Or.inl rfl⟩
  intro stack
  exact noteAbilityUse_cleanupMeasure { s with pending := stack } src index env.abilityCopyStamp stack (fun _ => rfl)

private theorem addEffect_nop : AddEffectTerminates .nop := by
  apply addEffect_single
  intro s p src env more
  exact ⟨s, [], rfl, rfl, .refl s, rfl, .refl _, Or.inl rfl⟩

private theorem addEffect_seq {program : EffectList} (body : AddSequenceTerminates program) :
    AddEffectTerminates (.seq program) := by
  intro s p src env more rest wf checked
  let start := { s with pending := .run p src env (.cons (.seq program) more) :: rest }
  let refreshed := env.withMight start.mightTable
  have step : workStep start = some ({ s with pending := .run p src refreshed (program.append more) :: rest }, []) :=
    runSingle_observed (s := start) (t := start) (wf.congr rfl rfl rfl rfl) checked rfl rfl (.refl start) rfl (Or.inl rfl)
  have enter := runPrefix (rest := rest) (program := .cons (.seq program) more) rfl step
  obtain ⟨t, n, events, might, ran, wellFormed, cards, board⟩ := body s p src refreshed more rest wf checked
  have refreshAgain : refreshed.withMight might = env.withMight might := rfl
  exact ⟨t, 1 + n, events, might, by simpa only [List.nil_append, refreshAgain] using enter.append ran,
    wellFormed, cards, board⟩

private theorem addEffect_ifThen {test : Condition} {yes no : Effect}
    (onYes : AddEffectTerminates yes) (onNo : AddEffectTerminates no) :
    AddEffectTerminates (.ifThen test yes no) := by
  intro s p src env more rest wf checked
  let start := { s with pending := .run p src env (.cons (.ifThen test yes no) more) :: rest }
  let refreshed := env.withMight start.mightTable
  have startWF : start.WF := wf.congr rfl rfl rfl rfl
  have sameEnv : refreshed.withMight start.mightTable = refreshed := rfl
  cases result : test.eval start p src refreshed with
  | none =>
    have rule : runEffect start p src refreshed (.ifThen test yes no) more effectAddPolicy =
        (start, [.run p src refreshed more], [.skipped src]) := by
      simp only [runEffect, Effect.pickSel?, runEffect1, sameEnv, result] <;> rfl
    have step := runSingle_observed startWF checked rfl rfl (.refl start) rule (Or.inr rfl)
    exact ⟨s, 1, [.skipped src], start.mightTable, runPrefix rfl step, wf, rfl, .refl _⟩
  | some answer =>
    let branch := if answer then yes else no
    have branchFinishes : AddEffectTerminates branch := by cases answer <;> first | exact onNo | exact onYes
    have rule : runEffect start p src refreshed (.ifThen test yes no) more effectAddPolicy =
        (start, [.run p src refreshed (.cons branch more)], []) := by
      simp only [runEffect, Effect.pickSel?, runEffect1, sameEnv, result] <;> rfl
    have step := runSingle_observed startWF checked rfl rfl (.refl start) rule (Or.inl rfl)
    have enter := runPrefix (rest := rest) (program := .cons (.ifThen test yes no) more) rfl step
    obtain ⟨t, n, events, might, ran, wellFormed, cards, board⟩ :=
      branchFinishes s p src refreshed more rest wf checked
    have refreshAgain : refreshed.withMight might = env.withMight might := rfl
    exact ⟨t, 1 + n, events, might, by simpa only [List.nil_append, refreshAgain] using enter.append ran,
      wellFormed, cards, board⟩

mutual

private theorem addEffect_of_check (e : Effect) (allowed : e.isTriggerAdd = true) :
    AddEffectTerminates e := by
  cases e with
  | prim pr => exact addEffect_prim pr allowed
  | seq program =>
    cases program with
    | nil => simp [Effect.isTriggerAdd] at allowed
    | cons first later =>
      simp only [Effect.isTriggerAdd, Bool.and_eq_true] at allowed
      exact addEffect_seq (addSequence_cons (addEffect_of_check first allowed.1)
        (addSequence_of_check later allowed.2))
  | ifThen test yes no =>
    cases no with
    | nop =>
      exact addEffect_ifThen
        (addEffect_of_check yes (by simpa only [Effect.isTriggerAdd] using allowed)) addEffect_nop
    | _ => simp [Effect.isTriggerAdd] at allowed
  | _ => simp [Effect.isTriggerAdd] at allowed
termination_by structural e

private theorem addSequence_of_check (program : EffectList) (allowed : program.areTriggerAdds = true) :
    AddSequenceTerminates program := by
  cases program with
  | nil => exact addSequence_nil
  | cons first later =>
    simp only [EffectList.areTriggerAdds, Bool.and_eq_true] at allowed
    exact addSequence_cons (addEffect_of_check first allowed.1) (addSequence_of_check later allowed.2)
termination_by structural program

end

/-- The actual engine finishes a scheduled immediate Add, including its use marker and any skipped
instructions, leaving the supplied continuation. Evaluating a condition may read the current state
even when the trigger was scheduled in an earlier state. -/
theorem PendTrigger.advance_immediateAddFrame_measured {detected : GameState} {trigger : PendTrigger}
    {frame : Frame} (scheduled : trigger.immediateAddFrame detected = some frame)
    (current : GameState) (rest : List Frame) (wf : current.WF) (checked : MightRead.database current.cards) :
    ∃ (t : GameState) (used : Nat) (events : List Event), 0 < used ∧
      AdvancePrefix { current with pending := frame :: rest } { t with pending := rest } used events ∧
      t.WF ∧ t.cards = current.cards ∧ SameCleanupMeasure current t := by
  unfold PendTrigger.immediateAddFrame at scheduled
  split at scheduled
  · split at scheduled
    · rename_i accepted
      simp only [Bool.and_eq_true] at accepted
      obtain rfl := Option.some.inj scheduled
      have program := addSequence_cons (addEffect_marker trigger.idx)
        (addSequence_cons (addEffect_of_check _ accepted.2) addSequence_nil)
      let env : Env := {
        slots := trigger.subject.toList.map Value.obj
        sourceCard := some trigger.card
        abilityCopyStamp := trigger.copyStamp
        eventAmount := trigger.eventAmount
        eventBattlefields := trigger.eventBattlefields
        shownOff := trigger.shownOff }
      obtain ⟨t, used, events, might, ran, wellFormed, cards, board⟩ :=
        program current trigger.controller trigger.source env .nil rest wf checked
      have pop := popNil t trigger.controller trigger.source (env.withMight might) rest wellFormed (cards ▸ checked)
      refine ⟨t, used + 1, events, by omega, ?_, wellFormed, cards, board⟩
      simpa only [EffectList.append, List.append_nil] using ran.append pop
    · contradiction
  · contradiction

/-- A scheduled immediate Add resolves through the actual engine and restores its continuation. -/
theorem PendTrigger.advance_immediateAddFrame {detected : GameState} {trigger : PendTrigger}
    {frame : Frame} (scheduled : trigger.immediateAddFrame detected = some frame)
    (current : GameState) (rest : List Frame) (wf : current.WF) (checked : MightRead.database current.cards) :
    ∃ (t : GameState) (used : Nat) (events : List Event), 0 < used ∧
      AdvancePrefix { current with pending := frame :: rest } { t with pending := rest } used events ∧
      t.WF ∧ t.cards = current.cards := by
  obtain ⟨t, used, events, positive, path, wellFormed, cards, _⟩ :=
    trigger.advance_immediateAddFrame_measured scheduled current rest wf checked
  exact ⟨t, used, events, positive, path, wellFormed, cards⟩

private theorem advance_immediateAdds (detected : GameState) (triggers : List PendTrigger) (current : GameState)
    (rest : List Frame) (wf : current.WF) (checked : MightRead.database current.cards) :
    ∃ (t : GameState) (used : Nat) (events : List Event), AdvancePrefix
      { current with pending := triggers.filterMap (·.immediateAddFrame detected) ++ rest }
      { t with pending := rest } used events ∧ t.WF ∧ t.cards = current.cards ∧ SameCleanupMeasure current t := by
  induction triggers generalizing current with
  | nil =>
    exact ⟨current, 0, [], by intro fuel events; simp, wf, rfl, .refl _⟩
  | cons first triggers ih =>
    cases scheduled : first.immediateAddFrame detected with
    | none =>
      simpa only [List.filterMap_cons, scheduled] using ih current wf checked
    | some frame =>
      let tail := triggers.filterMap (·.immediateAddFrame detected) ++ rest
      obtain ⟨t, used, events, _, ran, wellFormed, cards, board⟩ :=
        first.advance_immediateAddFrame_measured scheduled current tail wf checked
      obtain ⟨u, later, extra, stopped, finalWF, finalCards, finalBoard⟩ := ih t wellFormed (cards ▸ checked)
      exact ⟨u, used + later, events ++ extra,
        by simpa only [List.filterMap_cons, scheduled, List.cons_append] using ran.append stopped,
        finalWF, finalCards.trans cards, board.trans finalBoard⟩

/-- Through the real engine, every immediate Add in a detected batch runs before the ordinary
queue and the original continuation. The events remain in their emitted order. -/
theorem advance_insertDetectedTriggers_adds_measured (s : GameState) (triggers : List PendTrigger)
    (rest : List Frame) (wf : s.WF) (checked : MightRead.database s.cards) :
    ∃ (t : GameState) (used : Nat) (events : List Event), AdvancePrefix { s with pending := insertDetectedTriggers s triggers rest }
      { t with pending := ordinaryTriggerContinuation s triggers rest } used events ∧
      t.WF ∧ t.cards = s.cards ∧ SameCleanupMeasure s t := by
  unfold ordinaryTriggerContinuation insertDetectedTriggers
  simp only [List.filterMap_map, Function.comp_def]
  exact advance_immediateAdds s triggers s _ wf checked

/-- The actual engine resolves a batch of immediate Adds before its ordinary continuation. -/
theorem advance_insertDetectedTriggers_adds (s : GameState) (triggers : List PendTrigger)
    (rest : List Frame) (wf : s.WF) (checked : MightRead.database s.cards) :
    ∃ (t : GameState) (used : Nat) (events : List Event), AdvancePrefix { s with pending := insertDetectedTriggers s triggers rest }
      { t with pending := ordinaryTriggerContinuation s triggers rest } used events ∧
      t.WF ∧ t.cards = s.cards := by
  obtain ⟨t, used, events, path, wellFormed, cards, _⟩ :=
    advance_insertDetectedTriggers_adds_measured s triggers rest wf checked
  exact ⟨t, used, events, path, wellFormed, cards⟩

private theorem advance_leadingTriggers_checked (s : GameState) (wf : s.WF)
    (checked : MightRead.database s.cards) :
    ∃ t used, AdvancePrefix s t used [] ∧
      TriggerWorkStop (afterLeadingTriggers s.pending) t.pending := by
  have still : AdvancePrefix s s 0 [] := by intro fuel prior; simp
  cases pending : s.pending with
  | nil => exact ⟨s, 0, still, by rw [pending]; exact .resume⟩
  | cons frame rest =>
    cases frame with
    | triggers queue =>
      obtain ⟨t, used, _, ran, stop⟩ := advance_triggers_checkedMight s wf queue rest pending checked
      exact ⟨t, used, ran, by simpa only [pending, afterLeadingTriggers] using stop⟩
    | _ => exact ⟨s, 0, still, by rw [pending]; exact .resume⟩

/-- With checked Might reads, a detected batch runs its immediate Adds and any leading ordinary
queue through the actual dispatcher. Earlier outstanding resolution remains in its original
position in the stack. -/
theorem advance_detectedTriggers_checkedMight (s : GameState) (triggers : List PendTrigger)
    (rest : List Frame) (wf : s.WF) (checked : MightRead.database s.cards) :
    ∃ t used events, AdvancePrefix { s with pending := insertDetectedTriggers s triggers rest } t used events ∧
      TriggerWorkStop (afterLeadingTriggers (ordinaryTriggerContinuation s triggers rest)) t.pending := by
  obtain ⟨t, used, events, ran, wellFormed, cards⟩ := advance_insertDetectedTriggers_adds s triggers rest wf checked
  let next := { t with pending := ordinaryTriggerContinuation s triggers rest }
  obtain ⟨u, later, resolved, stop⟩ :=
    advance_leadingTriggers_checked next (wellFormed.congr rfl rfl rfl rfl) (cards ▸ checked)
  exact ⟨u, used + later, events, by simpa only [List.append_nil] using ran.append resolved, stop⟩

end Riftbound

end
