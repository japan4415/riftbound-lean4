module

public import Riftbound.Invariant.AddWork
public import Riftbound.Invariant.TriggerObservation

/-!
# Finite processing of the trigger queue (I12)

The ordinary trigger dispatcher decreases the number of pending abilities when it finalizes
an ability automatically. A group requiring a choice, an open Chain, or the original continuation
ends this segment of work. Immediate Adds run before that segment if event detection schedules them.
-/

@[expose] public section

namespace Riftbound

/-- Ways the ordinary trigger dispatcher hands control back to the engine. -/
inductive TriggerWorkStop (rest : List Frame) : List Frame → Prop where
  /-- The processing is finished and the original stack resumes. -/
  | resume : TriggerWorkStop rest rest
  /-- A newly opened Chain waits for the appropriate seat's decision. -/
  | priority (player passes) : TriggerWorkStop rest (.chainPass player passes :: rest)
  /-- The player must choose how to finalize pending abilities. -/
  | order (player first group others) :
      TriggerWorkStop rest (.triggerOrder player first group others :: rest)

private theorem triggerFrames_stop (s : GameState) (rest : List Frame) :
    TriggerWorkStop rest (triggerFrames s rest ++ rest) := by
  unfold triggerFrames
  split
  · exact .resume
  · split
    · exact .resume
    · exact .priority _ 0

private theorem rawTriggers_bound_and_observed (s : GameState) (queue : List PendTrigger) (rest : List Frame)
    (pending : s.pending = .triggers queue :: rest) :
    ∃ t used, used ≤ queue.length + 1 ∧ RawWorkPrefix s t used [] ∧
      TriggerWorkStop rest t.pending ∧
      (s.WF → s.mightWatches = [] → AdvancePrefix s t used []) := by
  have observe (wf : s.WF) (watches : s.mightWatches = []) :=
    workStep_triggers_noMightWatches s wf queue rest pending watches
  cases queue with
  | nil =>
    let next := { s with pending := triggerFrames s rest ++ rest }
    have raw : microStep0 s = some (next, []) := by
      simp only [microStep0, pending, triggersStep, next]
    refine ⟨next, 1, Nat.le_refl _, .single pending rfl raw, triggerFrames_stop s rest, ?_⟩
    intro wf watches
    exact AdvancePrefix.prepend (n := 0) pending rfl ((observe wf watches).trans raw) (by intro fuel prior; simp)
  | cons first more =>
    let sameGroup (t : PendTrigger) :=
      t.controller == first.controller && t.beforeStandardMove == first.beforeStandardMove
    let group := more.filter sameGroup
    let others := more.filter (fun t => !sameGroup t)
    by_cases automatic : (group.isEmpty && trigModes s first == [none] &&
        trigPlayerOptions s first == [none] && (trigChoices s first).isEmpty &&
        !trigOptional s first && trigCost s first == .free) = true
    · let next := { putTrigger s first [] with pending := .triggers others :: rest }
      have routed : triggersStep s (first :: more) rest = (putTrigger s first [], [.triggers others]) := by
        unfold triggersStep
        exact ite_eq_left automatic
      have raw : microStep0 s = some (next, []) := by
        simp only [microStep0, pending, routed, next] <;> rfl
      obtain ⟨t, used, bound, path, done, observed⟩ := rawTriggers_bound_and_observed next others rest rfl
      have shorter : others.length ≤ more.length := List.length_filter_le _ _
      refine ⟨t, used + 1, by simp only [List.length_cons]; omega,
        .next pending rfl raw path, done, ?_⟩
      intro wf watches
      have nextWF : next.WF := ((putTrigger_safe s first []).wf wf).congr rfl rfl rfl rfl
      have noWatches : next.mightWatches = [] := (putTrigger_automatic_mightWatches s wf first).trans watches
      exact (observed nextWF noWatches).prepend pending rfl ((observe wf watches).trans raw)
    · let next := { s with pending := .triggerOrder first.controller first group others :: rest }
      have routed : triggersStep s (first :: more) rest =
          (s, [.triggerOrder first.controller first group others]) := by
        unfold triggersStep
        exact ite_eq_right automatic
      have raw : microStep0 s = some (next, []) := by
        simp only [microStep0, pending, routed, next] <;> rfl
      refine ⟨next, 1, by simp, .single pending rfl raw, .order .., ?_⟩
      intro wf watches
      exact AdvancePrefix.prepend (n := 0) pending rfl ((observe wf watches).trans raw) (by intro fuel prior; simp)
termination_by queue.length
decreasing_by
  subst queue
  apply Nat.lt_succ_of_le
  exact List.length_filter_le _ _

/-- A pending ordinary trigger queue reaches a decision or hands control back to its original
continuation within its length plus one rule step. The final step can open Chain priority. -/
theorem rawTriggers_bound (s : GameState) (queue : List PendTrigger) (rest : List Frame)
    (pending : s.pending = .triggers queue :: rest) :
    ∃ t used, used ≤ queue.length + 1 ∧ RawWorkPrefix s t used [] ∧ TriggerWorkStop rest t.pending := by
  obtain ⟨next, used, bound, raw, done, _⟩ := rawTriggers_bound_and_observed s queue rest pending
  exact ⟨next, used, bound, raw, done⟩

/-- With no active watchers of Might thresholds, the actual engine processes the entire ordinary
trigger queue within its length plus one step and reaches a decision or its prior continuation. -/
theorem advance_triggers_noMightWatches (s : GameState) (wf : s.WF) (queue : List PendTrigger)
    (rest : List Frame) (pending : s.pending = .triggers queue :: rest) (watches : s.mightWatches = []) :
    ∃ t used, used ≤ queue.length + 1 ∧ AdvancePrefix s t used [] ∧ TriggerWorkStop rest t.pending := by
  obtain ⟨next, used, bound, _, done, observed⟩ := rawTriggers_bound_and_observed s queue rest pending
  exact ⟨next, used, bound, observed wf watches, done⟩

/-- The observed trigger work takes at most the queue length plus one step to reach the
continuation, wait for an answer or process an observer change. -/
theorem advance_triggers_bound (s : GameState) (queue : List PendTrigger) (rest : List Frame)
    (pending : s.pending = .triggers queue :: rest) :
    ∃ t used, used ≤ queue.length + 1 ∧ AdvancePrefix s t used [] ∧
      (TriggerWorkStop rest t.pending ∨ ∃ before expected, WorkObserverChange before expected t) := by
  obtain ⟨t, used, bound, path, done⟩ := rawTriggers_bound s queue rest pending
  rcases path.observe with reached |
    ⟨before, expected, actual, steps, emitted, changed, _, cut, reached, eventPrefix⟩
  · exact ⟨t, used, bound, reached, Or.inl done⟩
  · obtain ⟨extra, h⟩ := eventPrefix
    obtain ⟨rfl, _⟩ := List.append_eq_nil_iff.mp h
    exact ⟨actual, steps, Nat.le_trans cut bound, reached, Or.inr ⟨before, expected, changed⟩⟩

/-- Consume a trigger queue at the top of the stack. Other frames keep their existing priority. -/
def afterLeadingTriggers : List Frame → List Frame
  | .triggers _ :: rest => rest
  | stack => stack

private theorem rawLeadingTriggers (s : GameState) :
    ∃ t used, RawWorkPrefix s t used [] ∧
      TriggerWorkStop (afterLeadingTriggers s.pending) t.pending := by
  cases pending : s.pending with
  | nil => exact ⟨s, 0, .done s, by rw [pending]; exact .resume⟩
  | cons frame rest =>
    cases frame with
    | triggers queue =>
      obtain ⟨t, used, _, work, stop⟩ := rawTriggers_bound s queue rest pending
      exact ⟨t, used, work, by simpa only [pending, afterLeadingTriggers] using stop⟩
    | _ =>
      exact ⟨s, 0, .done s, by rw [pending]; exact .resume⟩

/-- After a batch of detected abilities, run all immediate Adds and a leading ordinary queue, if
there is one. Any resolution already ahead of the ordinary queue remains in the continuation. -/
theorem rawDetectedTriggers (s : GameState) (triggers : List PendTrigger) (rest : List Frame) :
    ∃ t used events,
      RawWorkPrefix { s with pending := insertDetectedTriggers s triggers rest } t used events ∧
      TriggerWorkStop (afterLeadingTriggers (ordinaryTriggerContinuation s triggers rest)) t.pending := by
  obtain ⟨t, adds, events, addWork⟩ := insertDetectedTriggers_addWork s triggers rest
  let next := { t with pending := ordinaryTriggerContinuation s triggers rest }
  obtain ⟨u, queued, queueWork, stop⟩ := rawLeadingTriggers next
  exact ⟨u, adds + queued, events, by simpa only [List.append_nil] using addWork.append queueWork, stop⟩

/-- The real engine follows the combined trigger work up to its decision or continuation, or to
the first change made by a new observation. The events before that change are preserved. -/
theorem advance_detectedTriggers (s : GameState) (triggers : List PendTrigger) (rest : List Frame) :
    let start := { s with pending := insertDetectedTriggers s triggers rest }
    ∃ t used events, AdvancePrefix start t used events ∧
      (TriggerWorkStop (afterLeadingTriggers (ordinaryTriggerContinuation s triggers rest)) t.pending ∨
        ∃ before expected, WorkObserverChange before expected t) := by
  obtain ⟨t, used, events, work, done⟩ := rawDetectedTriggers s triggers rest
  rcases work.observe with reached |
    ⟨before, expected, actual, steps, emitted, changed, _, _, reached, _⟩
  · exact ⟨t, used, events, reached, Or.inl done⟩
  · exact ⟨actual, steps, emitted, reached, Or.inr ⟨before, expected, changed⟩⟩

/-- When an ordinary step detects new abilities at a Might crossing, the actual engine proceeds
through that detected batch with the same fuel and event accounting as other trigger work. -/
theorem advance_triggers_afterMight (s : GameState) (wf : s.WF) (queue : List PendTrigger)
    (rest : List Frame) (pending : s.pending = .triggers queue :: rest) :
    let outcome := triggersStep s queue rest
    let next := { outcome.1 with pending := outcome.2 ++ rest }
    let detected := next.detect (s.mightyEvents next)
    (next.phase != .setup && next.pending.all (fun f => !f.isSetup) && !detected.isEmpty) = true →
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (TriggerWorkStop
        (afterLeadingTriggers (ordinaryTriggerContinuation next detected next.pending)) t.pending ∨
        ∃ before expected, WorkObserverChange before expected t) := by
  intro outcome next detected observe
  have observed := workStep_triggers_observed s wf queue rest pending
  change workStep s = some (if next.phase != .setup && next.pending.all (fun f => !f.isSetup) &&
    !detected.isEmpty then { next with pending := insertDetectedTriggers next detected next.pending }
    else next, ([] : List Event)) at observed
  rw [ite_eq_left observe] at observed
  obtain ⟨t, used, events, work, done⟩ := advance_detectedTriggers next detected next.pending
  exact ⟨t, used + 1, events, by omega, work.prepend pending rfl observed, done⟩

end Riftbound

end
