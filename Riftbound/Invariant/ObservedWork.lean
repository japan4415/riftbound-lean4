module

public import Riftbound.Invariant.ObservedAddWork

/-!
# Observed work and ordinary trigger insertion (I12)

Resolve immediate Adds while keeping the order in which ordinary triggers and pending work resume.
-/

@[expose] public section

namespace Riftbound

/-- Once immediate Adds have run, the event observer can finish the game, keep the underlying
continuation, or insert a nonempty queue into that continuation. -/
inductive ObservedWorkStack (rest : List Frame) : List Frame → Prop where
  /-- Sudden-death scoring cleared the stack. -/
  | empty : ObservedWorkStack rest []
  /-- No ordinary abilities remain from observation. -/
  | resume : ObservedWorkStack rest rest
  /-- Ordinary abilities wait behind outstanding resolution frames. -/
  | queue (triggers : List PendTrigger) : triggers ≠ [] →
      ObservedWorkStack rest (insertTriggers triggers rest)

/-- Consume all observed immediate Adds. If the stack survives observation, its Cleanup
measure is preserved along with the continuation up to ordinary trigger insertion. -/
theorem advance_observed_work_geometry (raw : GameState) (notices : List Event)
    (wf : raw.WF) (reads : MightRead.database raw.cards) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.WF ∧ t.cards = raw.cards ∧ ObservedWorkStack raw.pending t.pending ∧
      (t.pending ≠ [] → t.cleanupMeasure = raw.cleanupMeasure) ∧ t.zones = raw.zones := by
  have observedCards : (raw.withTriggers notices).cards = raw.cards := by
    obtain ⟨_, _, updated⟩ := withTriggers_pending raw notices
    rw [updated]
    rfl
  rcases withTriggers_cases raw notices with ⟨winner, finished, _⟩ | unchanged | ⟨queue, woven, _⟩
  · refine ⟨raw.withTriggers notices, 0, [], by intro fuel past; simp, withTriggers_wf notices wf, observedCards, ?_, ?_, ?_⟩
    · rw [finished]
      exact .empty
    · simp [finished]
    · rw [finished]
      rfl
  · refine ⟨raw.withTriggers notices, 0, [], by intro fuel past; simp, withTriggers_wf notices wf, observedCards, ?_, ?_, ?_⟩
    · rw [unchanged]
      exact .resume
    · intro _
      rw [unchanged]
      rfl
    · rw [unchanged]
      rfl
  · let ready := raw.recordTurnEvents notices
    let continuation := ordinaryTriggerContinuation ready queue raw.pending
    obtain ⟨board, used, events, path, wellFormed, cards, geometry⟩ :=
      advance_insertDetectedTriggers_adds_geometry ready queue raw.pending (wf.congr rfl rfl rfl rfl) reads
    refine ⟨{ board with pending := continuation }, used, events, by rw [woven]; exact path,
      wellFormed.congr rfl rfl rfl rfl, cards, ?_, ?_, geometry.zones⟩
    · change ObservedWorkStack raw.pending continuation
      unfold continuation ordinaryTriggerContinuation
      dsimp only
      split
      · exact .resume
      · rename_i nonempty
        exact .queue _ (fun h => nonempty (by rw [h]; rfl))
    · intro _
      refine (geometry.measure continuation).trans ?_
      unfold continuation ordinaryTriggerContinuation
      dsimp only
      split
      · rfl
      · exact cleanupMeasure_eq rfl rfl rfl rfl (insertTriggers_fightingAt raw _)

/-- Immediate Adds preserve the Cleanup measure when the continuation survives. -/
theorem advance_observed_work_measured (raw : GameState) (notices : List Event)
    (wf : raw.WF) (reads : MightRead.database raw.cards) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.WF ∧ t.cards = raw.cards ∧ ObservedWorkStack raw.pending t.pending ∧
      (t.pending ≠ [] → t.cleanupMeasure = raw.cleanupMeasure) := by
  obtain ⟨t, used, events, path, wellFormed, cards, route, measure, _⟩ :=
    advance_observed_work_geometry raw notices wf reads
  exact ⟨t, used, events, path, wellFormed, cards, route, measure⟩

/-- Consume all immediate Adds that the engine observed and preserve the rule continuation,
apart from a standard trigger insertion or a sudden-death finish. -/
theorem advance_observed_work (raw : GameState) (notices : List Event)
    (wf : raw.WF) (reads : MightRead.database raw.cards) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.WF ∧ t.cards = raw.cards ∧ ObservedWorkStack raw.pending t.pending := by
  obtain ⟨t, used, events, path, wellFormed, cards, route, _⟩ :=
    advance_observed_work_measured raw notices wf reads
  exact ⟨t, used, events, path, wellFormed, cards, route⟩

/-- Take a real work step and resolve the immediate Adds it observed. -/
theorem advance_rule_with_adds_geometry {s raw : GameState} {f : Frame} {rest : List Frame}
    {emitted : List Event} (pending : s.pending = f :: rest) (automatic : f.isWork = true)
    (step : microStep0 s = some (raw, emitted)) (wf : raw.WF)
    (known : raw.cards = s.cards) (reads : MightRead.database s.cards) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.WF ∧ t.cards = s.cards ∧ ObservedWorkStack raw.pending t.pending ∧ t.zones = raw.zones := by
  let notices := emitted ++ s.workTransitionEvents raw
  have actual : workStep s = some (raw.withTriggers notices, emitted) := by
    unfold workStep
    split
    · rename_i _ _ priority
      simp only [microStep0, priority] at step
      contradiction
    · simp only [microStep, step, Option.map_some, notices]
  obtain ⟨t, used, events, path, afterWF, cards, route, _, zones⟩ :=
    advance_observed_work_geometry raw notices wf (known ▸ reads)
  exact ⟨t, used + 1, emitted ++ events, by omega, path.prepend pending automatic actual,
    afterWF, cards.trans known, route, zones⟩

/-- Take a real work step and resolve the immediate Adds it observed. -/
theorem advance_rule_with_adds {s raw : GameState} {f : Frame} {rest : List Frame}
    {emitted : List Event} (pending : s.pending = f :: rest) (automatic : f.isWork = true)
    (step : microStep0 s = some (raw, emitted)) (wf : raw.WF)
    (known : raw.cards = s.cards) (reads : MightRead.database s.cards) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.WF ∧ t.cards = s.cards ∧ ObservedWorkStack raw.pending t.pending := by
  obtain ⟨t, used, events, positive, path, afterWF, cards, route, _⟩ :=
    advance_rule_with_adds_geometry pending automatic step wf known reads
  exact ⟨t, used, events, positive, path, afterWF, cards, route⟩

/-- Inserting a queue ahead of a non-resolution frame cannot move work behind that frame. -/
theorem insertTriggers_front (queue : List PendTrigger) (rest : List Frame)
    (before : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q) :
    insertTriggers queue rest = .triggers queue :: rest := by
  cases rest with
  | nil => rfl
  | cons f fs =>
    have rules := before f rfl
    unfold insertTriggers
    rw [ite_eq_right (by simp [rules.1])]
    split
    · exact False.elim (rules.2 _ rfl)
    · rfl

/-- A non-resolution continuation either resumes directly or waits while the leading
nonempty queue opens a decision. -/
theorem advance_observed_to_boundary (raw : GameState) (notices : List Event)
    (wf : raw.WF) (reads : MightRead.database raw.cards)
    (before : ∀ f, raw.pending.head? = some f →
      f.isResolution = false ∧ ∀ q, f ≠ .triggers q) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true ∨
        (t.pending = raw.pending ∧ t.WF ∧ t.cards = raw.cards)) := by
  obtain ⟨mid, used, events, path, wellFormed, cards, routed⟩ :=
    advance_observed_work raw notices wf reads
  generalize stack : mid.pending = frames at routed
  cases routed with
  | empty => exact ⟨mid, used, events, path, Or.inl (by rw [stack]; rfl)⟩
  | resume => exact ⟨mid, used, events, path, Or.inr ⟨stack, wellFormed, cards⟩⟩
  | queue qs nonempty =>
    have inserted := insertTriggers_front qs raw.pending before
    obtain ⟨t, elapsed, _, _, _, later, decisionStack, decision⟩ :=
      advance_triggers_to_decision mid wellFormed qs raw.pending (stack.trans inserted) (cards ▸ reads) (Or.inl nonempty)
    exact ⟨t, used + elapsed, events, by simpa only [List.append_nil] using path.append later,
      Or.inl (by simp [decisionStack, decision])⟩

/-- An idle stack that does not start with neutral priority survives preparation as-is. -/
theorem GameState.prepared_idle_of_nonpriority {s : GameState}
    (idle : s.pending.head?.all (fun frame => !frame.isWork) = true)
    (nonpriority : ∀ p tail, s.pending ≠ .priority p :: tail) :
    s.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true := by
  rcases s.preparePriority_cases with unchanged | ⟨p, tail, stack, _, _⟩
  · simpa only [unchanged] using idle
  · exact (nonpriority p tail stack).elim

private theorem advance_observed_decision_core (s : GameState) (rest : List Frame) (wf : s.WF)
    (reads : MightRead.database s.cards) (route : ObservedWorkStack rest s.pending)
    (boundary : rest.head?.all (fun frame => !frame.isWork) = true) :
    ∃ t used, AdvancePrefix s t used [] ∧
      t.pending.head?.all (fun frame => !frame.isWork) = true ∧
      ((∀ p tail, rest ≠ .priority p :: tail) →
        t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true) := by
  have done (stop : s.pending.head?.all (fun frame => !frame.isWork) = true)
      (nonpriority : (∀ p tail, rest ≠ .priority p :: tail) → ∀ p tail, s.pending ≠ .priority p :: tail) :
      ∃ t used, AdvancePrefix s t used [] ∧
        t.pending.head?.all (fun frame => !frame.isWork) = true ∧
        ((∀ p tail, rest ≠ .priority p :: tail) →
          t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true) :=
    ⟨s, 0, by intro fuel prior; simp, stop, fun same =>
      GameState.prepared_idle_of_nonpriority stop (nonpriority same)⟩
  generalize stack : s.pending = frames at route
  cases route with
  | empty => exact done (by rw [stack]; rfl) (by simp [stack])
  | resume =>
    exact done (stack.symm ▸ boundary) (fun nonpriority p tail equality =>
      nonpriority p tail (stack.symm.trans equality))
  | queue queue nonempty =>
    have lead (h : s.pending = .triggers queue :: rest) :
        ∃ t used, AdvancePrefix s t used [] ∧
          t.pending.head?.all (fun frame => !frame.isWork) = true ∧
          ((∀ p tail, rest ≠ .priority p :: tail) →
            t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true) := by
      obtain ⟨t, used, _, _, _, path, decisionStack, decision, ready⟩ :=
        advance_triggers_to_preparedDecision s wf queue rest h reads (Or.inl nonempty)
      exact ⟨t, used, path, by simp [decisionStack, decision], fun _ => ready⟩
    cases rest with
    | nil => exact lead stack
    | cons f tail =>
      have decision : f.isWork = false := by simpa using boundary
      by_cases outstanding : f.isResolution = true
      · have left : s.pending = f :: insertTriggers queue tail := by
          simp only [stack, insertTriggers, outstanding, ↓reduceIte]
        apply done (by simp [left, decision])
        intro _ p after equal
        rw [left, List.cons.injEq] at equal
        rw [equal.1] at outstanding
        cases outstanding
      · apply lead
        rw [stack]
        apply insertTriggers_front
        intro task head
        obtain rfl := Option.some.inj head
        refine ⟨by simpa using outstanding, ?_⟩
        intro q impossible
        cases impossible
        contradiction

/-- Resolve any ordinary triggers the observer put before a decision. -/
theorem advance_observed_decision (s : GameState) (rest : List Frame) (wf : s.WF)
    (reads : MightRead.database s.cards) (route : ObservedWorkStack rest s.pending)
    (boundary : rest.head?.all (fun frame => !frame.isWork) = true) :
    ∃ t used, AdvancePrefix s t used [] ∧
      t.pending.head?.all (fun frame => !frame.isWork) = true := by
  obtain ⟨t, used, path, stop, _⟩ := advance_observed_decision_core s rest wf reads route boundary
  exact ⟨t, used, path, stop⟩

/-- A non-neutral decision is ready after observation and resolution of its ordinary queue. -/
theorem advance_observed_prepared_decision (s : GameState) (rest : List Frame) (wf : s.WF)
    (reads : MightRead.database s.cards) (route : ObservedWorkStack rest s.pending)
    (boundary : rest.head?.all (fun frame => !frame.isWork) = true)
    (nonpriority : ∀ p tail, rest ≠ .priority p :: tail) :
    ∃ t used, AdvancePrefix s t used [] ∧
      t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true := by
  obtain ⟨t, used, path, _, ready⟩ := advance_observed_decision_core s rest wf reads route boundary
  exact ⟨t, used, path, ready nonpriority⟩

/-- A work continuation, possibly with a nonempty queue of ordinary triggers. -/
def TriggerWorkTail (rest frames : List Frame) : Prop :=
  frames = rest ∨ ∃ queue : List PendTrigger, queue ≠ [] ∧ frames = .triggers queue :: rest

/-- More ordinary triggers merge with those already waiting before the continuation. -/
theorem TriggerWorkTail.insert {rest frames : List Frame} (tail : TriggerWorkTail rest frames)
    (head : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (queue : List PendTrigger) (nonempty : queue ≠ []) :
    TriggerWorkTail rest (insertTriggers queue frames) := by
  rcases tail with rfl | ⟨older, _, rfl⟩
  · right
    refine ⟨queue, nonempty, ?_⟩
    exact insertTriggers_front queue frames head
  · exact Or.inr ⟨older ++ queue, fun empty => nonempty (List.append_eq_nil_iff.mp empty).2, rfl⟩

/-- Resolve an ordinary queue, when present, before resuming the rest of the stack. -/
theorem advance_trigger_tail (s : GameState) (rest : List Frame) (wf : s.WF)
    (reads : MightRead.database s.cards) (tail : TriggerWorkTail rest s.pending) :
    ∃ t used, AdvancePrefix s t used [] ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true ∨
        (t.pending = rest ∧ t.WF ∧ t.cards = s.cards)) := by
  rcases tail with resumed | ⟨queue, nonempty, waiting⟩
  · exact ⟨s, 0, by intro fuel past; simp, Or.inr ⟨resumed, wf, rfl⟩⟩
  · obtain ⟨t, used, _, _, _, run, stack, decision⟩ :=
      advance_triggers_to_decision s wf queue rest waiting reads (Or.inl nonempty)
    exact ⟨t, used, run, Or.inl (by simp [stack, decision])⟩

/-- A finite dispatcher run reaches a decision, an empty stack, or the specified continuation. -/
def AdvanceTo (s : GameState) (keeps : List Frame → Prop) : Prop :=
  ∃ t used events, AdvancePrefix s t used events ∧
    (t.pending.head?.all (fun f => !f.isWork) = true ∨
      (keeps t.pending ∧ t.WF ∧ t.cards = s.cards))

/-- A continuation already at the head of the stack is ready immediately. -/
theorem AdvanceTo.resume {s : GameState} {keeps : List Frame → Prop} (wf : s.WF)
    (kept : keeps s.pending) : AdvanceTo s keeps :=
  ⟨s, 0, [], by intro fuel past; simp, Or.inr ⟨kept, wf, rfl⟩⟩

/-- Run the next segment if the first segment reached its tracked continuation. -/
theorem AdvanceTo.then {s : GameState} {first last : List Frame → Prop}
    (before : AdvanceTo s first) (reads : MightRead.database s.cards)
    (after : ∀ t : GameState, t.WF → MightRead.database t.cards → first t.pending → AdvanceTo t last) :
    AdvanceTo s last := by
  obtain ⟨t, used, events, path, stop | ⟨kept, wf, cards⟩⟩ := before
  · exact ⟨t, used, events, path, Or.inl stop⟩
  · obtain ⟨u, later, emitted, run, done⟩ := after t wf (cards ▸ reads) kept
    exact ⟨u, used + later, events ++ emitted, path.append run,
      done.imp_right (fun ⟨lastStack, lastWF, lastCards⟩ => ⟨lastStack, lastWF, lastCards.trans cards⟩)⟩

/-- Dispatch a rule and its immediate Adds, keeping any ordinary trigger insertion in the
tracked continuation. -/
theorem AdvanceTo.rule {s raw : GameState} {frame : Frame} {rest : List Frame}
    {events : List Event} {keeps : List Frame → Prop}
    (pending : s.pending = frame :: rest) (automatic : frame.isWork = true)
    (rule : microStep0 s = some (raw, events)) (wf : raw.WF) (cards : raw.cards = s.cards)
    (reads : MightRead.database s.cards) (base : keeps raw.pending)
    (inserted : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    AdvanceTo s keeps := by
  obtain ⟨t, used, events, _, path, lastWF, lastCards, route⟩ :=
    advance_rule_with_adds pending automatic rule wf cards reads
  generalize stack : t.pending = frames at route
  cases route with
  | empty => exact ⟨t, used, events, path, Or.inl (by rw [stack]; rfl)⟩
  | resume => exact ⟨t, used, events, path, Or.inr ⟨stack.symm ▸ base, lastWF, lastCards⟩⟩
  | queue q nonempty =>
    exact ⟨t, used, events, path, Or.inr ⟨stack.symm ▸ inserted raw.pending base q nonempty, lastWF, lastCards⟩⟩

/-- Ordinary triggers wait behind every resolution frame in the supplied prefix. -/
theorem insertTriggers_append_resolution (frames rest : List Frame) (queue : List PendTrigger)
    (resolution : ∀ f ∈ frames, f.isResolution = true) :
    insertTriggers queue (frames ++ rest) = frames ++ insertTriggers queue rest := by
  induction frames with
  | nil => rfl
  | cons f fs ih =>
    have first := resolution f List.mem_cons_self
    simp only [List.cons_append, insertTriggers, first, ite_true, ih (fun g member =>
      resolution g (List.mem_cons_of_mem _ member))]

/-- The known resolution frames are followed by a tracked continuation. -/
def ResolutionPrefix (frames : List Frame) (keeps : List Frame → Prop) (stack : List Frame) : Prop :=
  ∃ tail, stack = frames ++ tail ∧ keeps tail

/-- Inserting ordinary triggers preserves the resolution prefix. -/
theorem ResolutionPrefix.insert {frames stack : List Frame} {keeps : List Frame → Prop}
    (tracked : ResolutionPrefix frames keeps stack)
    (resolution : ∀ f ∈ frames, f.isResolution = true)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail))
    (q : List PendTrigger) (nonempty : q ≠ []) :
    ResolutionPrefix frames keeps (insertTriggers q stack) := by
  obtain ⟨tail, rfl, kept⟩ := tracked
  exact ⟨_, insertTriggers_append_resolution frames tail q resolution, inserted tail kept q nonempty⟩

end Riftbound

end
