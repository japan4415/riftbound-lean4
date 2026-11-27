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
theorem advance_observed_work_measured (raw : GameState) (notices : List Event)
    (wf : raw.WF) (reads : MightRead.database raw.cards) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.WF ∧ t.cards = raw.cards ∧ ObservedWorkStack raw.pending t.pending ∧
      (t.pending ≠ [] → t.cleanupMeasure = raw.cleanupMeasure) := by
  have observedCards : (raw.withTriggers notices).cards = raw.cards := by
    obtain ⟨_, _, updated⟩ := withTriggers_pending raw notices
    rw [updated]
    rfl
  rcases withTriggers_cases raw notices with ⟨winner, finished, _⟩ | unchanged | ⟨queue, woven, _⟩
  · refine ⟨raw.withTriggers notices, 0, [], by intro fuel past; simp, withTriggers_wf notices wf, observedCards, ?_, ?_⟩
    · rw [finished]
      exact .empty
    · simp [finished]
  · refine ⟨raw.withTriggers notices, 0, [], by intro fuel past; simp, withTriggers_wf notices wf, observedCards, ?_, ?_⟩
    · rw [unchanged]
      exact .resume
    · intro _
      rw [unchanged]
      rfl
  · let ready := raw.recordTurnEvents notices
    let continuation := ordinaryTriggerContinuation ready queue raw.pending
    obtain ⟨board, used, events, path, wellFormed, cards, measure⟩ :=
      advance_insertDetectedTriggers_adds_measured ready queue raw.pending (wf.congr rfl rfl rfl rfl) reads
    refine ⟨{ board with pending := continuation }, used, events, by rw [woven]; exact path,
      wellFormed.congr rfl rfl rfl rfl, cards, ?_, ?_⟩
    · change ObservedWorkStack raw.pending continuation
      unfold continuation ordinaryTriggerContinuation
      dsimp only
      split
      · exact .resume
      · rename_i nonempty
        exact .queue _ (fun h => nonempty (by rw [h]; rfl))
    · intro _
      refine (measure continuation).trans ?_
      unfold continuation ordinaryTriggerContinuation
      dsimp only
      split
      · rfl
      · exact cleanupMeasure_eq rfl rfl rfl rfl (insertTriggers_fightingAt raw _)

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
theorem advance_rule_with_adds {s raw : GameState} {f : Frame} {rest : List Frame}
    {emitted : List Event} (pending : s.pending = f :: rest) (automatic : f.isWork = true)
    (step : microStep0 s = some (raw, emitted)) (wf : raw.WF)
    (known : raw.cards = s.cards) (reads : MightRead.database s.cards) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.WF ∧ t.cards = s.cards ∧ ObservedWorkStack raw.pending t.pending := by
  let notices := emitted ++ s.workTransitionEvents raw
  have actual : workStep s = some (raw.withTriggers notices, emitted) := by
    unfold workStep
    split
    · rename_i _ _ priority
      simp only [microStep0, priority] at step
      contradiction
    · simp only [microStep, step, Option.map_some, notices]
  obtain ⟨t, used, events, path, afterWF, cards, route⟩ :=
    advance_observed_work raw notices wf (known ▸ reads)
  exact ⟨t, used + 1, emitted ++ events, by omega, path.prepend pending automatic actual,
    afterWF, cards.trans known, route⟩

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

/-- An observer may put ordinary triggers ahead of a decision. Finish that queue if necessary
so that the actual dispatcher reaches a decision or an empty stack. -/
theorem advance_observed_decision (s : GameState) (rest : List Frame) (wf : s.WF)
    (reads : MightRead.database s.cards) (route : ObservedWorkStack rest s.pending)
    (boundary : rest.head?.all (fun frame => !frame.isWork) = true) :
    ∃ t used, AdvancePrefix s t used [] ∧
      t.pending.head?.all (fun frame => !frame.isWork) = true := by
  have done (stop : s.pending.head?.all (fun frame => !frame.isWork) = true) :
      ∃ t used, AdvancePrefix s t used [] ∧
        t.pending.head?.all (fun frame => !frame.isWork) = true :=
    ⟨s, 0, by intro fuel prior; simp, stop⟩
  generalize stack : s.pending = frames at route
  cases route with
  | empty => exact done (by rw [stack]; rfl)
  | resume => exact done (stack.symm ▸ boundary)
  | queue queue nonempty =>
    have lead (h : s.pending = .triggers queue :: rest) :
        ∃ t used, AdvancePrefix s t used [] ∧
          t.pending.head?.all (fun frame => !frame.isWork) = true := by
      obtain ⟨t, used, _, _, _, path, decisionStack, decision⟩ :=
        advance_triggers_to_decision s wf queue rest h reads (Or.inl nonempty)
      exact ⟨t, used, path, by simp [decisionStack, decision]⟩
    cases rest with
    | nil => exact lead stack
    | cons f tail =>
      have decision : f.isWork = false := by simpa using boundary
      by_cases outstanding : f.isResolution = true
      · exact done (by rw [stack]; simp [insertTriggers, outstanding, decision])
      · apply lead
        rw [stack]
        apply insertTriggers_front
        intro task head
        obtain rfl := Option.some.inj head
        refine ⟨by simpa using outstanding, ?_⟩
        intro q impossible
        cases impossible
        contradiction

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

end Riftbound

end
