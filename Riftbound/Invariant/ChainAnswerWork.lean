module

public import Riftbound.Invariant.ChainWork

/-!
# Answering effect decisions while resolving the Chain (I12)

Check the Runs actually scheduled by the answer. Process observation, then the chosen
program and its continuation up to the next decision or the empty stack.
-/

@[expose] public section

namespace Riftbound

/-- Follow the programs selected by an effect answer through chain completion. The observer
can stop earlier at a newly opened player decision or a game result. -/
theorem advance_observed_chain_runs_to_decision (raw : GameState) (notices : List Event)
    (wf : raw.WF) (reads : MightRead.database raw.cards) {body : List Frame} {item : ObjId}
    {tail original : List Frame} (pending : raw.pending = body ++ .finishSpell item :: tail)
    (supported : body.all runFrameSupported = true) (tracked : TriggerWorkTail original tail)
    (front : ∀ f, original.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : original.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  let finish := ResolutionPrefix [.finishSpell item] (TriggerWorkTail original)
  let runs := ResolutionPrefix body finish
  have finite (frame : Frame) (member : frame ∈ body) : frame.FiniteRun :=
    runFrameSupported_finite (List.all_eq_true.mp supported _ member)
  have insertFinish (stack : List Frame) (track : finish stack) (q : List PendTrigger) (ne : q ≠ []) :
      finish (insertTriggers q stack) :=
    track.insert (fun f member => (List.mem_singleton.mp member).symm ▸ rfl)
      (fun _ tail q ne => tail.insert front q ne) q ne
  have base : runs raw.pending := ⟨.finishSpell item :: tail, pending, ⟨tail, rfl, tracked⟩⟩
  obtain ⟨mid, used, earlier, entered, midWF, cards, route⟩ :=
    advance_observed_work raw notices wf reads
  have run (tracks : runs mid.pending) :
      ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
        t.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨t, later, events, path, stop⟩ :=
      advance_chain_runs_to_decision midWF (cards ▸ reads) tracks finite front decision
    exact ⟨t, used + later, earlier ++ events, entered.append path, stop⟩
  generalize stack : mid.pending = frames at route
  cases route with
  | empty => exact ⟨mid, used, earlier, entered, by rw [stack]; rfl⟩
  | resume => exact run (stack.symm ▸ base)
  | queue q ne => exact run (stack.symm ▸ base.insert (fun f member => (finite f member).isResolution) insertFinish q ne)

/-- Process the event observers and the Run prefix, then follow a retained continuation if
no decision interrupts it. -/
private theorem advance_observed_run_prefix_then_core (raw : GameState) (notices : List Event)
    {body : List Frame} {keeps : List Frame → Prop}
    (boundary : GameState → Prop)
    (accepted : ∀ t : GameState, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true → boundary t)
    (wf : raw.WF) (reads : MightRead.database raw.cards)
    (base : ResolutionPrefix body keeps raw.pending) (finite : ∀ f ∈ body, f.FiniteRun)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail))
    (resume : ∀ t : GameState, t.WF → MightRead.database t.cards → keeps t.pending →
      ∃ u used events, AdvancePrefix t u used events ∧ boundary u) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      boundary t := by
  obtain ⟨mid, entered, early, path, midWF, cards, route⟩ := advance_observed_work raw notices wf reads
  have run (now : ResolutionPrefix body keeps mid.pending) : ∃ t used events,
      AdvancePrefix (raw.withTriggers notices) t used events ∧ boundary t := by
    obtain ⟨after, elapsed, later, done, stop | ⟨tail, safe, known⟩⟩ :=
      advance_run_frames midWF (cards ▸ reads) now finite inserted
    · exact ⟨after, entered + elapsed, early ++ later, path.append done, accepted after stop⟩
    · obtain ⟨t, used, events, resumed, stop⟩ := resume after safe (known ▸ cards ▸ reads) tail
      exact ⟨t, entered + elapsed + used, (early ++ later) ++ events, (path.append done).append resumed, stop⟩
  generalize stack : mid.pending = frames at route
  cases route with
  | empty => exact ⟨mid, entered, early, path, accepted mid (GameState.prepared_idle_of_empty stack)⟩
  | resume => exact run (stack.symm ▸ base)
  | queue q ne => exact run (stack.symm ▸ base.insert (fun f h => (finite f h).isResolution) inserted q ne)

/-- Follow the observed Run prefix to a decision or its supplied continuation. -/
theorem advance_observed_run_prefix_then (raw : GameState) (notices : List Event)
    {body : List Frame} {keeps : List Frame → Prop}
    (wf : raw.WF) (reads : MightRead.database raw.cards)
    (base : ResolutionPrefix body keeps raw.pending) (finite : ∀ f ∈ body, f.FiniteRun)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail))
    (resume : ∀ t : GameState, t.WF → MightRead.database t.cards → keeps t.pending →
      ∃ u used events, AdvancePrefix t u used events ∧ u.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true :=
  advance_observed_run_prefix_then_core raw notices (fun t => t.pending.head?.all (fun f => !f.isWork) = true)
    (fun _ => GameState.idle_of_prepared) wf reads base finite inserted resume

/-- Follow the observed Run prefix and require a prepared decision from its continuation. -/
theorem advance_observed_run_prefix_then_prepared (raw : GameState) (notices : List Event)
    {body : List Frame} {keeps : List Frame → Prop}
    (wf : raw.WF) (reads : MightRead.database raw.cards)
    (base : ResolutionPrefix body keeps raw.pending) (finite : ∀ f ∈ body, f.FiniteRun)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail))
    (resume : ∀ t : GameState, t.WF → MightRead.database t.cards → keeps t.pending →
      ∃ u used events, AdvancePrefix t u used events ∧ u.preparePriority.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true :=
  advance_observed_run_prefix_then_core raw notices
    (fun t => t.preparePriority.pending.head?.all (fun f => !f.isWork) = true)
    (fun _ ready => ready) wf reads base finite inserted resume

/-- Run observed programs, handle their ordinary trigger queue, and resume the supplied
continuation if no decision interrupts it. -/
theorem advance_observed_runs_then (raw : GameState) (notices : List Event) {body rest : List Frame}
    (wf : raw.WF) (reads : MightRead.database raw.cards)
    (base : ResolutionPrefix body (TriggerWorkTail rest) raw.pending)
    (finite : ∀ f ∈ body, f.FiniteRun)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (resume : ∀ t : GameState, t.WF → MightRead.database t.cards → t.pending = rest →
      ∃ u used events, AdvancePrefix t u used events ∧ u.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  apply advance_observed_run_prefix_then raw notices wf reads base finite (fun _ track q ne => track.insert front q ne)
  intro state safe known tail
  obtain ⟨ready, queued, queuePath, stop | ⟨atRest, readyWF, readyCards⟩⟩ :=
    advance_trigger_tail state rest safe known tail
  · exact ⟨ready, queued, [], queuePath, stop⟩
  · obtain ⟨t, used, events, resumed, stop⟩ := resume ready readyWF (readyCards ▸ known) atRest
    exact ⟨t, queued + used, events, by simpa only [List.nil_append] using queuePath.append resumed, stop⟩

/-- Resolve observed Runs and any ordinary trigger queue before the prepared continuation. -/
theorem advance_observed_runs_then_prepared (raw : GameState) (notices : List Event) {body rest : List Frame}
    (wf : raw.WF) (reads : MightRead.database raw.cards)
    (base : ResolutionPrefix body (TriggerWorkTail rest) raw.pending)
    (finite : ∀ f ∈ body, f.FiniteRun)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (resume : ∀ t : GameState, t.WF → MightRead.database t.cards → t.pending = rest →
      ∃ u used events, AdvancePrefix t u used events ∧ u.preparePriority.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  apply advance_observed_run_prefix_then_prepared raw notices wf reads base finite (fun _ track q ne => track.insert front q ne)
  intro state safe known tail
  obtain ⟨ready, queued, queuePath, stop | ⟨atRest, readyWF, readyCards⟩⟩ :=
    advance_trigger_tail_prepared state rest safe known tail
  · exact ⟨ready, queued, [], queuePath, stop⟩
  · obtain ⟨t, used, events, resumed, stop⟩ := resume ready readyWF (readyCards ▸ known) atRest
    exact ⟨t, queued + used, events, by simpa only [List.nil_append] using queuePath.append resumed, stop⟩

/-- Lift the observed work after a raw decision to the declared action. Surcharge
payment preserves the card database and the pending frames. -/
private theorem advance_observed_frame_until {s raw : GameState} {a : Action} {notices : List Event}
    (boundary : GameState → Prop)
    (noCostChoice : s.actionDeathCostChoice a = none) (regular : a.kind ≠ .concede)
    (applied : applyFrame0 s a = some (raw, notices)) (rawWF : raw.WF)
    (reads : MightRead.database raw.cards)
    (run : let next := s.paySurcharge a raw
      let observed := (notices ++ extraEvents a notices) ++ s.actionTransitionEvents next a
      next.WF → MightRead.database next.cards → next.pending = raw.pending →
      ∃ t used events, AdvancePrefix (next.withTriggers observed) t used events ∧
        boundary t) :
    ∃ initial initialEvents t used events, applyDeclaredAction s a = some (initial, initialEvents) ∧
      AdvancePrefix initial t used events ∧ boundary t := by
  let next := s.paySurcharge a raw
  let events := notices ++ extraEvents a notices
  let observed := events ++ s.actionTransitionEvents next a
  have surcharge := GameState.paySurcharge_poolStep s a raw
  have same : next.cards = raw.cards := by
    rcases surcharge with h | ⟨p, pool, h⟩ <;>
      (have cards := congrArg GameState.cards h; exact cards)
  have answer : applyDeclaredAction s a = some (next.withTriggers observed, events) := by
    unfold applyDeclaredAction
    rw [noCostChoice]
    simp only [applyAction_of_ne regular, applyFrame, applied, Option.map_some, next, events, observed]
  obtain ⟨t, fuel, emitted, path, stopped⟩ :=
    run (surcharge.wf rawWF) (same ▸ reads) surcharge.pending_eq
  exact ⟨_, _, t, fuel, emitted, answer, path, stopped⟩

/-- Lift the raw rule transition and its observations to the declared action. -/
theorem advance_observed_frame_to_decision {s raw : GameState} {a : Action} {notices : List Event}
    (noCostChoice : s.actionDeathCostChoice a = none) (regular : a.kind ≠ .concede)
    (applied : applyFrame0 s a = some (raw, notices)) (rawWF : raw.WF)
    (reads : MightRead.database raw.cards)
    (run : let next := s.paySurcharge a raw
      let observed := (notices ++ extraEvents a notices) ++ s.actionTransitionEvents next a
      next.WF → MightRead.database next.cards → next.pending = raw.pending →
      ∃ t used events, AdvancePrefix (next.withTriggers observed) t used events ∧
        t.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ initial initialEvents t used events, applyDeclaredAction s a = some (initial, initialEvents) ∧
      AdvancePrefix initial t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true :=
  advance_observed_frame_until (fun t => t.pending.head?.all (fun f => !f.isWork) = true)
    noCostChoice regular applied rawWF reads run

/-- Lift the observed work after a raw decision to the actual legal action. Surcharge
payment preserves the card database and the pending frames. -/
theorem step_observed_frame_to_decision {s raw : GameState} {a : Action} {notices : List Event}
    (legal : Legal s a) (noCostChoice : s.actionDeathCostChoice a = none) (regular : a.kind ≠ .concede)
    (applied : applyFrame0 s a = some (raw, notices)) (rawWF : raw.WF)
    (reads : MightRead.database raw.cards)
    (run : let next := s.paySurcharge a raw
      let observed := (notices ++ extraEvents a notices) ++ s.actionTransitionEvents next a
      next.WF → MightRead.database next.cards → next.pending = raw.pending →
      ∃ t used events, AdvancePrefix (next.withTriggers observed) t used events ∧
        t.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  obtain ⟨_, before, t, used, events, declared, path, stopped⟩ :=
    advance_observed_frame_to_decision noCostChoice regular applied rawWF reads run
  refine ⟨t, used, before ++ events, stopped, fun extra => ?_⟩
  simp only [step, ite_eq_left legal, declared]
  exact path extra before

/-- Lift observed work ending at a prepared decision to the declared action. -/
theorem advance_observed_frame_to_preparedDecision {s raw : GameState} {a : Action} {notices : List Event}
    (noCostChoice : s.actionDeathCostChoice a = none) (regular : a.kind ≠ .concede)
    (applied : applyFrame0 s a = some (raw, notices)) (rawWF : raw.WF)
    (reads : MightRead.database raw.cards)
    (run : let next := s.paySurcharge a raw
      let observed := (notices ++ extraEvents a notices) ++ s.actionTransitionEvents next a
      next.WF → MightRead.database next.cards → next.pending = raw.pending →
      ∃ t used events, AdvancePrefix (next.withTriggers observed) t used events ∧
        t.preparePriority.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ initial initialEvents t used events, applyDeclaredAction s a = some (initial, initialEvents) ∧
      AdvancePrefix initial t used events ∧ t.preparePriority.pending.head?.all (fun f => !f.isWork) = true :=
  advance_observed_frame_until (fun t => t.preparePriority.pending.head?.all (fun f => !f.isWork) = true)
    noCostChoice regular applied rawWF reads run

/-- A legal action succeeds with the fuel used by its observed work when the destination
is already a prepared decision. The returned event list includes the action's own events. -/
theorem step_observed_frame_to_preparedDecision {s raw : GameState} {a : Action} {notices : List Event}
    (legal : Legal s a) (noCostChoice : s.actionDeathCostChoice a = none) (regular : a.kind ≠ .concede)
    (applied : applyFrame0 s a = some (raw, notices)) (rawWF : raw.WF)
    (reads : MightRead.database raw.cards)
    (run : let next := s.paySurcharge a raw
      let observed := (notices ++ extraEvents a notices) ++ s.actionTransitionEvents next a
      next.WF → MightRead.database next.cards → next.pending = raw.pending →
      ∃ t used events, AdvancePrefix (next.withTriggers observed) t used events ∧
        t.preparePriority.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
  obtain ⟨_, before, t, used, events, declared, path, ready⟩ :=
    advance_observed_frame_to_preparedDecision noCostChoice regular applied rawWF reads run
  refine ⟨t, used, before ++ events, ready, ?_, ?_⟩
  · intro extra
    simp only [step, ite_eq_left legal, declared]
    exact path extra before
  · simp only [step, ite_eq_left legal, declared]
    exact path.finish ready before

/-- Run action observers and any ordinary trigger queue when the raw action is already
waiting at a decision. -/
theorem step_observed_action_waits {s raw : GameState} {a : Action} {notices : List Event}
    (legal : Legal s a) (ordinary : a.kind ≠ .concede)
    (noCost : s.actionDeathCostChoice a = none) (applied : applyFrame0 s a = some (raw, notices))
    (wf : raw.WF) (reads : MightRead.database raw.cards)
    (waiting : raw.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  apply step_observed_frame_to_decision legal noCost ordinary applied wf reads
  intro next observed safe checked stack
  obtain ⟨mid, used, added, entered, midWF, cards, route⟩ :=
    advance_observed_work next observed safe checked
  obtain ⟨t, more, run, stop⟩ :=
    advance_observed_decision mid next.pending midWF (cards ▸ checked) route (stack.symm ▸ waiting)
  exact ⟨t, used + more, added, by simpa only [List.append_nil] using entered.append run, stop⟩

/-- Apply the action's event observers before continuing from an ordinary decision. If
preparation finds outstanding Cleanup at neutral priority, it runs before the decision. -/
theorem step_observed_waiting_to_preparedDecision {s raw : GameState} {a : Action} {notices : List Event}
    (legal : Legal s a) (regular : a.kind ≠ .concede) (noCost : s.actionDeathCostChoice a = none)
    (applied : applyFrame0 s a = some (raw, notices)) (wf : raw.WF) (reads : MightRead.database raw.cards)
    (waiting : raw.pending.head?.all (fun f => !f.isWork) = true)
    (quiet : ∀ p tail, raw.pending = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
  apply step_observed_frame_to_preparedDecision legal noCost regular applied wf reads
  intro next observed safe checked stack
  obtain ⟨mid, used, events, path, midWF, cards, route⟩ :=
    advance_observed_work next observed safe checked
  rw [stack] at route
  by_cases neutral : ∃ p tail, raw.pending = .priority p :: tail
  · obtain ⟨p, tail, priority⟩ := neutral
    rw [priority] at route
    generalize actual : mid.pending = frames at route
    cases route with
    | empty => exact ⟨mid, used, events, path, GameState.prepared_idle_of_empty actual⟩
    | resume =>
      obtain ⟨t, later, emitted, more, ready⟩ :=
        advance_waiting_to_preparedDecision midWF (cards ▸ checked) (by rw [actual]; rfl)
          (fun q suffix same => by
            rw [actual, List.cons.injEq] at same
            exact same.2 ▸ quiet p tail priority)
      exact ⟨t, used + later, events ++ emitted, path.append more, ready⟩
    | queue q nonempty =>
      have pending : mid.pending = .triggers q :: .priority p :: tail := actual
      obtain ⟨t, later, _, _, _, more, _, _, ready⟩ :=
        advance_triggers_to_preparedDecision mid midWF q _ pending (cards ▸ checked) (Or.inl nonempty)
      exact ⟨t, used + later, events, by simpa only [List.append_nil] using path.append more, ready⟩
  · obtain ⟨t, later, more, ready⟩ :=
      advance_observed_prepared_decision mid raw.pending midWF (cards ▸ checked) route waiting
        (fun p tail same => neutral ⟨p, tail, same⟩)
    exact ⟨t, used + later, events, by simpa only [List.append_nil] using path.append more, ready⟩

/-- The three effect decisions that resume with a Run program. -/
def isChainEffectAnswer (s : GameState) (a : Action) : Bool :=
  match s.pending.head?, a.kind with
  | some (.eitherDo ..), .decide _ | some (.mayDo ..), .decide _ | some (.pickDo ..), .choose _ => true
  | _, _ => false

/-- The stack is empty or a non-resolution decision is at its head. -/
def isOrdinaryDecisionTail (frames : List Frame) : Bool :=
  frames.head?.all (fun f => !f.isWork && !f.isResolution)

/-- Find the waiting decision tail, beneath a nonempty ordinary trigger queue if present. -/
def chainAnswerContinuation? : List Frame → Option (List Frame)
  | .triggers q :: rest => if !q.isEmpty && isOrdinaryDecisionTail rest then some rest else none
  | rest => if isOrdinaryDecisionTail rest then some rest else none

/-- A parsed continuation describes the actual waiting decision and any trigger queue. -/
theorem chainAnswerContinuation_sound {tail rest : List Frame}
    (ready : chainAnswerContinuation? tail = some rest) :
    TriggerWorkTail rest tail ∧ isOrdinaryDecisionTail rest = true := by
  unfold chainAnswerContinuation? at ready
  split at ready
  · rename_i queue suffix
    split at ready
    · rename_i valid
      obtain rfl := Option.some.inj ready
      have both := Bool.and_eq_true_iff.mp valid
      exact ⟨Or.inr ⟨queue, by intro e; simp [e] at both, rfl⟩, both.2⟩
    · contradiction
  · split at ready
    · obtain rfl := Option.some.inj ready
      exact ⟨Or.inl rfl, by assumption⟩
    · contradiction

/-- The ordinary decision permits trigger insertion immediately in front of it. -/
theorem isOrdinaryDecisionTail_front {rest : List Frame} (ready : isOrdinaryDecisionTail rest = true) :
    ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
  intro f head
  have both : (!f.isWork) = true ∧ (!f.isResolution) = true := by
    simpa only [isOrdinaryDecisionTail, head, Option.all_some, Bool.and_eq_true_iff] using ready
  refine ⟨by simpa using both.2, ?_⟩
  intro q isTriggers
  cases isTriggers
  cases both.1

/-- The dispatcher stops at an ordinary decision. -/
theorem isOrdinaryDecisionTail_boundary {rest : List Frame} (ready : isOrdinaryDecisionTail rest = true) :
    rest.head?.all (fun f => !f.isWork) = true := by
  cases head : rest.head? with
  | none => rfl
  | some f =>
    simp only [isOrdinaryDecisionTail, head, Option.all_some, Bool.and_eq_true_iff] at ready
    exact ready.1

/-- An effect answer replaces its decision frame directly and preserves the card database. -/
theorem chainEffectAnswer_rule {s raw : GameState} {a : Action} {events : List Event}
    (effect : isChainEffectAnswer s a = true) (applied : applyFrame0 s a = some (raw, events)) :
    s.actionDeathCostChoice a = none ∧ a.kind ≠ .concede ∧ raw.cards = s.cards := by
  cases stack : s.pending with
  | nil => simp [isChainEffectAnswer, stack] at effect
  | cons frame rest =>
    cases frame <;> simp [isChainEffectAnswer, stack] at effect
    all_goals
      cases kind : a.kind <;> simp [kind] at effect
      refine ⟨by simp [GameState.actionDeathCostChoice, stack], by simp, ?_⟩
      simp only [applyFrame0, stack, kind, Option.some.injEq, Prod.mk.injEq] at applied
      rw [← applied.1]

/-- Chance supplies the order of Main Deck cards Recycled from the Trash. -/
def isTrashRecycleOrderAnswer (s : GameState) (a : Action) : Bool :=
  match s.pending.head?, a.kind with
  | some (.chanceRecycleTrash ..), .arrange _ => true
  | _, _ => false

/-- Predict choices supply a card decision or an order for the cards to be Recycled. -/
def isPredictionAnswer (s : GameState) (a : Action) : Bool :=
  match s.pending.head?, a.kind with
  | some (.predict ..), .predictPick .. | some (.chancePredict ..), .arrange _ => true
  | _, _ => false

/-- A Predict decision preserves the card database and cannot start a payment replacement. -/
theorem predictionAnswer_rule {s raw : GameState} {a : Action} {events : List Event}
    (prediction : isPredictionAnswer s a = true) (applied : applyFrame0 s a = some (raw, events)) :
    s.actionDeathCostChoice a = none ∧ a.kind ≠ .concede ∧ raw.cards = s.cards := by
  cases pending : s.pending with
  | nil => simp [isPredictionAnswer, pending] at prediction
  | cons frame rest =>
    cases frame <;> simp [isPredictionAnswer, pending] at prediction
    all_goals
      cases kind : a.kind <;> simp [kind] at prediction
    case predict.predictPick p n first more top bottom id recycle =>
      simp only [applyFrame0, pending, kind, Option.some.injEq, Prod.mk.injEq] at applied
      have same := (continuePrediction_safe s p n ((first :: more).erase id)
        (if recycle then top else top ++ [id]) (if recycle then id :: bottom else bottom)).same
      unfold SameMeta at same
      have cards := congrArg GameState.cards same
      exact ⟨by simp [GameState.actionDeathCostChoice, pending], by simp,
        (congrArg GameState.cards applied.1.symm).trans cards⟩
    case chancePredict.arrange p n top _ bottom =>
      simp only [applyFrame0, pending, kind, Option.some.injEq, Prod.mk.injEq] at applied
      have same := (completePrediction_safe s p n top bottom).same
      unfold SameMeta at same
      have cards := congrArg GameState.cards same
      exact ⟨by simp [GameState.actionDeathCostChoice, pending], by simp,
        (congrArg GameState.cards applied.1.symm).trans cards⟩

/-- Name and card-type guesses provide a selection for the remaining Run program. -/
def isNamedChoiceAnswer (s : GameState) (a : Action) : Bool :=
  match s.pending.head?, a.kind with
  | some (.nameCard ..), .nameCard _ | some (.guessCardType ..), .guessCardType _ => true
  | _, _ => false

/-- A name or guess replaces its decision and preserves the card database. -/
theorem namedChoiceAnswer_rule {s raw : GameState} {a : Action} {events : List Event}
    (named : isNamedChoiceAnswer s a = true) (applied : applyFrame0 s a = some (raw, events)) :
    s.actionDeathCostChoice a = none ∧ a.kind ≠ .concede ∧ raw.cards = s.cards := by
  cases pending : s.pending with
  | nil => simp [isNamedChoiceAnswer, pending] at named
  | cons frame rest =>
    cases frame <;> simp [isNamedChoiceAnswer, pending] at named
    all_goals
      cases kind : a.kind <;> simp [kind] at named
      refine ⟨by simp [GameState.actionDeathCostChoice, pending], by simp, ?_⟩
      simp only [applyFrame0, pending, kind, Option.some.injEq, Prod.mk.injEq] at applied
      rw [← applied.1]

/-- Answers that resume a Run program or continue an existing effect or chance decision. -/
def isRunProgramAnswer (s : GameState) (a : Action) : Bool :=
  isChainEffectAnswer s a ||
    (isPredictionAnswer s a || (isNamedChoiceAnswer s a || isTrashRecycleOrderAnswer s a))

/-- A program answer uses the open frame directly and preserves the card database. -/
theorem runProgramAnswer_rule {s raw : GameState} {a : Action} {events : List Event}
    (answer : isRunProgramAnswer s a = true) (applied : applyFrame0 s a = some (raw, events)) :
    s.actionDeathCostChoice a = none ∧ a.kind ≠ .concede ∧ raw.cards = s.cards := by
  rcases Bool.or_eq_true_iff.mp answer with effect | other
  · exact chainEffectAnswer_rule effect applied
  rcases Bool.or_eq_true_iff.mp other with predict | other
  · exact predictionAnswer_rule predict applied
  rcases Bool.or_eq_true_iff.mp other with named | order
  · exact namedChoiceAnswer_rule named applied
  cases stack : s.pending with
  | nil => simp [isTrashRecycleOrderAnswer, stack] at order
  | cons frame rest =>
    cases frame <;> simp [isTrashRecycleOrderAnswer, stack] at order
    case chanceRecycleTrash =>
      cases kind : a.kind <;> simp [kind] at order
      case arrange ids =>
        simp only [applyFrame0, stack, kind, Option.some.injEq, Prod.mk.injEq] at applied
        have preserved := (recycleTrashCards_safe s ids).same
        unfold SameMeta at preserved
        have cards := congrArg GameState.cards preserved
        exact ⟨by simp [GameState.actionDeathCostChoice, stack], by simp,
          (congrArg GameState.cards applied.1.symm).trans cards⟩

/-- Check that the Predict answer leads directly to the next input before leaving Predict. -/
def predictAnswerWaits (s : GameState) (a : Action) : Bool :=
  isPredictionAnswer s a && (applyFrame0 s a).any (fun outcome =>
    outcome.1.pending.head?.all (fun f => !f.isWork))

/-- Continue a Predict decision whose rule output is already waiting for a decision. -/
theorem step_predictAnswer_waits_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (checked : predictAnswerWaits s a = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  unfold predictAnswerWaits at checked
  obtain ⟨isPredict, wait⟩ := Bool.and_eq_true_iff.mp checked
  cases applied : applyFrame0 s a with
  | none => simp [applied] at wait
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some] at wait
    obtain ⟨noCost, regular, cards⟩ := predictionAnswer_rule isPredict applied
    exact step_observed_action_waits legal regular noCost applied
      (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads) wait

/-- A Predict answer that returns directly to a waiting decision includes any Cleanup
needed to prepare ordinary priority. -/
theorem step_predictAnswer_waits_to_preparedDecision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (checked : predictAnswerWaits s a = true)
    (quiet : ∀ raw emitted p tail, applyFrame0 s a = some (raw, emitted) →
      raw.pending = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
  unfold predictAnswerWaits at checked
  obtain ⟨isPredict, wait⟩ := Bool.and_eq_true_iff.mp checked
  cases applied : applyFrame0 s a with
  | none => simp [applied] at wait
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some] at wait
    obtain ⟨noCost, regular, cards⟩ := predictionAnswer_rule isPredict applied
    exact step_observed_waiting_to_preparedDecision legal regular noCost applied
      (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads) wait
      (fun p tail => quiet raw events p tail applied)

/-- Inspect the actual Runs scheduled by a choice on the Chain. The check also recognizes the
item finish and a waiting decision, with or without an ordinary trigger queue. -/
def chainAnswerWorkSupported (s : GameState) (a : Action) : Bool :=
  isRunProgramAnswer s a && ((applyFrame0 s a).any fun result =>
    (result.1.pending.takeWhile isRunFrame).all runFrameSupported &&
      match result.1.pending.dropWhile isRunFrame with
      | .finishSpell _ :: tail => (chainAnswerContinuation? tail).isSome
      | _ => false)

private theorem chainAnswerWorkSupported_sound {s : GameState} {a : Action}
    (supported : chainAnswerWorkSupported s a = true) :
    ∃ raw events item tail original, applyFrame0 s a = some (raw, events) ∧
      isRunProgramAnswer s a = true ∧ (raw.pending.takeWhile isRunFrame).all runFrameSupported = true ∧
      raw.pending.dropWhile isRunFrame = .finishSpell item :: tail ∧ chainAnswerContinuation? tail = some original := by
  unfold chainAnswerWorkSupported at supported
  obtain ⟨effect, body⟩ := Bool.and_eq_true_iff.mp supported
  cases applied : applyFrame0 s a with
  | none => simp [applied] at body
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some, Bool.and_eq_true_iff] at body
    obtain ⟨programs, finishes⟩ := body
    split at finishes
    · rename_i item tail layout
      cases parsed : chainAnswerContinuation? tail with
      | none => simp [parsed] at finishes
      | some original => exact ⟨raw, events, item, tail, original, rfl, effect, programs, layout, parsed⟩
    · contradiction

/-- A checked legal program answer on the Chain reaches the next
decision through the actual dispatcher. Any later Cleanup consumes the remaining fuel. -/
theorem step_chainAnswer_checked_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : chainAnswerWorkSupported s a = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  obtain ⟨raw, _, item, tail, _, applied, effect, programs, layout, parsed⟩ :=
    chainAnswerWorkSupported_sound supported
  obtain ⟨tracked, ready⟩ := chainAnswerContinuation_sound parsed
  obtain ⟨noCost, regular, cards⟩ := runProgramAnswer_rule effect applied
  have rawWF := applyFrame_wf0 wf (legal.frame regular) applied
  have pending : raw.pending = raw.pending.takeWhile isRunFrame ++ .finishSpell item :: tail := by
    rw [← layout, List.takeWhile_append_dropWhile]
  apply step_observed_frame_to_decision legal noCost regular applied rawWF (cards.symm ▸ reads)
  intro next observed safe checked stack
  exact advance_observed_chain_runs_to_decision next observed safe checked
    (stack.trans pending) programs tracked (isOrdinaryDecisionTail_front ready)
    (isOrdinaryDecisionTail_boundary ready)

/-- A checked answer finishing a Chain item reaches a prepared decision, including any
deferred declarations and ordinary priority Cleanup. -/
theorem step_chainAnswer_checked_to_preparedDecision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : chainAnswerWorkSupported s a = true)
    (quiet : ∀ raw emitted item tail p rest, applyFrame0 s a = some (raw, emitted) →
      raw.pending.dropWhile isRunFrame = .finishSpell item :: tail →
      chainAnswerContinuation? tail = some (.priority p :: rest) → ∀ f ∈ rest, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
  obtain ⟨raw, events, item, tail, original, applied, effect, programs, layout, parsed⟩ :=
    chainAnswerWorkSupported_sound supported
  obtain ⟨tracked, ready⟩ := chainAnswerContinuation_sound parsed
  obtain ⟨noCost, regular, cards⟩ := runProgramAnswer_rule effect applied
  have pending : raw.pending = raw.pending.takeWhile isRunFrame ++ .finishSpell item :: tail := by
    rw [← layout, List.takeWhile_append_dropWhile]
  have front := isOrdinaryDecisionTail_front ready
  apply step_observed_frame_to_preparedDecision legal noCost regular applied
    (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads)
  intro next observed safe checked stack
  refine advance_observed_run_prefix_then_prepared next observed safe checked
    (keeps := ResolutionPrefix [.finishSpell item] (TriggerWorkTail original))
    ⟨_, stack.trans pending, tail, rfl, tracked⟩
    (fun f member => runFrameSupported_finite (List.all_eq_true.mp programs f member)) ?_ ?_
  · intro _ kept q ne
    exact kept.insert (fun f member => (List.mem_singleton.mp member).symm ▸ rfl)
      (fun _ route added nonempty => route.insert front added nonempty) q ne
  · intro _ wellFormed known kept
    obtain ⟨_, finishing, queued⟩ := kept
    exact (advance_finish_chain_until_decision wellFormed known finishing queued front).atPreparedDecision known
      (isOrdinaryDecisionTail_boundary ready)
      (fun p rest priority => quiet raw events item tail p rest applied layout (parsed.trans (congrArg some priority)))

/-- Check effect answers that return straight to a decision after their generated Runs. -/
def decisionRunAnswerWorkSupported (s : GameState) (a : Action) : Bool :=
  isRunProgramAnswer s a && (applyFrame0 s a).any (fun result =>
    (result.1.pending.takeWhile isRunFrame).all runFrameSupported &&
      (chainAnswerContinuation? (result.1.pending.dropWhile isRunFrame)).isSome)

/-- Run a checked program answer whose continuation is an ordinary decision,
possibly preceded by a trigger queue. -/
theorem step_decisionRunAnswer_checked_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : decisionRunAnswerWorkSupported s a = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  unfold decisionRunAnswerWorkSupported at supported
  obtain ⟨answer, condition⟩ := Bool.and_eq_true_iff.mp supported
  cases applied : applyFrame0 s a with
  | none => simp [applied] at condition
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some, Bool.and_eq_true_iff] at condition
    obtain ⟨programs, continuation⟩ := condition
    cases parsed : chainAnswerContinuation? (raw.pending.dropWhile isRunFrame) with
    | none => simp [parsed] at continuation
    | some rest =>
      obtain ⟨tracked, ready⟩ := chainAnswerContinuation_sound parsed
      obtain ⟨noCost, regular, cards⟩ := runProgramAnswer_rule answer applied
      apply step_observed_frame_to_decision legal noCost regular applied
        (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads)
      intro next observed safe checked stack
      refine advance_observed_runs_then next observed safe checked
        ⟨_, stack.trans List.takeWhile_append_dropWhile.symm, tracked⟩
        (fun f member => runFrameSupported_finite (List.all_eq_true.mp programs f member))
        (isOrdinaryDecisionTail_front ready) ?_
      intro t _ _ resumed
      exact ⟨t, 0, [], by intro fuel prior; simp, resumed.symm ▸ isOrdinaryDecisionTail_boundary ready⟩

/-- A checked program answer and its trigger queue reach a prepared decision in finite fuel. -/
theorem step_decisionRunAnswer_checked_to_preparedDecision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : decisionRunAnswerWorkSupported s a = true)
    (quiet : ∀ raw emitted p tail, applyFrame0 s a = some (raw, emitted) →
      chainAnswerContinuation? (raw.pending.dropWhile isRunFrame) = some (.priority p :: tail) →
      ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
  unfold decisionRunAnswerWorkSupported at supported
  obtain ⟨answer, condition⟩ := Bool.and_eq_true_iff.mp supported
  cases applied : applyFrame0 s a with
  | none => simp [applied] at condition
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some, Bool.and_eq_true_iff] at condition
    obtain ⟨programs, continuation⟩ := condition
    cases parsed : chainAnswerContinuation? (raw.pending.dropWhile isRunFrame) with
    | none => simp [parsed] at continuation
    | some rest =>
      obtain ⟨tracked, ready⟩ := chainAnswerContinuation_sound parsed
      obtain ⟨noCost, regular, cards⟩ := runProgramAnswer_rule answer applied
      apply step_observed_frame_to_preparedDecision legal noCost regular applied
        (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads)
      intro next observed safe checked stack
      refine advance_observed_runs_then_prepared next observed safe checked
        ⟨_, stack.trans List.takeWhile_append_dropWhile.symm, tracked⟩
        (fun f member => runFrameSupported_finite (List.all_eq_true.mp programs f member))
        (isOrdinaryDecisionTail_front ready) ?_
      intro t safe checked resumed
      exact advance_waiting_to_preparedDecision safe checked (resumed.symm ▸ isOrdinaryDecisionTail_boundary ready)
        (fun p tail priority => quiet raw events p tail applied
          (parsed.trans (congrArg some (resumed.symm.trans priority))))

/-- Finish a checked Play and its Chain item, then prepare the next input.
The check is performed on the live Run that begins resolving the item. -/
theorem advance_effectPlayChain_to_preparedDecision {s : GameState} {item : ObjId}
    {tail original : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (checked : effectPlayRunSupported s = true)
    (stack : s.pending.tail = .finishSpell item :: tail) (tracked : TriggerWorkTail original tail)
    (ready : isOrdinaryDecisionTail original = true)
    (quiet : ∀ p rest, original = .priority p :: rest → ∀ f ∈ rest, f.observesCombat = false) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      advance used s [] = .ok (t, events) := by
  let reachable := ResolutionPrefix [.finishSpell item] (TriggerWorkTail original)
  have front := isOrdinaryDecisionTail_front ready
  have keep : reachable s.pending.tail := ⟨tail, stack, tracked⟩
  have insert (pending : List Frame) (held : reachable pending) (q : List PendTrigger) (ne : q ≠ []) :
      reachable (insertTriggers q pending) :=
    held.insert (fun f member => (List.mem_singleton.mp member).symm ▸ rfl)
      (fun _ route added nonempty => route.insert front added nonempty) q ne
  have ran := advance_effectPlayRun_checked wf reads checked keep insert
  have finished : AdvanceTo s (· = original) := ran.then reads (fun _ safe known held => by
    obtain ⟨_, pending, waiting⟩ := held
    exact advance_finish_chain_until_decision safe known pending waiting front)
  obtain ⟨t, used, events, path, prepared⟩ :=
    finished.atPreparedDecision reads (isOrdinaryDecisionTail_boundary ready) quiet
  exact ⟨t, used, events, path, prepared, by simpa using path.finish prepared []⟩

/-- Finish a checked permanent Play using the common Chain continuation. -/
theorem advance_permanentPlayChain_to_preparedDecision {s : GameState} {item : ObjId}
    {tail original : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (checked : permanentPlayRunSupported s = true)
    (stack : s.pending.tail = .finishSpell item :: tail) (tracked : TriggerWorkTail original tail)
    (ready : isOrdinaryDecisionTail original = true)
    (quiet : ∀ p rest, original = .priority p :: rest → ∀ f ∈ rest, f.observesCombat = false) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      advance used s [] = .ok (t, events) :=
  advance_effectPlayChain_to_preparedDecision wf reads (Bool.or_eq_true_iff.mpr (Or.inl checked))
    stack tracked ready quiet

/-- Lift the checked Play back through the actual final Pass and its first
automatic step, retaining the events from all three transitions. -/
theorem step_effectPlayChain_to_preparedDecision {s initial running : GameState} {p : PlayerId}
    {before resolving : List Event} {workTail tail original : List Frame} {item : ObjId}
    (wf : s.WF) (legal : Legal s ⟨.player p, .pass⟩)
    (declared : applyDeclaredAction s ⟨.player p, .pass⟩ = some (initial, before))
    (scheduled : initial.pending = .resolveChain :: workTail)
    (opened : workStep initial = some (running, resolving))
    (reads : MightRead.database running.cards) (checked : effectPlayRunSupported running = true)
    (stack : running.pending.tail = .finishSpell item :: tail) (tracked : TriggerWorkTail original tail)
    (ready : isOrdinaryDecisionTail original = true)
    (quiet : ∀ q rest, original = .priority q :: rest → ∀ f ∈ rest, f.observesCombat = false) :
    ∃ t used events, 0 < used ∧ t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.player p, .pass⟩ = advance extra t events) ∧
      step used s ⟨.player p, .pass⟩ = .ok (t, events) := by
  have safe := workStep_wf (applyDeclaredAction_wf wf legal declared) opened
  obtain ⟨t, used, events, path, prepared, _⟩ :=
    advance_effectPlayChain_to_preparedDecision safe reads checked stack tracked ready quiet
  have pathFromPass := path.prepend scheduled rfl opened
  refine ⟨t, used + 1, before ++ (resolving ++ events), by omega, prepared, ?_, ?_⟩
  · intro extra
    simp only [step, ite_eq_left legal, declared]
    exact pathFromPass extra before
  · simp only [step, ite_eq_left legal, declared]
    exact pathFromPass.finish prepared before

/-- The permanent Play case of the checked final Pass. -/
theorem step_permanentPlayChain_to_preparedDecision {s initial running : GameState} {p : PlayerId}
    {before resolving : List Event} {workTail tail original : List Frame} {item : ObjId}
    (wf : s.WF) (legal : Legal s ⟨.player p, .pass⟩)
    (declared : applyDeclaredAction s ⟨.player p, .pass⟩ = some (initial, before))
    (scheduled : initial.pending = .resolveChain :: workTail)
    (opened : workStep initial = some (running, resolving))
    (reads : MightRead.database running.cards) (checked : permanentPlayRunSupported running = true)
    (stack : running.pending.tail = .finishSpell item :: tail) (tracked : TriggerWorkTail original tail)
    (ready : isOrdinaryDecisionTail original = true)
    (quiet : ∀ q rest, original = .priority q :: rest → ∀ f ∈ rest, f.observesCombat = false) :
    ∃ t used events, 0 < used ∧ t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.player p, .pass⟩ = advance extra t events) ∧
      step used s ⟨.player p, .pass⟩ = .ok (t, events) :=
  step_effectPlayChain_to_preparedDecision wf legal declared scheduled opened reads
    (Bool.or_eq_true_iff.mpr (Or.inl checked)) stack tracked ready quiet

end Riftbound

end
