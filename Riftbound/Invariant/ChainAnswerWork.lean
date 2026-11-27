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

/-- Complete a legal effect answer whose raw action schedules checked Run frames followed
by the current Chain item's finish. -/
private theorem step_observed_chain_answer_to_decision {s raw : GameState} {a : Action} {notices : List Event}
    {body tail original : List Frame} {item : ObjId} (legal : Legal s a)
    (noCostChoice : s.actionDeathCostChoice a = none) (regular : a.kind ≠ .concede)
    (applied : applyFrame0 s a = some (raw, notices)) (rawWF : raw.WF)
    (reads : MightRead.database raw.cards) (pending : raw.pending = body ++ .finishSpell item :: tail)
    (supported : body.all runFrameSupported = true) (tracked : TriggerWorkTail original tail)
    (front : ∀ f, original.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : original.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = .ok (t, events) := by
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
    advance_observed_chain_runs_to_decision next observed (surcharge.wf rawWF) (same ▸ reads)
      (surcharge.pending_eq.trans pending) supported tracked front decision
  have finished : step fuel s a = .ok (t, events ++ emitted) := by
    simp only [step, ite_eq_left legal, answer]
    exact path.finish stopped events
  exact ⟨t, fuel, _, stopped, fun extra => step_mono finished (Nat.le_add_right _ extra)⟩

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

private theorem chainAnswerContinuation_sound {tail rest : List Frame}
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

private theorem isOrdinaryDecisionTail_front {rest : List Frame} (ready : isOrdinaryDecisionTail rest = true) :
    ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
  intro f head
  have both : (!f.isWork) = true ∧ (!f.isResolution) = true := by
    simpa only [isOrdinaryDecisionTail, head, Option.all_some, Bool.and_eq_true_iff] using ready
  refine ⟨by simpa using both.2, ?_⟩
  intro q isTriggers
  cases isTriggers
  cases both.1

private theorem isOrdinaryDecisionTail_boundary {rest : List Frame} (ready : isOrdinaryDecisionTail rest = true) :
    rest.head?.all (fun f => !f.isWork) = true := by
  cases head : rest.head? with
  | none => rfl
  | some f =>
    simp only [isOrdinaryDecisionTail, head, Option.all_some, Bool.and_eq_true_iff] at ready
    exact ready.1

private theorem chainEffectAnswer_rule {s raw : GameState} {a : Action} {events : List Event}
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

/-- Inspect the actual Runs scheduled by a choice on the Chain. The check also recognizes the
item finish and a waiting decision, with or without an ordinary trigger queue. -/
def chainAnswerWorkSupported (s : GameState) (a : Action) : Bool :=
  isChainEffectAnswer s a && ((applyFrame0 s a).any fun result =>
    (result.1.pending.takeWhile isRunFrame).all runFrameSupported &&
      match result.1.pending.dropWhile isRunFrame with
      | .finishSpell _ :: tail => (chainAnswerContinuation? tail).isSome
      | _ => false)

/-- A checked legal answer to an optional effect, a branch choice or an object selection reaches
the next decision through the actual dispatcher. Additional fuel gives the same state and log. -/
theorem step_chainAnswer_checked_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : chainAnswerWorkSupported s a = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = .ok (t, events) := by
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
      | some original =>
        obtain ⟨tracked, ready⟩ := chainAnswerContinuation_sound parsed
        obtain ⟨noCost, regular, cards⟩ := chainEffectAnswer_rule effect applied
        have rawWF := applyFrame_wf0 wf (legal.frame regular) applied
        have pending : raw.pending = raw.pending.takeWhile isRunFrame ++ .finishSpell item :: tail := by
          rw [← layout, List.takeWhile_append_dropWhile]
        exact step_observed_chain_answer_to_decision legal noCost regular applied rawWF
          (cards.symm ▸ reads) pending programs tracked
          (isOrdinaryDecisionTail_front ready) (isOrdinaryDecisionTail_boundary ready)
    · contradiction

end Riftbound

end
