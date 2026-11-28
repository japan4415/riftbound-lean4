module

public import Riftbound.Invariant.CombatWork
public import Riftbound.Invariant.TurnPhaseWork

/-! # Work after Burn Out answers (I12) -/

@[expose] public section

namespace Riftbound

/-- Frames that can resume directly after either Burn Out answer. -/
def isBurnOutWorkFrame : Frame → Bool
  | .draw .. | .cleanup | .run .. => true
  | _ => false

/-- Checking a resumed draw or Cleanup needs no effect certificate. -/
def burnOutWorkFrameSupported : Frame → Bool
  | .draw .. | .cleanup => true
  | frame => runFrameSupported frame

private theorem burnOutWorkFrameSupported_resolution {f : Frame}
    (supported : burnOutWorkFrameSupported f = true) : f.isResolution = true := by
  cases f <;> simp [burnOutWorkFrameSupported, runFrameSupported, Frame.isResolution] at supported ⊢

private theorem advance_burn_out_prefix {s : GameState} {frames : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : ResolutionPrefix frames keeps s.pending)
    (supported : frames.all burnOutWorkFrameSupported = true)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  induction frames generalizing s with
  | nil =>
    obtain ⟨_, rfl, ready⟩ := pending
    exact .resume wf ready
  | cons frame later ih =>
    obtain ⟨tail, stack, tracked⟩ := pending
    obtain ⟨head, more⟩ := Bool.and_eq_true_iff.mp supported
    let rest := ResolutionPrefix later keeps
    have insertRest : ∀ suffix, rest suffix → ∀ q, q ≠ [] → rest (insertTriggers q suffix) := by
      intro _ waiting q ne
      apply waiting.insert _ inserted q ne
      intro f member
      exact burnOutWorkFrameSupported_resolution (List.all_eq_true.mp more f member)
    have work : AdvanceTo s rest := by
      cases frame with
      | draw p count hand =>
        obtain ⟨t, used, events, _, path, stop⟩ :=
          advance_draw_until_prepared wf reads stack rest ⟨tail, rfl, tracked⟩ insertRest
        exact ⟨t, used, events, path, stop⟩
      | cleanup =>
        obtain ⟨t, used, events, _, path, stop⟩ :=
          advance_cleanup_with_adds_prepared wf reads stack rest ⟨tail, rfl, tracked⟩ insertRest
        exact ⟨t, used, events, path,
          stop.imp_right (fun ⟨ready, safe, cards, _⟩ => ⟨ready, safe, cards⟩)⟩
      | run p src env program =>
        exact advance_run_program wf reads stack (EffectList.observedFinite_of_supported program head)
          rest ⟨tail, rfl, tracked⟩ insertRest
      | _ => simp [burnOutWorkFrameSupported, runFrameSupported] at head
    exact work.then reads (fun _ safe known rest => ih safe known rest more)

private inductive BurnOutBoundary : List Frame → Prop where
  | decision {rest : List Frame} (ready : isOrdinaryDecisionTail rest = true) : BurnOutBoundary rest
  | turn {rest : List Frame} (suffix : TurnPhaseSuffix rest) : BurnOutBoundary rest

private theorem BurnOutBoundary.front {rest : List Frame} (boundary : BurnOutBoundary rest) :
    ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
  cases boundary with
  | decision ready => exact isOrdinaryDecisionTail_front ready
  | turn suffix => exact suffix.front

private inductive BurnOutTail (rest : List Frame) : List Frame → Prop where
  | waiting {frames : List Frame} (tracked : TriggerWorkTail rest frames) : BurnOutTail rest frames
  | finish (item : ObjId) {frames : List Frame}
      (tracked : ResolutionPrefix [.finishSpell item] (TriggerWorkTail rest) frames) : BurnOutTail rest frames
  | combatFinish (field : ObjId) {suffix frames : List Frame}
      (stage : TriggerWorkTail (.combatFinish field :: suffix) frames)
      (tracked : TriggerWorkTail rest suffix) : BurnOutTail rest frames

private theorem BurnOutTail.insert {rest frames : List Frame} (tail : BurnOutTail rest frames)
    (boundary : BurnOutBoundary rest) (q : List PendTrigger) (ne : q ≠ []) :
    BurnOutTail rest (insertTriggers q frames) := by
  cases tail with
  | waiting tracked => exact .waiting (tracked.insert boundary.front q ne)
  | finish item tracked =>
    exact .finish item (tracked.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl)
      (fun _ kept added nonempty => kept.insert boundary.front added nonempty) q ne)
  | combatFinish field stage tracked =>
    exact .combatFinish field (stage.insert (combatFinish_head _ _) q ne) tracked

/-- Locate the decision or remaining turn phases after outstanding Burn Out work. -/
def burnOutContinuation? (stack : List Frame) : Option (List Frame) :=
  match stack with
  | .finishSpell _ :: rest => waiting? rest
  | .combatFinish _ :: rest => waiting? rest
  | .triggers (_ :: _) :: .combatFinish _ :: rest => waiting? rest
  | _ => waiting? stack
where
  waiting? : List Frame → Option (List Frame)
    | stack@(.triggers (_ :: _) :: rest) =>
      if isTurnPhaseSuffix rest then some rest else chainAnswerContinuation? stack
    | rest => if isTurnPhaseSuffix rest then some rest else chainAnswerContinuation? rest

private theorem burnOutWaiting_sound {stack rest : List Frame}
    (ready : burnOutContinuation?.waiting? stack = some rest) :
    TriggerWorkTail rest stack ∧ BurnOutBoundary rest := by
  have ordinary {frames original : List Frame} (parsed : chainAnswerContinuation? frames = some original) :
      TriggerWorkTail original frames ∧ BurnOutBoundary original := by
    obtain ⟨tracked, done⟩ := chainAnswerContinuation_sound parsed
    exact ⟨tracked, .decision done⟩
  unfold burnOutContinuation?.waiting? at ready
  split at ready
  · split at ready
    · rename_i phases
      obtain rfl := Option.some.inj ready
      exact ⟨Or.inr ⟨_, by simp, rfl⟩, .turn (isTurnPhaseSuffix_sound phases)⟩
    · exact ordinary ready
  · split at ready
    · rename_i phases
      obtain rfl := Option.some.inj ready
      exact ⟨Or.inl rfl, .turn (isTurnPhaseSuffix_sound phases)⟩
    · exact ordinary ready

private theorem burnOutContinuation_sound {stack rest : List Frame}
    (ready : burnOutContinuation? stack = some rest) : BurnOutTail rest stack ∧ BurnOutBoundary rest := by
  unfold burnOutContinuation? at ready
  split at ready
  · obtain ⟨tracked, boundary⟩ := burnOutWaiting_sound ready
    exact ⟨.finish _ ⟨_, rfl, tracked⟩, boundary⟩
  · obtain ⟨tracked, boundary⟩ := burnOutWaiting_sound ready
    exact ⟨.combatFinish _ (Or.inl rfl) tracked, boundary⟩
  · obtain ⟨tracked, boundary⟩ := burnOutWaiting_sound ready
    exact ⟨.combatFinish _ (Or.inr ⟨_, by simp, rfl⟩) tracked, boundary⟩
  · obtain ⟨tracked, boundary⟩ := burnOutWaiting_sound ready
    exact ⟨.waiting tracked, boundary⟩

private theorem advance_burnOutEnd {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (tail : BurnOutTail rest s.pending) (boundary : BurnOutBoundary rest)
    (quiet : ∀ p later, rest = .priority p :: later → ∀ f ∈ later, f.observesCombat = false) :
    ∃ t used events, AdvancePrefix s t used events ∧ t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  have work : AdvanceTo s (· = rest) := by
    cases tail with
    | waiting tracked => exact advance_trigger_tail_until_decision wf reads tracked
    | finish item tracked =>
      obtain ⟨_, atFinish, waiting⟩ := tracked
      exact advance_finish_chain_until_decision wf reads atFinish waiting boundary.front
    | combatFinish field stage tracked =>
      exact (advance_combat_finish_queue wf reads stage tracked
        (fun _ kept q ne => kept.insert boundary.front q ne)).then reads
          (fun _ safe known kept => advance_trigger_tail_until_decision safe known kept)
  cases boundary with
  | decision ready => exact work.atPreparedDecision reads (isOrdinaryDecisionTail_boundary ready) quiet
  | turn suffix =>
    obtain ⟨mid, used, events, path, ready | ⟨atPhase, midWF, cards⟩⟩ := work
    · exact ⟨mid, used, events, path, ready⟩
    · obtain ⟨t, more, emitted, _, ran, stopped⟩ :=
        advance_turnPhaseSuffix_to_preparedDecision midWF (cards ▸ reads) atPhase suffix
      exact ⟨t, used + more, events ++ emitted, path.append ran, stopped⟩

/-- A recorded Trash order or an opponent choice answering Burn Out. -/
def isBurnOutAnswer (s : GameState) (a : Action) : Bool :=
  match s.pending.head?, a.kind with
  | some (.chanceBurnOut _), .arrange _
  | some (.chooseBurnOut _), .burnOutTarget _
  | some (.chooseBurnOutAmong ..), .burnOutTarget _ => true
  | _, _ => false

private theorem burnOutAnswer_rule {s raw : GameState} {a : Action} {events : List Event}
    (answer : isBurnOutAnswer s a = true) (applied : applyFrame0 s a = some (raw, events)) :
    s.actionDeathCostChoice a = none ∧ a.kind ≠ .concede ∧ raw.cards = s.cards := by
  cases pending : s.pending with
  | nil => simp [isBurnOutAnswer, pending] at answer
  | cons frame tail =>
    cases frame <;> simp [isBurnOutAnswer, pending] at answer
    all_goals
      cases kind : a.kind <;> simp [kind] at answer
      refine ⟨by simp [GameState.actionDeathCostChoice, pending], by simp, ?_⟩
    case chanceBurnOut.arrange =>
      simp only [applyFrame0, pending, kind, Option.map_eq_some_iff] at applied
      obtain ⟨board, moved, equal⟩ := applied
      simp only [Prod.mk.injEq] at equal
      rw [← equal.1]
      exact (recycleAll_meta _ _ moved).cards
    all_goals
      simp only [applyFrame0, pending, kind, Option.some.injEq, Prod.mk.injEq] at applied
      rw [← applied.1]
      rfl

/-- Inspect the work actually scheduled by a Burn Out answer. -/
def burnOutAnswerWorkSupported (s : GameState) (a : Action) : Bool :=
  isBurnOutAnswer s a && (applyFrame0 s a).any (fun result =>
    (result.1.pending.takeWhile isBurnOutWorkFrame).all burnOutWorkFrameSupported &&
      (burnOutContinuation? (result.1.pending.dropWhile isBurnOutWorkFrame)).isSome)

/-- Both Burn Out answers reach the next prepared input, including a resumed draw batch,
remaining turn phases, Chain conclusion or Combat finish when those frames pass the check. -/
theorem step_burnOutAnswer_checked_to_preparedDecision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (checked : burnOutAnswerWorkSupported s a = true)
    (quiet : ∀ raw emitted p tail, applyFrame0 s a = some (raw, emitted) →
      burnOutContinuation? (raw.pending.dropWhile isBurnOutWorkFrame) = some (.priority p :: tail) →
      ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
  unfold burnOutAnswerWorkSupported at checked
  obtain ⟨answer, condition⟩ := Bool.and_eq_true_iff.mp checked
  cases applied : applyFrame0 s a with
  | none => simp [applied] at condition
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some, Bool.and_eq_true_iff] at condition
    obtain ⟨programs, found⟩ := condition
    cases parsed : burnOutContinuation? (raw.pending.dropWhile isBurnOutWorkFrame) with
    | none => simp [parsed] at found
    | some rest =>
      obtain ⟨tracked, boundary⟩ := burnOutContinuation_sound parsed
      obtain ⟨noCost, regular, cards⟩ := burnOutAnswer_rule answer applied
      apply step_observed_frame_to_preparedDecision legal noCost regular applied
        (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads)
      intro next observed safe known stack
      let body := raw.pending.takeWhile isBurnOutWorkFrame
      let keeps := BurnOutTail rest
      have insertTail : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail) :=
        fun _ route q ne => route.insert boundary q ne
      have base : ResolutionPrefix body keeps next.pending :=
        ⟨_, stack.trans List.takeWhile_append_dropWhile.symm, tracked⟩
      obtain ⟨mid, used, emitted, path, midWF, same, route⟩ := advance_observed_work next observed safe known
      have run (waiting : ResolutionPrefix body keeps mid.pending) :
          ∃ t more events, AdvancePrefix (next.withTriggers observed) t more events ∧
            t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
        obtain ⟨later, count, during, resolved, ready | ⟨restored, laterWF, laterCards⟩⟩ :=
          advance_burn_out_prefix midWF (same ▸ known) waiting programs insertTail
        · exact ⟨later, used + count, emitted ++ during, path.append resolved, ready⟩
        · obtain ⟨t, more, past, finished, ready⟩ :=
            advance_burnOutEnd laterWF (laterCards ▸ same ▸ known) restored boundary
              (fun p tail priority => quiet raw events p tail applied (parsed.trans (congrArg some priority)))
          exact ⟨t, used + count + more, (emitted ++ during) ++ past, (path.append resolved).append finished, ready⟩
      generalize actual : mid.pending = frames at route
      cases route with
      | empty => exact ⟨mid, used, emitted, path, GameState.prepared_idle_of_empty actual⟩
      | resume => exact run (actual.symm ▸ base)
      | queue q ne =>
        exact run (actual.symm ▸ base.insert
          (fun f member => burnOutWorkFrameSupported_resolution (List.all_eq_true.mp programs f member)) insertTail q ne)

end Riftbound

end
