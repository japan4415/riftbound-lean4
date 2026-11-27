module

public import Riftbound.Invariant.ChainAnswerWork
public import Riftbound.Invariant.ObservedCleanupWork

/-!
# Standard movement and decisions during Cleanup (I12)

Movement is applied before Cleanup. Its event observers can add work, and Cleanup can open
a Showdown, a replacement decision, or an ordinary priority window.
-/

@[expose] public section

namespace Riftbound

private theorem cleanupContinuation_insert {rest stack : List Frame}
    (decision : isOrdinaryDecisionTail rest = true)
    (kept : ResolutionPrefix [.cleanup] (TriggerWorkTail rest) stack)
    (queue : List PendTrigger) (nonempty : queue ≠ []) :
    ResolutionPrefix [.cleanup] (TriggerWorkTail rest) (insertTriggers queue stack) :=
  kept.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl)
    (fun _ track q ne => track.insert (isOrdinaryDecisionTail_front decision) q ne) queue nonempty

private theorem advance_cleanup_to_decision {s : GameState} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (kept : ResolutionPrefix [.cleanup] (TriggerWorkTail rest) s.pending)
    (decision : isOrdinaryDecisionTail rest = true) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨tail, pending, track⟩ := kept
  obtain ⟨after, elapsed, events, _, path, stop | ⟨tracked, safe, same⟩⟩ :=
    advance_cleanup_with_adds wf reads pending (TriggerWorkTail rest) track
      (fun _ kept q ne => kept.insert (isOrdinaryDecisionTail_front decision) q ne)
  · exact ⟨after, elapsed, events, path, stop⟩
  · obtain ⟨t, queued, finalized, stopped⟩ := advance_trigger_tail after rest safe (same ▸ reads) tracked
    exact ⟨t, elapsed + queued, events, by simpa only [List.append_nil] using path.append finalized,
      stopped.elim id (fun h => h.1.symm ▸ isOrdinaryDecisionTail_boundary decision)⟩

/-- Follow event observation and Cleanup before returning to a decision. -/
theorem advance_observed_cleanup_to_decision (raw : GameState) (notices : List Event) {rest : List Frame}
    (wf : raw.WF) (reads : MightRead.database raw.cards)
    (stack : raw.pending = .cleanup :: rest) (decision : isOrdinaryDecisionTail rest = true) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true :=
  advance_observed_run_prefix_then raw notices wf reads (body := [])
    (keeps := ResolutionPrefix [.cleanup] (TriggerWorkTail rest)) ⟨_, rfl, rest, stack, Or.inl rfl⟩
    (by simp) (fun _ => cleanupContinuation_insert decision)
    (fun _ safe known kept => advance_cleanup_to_decision safe known kept decision)

/-- A legal Standard Move runs Cleanup and its event observers to the next decision. -/
theorem step_standardMove_to_decision {s : GameState} {p : PlayerId} {u : ObjId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .standardMove u dest pay⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .standardMove u dest pay⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .standardMove u dest pay⟩
  have regular : action.kind ≠ .concede := by intro eq; cases eq
  have frame := legal.frame regular
  simp only [LegalFrame, pending] at frame
  obtain ⟨⟨board, events⟩, applied⟩ := applyMove_isSome wf frame.2.1
  let raw := { board with pending := .cleanup :: .priority p :: rest }
  have rawStep : applyFrame0 s action = some (raw, events) := by
    simp only [applyFrame0, pending, action, applied, Option.map_some, raw]
  have safety := applyMove_safe applied
  have cards : raw.cards = s.cards := by
    have db := congrArg GameState.cards safety.same
    exact db
  have noCost : s.actionDeathCostChoice action = none := by
    simp only [GameState.actionDeathCostChoice, pending, action, GameState.actionKillCosts,
      GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  apply step_observed_frame_to_decision legal noCost regular rawStep
    ((safety.wf wf).congr rfl rfl rfl rfl) (cards.symm ▸ reads)
  intro next notices safe checked stack
  exact advance_observed_cleanup_to_decision next notices safe checked stack rfl

/-- Confirming a legal group move runs Cleanup before the restored ordinary decision. -/
theorem step_confirmGroupMove_to_decision {s : GameState} {p : PlayerId} {units : List ObjId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .decide true⟩) (decision : isOrdinaryDecisionTail rest = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .decide true⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .decide true⟩
  have regular : action.kind ≠ .concede := by intro eq; cases eq
  have frame := legal.frame regular
  simp only [LegalFrame, pending, GameState.groupMoveReady, Bool.and_eq_true] at frame
  obtain ⟨⟨board, events⟩, applied⟩ := Option.isSome_iff_exists.mp frame.2.2
  let raw := { board with pending := .cleanup :: rest }
  have rawStep : applyFrame0 s action = some (raw, events) := by
    simp only [applyFrame0, pending, action, applied, Option.map_some, raw]
  have safety := applyGroupMove_safe applied
  have cards : raw.cards = s.cards := by
    have db := congrArg GameState.cards safety.same
    exact db
  have noCost : s.actionDeathCostChoice action = none := by simp only [GameState.actionDeathCostChoice, pending]
  apply step_observed_frame_to_decision legal noCost regular rawStep
    ((safety.wf wf).congr rfl rfl rfl rfl) (cards.symm ▸ reads)
  intro next notices safe checked stack
  exact advance_observed_cleanup_to_decision next notices safe checked stack decision

/-- A legal choice of a staged battlefield opens its Showdown. -/
theorem step_chooseShowdown_to_decision {s : GameState} {p : PlayerId} {bf : ObjId}
    {first : ObjId × PlayerId} {more : List (ObjId × PlayerId)} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .chooseShowdown p first more :: rest)
    (legal : Legal s ⟨.player p, .choose bf⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .choose bf⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .choose bf⟩
  have regular : action.kind ≠ .concede := by intro eq; cases eq
  have frame := legal.frame regular
  simp only [LegalFrame, pending] at frame
  obtain ⟨focus, found⟩ := Option.isSome_iff_exists.mp frame.2
  let scheduled := Frame.showdown bf focus 0 :: .cleanup :: rest
  let raw := continueAfterCleanup s scheduled
  have applied : applyFrame0 s action = some raw := by
    simp only [applyFrame0, pending, action, found, Option.map_some, scheduled, raw]
  have noCost : s.actionDeathCostChoice action = none := by simp only [GameState.actionDeathCostChoice, pending]
  exact step_observed_action_waits legal regular noCost applied (wf.congr rfl rfl rfl rfl) reads rfl

/-- Starting a group move opens its selection decision before moving any units. -/
theorem step_startGroupMove_to_decision {s : GameState} {p : PlayerId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .startGroupMove dest pay⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .startGroupMove dest pay⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .startGroupMove dest pay⟩
  let raw := { s with pending := .groupMove p dest pay [] :: .priority p :: rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw]
  have noCost : s.actionDeathCostChoice action = none := by
    simp only [GameState.actionDeathCostChoice, pending, action, GameState.actionKillCosts,
      GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads rfl

/-- Picking a unit to move updates the group and waits for the next choice. -/
theorem step_chooseGroupMove_to_decision {s : GameState} {p : PlayerId}
    {dest : MoveDest} {pay : Cost} {u : ObjId} {units : List ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .choose u⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .choose u⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .choose u⟩
  let raw := { s with pending := .groupMove p dest pay (units ++ [u]) :: rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw]
  have noCost : s.actionDeathCostChoice action = none := by simp only [GameState.actionDeathCostChoice, pending]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads rfl

/-- Cancelling a group move restores the original waiting decision. -/
theorem step_cancelGroupMove_to_decision {s : GameState} {p : PlayerId}
    {dest : MoveDest} {pay : Cost} {units : List ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .decide false⟩) (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .decide false⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .decide false⟩
  let raw := { s with pending := rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw]
  have noCost : s.actionDeathCostChoice action = none := by simp only [GameState.actionDeathCostChoice, pending]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads decision

/-- Check the Run prefix scheduled by a Cleanup answer and the decision after Cleanup. -/
def cleanupAnswerWorkSupported (s : GameState) (a : Action) : Bool :=
  isRunProgramAnswer s a && (applyFrame0 s a).any (fun result =>
    (result.1.pending.takeWhile isRunFrame).all runFrameSupported &&
      match result.1.pending.dropWhile isRunFrame with
      | .cleanup :: tail => (chainAnswerContinuation? tail).isSome
      | _ => false)

/-- An accepted effect answer immediately before Cleanup reaches the next decision or the
empty stack, preserving the order of effects, Cleanup, and ordinary trigger decisions. -/
theorem step_cleanupAnswer_checked_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : cleanupAnswerWorkSupported s a = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = .ok (t, events) := by
  unfold cleanupAnswerWorkSupported at supported
  obtain ⟨answer, condition⟩ := Bool.and_eq_true_iff.mp supported
  cases applied : applyFrame0 s a with
  | none => simp [applied] at condition
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some, Bool.and_eq_true_iff] at condition
    obtain ⟨programs, continuation⟩ := condition
    split at continuation
    · rename_i tail layout
      cases parsed : chainAnswerContinuation? tail with
      | none => simp [parsed] at continuation
      | some rest =>
        obtain ⟨tracked, decision⟩ := chainAnswerContinuation_sound parsed
        obtain ⟨noCost, regular, cards⟩ := runProgramAnswer_rule answer applied
        apply step_observed_frame_to_decision legal noCost regular applied
          (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads)
        intro next observed safe checked stack
        have shape : raw.pending = raw.pending.takeWhile isRunFrame ++ .cleanup :: tail := by
          rw [← layout, List.takeWhile_append_dropWhile]
        exact advance_observed_run_prefix_then next observed safe checked
          (keeps := ResolutionPrefix [.cleanup] (TriggerWorkTail rest))
          ⟨.cleanup :: tail, stack.trans shape, tail, rfl, tracked⟩
          (fun f member => runFrameSupported_finite (List.all_eq_true.mp programs f member))
          (fun _ => cleanupContinuation_insert decision)
          (fun _ clean known kept => advance_cleanup_to_decision clean known kept decision)
    · contradiction

end Riftbound

end
