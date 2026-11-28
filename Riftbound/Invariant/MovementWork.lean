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

private theorem advance_cleanup_to_preparedDecision {s : GameState} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (kept : ResolutionPrefix [.cleanup] (TriggerWorkTail rest) s.pending)
    (decision : isOrdinaryDecisionTail rest = true)
    (quiet : ∀ p tail, rest = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨tail, pending, track⟩ := kept
  obtain ⟨after, elapsed, events, _, path, ready | ⟨tracked, safe, cards, notQuiet⟩⟩ :=
    advance_cleanup_with_adds_prepared_quiet wf reads pending (TriggerWorkTail rest) track
      (fun _ keeps q ne => keeps.insert (isOrdinaryDecisionTail_front decision) q ne)
  · exact ⟨after, elapsed, events, path, ready⟩
  · rcases tracked with resumed | ⟨queue, nonempty, queued⟩
    · have ready := GameState.prepared_idle_of_nonpriority
        (resumed.symm ▸ isOrdinaryDecisionTail_boundary decision) (fun p tail equal =>
          notQuiet ⟨p, tail, equal, quiet p tail (resumed.symm.trans equal)⟩)
      exact ⟨after, elapsed, events, path, ready⟩
    · obtain ⟨t, queuedSteps, _, _, _, more, _, _, ready⟩ :=
        advance_triggers_to_preparedDecision after safe queue rest queued (cards ▸ reads) (Or.inl nonempty)
      exact ⟨t, elapsed + queuedSteps, events, by simpa only [List.append_nil] using path.append more, ready⟩

/-- Follow the event observers, Cleanup and any leading ordinary queue to a prepared decision
when a neutral continuation has no combat observation frame. -/
theorem advance_observed_cleanup_to_preparedDecision (raw : GameState) (notices : List Event)
    {rest : List Frame} (wf : raw.WF) (reads : MightRead.database raw.cards)
    (stack : raw.pending = .cleanup :: rest) (decision : isOrdinaryDecisionTail rest = true)
    (quiet : ∀ p tail, rest = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨mid, used, events, path, safe, cards, route⟩ := advance_observed_work raw notices wf reads
  let keeps := ResolutionPrefix [.cleanup] (TriggerWorkTail rest)
  have base : keeps raw.pending := ⟨rest, stack, Or.inl rfl⟩
  have run (kept : keeps mid.pending) : ∃ t elapsed later,
      AdvancePrefix (raw.withTriggers notices) t elapsed later ∧
        t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨t, elapsed, later, more, ready⟩ :=
      advance_cleanup_to_preparedDecision safe (cards ▸ reads) kept decision quiet
    exact ⟨t, used + elapsed, events ++ later, path.append more, ready⟩
  generalize actual : mid.pending = frames at route
  cases route with
  | empty => exact ⟨mid, used, events, path, GameState.prepared_idle_of_empty actual⟩
  | resume => exact run (actual.symm ▸ base)
  | queue q nonempty => exact run (actual.symm ▸ cleanupContinuation_insert decision base q nonempty)

/-- Run any Cleanup that preparation schedules before returning a waiting decision. -/
theorem advance_waiting_to_preparedDecision {s : GameState} (wf : s.WF)
    (reads : MightRead.database s.cards) (waiting : s.pending.head?.all (fun f => !f.isWork) = true)
    (quiet : ∀ p tail, s.pending = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  rcases s.preparePriority_cases with unchanged | ⟨p, tail, stack, _, prepared⟩
  · exact ⟨s, 0, [], by intro fuel events; simp, by simpa only [unchanged] using waiting⟩
  · have staged : s.preparePriority.pending = .cleanup :: .priority p :: tail := by
      rw [prepared]
      exact congrArg (Frame.cleanup :: ·) stack
    have check : MightRead.database s.preparePriority.cards := by rw [prepared]; exact reads
    have agrees : s.preparePriority.preparePriority = s.preparePriority :=
      GameState.preparePriority_of_work staged rfl
    have same (fuel : Nat) (seen : List Event) : advance fuel s seen = advance fuel s.preparePriority seen := by
      cases fuel <;> simp only [advance, agrees]
    obtain ⟨t, used, events, path, ready⟩ :=
      advance_observed_cleanup_to_preparedDecision s.preparePriority [] wf.preparePriority check staged rfl
        (fun q suffix equal => by cases equal; exact quiet p tail stack)
    rw [withTriggers_nil] at path
    exact ⟨t, used, events, fun fuel seen => (same (used + fuel) seen).trans (path fuel seen), ready⟩

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

private theorem standardMove_frame {s : GameState} {p : PlayerId} {u : ObjId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .standardMove u dest pay⟩) :
    s.actionDeathCostChoice ⟨.player p, .standardMove u dest pay⟩ = none ∧
    ∃ raw events, applyFrame0 s ⟨.player p, .standardMove u dest pay⟩ = some (raw, events) ∧
      raw.WF ∧ raw.cards = s.cards ∧ raw.pending = .cleanup :: .priority p :: rest := by
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
  exact ⟨noCost, raw, events, rawStep, (safety.wf wf).congr rfl rfl rfl rfl, cards, rfl⟩

/-- A legal Standard Move runs Cleanup and its event observers to the next decision. -/
theorem step_standardMove_to_decision {s : GameState} {p : PlayerId} {u : ObjId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .standardMove u dest pay⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .standardMove u dest pay⟩ = advance extra t events := by
  obtain ⟨noCost, raw, events, applied, safe, cards, layout⟩ := standardMove_frame wf pending legal
  apply step_observed_frame_to_decision legal noCost (by intro h; cases h) applied safe (cards.symm ▸ reads)
  intro next notices sound checked stack
  exact advance_observed_cleanup_to_decision next notices sound checked (stack.trans layout) rfl

/-- A legal Standard Move returns a prepared decision after its observers and Cleanup. -/
theorem step_standardMove_to_preparedDecision {s : GameState} {p : PlayerId} {u : ObjId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .standardMove u dest pay⟩)
    (quiet : ∀ f ∈ rest, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.player p, .standardMove u dest pay⟩ = advance extra t events) ∧
      step used s ⟨.player p, .standardMove u dest pay⟩ = .ok (t, events) := by
  obtain ⟨noCost, raw, events, applied, safe, cards, layout⟩ := standardMove_frame wf pending legal
  apply step_observed_frame_to_preparedDecision legal noCost (by intro h; cases h) applied safe (cards.symm ▸ reads)
  intro next notices sound checked stack
  apply advance_observed_cleanup_to_preparedDecision next notices sound checked (stack.trans layout) rfl
  intro owner tail same
  cases same
  exact quiet

private theorem confirmGroupMove_frame {s : GameState} {p : PlayerId} {units : List ObjId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .decide true⟩) :
    s.actionDeathCostChoice ⟨.player p, .decide true⟩ = none ∧
    ∃ raw events, applyFrame0 s ⟨.player p, .decide true⟩ = some (raw, events) ∧
      raw.WF ∧ raw.cards = s.cards ∧ raw.pending = .cleanup :: rest := by
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
  exact ⟨noCost, raw, events, rawStep, (safety.wf wf).congr rfl rfl rfl rfl, cards, rfl⟩

/-- Confirming a legal group move runs Cleanup before the restored ordinary decision. -/
theorem step_confirmGroupMove_to_decision {s : GameState} {p : PlayerId} {units : List ObjId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .decide true⟩) (decision : isOrdinaryDecisionTail rest = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .decide true⟩ = advance extra t events := by
  obtain ⟨noCost, raw, events, applied, safe, cards, layout⟩ := confirmGroupMove_frame wf pending legal
  apply step_observed_frame_to_decision legal noCost (by intro h; cases h) applied safe (cards.symm ▸ reads)
  intro next notices sound checked stack
  exact advance_observed_cleanup_to_decision next notices sound checked (stack.trans layout) decision

/-- Confirming a legal group move returns a prepared decision after Cleanup. -/
theorem step_confirmGroupMove_to_preparedDecision {s : GameState} {p : PlayerId} {units : List ObjId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .decide true⟩) (decision : isOrdinaryDecisionTail rest = true)
    (quiet : ∀ owner tail, rest = .priority owner :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.player p, .decide true⟩ = advance extra t events) ∧
      step used s ⟨.player p, .decide true⟩ = .ok (t, events) := by
  obtain ⟨noCost, raw, events, applied, safe, cards, layout⟩ := confirmGroupMove_frame wf pending legal
  apply step_observed_frame_to_preparedDecision legal noCost (by intro h; cases h) applied safe (cards.symm ▸ reads)
  intro next notices sound checked stack
  apply advance_observed_cleanup_to_preparedDecision next notices sound checked (stack.trans layout) decision
  exact quiet

/-- A legal choice of a staged battlefield opens its Showdown. -/
theorem step_chooseShowdown_to_preparedDecision {s : GameState} {p : PlayerId} {bf : ObjId}
    {first : ObjId × PlayerId} {more : List (ObjId × PlayerId)} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .chooseShowdown p first more :: rest)
    (legal : Legal s ⟨.player p, .choose bf⟩) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.player p, .choose bf⟩ = advance extra t events) ∧
      step used s ⟨.player p, .choose bf⟩ = .ok (t, events) := by
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
  exact step_observed_waiting_to_preparedDecision legal regular noCost applied (wf.congr rfl rfl rfl rfl) reads rfl
    (by intro owner tail equality; cases equality)

/-- The observed action has a finite continuation up to an input. -/
theorem step_chooseShowdown_to_decision {s : GameState} {p : PlayerId} {bf : ObjId}
    {first : ObjId × PlayerId} {more : List (ObjId × PlayerId)} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .chooseShowdown p first more :: rest)
    (legal : Legal s ⟨.player p, .choose bf⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .choose bf⟩ = advance extra t events := by
  obtain ⟨t, used, events, ready, run, _⟩ := step_chooseShowdown_to_preparedDecision wf reads pending legal
  exact ⟨t, used, events, by simpa only [GameState.preparePriority_of_idle ready] using ready, run⟩

/-- Starting a group move opens its selection decision before moving any units. -/
theorem step_startGroupMove_to_preparedDecision {s : GameState} {p : PlayerId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .startGroupMove dest pay⟩) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.player p, .startGroupMove dest pay⟩ = advance extra t events) ∧
      step used s ⟨.player p, .startGroupMove dest pay⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .startGroupMove dest pay⟩
  let raw := { s with pending := .groupMove p dest pay [] :: .priority p :: rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw]
  have noCost : s.actionDeathCostChoice action = none := by
    simp only [GameState.actionDeathCostChoice, pending, action, GameState.actionKillCosts,
      GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  exact step_observed_waiting_to_preparedDecision legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads rfl
    (by intro owner tail equality; cases equality)

/-- The observed action has a finite continuation up to an input. -/
theorem step_startGroupMove_to_decision {s : GameState} {p : PlayerId}
    {dest : MoveDest} {pay : Cost} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .startGroupMove dest pay⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .startGroupMove dest pay⟩ = advance extra t events := by
  obtain ⟨t, used, events, ready, run, _⟩ := step_startGroupMove_to_preparedDecision wf reads pending legal
  exact ⟨t, used, events, by simpa only [GameState.preparePriority_of_idle ready] using ready, run⟩

/-- Picking a unit to move updates the group and waits for the next choice. -/
theorem step_chooseGroupMove_to_preparedDecision {s : GameState} {p : PlayerId}
    {dest : MoveDest} {pay : Cost} {u : ObjId} {units : List ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .choose u⟩) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.player p, .choose u⟩ = advance extra t events) ∧
      step used s ⟨.player p, .choose u⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .choose u⟩
  let raw := { s with pending := .groupMove p dest pay (units ++ [u]) :: rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw]
  have noCost : s.actionDeathCostChoice action = none := by simp only [GameState.actionDeathCostChoice, pending]
  exact step_observed_waiting_to_preparedDecision legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads rfl
    (by intro owner tail equality; cases equality)

/-- The observed action has a finite continuation up to an input. -/
theorem step_chooseGroupMove_to_decision {s : GameState} {p : PlayerId}
    {dest : MoveDest} {pay : Cost} {u : ObjId} {units : List ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .choose u⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .choose u⟩ = advance extra t events := by
  obtain ⟨t, used, events, ready, run, _⟩ := step_chooseGroupMove_to_preparedDecision wf reads pending legal
  exact ⟨t, used, events, by simpa only [GameState.preparePriority_of_idle ready] using ready, run⟩

/-- Cancelling a group move restores the original waiting decision. -/
theorem step_cancelGroupMove_to_decision {s : GameState} {p : PlayerId}
    {dest : MoveDest} {pay : Cost} {units : List ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .decide false⟩) (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .decide false⟩ = advance extra t events := by
  let action : Action := ⟨.player p, .decide false⟩
  let raw := { s with pending := rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw]
  have noCost : s.actionDeathCostChoice action = none := by simp only [GameState.actionDeathCostChoice, pending]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads decision

/-- Cancelling a group move returns the previously waiting decision after preparation. -/
theorem step_cancelGroupMove_to_preparedDecision {s : GameState} {p : PlayerId}
    {dest : MoveDest} {pay : Cost} {units : List ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .groupMove p dest pay units :: rest)
    (legal : Legal s ⟨.player p, .decide false⟩) (decision : rest.head?.all (fun f => !f.isWork) = true)
    (quiet : ∀ owner tail, rest = .priority owner :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.player p, .decide false⟩ = advance extra t events) ∧
      step used s ⟨.player p, .decide false⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .decide false⟩
  let raw := { s with pending := rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw]
  have noCost : s.actionDeathCostChoice action = none := by simp only [GameState.actionDeathCostChoice, pending]
  exact step_observed_waiting_to_preparedDecision legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads decision quiet

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
      ∀ extra, step (used + extra) s a = advance extra t events := by
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
/-- An accepted effect answer immediately before Cleanup reaches the next decision or the
empty stack, preserving the order of effects, Cleanup, and ordinary trigger decisions. -/
theorem step_cleanupAnswer_checked_to_preparedDecision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : cleanupAnswerWorkSupported s a = true)
    (quiet : ∀ raw emitted stack rest owner tail, applyFrame0 s a = some (raw, emitted) →
      raw.pending.dropWhile isRunFrame = .cleanup :: stack →
      chainAnswerContinuation? stack = some rest → rest = .priority owner :: tail →
      ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
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
        apply step_observed_frame_to_preparedDecision legal noCost regular applied
          (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads)
        intro next observed safe checked stack
        have shape : raw.pending = raw.pending.takeWhile isRunFrame ++ .cleanup :: tail := by
          rw [← layout, List.takeWhile_append_dropWhile]
        exact advance_observed_run_prefix_then_prepared next observed safe checked
          (keeps := ResolutionPrefix [.cleanup] (TriggerWorkTail rest))
          ⟨.cleanup :: tail, stack.trans shape, tail, rfl, tracked⟩
          (fun f member => runFrameSupported_finite (List.all_eq_true.mp programs f member))
          (fun _ => cleanupContinuation_insert decision)
          (fun _ clean known kept => advance_cleanup_to_preparedDecision clean known kept decision
            (quiet raw events tail rest · · applied layout parsed))
    · contradiction

end Riftbound

end
