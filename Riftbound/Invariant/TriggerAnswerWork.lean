module

public import Riftbound.Invariant.ChainAnswerWork

/-!
# Trigger decisions and locked trigger declarations (I12)

An answer can open or update a funding window, put an ability on the Chain, skip it,
or ask for a replacement. A replacement answer can resume the original declaration.
-/

@[expose] public section

namespace Riftbound

/-- Closing an ordinary trigger queue at a decision continuation reaches another
decision even when the last ability was skipped. -/
theorem advance_triggers_at_decision {s : GameState} {queue : List PendTrigger} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .triggers queue :: rest)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used, AdvancePrefix s t used [] ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨t, used, _, path, stop⟩ := advance_triggers_checkedMight s wf queue rest pending reads
  refine ⟨t, used, path, ?_⟩
  generalize stack : t.pending = frames at stop
  cases stop with
  | resume => exact stack.symm ▸ decision
  | priority p n => rfl
  | order p first group others => rfl

private theorem advance_putTrigger_to_decision {s : GameState} {p : PlayerId} {first : PendTrigger}
    {group others : List PendTrigger} {funding : Option TriggerFunding}
    {index : Nat} {targets : List ObjId} {payment : TriggerPayment} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .triggerOrder p first group others funding :: rest)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ initial initialEvents t used events,
      applyDeclaredAction s ⟨.player p, .putTrigger index targets payment⟩ = some (initial, initialEvents) ∧
      AdvancePrefix initial t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  let action : Action := ⟨.player p, .putTrigger index targets payment⟩
  cases replace : s.actionDeathCostChoice action with
  | some choice =>
    obtain ⟨unit, who, a, b⟩ := choice
    let t := { s with pending := .eitherDo who unit {} a b .nil :: .resumeCost action :: s.pending }
    have answer : applyDeclaredAction s action = some (t, []) := by
      simp only [applyDeclaredAction, replace, t]
    exact ⟨t, [], t, 0, [], answer, by intro _ _; simp, rfl⟩
  | none =>
    let others := (first :: group).eraseIdx index ++ others
    let finalized := finishTrigger s (first :: group) funding index targets payment
    let raw := { finalized.1 with pending := .triggers others :: rest }
    let next := s.paySurcharge action raw
    let events := finalized.2 ++ extraEvents action finalized.2
    let notices := events ++ s.actionTransitionEvents next action
    have rawApply : applyFrame0 s action = some (raw, finalized.2) := by
      simp only [applyFrame0, pending, action, raw, finalized, others]
    have answer : applyDeclaredAction s action = some (next.withTriggers notices, events) := by
      simp only [applyDeclaredAction, replace, applyAction_of_ne (show action.kind ≠ .concede by
        intro h; cases h), applyFrame, rawApply, Option.map_some, next, notices, events]
    have safe := finishTrigger_safe s (first :: group) funding index targets payment
    have rawWF : raw.WF := (safe.wf wf).congr rfl rfl rfl rfl
    have cardEq : raw.cards = s.cards := by
      have same := congrArg GameState.cards safe.same
      exact same
    have surcharge := GameState.paySurcharge_poolStep s action raw
    have nextWF := surcharge.wf rawWF
    have nextCards : next.cards = s.cards := by
      have rawSame : next.cards = raw.cards := by
        rcases surcharge with h | ⟨p, pool, h⟩ <;> (have same := congrArg GameState.cards h; exact same)
      exact rawSame.trans cardEq
    obtain ⟨mid, used, added, path, midWF, cards, route⟩ :=
      advance_observed_work next notices nextWF (nextCards ▸ reads)
    have complete (q : List PendTrigger) (stack : mid.pending = .triggers q :: rest) :
        ∃ t used events, AdvancePrefix (next.withTriggers notices) t used events ∧
          t.pending.head?.all (fun f => !f.isWork) = true := by
      obtain ⟨t, after, done, stop⟩ := advance_triggers_at_decision midWF (cards ▸ nextCards ▸ reads) stack decision
      exact ⟨t, used + after, added, by simpa only [List.append_nil] using path.append done, stop⟩
    have reaches : ∃ t used events, AdvancePrefix (next.withTriggers notices) t used events ∧
        t.pending.head?.all (fun f => !f.isWork) = true := by
      have rawStack : next.pending = .triggers others :: rest := surcharge.pending_eq
      rw [rawStack] at route
      generalize stack : mid.pending = frames at route
      cases route with
      | empty => exact ⟨mid, used, added, path, by rw [stack]; rfl⟩
      | resume => exact complete others stack
      | queue q ne => exact complete (others ++ q) stack
    obtain ⟨t, fuel, emitted, ran, stop⟩ := reaches
    exact ⟨_, events, t, fuel, emitted, answer, ran, stop⟩

/-- Finalizing a trigger processes the remaining queue or opens a replacement prompt.
The dispatcher reaches a decision when the original continuation is already a decision. -/
theorem step_putTrigger_to_decision {s : GameState} {p : PlayerId} {first : PendTrigger}
    {group others : List PendTrigger} {funding : Option TriggerFunding}
    {index : Nat} {targets : List ObjId} {payment : TriggerPayment} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .triggerOrder p first group others funding :: rest)
    (legal : Legal s ⟨.player p, .putTrigger index targets payment⟩)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .putTrigger index targets payment⟩ = advance extra t events := by
  obtain ⟨initial, before, t, used, events, applied, ran, stop⟩ :=
    advance_putTrigger_to_decision (index := index) (targets := targets) (payment := payment)
      wf reads pending decision
  refine ⟨t, used, before ++ events, stop, fun extra => ?_⟩
  simp only [step, ite_eq_left legal, applied]
  exact ran extra before

/-- Preparing a funded trigger opens the resource choice window. -/
theorem step_prepareTrigger_to_decision {s : GameState} {p : PlayerId} {first : PendTrigger}
    {group others : List PendTrigger} {rest : List Frame}
    {index : Nat} {targets : List ObjId} {payment : TriggerPayment}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .triggerOrder p first group others none :: rest)
    (legal : Legal s ⟨.player p, .prepareTrigger index targets payment⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .prepareTrigger index targets payment⟩ = advance extra t events := by
  let action : Action := ⟨.player p, .prepareTrigger index targets payment⟩
  let plan : TriggerFunding := { index := index, targets := targets, payment := payment }
  let raw := { s with pending := .triggerOrder p first group others (some plan) :: rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw, plan]
  have noCost : s.actionDeathCostChoice action = none := by
    simp only [GameState.actionDeathCostChoice, pending, GameState.actionKillCosts, action,
      GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied
    (wf.congr rfl rfl rfl rfl) reads rfl

/-- Choosing one of the available Adds keeps the funded trigger waiting for an answer. -/
theorem step_triggerAdd_to_decision {s : GameState} {p : PlayerId} {first : PendTrigger}
    {group others : List PendTrigger} {rest : List Frame} {plan : TriggerFunding} {add : EffectAdd}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .triggerOrder p first group others (some plan) :: rest)
    (legal : Legal s ⟨.player p, .triggerAdd add⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .triggerAdd add⟩ = advance extra t events := by
  let action : Action := ⟨.player p, .triggerAdd add⟩
  let chosen := { plan with adds := plan.adds ++ [add] }
  let raw := { s with pending := .triggerOrder p first group others (some chosen) :: rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw, chosen]
  have noCost : s.actionDeathCostChoice action = none := by
    simp only [GameState.actionDeathCostChoice, pending, GameState.actionKillCosts, action,
      GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied
    (wf.congr rfl rfl rfl rfl) reads rfl

/-- Cancelling trigger funding returns to the ordinary trigger order window. -/
theorem step_cancelTriggerFunding_to_decision {s : GameState} {p : PlayerId} {first : PendTrigger}
    {group others : List PendTrigger} {rest : List Frame} {plan : TriggerFunding}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .triggerOrder p first group others (some plan) :: rest)
    (legal : Legal s ⟨.player p, .decide false⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .decide false⟩ = advance extra t events := by
  let action : Action := ⟨.player p, .decide false⟩
  let raw := { s with pending := .triggerOrder p first group others :: rest }
  have applied : applyFrame0 s action = some (raw, []) := by simp only [applyFrame0, pending, action, raw]
  have noCost : s.actionDeathCostChoice action = none := by
    simp only [GameState.actionDeathCostChoice, pending, GameState.actionKillCosts, action,
      GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied
    (wf.congr rfl rfl rfl rfl) reads rfl

/-- Resume a locked trigger declaration after a death-replacement answer. A declaration
that has become illegal restores the original trigger decision. -/
theorem advance_locked_putTrigger_to_decision {s : GameState} {p : PlayerId} {first : PendTrigger}
    {group others : List PendTrigger} {funding : Option TriggerFunding} {index : Nat}
    {targets : List ObjId} {payment : TriggerPayment} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .resumeCost ⟨.player p, .putTrigger index targets payment⟩ ::
      .triggerOrder p first group others funding :: rest)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix s t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  let action : Action := ⟨.player p, .putTrigger index targets payment⟩
  let restored := { s with pending := .triggerOrder p first group others funding :: rest }
  have notTime : action.kind ≠ .timeCalled := by intro eq; cases eq
  have workRule : workStep s = if action.kind ≠ .timeCalled ∧ Legal restored action then
      applyDeclaredAction restored action else some (restored, []) := by
    simp only [workStep, pending]
    rfl
  by_cases permitted : Legal restored action
  · obtain ⟨initial, before, t, used, events, applied, ran, stop⟩ :=
      advance_putTrigger_to_decision (s := restored) (index := index) (targets := targets) (payment := payment)
        (wf.congr rfl rfl rfl rfl) reads rfl decision
    have work : workStep s = some (initial, before) := by
      rw [workRule, ite_eq_left ⟨notTime, permitted⟩]
      exact applied
    exact ⟨t, used + 1, before ++ events, ran.prepend pending rfl work, stop⟩
  · have work : workStep s = some (restored, []) := by
      rw [workRule, ite_eq_right (fun h => permitted h.2)]
    have stable : AdvancePrefix restored restored 0 [] := by intro _ _; simp
    exact ⟨restored, 1, [], stable.prepend pending rfl work, rfl⟩

private theorem advance_observed_locked_trigger_runs (raw : GameState) (observed : List Event)
    {p : PlayerId} {first : PendTrigger} {group others : List PendTrigger}
    {funding : Option TriggerFunding} {index : Nat} {targets : List ObjId}
    {payment : TriggerPayment} {body rest : List Frame}
    (wf : raw.WF) (reads : MightRead.database raw.cards)
    (pending : raw.pending = body ++ (.resumeCost ⟨.player p, .putTrigger index targets payment⟩ ::
      .triggerOrder p first group others funding :: rest))
    (supported : body.all runFrameSupported = true)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix (raw.withTriggers observed) t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  let locked := Frame.resumeCost ⟨.player p, .putTrigger index targets payment⟩ ::
    .triggerOrder p first group others funding :: rest
  have front : ∀ f, locked.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
    intro f head
    obtain rfl := Option.some.inj head
    exact ⟨rfl, by intro q eq; cases eq⟩
  refine advance_observed_runs_then raw observed wf reads ⟨locked, pending, Or.inl rfl⟩
    (fun f member => runFrameSupported_finite (List.all_eq_true.mp supported f member)) front ?_
  intro ready readyWF readyReads atLocked
  exact advance_locked_putTrigger_to_decision readyWF readyReads atLocked decision

/-- Check the programs generated by a replacement answer for a locked trigger, and
recognize the original trigger decision and the continuation it can return to. -/
def triggerCostAnswerWorkSupported (s : GameState) (a : Action) : Bool :=
  isChainEffectAnswer s a && (applyFrame0 s a).any (fun result =>
    (result.1.pending.takeWhile isRunFrame).all runFrameSupported &&
      match result.1.pending.dropWhile isRunFrame with
      | .resumeCost ⟨.player actor, .putTrigger ..⟩ :: .triggerOrder p _ _ _ _ :: rest =>
        actor == p && rest.head?.all (fun f => !f.isWork)
      | _ => false)

/-- An accepted answer to a locked trigger cost runs the chosen effect, resumes the
declaration and reaches a decision using finite fuel. -/
theorem step_triggerCostAnswer_checked_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : triggerCostAnswerWorkSupported s a = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  unfold triggerCostAnswerWorkSupported at supported
  obtain ⟨answer, condition⟩ := Bool.and_eq_true_iff.mp supported
  cases applied : applyFrame0 s a with
  | none => simp [applied] at condition
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some, Bool.and_eq_true_iff] at condition
    obtain ⟨programs, continuation⟩ := condition
    split at continuation
    · obtain ⟨same, decision⟩ := Bool.and_eq_true_iff.mp continuation
      have seats := eq_of_beq same
      subst seats
      rename_i layout
      obtain ⟨noCost, regular, cards⟩ := chainEffectAnswer_rule answer applied
      have rawWF := applyFrame_wf0 wf (legal.frame regular) applied
      apply step_observed_frame_to_decision legal noCost regular applied rawWF (cards.symm ▸ reads)
      intro next observed safe checked stack
      have shape : raw.pending = raw.pending.takeWhile isRunFrame ++ raw.pending.dropWhile isRunFrame :=
        (List.takeWhile_append_dropWhile).symm
      rw [layout] at shape
      exact advance_observed_locked_trigger_runs next observed safe checked
        (stack.trans shape) programs decision
    · contradiction

end Riftbound

end
