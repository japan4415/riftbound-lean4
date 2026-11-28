module

public import Riftbound.Invariant.TriggerAnswerWork
public import Riftbound.Invariant.MovementWork

/-!
# Card play and ability declarations (I12)

Follow a declaration, including its observed events, through the actual dispatcher.
-/

@[expose] public section

namespace Riftbound

/-- A player can play a card or activate an ability at these decision frames. -/
def isPlayDeclaration (s : GameState) (a : Action) : Bool :=
  match s.pending.head?, a.kind with
  | some (.priority ..), .playCard .. | some (.priority ..), .activate ..
  | some (.chainPass ..), .playCard .. | some (.chainPass ..), .activate ..
  | some (.showdown ..), .playCard .. | some (.showdown ..), .activate ..
  | some (.teamInvitation ..), .playCard .. | some (.teamInvitation ..), .activate .. => true
  | _, _ => false

private theorem isPlayDeclaration_regular {s : GameState} {a : Action}
    (play : isPlayDeclaration s a = true) : a.kind ≠ .concede := by
  intro kind
  have invalid : isPlayDeclaration s a = false := by
    unfold isPlayDeclaration
    rw [kind]
    cases s.pending.head? with
    | none => rfl
    | some frame => cases frame <;> rfl
  rw [invalid] at play
  contradiction

private theorem playDeclaration_raw {s raw : GameState} {a : Action} {events : List Event}
    (play : isPlayDeclaration s a = true) (rawStep : applyFrame0 s a = some (raw, events)) :
    raw.cards = s.cards ∧
      ((∃ rest, raw.pending = .cleanup :: rest ∧ isOrdinaryDecisionTail rest = true ∧
        (∀ p tail, rest = .priority p :: tail → s.pending = .priority p :: tail)) ∨
        ∃ body rest, raw.pending = body ++ rest ∧
          (∀ f ∈ body, f.FiniteRun) ∧ isOrdinaryDecisionTail rest = true ∧ NonNeutralDecision rest) := by
  cases pending : s.pending with
  | nil => simp [isPlayDeclaration, pending] at play
  | cons frame rest =>
    cases frame <;> simp [isPlayDeclaration, pending] at play
    all_goals cases action : a.kind <;> simp [action] at play
    all_goals simp only [applyFrame0, pending, action] at rawStep
    case cons.priority.playCard =>
      obtain ⟨_, _, _, _, cards, stack⟩ := applyPlayCard_meta rawStep
      rcases stack with h | h
      · exact ⟨cards, Or.inl ⟨_, h, by rw [pending]; rfl, fun _ _ eq => pending.symm.trans eq⟩⟩
      · exact ⟨cards, Or.inr ⟨[], _, h, by simp, rfl, rfl⟩⟩
    case cons.chainPass.playCard | cons.showdown.playCard | cons.teamInvitation.playCard =>
      obtain ⟨_, _, _, _, cards, stack⟩ := reactStep_meta rawStep
      rcases stack with resumed | cleanup
      · exact ⟨cards, Or.inr ⟨[], _, resumed, by simp, rfl, rfl⟩⟩
      · exact ⟨cards, Or.inl ⟨_, cleanup, rfl, by intro p tail eq; cases eq⟩⟩
    all_goals
      obtain ⟨_, _, _, _, cards, stack⟩ := activateStep_meta rawStep
      exact ⟨cards, Or.inr ⟨_, _, stack, activationRecycleFrames_finite _ _ _ _ _, rfl, rfl⟩⟩

private theorem playDeclaration_isSome {s : GameState} {a : Action}
    (wf : s.WF) (play : isPlayDeclaration s a = true) (legal : LegalFrame s a) :
    ∃ result, applyFrame0 s a = some result := by
  cases pending : s.pending with
  | nil => simp [isPlayDeclaration, pending] at play
  | cons frame rest =>
    cases frame <;> simp [isPlayDeclaration, pending] at play
    all_goals cases action : a.kind <;> simp [action] at play
    all_goals
      simp only [LegalFrame, pending, action] at legal
      simp only [applyFrame0, pending, action]
    case cons.priority.playCard =>
      exact applyPlayCard_isSome (rest := rest) wf legal.2.1 legal.2.2.1
    case cons.chainPass.playCard p _ c pay ts flow _ pick =>
      have playable : castable s p c pay ts flow pick = true ∨
          ∃ d xs choice, Riftbound.playable s p c pay d xs choice = true := by
        rcases reactable_spec.mp legal.2.2.1 with ⟨(h | h) | h, -⟩ | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr ⟨none, ts, pick, h.2.2⟩
        · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h.2
          exact Or.inr ⟨some b, ts, pick, hb⟩
        · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h.2
          exact Or.inr ⟨some b, ts, pick, hb⟩
      exact reactStep_isSome (new := .chainPass p 0 :: rest) wf legal.2.1 playable
    case cons.showdown.playCard bf p _ _ _ _ _ _ _ =>
      exact reactStep_isSome (new := .chainPass p 0 :: .showdown bf p 0 :: rest)
        wf legal.2.1 (showdownable_spec legal.2.2.1)
    case cons.teamInvitation.playCard p _ _ _ _ _ _ =>
      exact reactStep_isSome (new := .chainPass p 0 :: rest) wf legal.2.1 (.inl legal.2.2.1)
    case cons.showdown.activate =>
      simp only [activatableSD, Bool.and_eq_true] at legal
      exact activateStep_isSome legal.2.1.1
    all_goals exact activateStep_isSome legal.2.1

private theorem advance_playDeclaration_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (play : isPlayDeclaration s a = true) (legal : Legal s a) :
    ∃ initial before t used events, applyDeclaredAction s a = some (initial, before) ∧
      AdvancePrefix initial t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  cases needs : s.actionDeathCostChoice a with
  | some choice =>
    obtain ⟨target, who, first, other⟩ := choice
    let next := { s with pending := .eitherDo who target {} first other .nil :: .resumeCost a :: s.pending }
    have applied : applyDeclaredAction s a = some (next, []) := by
      simp only [applyDeclaredAction, needs, next]
    exact ⟨next, [], next, 0, [], applied, by intro fuel prior; simp, rfl⟩
  | none =>
    have regular := isPlayDeclaration_regular play
    obtain ⟨⟨raw, events⟩, applied⟩ := playDeclaration_isSome wf play (legal.frame regular)
    obtain ⟨same, plan⟩ := playDeclaration_raw play applied
    apply advance_observed_frame_to_decision needs regular applied
      (applyFrame_wf0 wf (legal.frame regular) applied) (same.symm ▸ reads)
    intro next notices safe checked stack
    rcases plan with ⟨rest, pending, decision, _⟩ | ⟨body, rest, pending, finite, decision, _⟩
    · exact advance_observed_cleanup_to_decision next notices safe checked (stack.trans pending) decision
    · refine advance_observed_runs_then next notices safe checked ⟨rest, stack.trans pending, Or.inl rfl⟩
        finite (isOrdinaryDecisionTail_front decision) ?_
      intro t _ _ resumed
      exact ⟨t, 0, [], by intro fuel prior; simp, resumed.symm ▸ isOrdinaryDecisionTail_boundary decision⟩

/-- A legal card play or activation reaches a decision through any Recycle payment,
replacement prompt, or event observation that the declaration starts. -/
theorem step_playDeclaration_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (play : isPlayDeclaration s a = true) (legal : Legal s a) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  obtain ⟨_, before, t, used, events, declared, path, stopped⟩ :=
    advance_playDeclaration_to_decision wf reads play legal
  refine ⟨t, used, before ++ events, stopped, fun extra => ?_⟩
  simp only [step, ite_eq_left legal, declared]
  exact path extra before

private theorem advance_playDeclaration_to_preparedDecision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (play : isPlayDeclaration s a = true) (legal : Legal s a)
    (quiet : ∀ p tail, s.pending = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ initial before t used events, applyDeclaredAction s a = some (initial, before) ∧
      AdvancePrefix initial t used events ∧ t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  cases needs : s.actionDeathCostChoice a with
  | some choice =>
    obtain ⟨target, who, first, other⟩ := choice
    let next := { s with pending := .eitherDo who target {} first other .nil :: .resumeCost a :: s.pending }
    have applied : applyDeclaredAction s a = some (next, []) := by
      simp only [applyDeclaredAction, needs, next]
    exact ⟨next, [], next, 0, [], applied, by intro fuel prior; simp, rfl⟩
  | none =>
    have regular := isPlayDeclaration_regular play
    obtain ⟨⟨raw, events⟩, applied⟩ := playDeclaration_isSome wf play (legal.frame regular)
    obtain ⟨same, plan⟩ := playDeclaration_raw play applied
    apply advance_observed_frame_to_preparedDecision needs regular applied
      (applyFrame_wf0 wf (legal.frame regular) applied) (same.symm ▸ reads)
    intro next notices safe checked stack
    rcases plan with ⟨rest, pending, decision, fromOriginal⟩ | ⟨body, rest, pending, finite, decision, nonNeutral⟩
    · exact advance_observed_cleanup_to_preparedDecision next notices safe checked (stack.trans pending) decision
        (fun p tail atEnd => quiet p tail (fromOriginal p tail atEnd))
    · refine advance_observed_runs_then_prepared next notices safe checked ⟨rest, stack.trans pending, Or.inl rfl⟩
        finite (isOrdinaryDecisionTail_front decision) ?_
      intro t _ _ resumed
      have ready := GameState.prepared_idle_of_nonpriority (resumed.symm ▸ nonNeutral.idle)
        (resumed.symm ▸ nonNeutral.ne_priority)
      exact ⟨t, 0, [], by intro fuel prior; simp, ready⟩

/-- A legal card play or activation returns a prepared decision after payment, replacement
and observed Cleanup. The declared action and automatic work contribute their events in order. -/
theorem step_playDeclaration_to_preparedDecision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (play : isPlayDeclaration s a = true) (legal : Legal s a)
    (quiet : ∀ p tail, s.pending = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
  obtain ⟨_, before, t, used, events, declared, path, ready⟩ :=
    advance_playDeclaration_to_preparedDecision wf reads play legal quiet
  refine ⟨t, used, before ++ events, ready, ?_, ?_⟩
  · intro extra
    simp only [step, ite_eq_left legal, declared]
    exact path extra before
  · simp only [step, ite_eq_left legal, declared]
    exact path.finish ready before

private theorem isPlayDeclaration_resume {s : GameState} {a : Action}
    (play : isPlayDeclaration s a = true) :
    a.kind ≠ .timeCalled ∧ s.pending.head?.all (fun f => !f.isWork) = true := by
  cases pending : s.pending with
  | nil => simp [isPlayDeclaration, pending] at play
  | cons frame rest =>
    cases frame <;> simp [isPlayDeclaration, pending] at play
    all_goals cases action : a.kind <;> simp [action] at play
    all_goals exact ⟨by simp, rfl⟩

/-- Retry a play or activation after its death replacement has been selected. The
dispatcher restores the original decision if the declaration is no longer legal. -/
theorem advance_locked_playDeclaration_to_decision {s : GameState} {a : Action} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .resumeCost a :: rest)
    (play : isPlayDeclaration { s with pending := rest } a = true) :
    ∃ t used events, AdvancePrefix s t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  let restored := { s with pending := rest }
  obtain ⟨notTime, decision⟩ := isPlayDeclaration_resume play
  have workRule : workStep s = if a.kind ≠ .timeCalled ∧ Legal restored a then
      applyDeclaredAction restored a else some (restored, []) := by
    simp only [workStep, pending]
    rfl
  by_cases permitted : Legal restored a
  · obtain ⟨initial, before, t, used, events, applied, ran, stop⟩ :=
      advance_playDeclaration_to_decision (s := restored) (wf.congr rfl rfl rfl rfl) reads play permitted
    have work : workStep s = some (initial, before) := by
      rw [workRule, ite_eq_left ⟨notTime, permitted⟩]
      exact applied
    exact ⟨t, used + 1, before ++ events, ran.prepend pending rfl work, stop⟩
  · have work : workStep s = some (restored, []) := by
      rw [workRule, ite_eq_right (fun h => permitted h.2)]
    have stable : AdvancePrefix restored restored 0 [] := by intro _ _; simp
    exact ⟨restored, 1, [], stable.prepend pending rfl work, decision⟩

/-- Resume the locked declaration, or prepare the restored decision if it became illegal. -/
theorem advance_locked_playDeclaration_to_preparedDecision {s : GameState} {a : Action} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .resumeCost a :: rest)
    (play : isPlayDeclaration { s with pending := rest } a = true)
    (quiet : ∀ p tail, rest = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  let restored := { s with pending := rest }
  have restoredWF : restored.WF := wf.congr rfl rfl rfl rfl
  obtain ⟨notTime, decision⟩ := isPlayDeclaration_resume play
  have workRule : workStep s = if a.kind ≠ .timeCalled ∧ Legal restored a then
      applyDeclaredAction restored a else some (restored, []) := by
    simp only [workStep, pending]
    rfl
  by_cases permitted : Legal restored a
  · obtain ⟨initial, before, t, used, events, applied, ran, ready⟩ :=
      advance_playDeclaration_to_preparedDecision (s := restored) restoredWF reads play permitted quiet
    have work : workStep s = some (initial, before) := by
      rw [workRule, ite_eq_left ⟨notTime, permitted⟩]
      exact applied
    exact ⟨t, used + 1, before ++ events, ran.prepend pending rfl work, ready⟩
  · have work : workStep s = some (restored, []) := by
      rw [workRule, ite_eq_right (fun h => permitted h.2)]
    obtain ⟨t, used, events, path, ready⟩ :=
      advance_waiting_to_preparedDecision (s := restored) restoredWF reads decision quiet
    exact ⟨t, used + 1, events, by simpa only [List.nil_append] using path.prepend pending rfl work, ready⟩

/-- Check the replacement program and identify the card play or activation it resumes. -/
def playCostAnswerWorkSupported (s : GameState) (a : Action) : Bool :=
  isChainEffectAnswer s a && (applyFrame0 s a).any (fun result =>
    (result.1.pending.takeWhile isRunFrame).all runFrameSupported &&
      match result.1.pending.dropWhile isRunFrame with
      | .resumeCost locked :: rest => isPlayDeclaration { result.1 with pending := rest } locked
      | _ => false)

/-- A checked replacement answer resumes the locked declaration and reaches the next
decision through the actual dispatcher. -/
theorem step_playCostAnswer_checked_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : playCostAnswerWorkSupported s a = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  unfold playCostAnswerWorkSupported at supported
  obtain ⟨answer, condition⟩ := Bool.and_eq_true_iff.mp supported
  cases applied : applyFrame0 s a with
  | none => simp [applied] at condition
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some, Bool.and_eq_true_iff] at condition
    obtain ⟨programs, continuation⟩ := condition
    split at continuation
    · rename_i locked rest layout
      obtain ⟨noCost, regular, cards⟩ := chainEffectAnswer_rule answer applied
      apply step_observed_frame_to_decision legal noCost regular applied
        (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads)
      intro next observed safe checked stack
      have shape : raw.pending = raw.pending.takeWhile isRunFrame ++ .resumeCost locked :: rest := by
        rw [← layout, List.takeWhile_append_dropWhile]
      refine advance_observed_runs_then next observed safe checked
        ⟨_, stack.trans shape, Or.inl rfl⟩
        (fun f member => runFrameSupported_finite (List.all_eq_true.mp programs f member)) ?_ ?_
      · intro f head
        obtain rfl := Option.some.inj head
        exact ⟨rfl, by intro q eq; cases eq⟩
      · intro t wf reads resumed
        exact advance_locked_playDeclaration_to_decision wf reads resumed continuation
    · contradiction
/-- A checked replacement answer resumes the locked declaration and reaches the next
decision through the actual dispatcher. -/
theorem step_playCostAnswer_checked_to_preparedDecision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (supported : playCostAnswerWorkSupported s a = true)
    (quiet : ∀ raw emitted locked owner tail, applyFrame0 s a = some (raw, emitted) →
      raw.pending.dropWhile isRunFrame = .resumeCost locked :: .priority owner :: tail →
      ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
  unfold playCostAnswerWorkSupported at supported
  obtain ⟨answer, condition⟩ := Bool.and_eq_true_iff.mp supported
  cases applied : applyFrame0 s a with
  | none => simp [applied] at condition
  | some result =>
    obtain ⟨raw, events⟩ := result
    simp only [applied, Option.any_some, Bool.and_eq_true_iff] at condition
    obtain ⟨programs, continuation⟩ := condition
    split at continuation
    · rename_i locked rest layout
      obtain ⟨noCost, regular, cards⟩ := chainEffectAnswer_rule answer applied
      apply step_observed_frame_to_preparedDecision legal noCost regular applied
        (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads)
      intro next observed safe checked stack
      have shape : raw.pending = raw.pending.takeWhile isRunFrame ++ .resumeCost locked :: rest := by
        rw [← layout, List.takeWhile_append_dropWhile]
      refine advance_observed_runs_then_prepared next observed safe checked
        ⟨_, stack.trans shape, Or.inl rfl⟩
        (fun f member => runFrameSupported_finite (List.all_eq_true.mp programs f member)) ?_ ?_
      · intro f head
        obtain rfl := Option.some.inj head
        exact ⟨rfl, by intro q eq; cases eq⟩
      · intro t wf reads resumed
        apply advance_locked_playDeclaration_to_preparedDecision wf reads resumed continuation
        intro owner tail neutral
        exact quiet raw events locked owner tail applied (by rw [layout, neutral])
    · contradiction

end Riftbound

end
