module

public import Riftbound.Invariant.ChainAnswerWork
import Riftbound.Invariant.Sound
import Riftbound.Invariant.ClockRun

/-! # Decisions that hand play to another seat or keep an assignment open (I12) -/

@[expose] public section

namespace Riftbound

/-- A Showdown Pass before the last gives Focus to the next participant. -/
theorem step_showdownPass_next_to_decision {s : GameState} {p : PlayerId} {field : ObjId}
    {passes : Nat} {rest : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .showdown field p passes :: rest)
    (remaining : passes + 1 < s.participatingCount) (legal : Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .pass⟩ = advance extra t events := by
  let a : Action := ⟨.player p, .pass⟩
  let raw := { s with pending := .showdown field (s.nextParticipant p) (passes + 1) :: rest }
  have applied : applyFrame0 s a = some (raw, []) := by
    simp only [applyFrame0, pending, a, remaining, ite_true, raw]
  have noCost : s.actionDeathCostChoice a = none := by
    simp only [GameState.actionDeathCostChoice, pending, a, GameState.actionKillCosts,
      GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads rfl

/-- An invitation opens a teammate's decision without starting a Chain. -/
theorem step_inviteTeammate_to_decision {s : GameState} {p guest : PlayerId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .inviteTeammate guest⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .inviteTeammate guest⟩ = advance extra t events := by
  let a : Action := ⟨.player p, .inviteTeammate guest⟩
  let raw := { s with pending := .teamInvitation guest :: .priority p :: rest }
  have applied : applyFrame0 s a = some (raw, []) := by simp only [applyFrame0, pending, a, raw]
  have noCost : s.actionDeathCostChoice a = none := by
    simp only [GameState.actionDeathCostChoice, pending, a, GameState.actionKillCosts,
      GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads rfl

/-- Passing on a teammate invitation restores the waiting continuation. -/
theorem step_teamInvitationPass_to_decision {s : GameState} {guest : PlayerId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .teamInvitation guest :: rest)
    (legal : Legal s ⟨.player guest, .pass⟩) (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player guest, .pass⟩ = advance extra t events := by
  let a : Action := ⟨.player guest, .pass⟩
  let raw := { s with pending := rest }
  have applied : applyFrame0 s a = some (raw, []) := by simp only [applyFrame0, pending, a, raw]
  have noCost : s.actionDeathCostChoice a = none := by
    simp only [GameState.actionDeathCostChoice, pending, a, GameState.actionKillCosts,
      GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads decision

/-- Selecting a unit for damage assignment keeps the decision open. -/
theorem step_assignPick_to_decision {s : GameState} {field unit : ObjId} {attacker side : PlayerId}
    {chosen : List ObjId} {done : List (ObjId × Nat)} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .assign field attacker side chosen done :: rest)
    (legal : Legal s ⟨.player side, .assignPick unit⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player side, .assignPick unit⟩ = advance extra t events := by
  let a : Action := ⟨.player side, .assignPick unit⟩
  let raw := { s with pending := .assign field attacker side (chosen ++ [unit]) done :: rest }
  have applied : applyFrame0 s a = some (raw, []) := by simp only [applyFrame0, pending, a, raw]
  have noCost : s.actionDeathCostChoice a = none := by simp only [GameState.actionDeathCostChoice, pending]
  exact step_observed_action_waits legal (by intro eq; cases eq) noCost applied (wf.congr rfl rfl rfl rfl) reads rfl

/-- Setting aside a legal opening card returns to the same player's Mulligan decision. -/
theorem step_mulliganPick_to_decision {s : GameState} {p : PlayerId} {card : ObjId}
    {count : Nat} {rest : List Frame} (wf : s.WF) (owners : s.OwnerOk)
    (reads : MightRead.database s.cards) (pending : s.pending = .mulligan p count :: rest)
    (legal : Legal s ⟨.player p, .mulliganPick card⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .mulliganPick card⟩ = advance extra t events := by
  let a : Action := ⟨.player p, .mulliganPick card⟩
  have ordinary : a.kind ≠ .concede := by intro equal; cases equal
  obtain ⟨result, applied⟩ := applyFrame_isSome0 wf owners (Legal.frame (a := a) legal ordinary)
  have rawResult := applied
  simp only [applyFrame0, pending, a, Option.map_eq_some_iff] at rawResult
  obtain ⟨⟨moved, id⟩, transfer, rfl⟩ := rawResult
  obtain ⟨_, _, movedSpec⟩ := moveObj_spec transfer
  have finalWF : ({ moved with pending := .mulligan p (count + 1) :: rest }).WF :=
    (moveObj_wf wf transfer).congr rfl rfl rfl rfl
  have finalReads := movedSpec.other.cards ▸ reads
  have noCost : s.actionDeathCostChoice a = none := by
    simp only [GameState.actionDeathCostChoice, pending]
  exact step_observed_action_waits legal ordinary noCost applied finalWF finalReads rfl

/-- A recorded time call at an input reaches a prepared decision and keeps the new deadline. -/
theorem step_timeCalled_to_preparedDecision {s : GameState} (wf : s.WF)
    (reads : MightRead.database s.cards) (legal : Legal s ⟨.clock, .timeCalled⟩)
    (waiting : s.pending.head?.all (fun f => !f.isWork) = true)
    (quiet : ∀ p tail, s.pending = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, t.clock = some (s.config.ruleSet.callClock s.turn) ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.clock, .timeCalled⟩ = advance extra t events) ∧
      step used s ⟨.clock, .timeCalled⟩ = .ok (t, events) := by
  let action : Action := ⟨.clock, .timeCalled⟩
  have regular : action.kind ≠ .concede := by decide
  have noCost : s.actionDeathCostChoice action = none := by
    cases stack : s.pending with
    | nil => simp [GameState.actionDeathCostChoice, stack]
    | cons frame rest =>
      cases frame <;> simp [GameState.actionDeathCostChoice, GameState.actionKillCosts, stack, action,
        GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil]
  have applied := applyFrame0_timeCalled s .clock
  obtain ⟨t, used, events, ready, path, done⟩ :=
    step_observed_waiting_to_preparedDecision legal regular noCost applied
      (wf.congr rfl rfl rfl rfl) reads waiting quiet
  have noClock := (legal_timeCalled (a := action) rfl (legal.frame regular)).2.2.2.1
  have clockOk : ClockOk s := by
    intro clock old
    rw [noClock] at old
    cases old
  exact ⟨t, used, events, (step_keep clockOk done).2.2 rfl, ready, path, done⟩

end Riftbound

end
