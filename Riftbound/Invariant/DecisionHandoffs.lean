module

public import Riftbound.Invariant.ChainAnswerWork

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

end Riftbound

end
