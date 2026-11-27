module

public import Riftbound.Invariant.MovementWork

/-!
# Immediate resource activations (I12)

Basic Runes and Add abilities enter the same event observer as other actions.
Add at ordinary priority also runs Cleanup before returning to a decision.
-/

@[expose] public section

namespace Riftbound

/-- Resource gains add their full total to the balance left after payment. A sequence of
fixed gains contributes the sum of its parts. -/
theorem ManaKind.total_add (kind : ManaKind) (pool : RunePool) (payment : RunePool.Payment) :
    (kind.add pool payment).total = pool.total + (kind.add {} payment).total := by
  induction kind generalizing pool with
  | combined first second firstTotal secondTotal =>
    simp only [ManaKind.add]
    rw [secondTotal (first.add pool payment), secondTotal (first.add {} payment), firstTotal, Nat.add_assoc]
  | power domain amount =>
    cases domain <;> simp [ManaKind.add, RunePool.total, RunePool.totalPower, RunePool.addPower] <;> omega
  | energy amount | unitEnergy amount | spellEnergy amount | any amount | gear amount |
      permanent | powerToEnergy | energyToPower =>
    simp [ManaKind.add, RunePool.total, RunePool.totalPower, RunePool.addEnergy, RunePool.addAny,
      RunePool.addUnitEnergy, RunePool.addSpellEnergy] <;> omega

/-- Basic Rune and immediate Add activations. Legality determines which windows permit them. -/
def ActionKind.isResourceActivation : ActionKind → Bool
  | .runeAbility .. | .manaAbility .. => true
  | _ => false

private theorem GameState.actionDeathCostChoice_of_noKill {s : GameState} {a : Action}
    (noKill : s.actionKillCosts a = []) : s.actionDeathCostChoice a = none := by
  unfold GameState.actionDeathCostChoice
  split <;> simp [noKill, GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil]

private theorem step_rune_to_decision {s board : GameState} {a : Action} {p : PlayerId}
    {card : ObjId} {ability : RuneAbility} {events : List Event}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a) (regular : a.kind ≠ .concede)
    (noCost : s.actionDeathCostChoice a = none) (rest : s.pending.head?.all (fun f => !f.isWork) = true)
    (rune : applyRune s p card ability = some (board, events))
    (applied : applyFrame0 s a = some (board, events)) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  have cards : board.cards = s.cards := by
    have cardEq := congrArg GameState.cards (applyRune_sameMeta rune)
    exact cardEq
  exact step_observed_action_waits legal regular noCost applied (applyRune_wf wf rune)
    (cards.symm ▸ reads) ((applyRune_sameMeta rune).pending.symm ▸ rest)

private theorem step_fastMana_to_decision {s board : GameState} {a : Action} {p : PlayerId}
    {source : ObjId} {index : Nat} {pay : RunePool.Payment} {chosen : Option ObjId} {events : List Event}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a) (regular : a.kind ≠ .concede)
    (noCost : s.actionDeathCostChoice a = none) (rest : s.pending.head?.all (fun f => !f.isWork) = true)
    (mana : applyMana s p source index pay chosen = some (board, events))
    (applied : applyFrame0 s a = some (board, events)) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  obtain ⟨paid, pool, safe, rfl⟩ := applyMana_cases mana
  have cards : (paid.setPool p pool).cards = s.cards := by
    have cardEq := congrArg GameState.cards safe.same
    exact cardEq
  exact step_observed_action_waits legal regular noCost applied (applyMana_wf wf mana)
    (cards.symm ▸ reads) ((applyMana_meta mana).2.2.2.2.symm ▸ rest)

/-- The immediate Add at ordinary priority is followed by Cleanup before priority is restored. -/
theorem step_priorityMana_to_decision {s : GameState} {p : PlayerId} {rest : List Frame}
    {source : ObjId} {index : Nat} {pay : RunePool.Payment} {chosen : Option ObjId}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .manaAbility source index pay chosen⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .manaAbility source index pay chosen⟩ = advance extra t events := by
  let action : Action := ⟨.player p, .manaAbility source index pay chosen⟩
  have regular : action.kind ≠ .concede := by intro eq; cases eq
  have frame := legal.frame regular
  simp only [LegalFrame, pending] at frame
  obtain ⟨⟨board, events⟩, mana⟩ := applyMana_isSome frame.2
  let raw := { board with pending := .cleanup :: .priority p :: rest }
  have applied : applyFrame0 s action = some (raw, events) := by
    simp only [applyFrame0, pending, action, mana, Option.map_some, raw]
  have rawWF : raw.WF := (applyMana_wf wf mana).congr rfl rfl rfl rfl
  have cards : raw.cards = s.cards := by
    obtain ⟨paid, pool, safe, eq⟩ := applyMana_cases mana
    change board.cards = s.cards
    rw [eq]
    have cardEq := congrArg GameState.cards safe.same
    exact cardEq
  have noCost := GameState.actionDeathCostChoice_of_noKill (s := s) (a := action) (by simp [GameState.actionKillCosts, pending, action])
  apply step_observed_frame_to_decision legal noCost regular applied rawWF (cards.symm ▸ reads)
  intro next observed wf reads stack
  exact advance_observed_cleanup_to_decision next observed wf reads stack rfl

/-- A legal Rune or immediate Add reaches the next decision through all legal input windows,
including Add during payment and Cleanup after the ordinary-priority Add. -/
theorem step_resourceActivation_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (resource : a.kind.isResourceActivation = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  have regular : a.kind ≠ .concede := by
    intro eq
    rw [eq] at resource
    contradiction
  have frameLegal := legal.frame regular
  cases pending : s.pending with
  | nil => cases kind : a.kind <;> simp [ActionKind.isResourceActivation, kind] at resource <;>
      simp [LegalFrame, pending, kind] at frameLegal
  | cons frame rest =>
    cases kind : a.kind <;> simp [ActionKind.isResourceActivation, kind] at resource
    case runeAbility =>
      cases frame <;> simp only [LegalFrame, pending, kind] at frameLegal <;> try contradiction
      all_goals
        have noCost := GameState.actionDeathCostChoice_of_noKill (s := s) (a := a)
          (by simp [GameState.actionKillCosts, pending, kind])
        have waits : s.pending.head?.all (fun f => !f.isWork) = true := by rw [pending]; rfl
        obtain ⟨⟨board, events⟩, rune⟩ :=
          applyRune_isSome wf frameLegal.2.1 (by first | exact frameLegal.2.2 | exact frameLegal.2.2.1)
        exact step_rune_to_decision wf reads legal regular noCost waits rune
          (by simp only [applyFrame0, pending, kind]; exact rune)
    case manaAbility source index pay chosen =>
      cases frame <;> simp only [LegalFrame, pending, kind] at frameLegal <;> try contradiction
      case priority p =>
        have actor : a.actor = .player p := frameLegal.1
        have action : a = ⟨.player p, .manaAbility source index pay chosen⟩ := by
          cases a
          simp_all
        subst a
        exact step_priorityMana_to_decision wf reads pending legal
      all_goals
        have noCost := GameState.actionDeathCostChoice_of_noKill (s := s) (a := a)
          (by simp [GameState.actionKillCosts, pending, kind])
        have waits : s.pending.head?.all (fun f => !f.isWork) = true := by rw [pending]; rfl
        obtain ⟨⟨board, events⟩, mana⟩ :=
          applyMana_isSome (by first | exact frameLegal.2 | exact frameLegal.2.1)
        exact step_fastMana_to_decision wf reads legal regular noCost waits mana
          (by simp only [applyFrame0, pending, kind]; exact mana)

end Riftbound

end
