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

private theorem priorityMana_applies {s : GameState} {p : PlayerId} {rest : List Frame}
    {source : ObjId} {index : Nat} {pay : RunePool.Payment} {chosen : Option ObjId}
    (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .manaAbility source index pay chosen⟩) :
    s.actionDeathCostChoice ⟨.player p, .manaAbility source index pay chosen⟩ = none ∧
      ∃ raw events, applyFrame0 s ⟨.player p, .manaAbility source index pay chosen⟩ = some (raw, events) ∧
        raw.cards = s.cards ∧ raw.pending = .cleanup :: .priority p :: rest := by
  let action : Action := ⟨.player p, .manaAbility source index pay chosen⟩
  have regular : action.kind ≠ .concede := by intro eq; cases eq
  have frame := legal.frame regular
  simp only [LegalFrame, pending] at frame
  obtain ⟨⟨board, events⟩, mana⟩ := applyMana_isSome frame.2
  let raw := { board with pending := .cleanup :: .priority p :: rest }
  have applied : applyFrame0 s action = some (raw, events) := by
    simp only [applyFrame0, pending, action, mana, Option.map_some, raw]
  have cards : raw.cards = s.cards := by
    obtain ⟨paid, pool, safe, eq⟩ := applyMana_cases mana
    change board.cards = s.cards
    rw [eq]
    have cardEq := congrArg GameState.cards safe.same
    exact cardEq
  have noCost := GameState.actionDeathCostChoice_of_noKill (s := s) (a := action) (by simp [GameState.actionKillCosts, pending, action])
  exact ⟨noCost, raw, events, applied, cards, rfl⟩

/-- The immediate Add at ordinary priority is followed by Cleanup before priority is restored. -/
theorem step_priorityMana_to_decision {s : GameState} {p : PlayerId} {rest : List Frame}
    {source : ObjId} {index : Nat} {pay : RunePool.Payment} {chosen : Option ObjId}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .priority p :: rest)
    (legal : Legal s ⟨.player p, .manaAbility source index pay chosen⟩) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .manaAbility source index pay chosen⟩ = advance extra t events := by
  obtain ⟨noCost, raw, events, applied, cards, layout⟩ := priorityMana_applies pending legal
  have regular : (⟨.player p, .manaAbility source index pay chosen⟩ : Action).kind ≠ .concede := by
    intro equal
    cases equal
  apply step_observed_frame_to_decision legal noCost regular applied
    (applyFrame_wf0 wf (legal.frame regular) applied) (cards.symm ▸ reads)
  intro next observed sound checked stack
  exact advance_observed_cleanup_to_decision next observed sound checked (stack.trans layout) rfl

private inductive ResourceActivationRoute : List Frame → List Frame → Prop where
  | waiting (stack : List Frame) :
      stack.head?.all (fun f => !f.isWork) = true → ResourceActivationRoute stack stack
  | cleanup (p : PlayerId) (rest : List Frame) :
      ResourceActivationRoute (.priority p :: rest) (.cleanup :: .priority p :: rest)

private theorem ResourceActivationRoute.of_waiting {s raw : GameState}
    (same : raw.pending = s.pending) (waits : s.pending.head?.all (fun f => !f.isWork) = true) :
    ResourceActivationRoute s.pending raw.pending :=
  same.symm ▸ .waiting s.pending waits

private theorem resourceActivation_regular {a : Action} (resource : a.kind.isResourceActivation = true) :
    a.kind ≠ .concede := by
  intro equal
  rw [equal] at resource
  contradiction

private theorem resourceActivation_applies {s : GameState} {a : Action}
    (wf : s.WF) (legal : Legal s a) (resource : a.kind.isResourceActivation = true) :
    s.actionDeathCostChoice a = none ∧
      ∃ raw events, applyFrame0 s a = some (raw, events) ∧ raw.cards = s.cards ∧
        ResourceActivationRoute s.pending raw.pending := by
  have regular := resourceActivation_regular resource
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
        have applied : applyFrame0 s a = some (board, events) := by
          simp only [applyFrame0, pending, kind]
          exact rune
        have unchanged := applyRune_sameMeta rune
        exact ⟨noCost, board, events, applied, unchanged.cards,
          by rw [← pending]; exact ResourceActivationRoute.of_waiting unchanged.pending waits⟩
    case manaAbility source index pay chosen =>
      cases frame <;> simp only [LegalFrame, pending, kind] at frameLegal <;> try contradiction
      case priority p =>
        have actor : a.actor = .player p := frameLegal.1
        have action : a = ⟨.player p, .manaAbility source index pay chosen⟩ := by
          cases a
          simp_all
        subst a
        obtain ⟨noCost, raw, events, applied, cards, layout⟩ := priorityMana_applies pending legal
        exact ⟨noCost, raw, events, applied, cards, by rw [layout]; exact .cleanup p rest⟩
      all_goals
        have noCost := GameState.actionDeathCostChoice_of_noKill (s := s) (a := a)
          (by simp [GameState.actionKillCosts, pending, kind])
        have waits : s.pending.head?.all (fun f => !f.isWork) = true := by rw [pending]; rfl
        obtain ⟨⟨board, events⟩, mana⟩ :=
          applyMana_isSome (by first | exact frameLegal.2 | exact frameLegal.2.1)
        have applied : applyFrame0 s a = some (board, events) := by
          simp only [applyFrame0, pending, kind]
          exact mana
        have same := (applyMana_meta mana).2.2.2.2
        obtain ⟨paid, pool, safe, rfl⟩ := applyMana_cases mana
        exact ⟨noCost, _, events, applied, safe.same.cards,
          by rw [← pending]; exact ResourceActivationRoute.of_waiting same waits⟩

/-- A legal Rune or immediate Add reaches the next decision through all legal input windows,
including Add during payment and Cleanup after the ordinary-priority Add. -/
theorem step_resourceActivation_to_decision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (resource : a.kind.isResourceActivation = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s a = advance extra t events := by
  have regular := resourceActivation_regular resource
  obtain ⟨noCost, raw, events, applied, cards, route⟩ := resourceActivation_applies wf legal resource
  have safe := applyFrame_wf0 wf (legal.frame regular) applied
  generalize start : s.pending = before at route
  generalize finish : raw.pending = after at route
  cases route with
  | waiting stack idle =>
    exact step_observed_action_waits legal regular noCost applied safe (cards.symm ▸ reads) (finish ▸ idle)
  | cleanup p rest =>
    apply step_observed_frame_to_decision legal noCost regular applied safe (cards.symm ▸ reads)
    intro next observed nextWF checked stack
    exact advance_observed_cleanup_to_decision next observed nextWF checked (stack.trans finish) rfl

/-- A legal Rune or immediate Add succeeds with finite fuel. The neutral priority
continuation may first require Cleanup, followed by any choice or trigger it creates. -/
theorem step_resourceActivation_to_preparedDecision {s : GameState} {a : Action}
    (wf : s.WF) (reads : MightRead.database s.cards) (legal : Legal s a)
    (resource : a.kind.isResourceActivation = true)
    (quiet : ∀ p rest, s.pending = .priority p :: rest → ∀ f ∈ rest, f.observesCombat = false) :
    ∃ t used events, t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s a = advance extra t events) ∧
      step used s a = .ok (t, events) := by
  have regular := resourceActivation_regular resource
  obtain ⟨noCost, raw, events, applied, cards, route⟩ := resourceActivation_applies wf legal resource
  have safe := applyFrame_wf0 wf (legal.frame regular) applied
  generalize start : s.pending = before at route
  generalize finish : raw.pending = after at route
  cases route with
  | waiting stack idle =>
    exact step_observed_waiting_to_preparedDecision legal regular noCost applied safe (cards.symm ▸ reads)
      (finish ▸ idle) (fun p rest same => quiet p rest (start.trans (finish.symm.trans same)))
  | cleanup p rest =>
    apply step_observed_frame_to_preparedDecision legal noCost regular applied safe (cards.symm ▸ reads)
    intro next observed nextWF checked stack
    apply advance_observed_cleanup_to_preparedDecision next observed nextWF checked (stack.trans finish) rfl
    intro owner suffix same
    exact quiet owner suffix (start.trans same)

end Riftbound

end
