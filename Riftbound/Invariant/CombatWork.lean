module

public import Riftbound.Invariant.ObservedCleanupWork
public import Riftbound.Invariant.DamageWork
public import Riftbound.Invariant.Step

/-!
# Combat work under the observed dispatcher (I12)

The final Showdown Pass and assignment confirmation may present a replacement or assignment
decision, or advance through damage, recall, control and Combat Cleanup.
-/

@[expose] public section

namespace Riftbound

/-- Announcing a Combat result resolves its immediate Adds, keeping any ordinary queue ahead of Control. -/
theorem advance_combat_result {s : GameState} {bf : ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .combatResult bf :: .combatControl bf :: rest) :
    AdvanceTo s (fun frames => frames = .combatControl bf :: rest) := by
  let continuation := Frame.combatControl bf :: rest
  let raw := { s with pending := continuation }
  let recalled := (s.combat.filter (·.battlefield == bf)).any (·.recalled)
  let notices := combatResultEvents s bf recalled
  have rule : microStep0 s = some (raw, notices) := by simp only [microStep0, pending, continuation, raw, recalled, notices]
  obtain ⟨mid, used, events, _, path, midWF, cards, route⟩ :=
    advance_rule_with_adds pending rfl rule (microStep_wf0 wf rule) rfl reads
  have front : ∀ f, continuation.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
    intro f head
    obtain rfl := Option.some.inj head
    exact ⟨rfl, by intro q h; cases h⟩
  change ObservedWorkStack continuation mid.pending at route
  generalize stack : mid.pending = ready at route
  cases route with
  | empty => exact ⟨mid, used, events, path, Or.inl (by rw [stack]; rfl)⟩
  | resume => exact ⟨mid, used, events, path, Or.inr ⟨stack, midWF, cards⟩⟩
  | queue q ne =>
    have waiting := stack.trans (insertTriggers_front q continuation front)
    obtain ⟨t, elapsed, _, _, _, resolved, decisionStack, decision⟩ :=
      advance_triggers_to_decision mid midWF q continuation waiting (cards ▸ reads) (Or.inl ne)
    exact ⟨t, used + elapsed, events, by simpa only [List.append_nil] using path.append resolved,
      Or.inl (by simp [decisionStack, decision])⟩

private theorem observed_cleanup_step {s raw : GameState} {f : Frame} {rest cleanupTail : List Frame}
    {events : List Event} {keeps : List Frame → Prop} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = f :: rest) (automatic : f.isWork = true)
    (rule : microStep0 s = some (raw, events)) (known : raw.cards = s.cards)
    (after : raw.pending = .cleanup :: cleanupTail) (base : keeps cleanupTail)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  let tracked := ResolutionPrefix [.cleanup] keeps
  have entered : AdvanceTo s tracked :=
    .rule pending automatic rule (microStep_wf0 wf rule) known reads ⟨cleanupTail, after, base⟩
      (fun _ route q ne => route.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) inserted q ne)
  apply entered.then reads
  intro state safe checked continued
  obtain ⟨tail, cleanup, kept⟩ := continued
  obtain ⟨t, used, emitted, _, ran, done⟩ :=
    advance_cleanup_with_adds safe checked cleanup keeps kept inserted
  exact ⟨t, used, emitted, ran, done⟩

/-- Combat Cleanup heals, recalls and settles the board before the Combat result. -/
theorem advance_combat_recall {s : GameState} {bf : ObjId} {att : PlayerId} {rest : List Frame}
    {keeps : List Frame → Prop} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .combatResolve bf att :: rest) (base : keeps rest)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  let resolved := combatCleanup s bf att
  let recalled := resolved.2.any (fun | .recalled _ => true | _ => false)
  let raw := { resolved.1 with
    pending := .cleanup :: rest
    combat := resolved.1.combat.map (fun (c : CombatParticipation) => { c with recalled := recalled }) }
  have rule : microStep0 s = some (raw, resolved.2) := by
    simp only [microStep0, pending]
    rfl
  have known : raw.cards = s.cards := by
    have cards := congrArg GameState.cards (combatCleanup_safe s bf att).same
    exact cards
  exact observed_cleanup_step wf reads pending rfl rule known rfl base inserted

/-- Release temporary Combat effects and settle the board before the original continuation. -/
theorem advance_combat_finish {s : GameState} {bf : ObjId} {rest : List Frame}
    {keeps : List Frame → Prop} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .combatFinish bf :: rest) (base : keeps rest)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  let units := ((s.combat.filter (·.battlefield == bf)).map (·.units)).getD []
  let cleared := clearCombatExcess (s.mapObjects endShowdownObj) bf
  let raw := { cleared with combat := none, pending := .cleanup :: rest }
  have rule : microStep0 s = some (raw, [.combatEnded bf units]) := by
    simp only [microStep0, pending, units, raw, cleared]
  exact observed_cleanup_step wf reads pending rfl rule rfl rfl base inserted

/-- Resolve the optional draw for establishing control and the following Cleanup. -/
theorem advance_combat_control {s : GameState} {bf : ObjId} {rest : List Frame}
    {keeps : List Frame → Prop} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .combatControl bf :: rest) (base : keeps rest)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  let result := combatControl s bf
  let raw := { result.1 with pending := result.2.1 ++ Frame.cleanup :: rest }
  let cleaned := ResolutionPrefix [.cleanup] keeps
  let drawing := ResolutionPrefix result.2.1 cleaned
  have rule : microStep0 s = some (raw, result.2.2) := by simp only [microStep0, pending, raw, result]
  have known : raw.cards = s.cards := by
    change result.1.cards = s.cards
    obtain ⟨board, safe, changePoints⟩ := combatControl_safeP s bf
    have cards := congrArg GameState.cards safe.same
    rcases changePoints with normal | ⟨who, points, withPoints⟩
    · rw [show result.1 = board from normal]
      exact cards
    · rw [show result.1 = board.gainPoints who points from withPoints]
      exact cards
  have kept (stack : List Frame) (track : cleaned stack) (q : List PendTrigger) (ne : q ≠ []) :
      cleaned (insertTriggers q stack) :=
    track.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) inserted q ne
  have generated : ∀ f ∈ result.2.1, f.isResolution = true := by
    intro f member
    obtain ⟨_, rfl⟩ := combatControl_frames s bf f member
    rfl
  have entered : AdvanceTo s drawing :=
    .rule pending rfl rule (microStep_wf0 wf rule) known reads
      ⟨.cleanup :: rest, rfl, ⟨rest, rfl, base⟩⟩
      (fun _ route q ne => route.insert generated kept q ne)
  apply entered.then reads
  intro mid safe checked route
  have afterDraws := advance_draw_frames 1 (combatControl_frames s bf) safe checked route kept
  apply afterDraws.then checked
  intro t drawWF drawReads after
  obtain ⟨tail, cleanup, tracked⟩ := after
  obtain ⟨u, used, events, _, path, done⟩ :=
    advance_cleanup_with_adds drawWF drawReads cleanup keeps tracked inserted
  exact ⟨u, used, events, path, done⟩

private theorem advance_combat_leading {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (tail : TriggerWorkTail rest s.pending) :
    AdvanceTo s (fun frames => frames = rest) := by
  obtain ⟨t, used, path, done⟩ := advance_trigger_tail s rest wf reads tail
  exact ⟨t, used, [], path, done⟩

/-- Follow the automatic post-damage stages through the Combat result, Control and Cleanup.
A decision or sudden-death finish can interrupt any stage. -/
theorem advance_combat_after_damage {s : GameState} {bf : ObjId} {att : PlayerId}
    {tail rest : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .combatResolve bf att :: tail)
    (tracked : TriggerWorkTail (combatSteps bf ++ rest) tail)
    (base : keeps rest)
    (inserted : ∀ stack, keeps stack → ∀ queue, queue ≠ [] → keeps (insertTriggers queue stack)) :
    AdvanceTo s keeps := by
  have recalled : AdvanceTo s (TriggerWorkTail (combatSteps bf ++ rest)) :=
    advance_combat_recall wf reads pending tracked
      (fun _ track q ne => track.insert
        (by intro f h; cases Option.some.inj h; exact ⟨rfl, by intro _ e; cases e⟩) q ne)
  apply recalled.then reads
  intro t safe checked waiting
  apply (advance_combat_leading safe checked waiting).then checked
  intro resultState resultWF resultReads atResult
  apply (advance_combat_result resultWF resultReads atResult).then resultReads
  intro controlState controlWF controlReads atControl
  have control : AdvanceTo controlState (TriggerWorkTail (.combatFinish bf :: rest)) :=
    advance_combat_control controlWF controlReads atControl (Or.inl rfl)
      (fun _ track q ne => track.insert
        (by intro f h; cases Option.some.inj h; exact ⟨rfl, by intro _ e; cases e⟩) q ne)
  apply control.then controlReads
  intro drawState drawWF drawReads atDrawEnd
  apply (advance_combat_leading drawWF drawReads atDrawEnd).then drawReads
  intro finishState finishWF finishReads atFinish
  exact advance_combat_finish finishWF finishReads atFinish base inserted

private theorem damageOrderFrames_finite (s : GameState) (bf : ObjId) (att side : PlayerId)
    {f : Frame} (member : f ∈ damageOrderFrames s bf att side) : f.FiniteRun := by
  unfold damageOrderFrames at member
  split at member
  · simp at member
  · obtain ⟨u, _, built⟩ := List.mem_filterMap.mp member
    dsimp only at built
    split at built
    · obtain rfl := Option.some.inj built
      exact ⟨_, _, _, _, rfl, .cons (.orderCombatDamage _ _ _) .nil⟩
    · simp at built

private theorem choice_head {s : GameState} {bf : ObjId} {att side : PlayerId}
    {assigned : Frame} {done : List (ObjId × Nat)} {rest : List Frame}
    (ready : s.assignFrame bf att side done = some assigned) :
    ∃ f, (combatAssignmentChoices s bf side ++ assigned :: rest).head? = some f ∧
      f.isWork = false ∧ f.isResolution = false := by
  unfold GameState.assignFrame at ready
  split at ready
  · obtain rfl := Option.some.inj ready
    unfold combatAssignmentChoices
    dsimp only
    cases choices : List.filterMap _ (s.assignmentTargets bf side) with
    | nil => exact ⟨_, rfl, rfl, rfl⟩
    | cons first later =>
      have member : first ∈ List.filterMap
          (fun u => if s.isTank bf side u && s.hasBackline u &&
              ((s.assignmentTargets bf side).filter (fun u => !s.isTank bf side u && !s.hasBackline u)).any
                (fun peer => s.controllerOf peer == s.controllerOf u)
            then some (.eitherDo side u {} (.prim (.markOn .self (.combatAssignmentPriority .tank)))
              (.prim (.markOn .self (.combatAssignmentPriority .backline))) .nil)
            else none) (s.assignmentTargets bf side) := by rw [choices]; exact List.mem_cons_self
      obtain ⟨u, _, picked⟩ := List.mem_filterMap.mp member
      split at picked
      · obtain rfl := Option.some.inj picked
        exact ⟨_, rfl, rfl, rfl⟩
      · simp at picked
  · simp at ready

private theorem combat_result_head (bf : ObjId) (rest : List Frame) :
    ∀ f, (combatSteps bf ++ rest).head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
  intro f h
  obtain rfl := Option.some.inj h
  exact ⟨rfl, by intro q e; cases e⟩

private theorem advance_to_boundary {s : GameState} {keeps : List Frame → Prop}
    (work : AdvanceTo s keeps) (boundary : ∀ stack, keeps stack → stack.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix s t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨t, used, events, path, stop | ⟨tracked, _, _⟩⟩ := work
  · exact ⟨t, used, events, path, stop⟩
  · exact ⟨t, used, events, path, boundary t.pending tracked⟩

private theorem advance_combat_damage_to_cleanup {s : GameState} {bf : ObjId} {att : PlayerId}
    {rest : List Frame} {keeps : List Frame → Prop} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : ResolutionPrefix [.cleanup, .combatResolve bf att]
      (TriggerWorkTail (combatSteps bf ++ rest)) s.pending)
    (base : keeps rest)
    (inserted : ∀ stack, keeps stack → ∀ queue, queue ≠ [] → keeps (insertTriggers queue stack)) :
    AdvanceTo s keeps := by
  let continues := TriggerWorkTail (combatSteps bf ++ rest)
  let recalled := ResolutionPrefix [.combatResolve bf att] continues
  have insertKeeps (tail : List Frame) (tracked : continues tail) (q : List PendTrigger) (ne : q ≠ []) :
      continues (insertTriggers q tail) := tracked.insert (combat_result_head bf rest) q ne
  obtain ⟨tail, clear, waiting⟩ := pending
  obtain ⟨t, used, events, _, path, done⟩ :=
    advance_cleanup_with_adds wf reads clear recalled ⟨tail, rfl, waiting⟩
      (fun _ tracked q ne => tracked.insert
        (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) insertKeeps q ne)
  have cleanup : AdvanceTo s recalled := ⟨t, used, events, path, done⟩
  apply cleanup.then reads
  intro mid safe checked ran
  obtain ⟨tail, atRecall, tracked⟩ := ran
  exact advance_combat_after_damage safe checked atRecall tracked base inserted

/-- The automatic start of Combat Damage processes any replacement ordering, yields to
assignment if needed, and otherwise proceeds through the post-damage stages. -/
theorem advance_combat_damage {s : GameState} {bf : ObjId} {att : PlayerId} {rest : List Frame}
    {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .combatDamage bf att :: rest)
    (base : keeps rest)
    (inserted : ∀ stack, keeps stack → ∀ queue, queue ≠ [] → keeps (insertTriggers queue stack)) :
    AdvanceTo s keeps := by
  let combat := (s.observeCombat [.showdown bf att 0]).1
  let raw := { s with pending := s.startCombat bf att ++ combatSteps bf ++ rest, combat := combat }
  let defender := s.defenderAt bf att
  let orders := damageOrderFrames s bf att att ++ damageOrderFrames s bf att defender
  let final := combatSteps bf ++ rest
  have rule : microStep0 s = some (raw, []) := by simp only [microStep0, pending, combat, raw]
  have finite : ∀ f ∈ orders, f.FiniteRun := by
    intro f member
    rcases List.mem_append.mp member with first | second
    · exact damageOrderFrames_finite s bf att att first
    · exact damageOrderFrames_finite s bf att defender second
  have work (keeps : List Frame → Prop) (track : ResolutionPrefix orders keeps raw.pending)
      (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
      AdvanceTo s keeps := by
    have entered : AdvanceTo s (ResolutionPrefix orders keeps) :=
      .rule pending rfl rule (microStep_wf0 wf rule) rfl reads track
        (fun _ tracked q ne => tracked.insert (fun f member => (finite f member).isResolution) inserted q ne)
    exact entered.then reads (fun _ safe checked tracked =>
      advance_run_frames safe checked tracked finite inserted)
  have assign {side : PlayerId} {f : Frame} (assigned : s.assignFrame bf att side [] = some f)
      (stack : raw.pending = orders ++ (combatAssignmentChoices s bf side ++ f :: final)) :
      AdvanceTo s keeps := by
    let choices := combatAssignmentChoices s bf side ++ f :: final
    obtain ⟨choice, head, nonwork, nonresolution⟩ := choice_head (rest := final) assigned
    change choices.head? = some choice at head
    have insertChoices (tail : List Frame) (tracked : TriggerWorkTail choices tail) (q : List PendTrigger)
        (ne : q ≠ []) : TriggerWorkTail choices (insertTriggers q tail) := by
      apply tracked.insert _ q ne
      intro first firstHead
      obtain rfl := Option.some.inj (head.symm.trans firstHead)
      exact ⟨nonresolution, by intro q eq; cases eq; contradiction⟩
    have ordered := work (TriggerWorkTail choices) ⟨choices, stack, Or.inl rfl⟩ insertChoices
    refine ordered.then reads ?_
    intro t safe checked tracked
    obtain ⟨u, used, path, stop | ⟨atChoice, _, _⟩⟩ := advance_trigger_tail t choices safe checked tracked
    · exact ⟨u, used, [], path, Or.inl stop⟩
    · exact ⟨u, used, [], path, Or.inl (by simp [atChoice, head, nonwork])⟩
  cases attackerChoice : s.assignFrame bf att att [] with
  | some first =>
    apply assign attackerChoice
    simp only [raw, GameState.startCombat, ← show defender = s.defenderAt bf att from rfl,
      attackerChoice, orders, final, List.append_assoc, List.cons_append, List.nil_append]
  | none =>
    cases defenderChoice : s.assignFrame bf att defender [] with
    | some second =>
      apply assign defenderChoice
      simp only [raw, GameState.startCombat, ← show defender = s.defenderAt bf att from rfl,
        attackerChoice, defenderChoice, orders, final, List.append_assoc, List.cons_append, List.nil_append]
    | none =>
      let waiting := ResolutionPrefix [.cleanup, .combatResolve bf att] (TriggerWorkTail final)
      have tracked : ResolutionPrefix orders waiting raw.pending := by
        refine ⟨.cleanup :: .combatResolve bf att :: final, ?_, ⟨final, rfl, Or.inl rfl⟩⟩
        simp only [raw, GameState.startCombat, ← show defender = s.defenderAt bf att from rfl,
          attackerChoice, defenderChoice, orders, final, List.append_assoc, List.cons_append, List.nil_append]
      have ordered := work waiting tracked (fun _ route q ne => route.insert
        (by intro f member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> rfl)
        (fun _ tail q ne => tail.insert (combat_result_head bf rest) q ne) q ne)
      exact ordered.then reads (fun _ safe checked route =>
        advance_combat_damage_to_cleanup safe checked route base inserted)

private theorem advance_action_observation (raw : GameState) (notices : List Event)
    (wf : raw.WF) (reads : MightRead.database raw.cards) {keeps : List Frame → Prop}
    (base : keeps raw.pending)
    (inserted : ∀ stack, keeps stack → ∀ queue, queue ≠ [] → keeps (insertTriggers queue stack)) :
    AdvanceTo (raw.withTriggers notices) keeps := by
  obtain ⟨t, used, events, path, safe, cards, route⟩ :=
    advance_observed_work raw notices wf reads
  have known : t.cards = (raw.withTriggers notices).cards := by
    obtain ⟨_, _, updated⟩ := withTriggers_pending raw notices
    rw [updated]
    exact cards
  generalize stack : t.pending = frames at route
  cases route with
  | empty => exact ⟨t, used, events, path, Or.inl (by rw [stack]; rfl)⟩
  | resume => exact ⟨t, used, events, path, Or.inr ⟨stack.symm ▸ base, safe, known⟩⟩
  | queue q ne =>
    exact ⟨t, used, events, path, Or.inr ⟨stack.symm ▸ inserted raw.pending base q ne, safe, known⟩⟩

private theorem advance_action_observation_reads (raw : GameState) (notices : List Event)
    (reads : MightRead.database raw.cards) : MightRead.database (raw.withTriggers notices).cards := by
  obtain ⟨_, _, updated⟩ := withTriggers_pending raw notices
  rw [updated]
  exact reads

private def CombatContinuation (cleanups : Nat) (rest : List Frame) : List Frame → Prop :=
  ResolutionPrefix (List.replicate cleanups .cleanup) (TriggerWorkTail rest)

private theorem CombatContinuation.ready (cleanups : Nat) (rest : List Frame) :
    CombatContinuation cleanups rest (List.replicate cleanups .cleanup ++ rest) :=
  ⟨rest, rfl, Or.inl rfl⟩

private theorem CombatContinuation.insert {cleanups : Nat} {rest stack : List Frame}
    (continuation : CombatContinuation cleanups rest stack)
    (decision : rest.head?.all (fun f => !f.isWork) = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false)
    (q : List PendTrigger) (nonempty : q ≠ []) :
    CombatContinuation cleanups rest (insertTriggers q stack) := by
  have before : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
    intro f head
    refine ⟨front f head, ?_⟩
    intro q trigger
    have nonwork : f.isWork = false := by simpa [head] using decision
    cases trigger
    contradiction
  exact ResolutionPrefix.insert continuation (fun _ member => (List.eq_of_mem_replicate member).symm ▸ rfl)
    (fun _ tracked q ne => tracked.insert before q ne) q nonempty

private theorem advance_combat_cleanups {s : GameState} {rest : List Frame} (cleanups : Nat)
    (wf : s.WF) (reads : MightRead.database s.cards)
    (continuation : CombatContinuation cleanups rest s.pending)
    (decision : rest.head?.all (fun f => !f.isWork) = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false) :
    AdvanceTo s (fun frames => frames = rest) := by
  induction cleanups generalizing s with
  | zero =>
    obtain ⟨tail, atTail, tracked⟩ := continuation
    exact advance_combat_leading wf reads (atTail.symm ▸ tracked)
  | succ remaining ih =>
    obtain ⟨tail, atCleanup, tracked⟩ := continuation
    let keeps := CombatContinuation remaining rest
    obtain ⟨t, used, events, _, path, done⟩ :=
      advance_cleanup_with_adds wf reads atCleanup keeps ⟨tail, rfl, tracked⟩
        (fun _ continued q ne => continued.insert decision front q ne)
    have before : AdvanceTo s keeps := ⟨t, used, events, path, done⟩
    exact before.then reads (fun _ safe checked keeps => ih safe checked keeps)

private theorem advance_combat_to_decision {s : GameState} {rest : List Frame} {cleanups : Nat}
    (reads : MightRead.database s.cards) (run : AdvanceTo s (CombatContinuation cleanups rest))
    (decision : rest.head?.all (fun f => !f.isWork) = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false) :
    ∃ t used events, AdvancePrefix s t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  apply advance_to_boundary
    (run.then reads fun _ wf checked tail => advance_combat_cleanups cleanups wf checked tail decision front)
  intro _ atRest
  exact atRest.symm ▸ decision

private theorem applyDeclaredAction_showdownPass {s : GameState} {bf : ObjId} {p : PlayerId}
    {passes : Nat} {rest : List Frame} (pending : s.pending = .showdown bf p passes :: rest)
    (last : s.participatingCount ≤ passes + 1) :
    let result := showdownEnd s bf rest
    let next := s.paySurcharge ⟨.player p, .pass⟩ result.1
    applyDeclaredAction s ⟨.player p, .pass⟩ =
      some (next.withTriggers (result.2 ++ s.actionTransitionEvents next ⟨.player p, .pass⟩), result.2) := by
  unfold applyDeclaredAction
  simp only [GameState.actionDeathCostChoice, pending, GameState.actionKillCosts,
    GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  unfold applyAction applyFrame
  simp only [applyFrame0, pending, Nat.not_lt.mpr last, ite_false, Option.map_some, extraEvents, List.append_nil]

/-- The last Showdown Pass yields to damage replacement or assignment, or completes the
automatic control/scoring route when there is no player decision. -/
theorem step_showdownPass_last_to_decision {s : GameState} {bf : ObjId} {p : PlayerId}
    {passes cleanups : Nat} {rest : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .showdown bf p passes :: List.replicate cleanups .cleanup ++ rest)
    (last : s.participatingCount ≤ passes + 1)
    (legal : Legal s ⟨.player p, .pass⟩)
    (boundary : rest.head?.all (fun f => !f.isWork) = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .pass⟩ = advance extra t events := by
  let action : Action := ⟨.player p, .pass⟩
  let suffix := List.replicate cleanups Frame.cleanup ++ rest
  let result := showdownEnd s bf suffix
  let next := s.paySurcharge action result.1
  let notices := result.2 ++ s.actionTransitionEvents next action
  have declaration : applyDeclaredAction s action = some (next.withTriggers notices, result.2) :=
    applyDeclaredAction_showdownPass pending last
  have safe := GameState.paySurcharge_poolStep s action result.1
  have nextWF : next.WF := safe.wf (showdownEnd_preservesBoard s bf suffix wf).1
  have pendingEq : next.pending = result.1.pending := safe.pending_eq
  have resultCards : result.1.cards = s.cards := by
    rcases showdownEnd_cases s bf suffix with ⟨a, atCombat⟩ | settled
    · rw [show result.1 = _ from atCombat]
    · rw [show result.1 = _ from settled]
      change (endShowdown s bf).1.cards = s.cards
      obtain ⟨board, sameBoard, changePoints⟩ := endShowdown_safeP s bf
      have cards := congrArg GameState.cards sameBoard.same
      rcases changePoints with normal | ⟨who, points, withPoints⟩
      · rw [normal]; exact cards
      · rw [withPoints]; exact cards
  have nextCards : next.cards = s.cards := by
    change next.cards = _ at *
    rcases safe with same | ⟨who, pool, paid⟩
    · exact (congrArg GameState.cards same).trans resultCards
    · exact (congrArg GameState.cards paid).trans resultCards
  have nextReads := nextCards ▸ reads
  have observedReads := advance_action_observation_reads next notices nextReads
  let resume := CombatContinuation cleanups rest
  have insertTail (stack : List Frame) (kept : resume stack) (q : List PendTrigger) (ne : q ≠ []) :
      resume (insertTriggers q stack) := kept.insert boundary front q ne
  have base : resume suffix := CombatContinuation.ready cleanups rest
  have work : AdvanceTo (next.withTriggers notices) resume := by
    rcases showdownEnd_cases s bf suffix with ⟨att, atCombat⟩ | settled
    · let keeps := ResolutionPrefix [.combatDamage bf att] resume
      have tracks : keeps next.pending :=
        ⟨suffix, pendingEq.trans (congrArg GameState.pending atCombat), base⟩
      have entered : AdvanceTo (next.withTriggers notices) keeps :=
        advance_action_observation next notices nextWF nextReads tracks
          (fun _ track q ne => track.insert
            (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) insertTail q ne)
      apply entered.then observedReads
      intro t tWF tReads track
      obtain ⟨tail, ready, tracked⟩ := track
      exact advance_combat_damage tWF tReads ready tracked insertTail
    · let draws := (endShowdown s bf).2.1
      let keeps := ResolutionPrefix draws resume
      have tracks : keeps next.pending :=
        ⟨suffix, pendingEq.trans (congrArg GameState.pending settled), base⟩
      have generated : ∀ f ∈ draws, f.isResolution = true := by
        intro f member
        obtain ⟨q, rfl⟩ := endShowdown_frames s bf true f member
        rfl
      have entered : AdvanceTo (next.withTriggers notices) keeps :=
        advance_action_observation next notices nextWF nextReads tracks
          (fun _ track q ne => track.insert generated insertTail q ne)
      exact entered.then observedReads (fun _ tWF tReads track =>
        advance_draw_frames 1 (endShowdown_frames s bf true) tWF tReads track insertTail)
  obtain ⟨t, used, events, path, stop⟩ := advance_combat_to_decision observedReads work boundary front
  refine ⟨t, used, result.2 ++ events, stop, fun extra => ?_⟩
  change step (used + extra) s action = _
  simp only [step, ite_eq_left (show Legal s action from legal), declaration]
  exact path extra result.2

private theorem Effect.ObservedFinite.endCombatDamage (excess : Nat × Nat) :
    (Effect.endCombatDamage excess).ObservedFinite :=
  Effect.SingleRun.observed (fun s _ src _ _ => ⟨recordCombatDamage s src excess, [], rfl⟩)

private theorem assignDoneStep_work_cases (s : GameState) (bf : ObjId) (att side : PlayerId)
    (acc : List ObjId) (done : List (ObjId × Nat)) (rest : List Frame) :
    (∃ q assigned history, s.assignFrame bf att q history = some assigned ∧
      (assignDoneStep s bf att side acc done rest).1 =
        { s with pending := combatAssignmentChoices s bf q ++ assigned :: rest }) ∨
    (∃ batch excess,
      (assignDoneStep s bf att side acc done rest).1 = { s with
        pending := Frame.run att bf {} (.cons (.resolveEffectDamage batch none) (.cons (.endCombatDamage excess) .nil)) ::
          .cleanup :: .combatResolve bf att :: rest }) ∨
    (∃ r, Safe s r ∧ (assignDoneStep s bf att side acc done rest).1 =
      { r with pending := .cleanup :: .combatResolve bf att :: rest }) := by
  unfold assignDoneStep
  dsimp only
  split
  · rename_i f hf
    split at hf
    · exact Or.inl ⟨_, f, _, hf, rfl⟩
    · simp at hf
  · right
    split
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr ⟨_, (commitEffectDamage_safe s _).trans (recordCombatDamage_safe _ _ _), rfl⟩

private theorem applyDeclaredAction_assignDone {s : GameState} {bf : ObjId} {att side : PlayerId}
    {acc : List ObjId} {done : List (ObjId × Nat)} {rest : List Frame}
    (pending : s.pending = .assign bf att side acc done :: rest) :
    let action : Action := ⟨.player side, .assignDone⟩
    let result := assignDoneStep s bf att side acc done rest
    let next := s.paySurcharge action result.1
    applyDeclaredAction s action =
      some (next.withTriggers (result.2 ++ s.actionTransitionEvents next action), result.2) := by
  simp only [applyDeclaredAction, GameState.actionDeathCostChoice, pending, applyAction, applyFrame,
    applyFrame0, Option.map_some, extraEvents, List.append_nil]

/-- After an assignment is confirmed, the real action observer and work dispatcher reach
the other side's assignment, a replacement decision, another decision, or game end. -/
theorem step_assignDone_to_decision {s : GameState} {bf : ObjId} {att side : PlayerId}
    {acc : List ObjId} {done : List (ObjId × Nat)} {cleanups : Nat} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending =
      .assign bf att side acc done :: combatSteps bf ++ (List.replicate cleanups .cleanup ++ rest))
    (legal : Legal s ⟨.player side, .assignDone⟩)
    (boundary : rest.head?.all (fun f => !f.isWork) = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player side, .assignDone⟩ = advance extra t events := by
  let action : Action := ⟨.player side, .assignDone⟩
  let suffix := List.replicate cleanups Frame.cleanup ++ rest
  let tail := combatSteps bf ++ suffix
  let result := assignDoneStep s bf att side acc done tail
  let next := s.paySurcharge action result.1
  let notices := result.2 ++ s.actionTransitionEvents next action
  have declaration : applyDeclaredAction s action = some (next.withTriggers notices, result.2) :=
    applyDeclaredAction_assignDone pending
  have safe := GameState.paySurcharge_poolStep s action result.1
  have pendingEq : next.pending = result.1.pending := safe.pending_eq
  have casesRaw := assignDoneStep_work_cases s bf att side acc done tail
  have resultWF : result.1.WF := by
    rcases casesRaw with ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨r, safe, h⟩ <;>
      change result.1 = _ at h <;> rw [h]
    · exact wf.congr rfl rfl rfl rfl
    · exact wf.congr rfl rfl rfl rfl
    · exact (safe.wf wf).congr rfl rfl rfl rfl
  have nextWF : next.WF := safe.wf resultWF
  have resultCards : result.1.cards = s.cards := by
    rcases casesRaw with ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨r, safe, h⟩ <;>
      change result.1 = _ at h <;> rw [h]
    have cards := congrArg GameState.cards safe.same
    exact cards
  have nextCards : next.cards = s.cards := by
    rcases safe with same | ⟨who, pool, paid⟩
    · exact (congrArg GameState.cards same).trans resultCards
    · exact (congrArg GameState.cards paid).trans resultCards
  have nextReads := nextCards ▸ reads
  have observedReads := advance_action_observation_reads next notices nextReads
  let resume := CombatContinuation cleanups rest
  have insertTail (stack : List Frame) (kept : resume stack) (q : List PendTrigger) (ne : q ≠ []) :
      resume (insertTriggers q stack) := kept.insert boundary front q ne
  have base : resume suffix := CombatContinuation.ready cleanups rest
  let waiting := ResolutionPrefix [.cleanup, .combatResolve bf att] (TriggerWorkTail tail)
  have insertWaiting (stack : List Frame) (tracked : waiting stack) (q : List PendTrigger) (ne : q ≠ []) :
      waiting (insertTriggers q stack) :=
    tracked.insert (by
      intro f member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl)
      (fun _ continued q ne => continued.insert (combat_result_head bf suffix) q ne) q ne
  have proceed : ∀ t : GameState, t.WF → MightRead.database t.cards → waiting t.pending →
      AdvanceTo t resume := by
    intro t safe checked ready
    exact advance_combat_damage_to_cleanup safe checked ready base insertTail
  have work : AdvanceTo (next.withTriggers notices) resume := by
    rcases casesRaw with ⟨q, assigned, history, ready, atChoice⟩ |
      ⟨batch, excess, atDamage⟩ | ⟨r, safe, atCleanup⟩
    · let choices := combatAssignmentChoices s bf q ++ assigned :: tail
      have base : TriggerWorkTail choices next.pending := Or.inl
        (pendingEq.trans (congrArg GameState.pending atChoice))
      obtain ⟨first, head, nonwork, nonresolution⟩ := choice_head (rest := tail) ready
      change choices.head? = some first at head
      have insertChoices (stack : List Frame) (tracked : TriggerWorkTail choices stack)
          (q : List PendTrigger) (ne : q ≠ []) : TriggerWorkTail choices (insertTriggers q stack) := by
        apply tracked.insert _ q ne
        intro first' firstHead
        obtain rfl := Option.some.inj (head.symm.trans firstHead)
        exact ⟨nonresolution, by intro q eq; cases eq; contradiction⟩
      have entered := advance_action_observation next notices nextWF nextReads base insertChoices
      apply entered.then observedReads
      intro t safe reads tracked
      obtain ⟨u, used, path, stop | ⟨atChoices, _, _⟩⟩ := advance_trigger_tail t choices safe reads tracked
      · exact ⟨u, used, [], path, Or.inl stop⟩
      · exact ⟨u, used, [], path, Or.inl (by simp [atChoices, head, nonwork])⟩
    · let program := EffectList.cons (.resolveEffectDamage batch none) (.cons (.endCombatDamage excess) .nil)
      let running := RunContinuation att bf program waiting
      have stack : next.pending = .run att bf {} program :: .cleanup :: .combatResolve bf att :: tail :=
        pendingEq.trans (congrArg GameState.pending atDamage)
      have base : running next.pending := ⟨{}, _, stack, tail, rfl, Or.inl rfl⟩
      have entered := advance_action_observation next notices nextWF nextReads base
        (fun _ (tracked : running _) q ne => tracked.insert insertWaiting q ne)
      apply entered.then observedReads
      intro t safe checked tracked
      obtain ⟨env, tail, atRun, ready⟩ := tracked
      have finite : program.ObservedFinite :=
        .cons (.resolveDamage batch none) (.cons (.endCombatDamage excess) .nil)
      exact (advance_run_program safe checked atRun finite waiting ready insertWaiting).then checked proceed
    · have stack : next.pending = .cleanup :: .combatResolve bf att :: tail :=
        pendingEq.trans (congrArg GameState.pending atCleanup)
      have base : waiting next.pending := ⟨tail, stack, Or.inl rfl⟩
      exact (advance_action_observation next notices nextWF nextReads base insertWaiting).then observedReads proceed
  obtain ⟨t, used, events, path, stop⟩ := advance_combat_to_decision observedReads work boundary front
  refine ⟨t, used, result.2 ++ events, stop, fun extra => ?_⟩
  change step (used + extra) s action = _
  simp only [step, ite_eq_left (show Legal s action from legal), declaration]
  exact path extra result.2

end Riftbound

end
