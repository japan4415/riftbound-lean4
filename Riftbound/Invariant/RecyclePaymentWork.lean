module

public import Riftbound.Invariant.RunWorkCore

/-!
# Recycle payment under the work dispatcher (I12)

Run the payment programs that select and Recycle Runes or cards from the Trash.
-/

@[expose] public section

namespace Riftbound

private theorem advance_run_next_from {s : GameState} {p : PlayerId} {src : ObjId} {env nextEnv : Env}
    {effect next : Effect} {more : EffectList} {rest : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons effect more) :: rest)
    (known : (runEffect s p src (env.withMight s.mightTable) effect more effectAddPolicy).2.1 =
      [.run p src nextEnv (.cons next more)])
    (finite : next.ObservedFinite) (base : keeps rest)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s (RunContinuation p src more keeps) := by
  have entered : AdvanceTo s (RunContinuation p src (.cons next more) keeps) := by
    apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
    dsimp only
    rw [known]
    exact ⟨nextEnv, rest, rfl, base⟩
  refine entered.then reads ?_
  intro t safe checked tracks
  obtain ⟨continuation, tail, ready, kept⟩ := tracks
  exact finite t p src continuation more tail keeps safe checked ready kept inserted

/-- Ordering Rune Recycle consumes empty groups and singletons, or asks the owner about a group. -/
theorem Effect.ObservedFinite.orderRuneRecycle (groups : List (PlayerId × List ObjId)) (picked : List ObjId) :
    (Effect.orderRuneRecycle groups picked).ObservedFinite := by
  induction groups generalizing picked with
  | nil =>
    exact Effect.SingleRun.observed (fun s _ _ _ _ => ⟨(recycleList picked.reverse s).1,
      (recycleList picked.reverse s).2, rfl⟩)
  | cons group later ih =>
    obtain ⟨owner, ids⟩ := group
    cases ids with
    | nil =>
      intro s p src env more rest keeps wf reads pending base inserted
      exact advance_run_next_from wf reads pending rfl (ih picked) base inserted
    | cons first ids =>
      cases ids with
      | nil =>
        intro s p src env more rest keeps wf reads pending base inserted
        exact advance_run_next_from wf reads pending rfl (ih (first :: picked)) base inserted
      | cons second rest =>
        intro s p src env more rest keeps wf reads pending _ _
        exact advance_run_decision wf reads pending rfl

/-- Recording a Rune choice returns to the remaining groups. -/
theorem Effect.ObservedFinite.recordRuneRecycle (remaining : List ObjId)
    (later : List (PlayerId × List ObjId)) (picked : List ObjId) :
    (Effect.recordRuneRecycle remaining later picked).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  have skip (frames : (runEffect s p src live (.recordRuneRecycle remaining later picked)
      more effectAddPolicy).2.1 = [.run p src live more]) :
      AdvanceTo s (RunContinuation p src more keeps) := by
    apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
    dsimp only
    rw [frames]
    exact ⟨_, rest, rfl, base⟩
  cases found : live.lookup pickVar with
  | none => exact skip (by simp only [runEffect, Effect.pickSel?, runEffect1, found])
  | some value =>
    cases value <;> try (apply skip; simp only [runEffect, Effect.pickSel?, runEffect1, found]; done)
    case obj id =>
      by_cases legal : remaining.contains id = true
      · refine advance_run_next_from (nextEnv := live) wf reads pending ?_
          (.orderRuneRecycle ((p, remaining.erase id) :: later) (id :: picked)) base inserted
        simp only [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl,
          found, legal, ite_true]
      · exact skip (by simp only [runEffect, Effect.pickSel?, runEffect1, found, ite_eq_right legal])

private theorem recycleTrashStep_finite {effect : Effect}
    (selected : ∀ s p src env more, ∃ chosen,
      runEffect s p src env effect more effectAddPolicy = recycleTrashStep s p src env more chosen) :
    effect.ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  obtain ⟨chosen, rule⟩ := selected s p src live more
  let selectedCards := (chosen.filter s.inTrash).eraseDups
  cases partition : selectedCards.partition (fun id => recycleKind s id == .runeDeck) with
  | mk runes cards =>
    let owned (owner : PlayerId) (ids : List ObjId) :=
      ids.filter (fun id => (s.obj? id).any (·.owner == owner))
    let groups := s.pickOrder.map (fun q => (q, owned q runes))
    let resume := Frame.run p src live more
    let program := EffectList.cons (.orderRuneRecycle groups []) .nil
    let follows := if runes.isEmpty then [resume] else [.run p src live program, resume]
    let chance := s.players.any (fun q => decide (2 ≤ (owned q cards).length))
    have form : (runEffect s p src live effect more effectAddPolicy).2.1 =
        if chance then .chanceRecycleTrash p src cards :: follows else follows := by
      rw [rule]
      unfold recycleTrashStep
      rw [show (chosen.filter s.inTrash).eraseDups = selectedCards from rfl, partition]
      change (if chance then (s, .chanceRecycleTrash p src cards :: follows, [])
        else ((recycleTrashCards s cards).1, follows, (recycleTrashCards s cards).2)).2.1 = _
      cases chance <;> rfl
    by_cases needsChance : chance = true
    · apply advance_run_decision wf reads pending
      dsimp only
      rw [form, ite_eq_left needsChance]
      rfl
    · have noChance := form.trans (ite_eq_right needsChance)
      by_cases onlyCards : runes.isEmpty = true
      · apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
        dsimp only
        rw [noChance, show follows = [resume] by simp only [follows, onlyCards, ite_true]]
        exact ⟨live, rest, rfl, base⟩
      · let continuation := RunContinuation p src more keeps
        let ordered := RunContinuation p src program continuation
        have enter : AdvanceTo s ordered := by
          apply advance_run_rule wf reads pending ?_ ?_
          · dsimp only
            rw [noChance, show follows = [.run p src live program, resume] by
              simp only [follows, ite_eq_right onlyCards]]
            exact ⟨live, _, rfl, ⟨live, rest, rfl, base⟩⟩
          · exact fun _ tracked q ne => tracked.insert (fun _ tail qs nonempty => tail.insert inserted qs nonempty) q ne
        apply enter.then reads
        intro next safe checked track
        obtain ⟨context, tail, ready, queued⟩ := track
        exact advance_run_program safe checked ready (.cons (.orderRuneRecycle groups []) .nil)
          continuation queued (fun _ next q ne => next.insert inserted q ne)

/-- Finish the selected Trash Recycle, including a chance or Rune ordering decision. -/
theorem Effect.ObservedFinite.finishTrashRecycle (picked : List ObjId) :
    (Effect.finishTrashRecycle picked).ObservedFinite :=
  recycleTrashStep_finite (fun _ _ _ _ _ => ⟨picked.reverse, rfl⟩)

/-- Recycle the Trash targets saved in the resolution slots. -/
theorem Effect.ObservedFinite.recycleTrashTargets : Effect.recycleTrashTargets.ObservedFinite :=
  recycleTrashStep_finite (fun s p src env _ =>
    ⟨((Selector.slotsFrom 0).eval s p src env).getD [], rfl⟩)

/-- The automatic part of Trash Recycle either presents a choice or finishes the selected cards. -/
theorem Effect.ObservedFinite.recycleFromTrash (side : Side) (count : Nat) (upTo : Bool) (picked : List ObjId) :
    (Effect.recycleFromTrash side count upTo picked).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  let candidates := s.trashRecycleCandidates p src live side (picked ++ more.trashPaymentRestrictions.1)
    more.trashPaymentRestrictions.2
  have continuation (done : (runEffect s p src live (.recycleFromTrash side count upTo picked)
      more effectAddPolicy).2.1 = [.run p src live (.cons (.finishTrashRecycle picked) more)]) :
      AdvanceTo s (RunContinuation p src more keeps) :=
    advance_run_next_from wf reads pending done (.finishTrashRecycle picked) base inserted
  cases count with
  | zero => exact continuation rfl
  | succ n =>
    cases available : candidates with
    | nil =>
      apply continuation
      simp only [runEffect, Effect.pickSel?, runEffect1, ← show candidates = s.trashRecycleCandidates p src live side
        (picked ++ more.trashPaymentRestrictions.1) more.trashPaymentRestrictions.2 from rfl, available]
    | cons first other =>
      apply advance_run_decision wf reads pending
      simp only [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl,
        ← show candidates = s.trashRecycleCandidates p src live side
          (picked ++ more.trashPaymentRestrictions.1) more.trashPaymentRestrictions.2 from rfl, available]
      cases upTo <;> rfl

/-- An accepted optional Recycle opens the object selection or finishes when there are no candidates. -/
theorem Effect.ObservedFinite.chooseTrashRecycle (side : Side) (count : Nat) (picked : List ObjId) :
    (Effect.chooseTrashRecycle side count picked).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  cases available : s.trashRecycleCandidates p src live side (picked ++ more.trashPaymentRestrictions.1)
      more.trashPaymentRestrictions.2 with
  | nil =>
    refine advance_run_next_from (nextEnv := live) wf reads pending ?_ (.finishTrashRecycle picked) base inserted
    simp only [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl, available]
  | cons first others =>
    apply advance_run_decision wf reads pending
    simp only [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl, available]
    rfl

/-- Recycle selections are recorded with the chosen binding removed from the environment. -/
theorem Effect.ObservedFinite.recordTrashRecycle (side : Side) (count : Nat) (upTo : Bool) (picked : List ObjId) :
    (Effect.recordTrashRecycle side count upTo picked).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  have skip (frames : (runEffect s p src live (.recordTrashRecycle side count upTo picked)
      more effectAddPolicy).2.1 = [.run p src live more]) :
      AdvanceTo s (RunContinuation p src more keeps) := by
    apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
    dsimp only
    rw [frames]
    exact ⟨live, rest, rfl, base⟩
  cases bindings : live.bindings with
  | nil =>
    apply skip
    simp only [runEffect, Effect.pickSel?, runEffect1, bindings]
  | cons head previous =>
    obtain ⟨var, val⟩ := head
    cases val <;> try (apply skip; simp only [runEffect, Effect.pickSel?, runEffect1, bindings]; done)
    case obj id =>
      by_cases pickedVar : (var == pickVar) = true
      · let context := { live with bindings := previous }
        refine advance_run_next_from (nextEnv := context) wf reads pending ?_
          (.recycleFromTrash side count upTo (id :: picked)) base inserted
        simp only [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl,
          bindings, pickedVar, ite_true, context]
      · apply skip
        simp only [runEffect, Effect.pickSel?, runEffect1, bindings, ite_eq_right pickedVar]

/-- Completion emits the actual activation event after Recycle payment. -/
theorem Effect.ObservedFinite.completeActivation (source : ObjId) (index : Nat) (baseEnergy : Option Nat)
    (targets : List ObjId) (filters : FilterList) :
    (Effect.completeActivation source index baseEnergy targets filters).ObservedFinite :=
  Effect.SingleRun.observed (fun s p _ _ _ => ⟨s, [.activated p source index baseEnergy], rfl⟩)

/-- The optional Recycle payment inserted during an activation has finite observed work. -/
theorem activationRecycleFrames_finite (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat)
    (targets : List ObjId) : ∀ f ∈ activationRecycleFrames s p src idx targets, f.FiniteRun := by
  intro f member
  unfold activationRecycleFrames at member
  split at member
  · split at member
    · obtain rfl := List.mem_singleton.mp member
      exact ⟨_, _, _, _, rfl, .cons (.recycleFromTrash _ _ _ _) (.cons (.completeActivation _ _ _ _ _) .nil)⟩
    · simp at member
  · simp at member

end Riftbound

end
