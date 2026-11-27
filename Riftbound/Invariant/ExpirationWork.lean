module

public import Riftbound.Invariant.CleanupWork
public import Riftbound.Invariant.TriggerObservation

/-!
# Finite turn Expiration and Cleanup work

Expiration clears the state that would call for another pass. Cleanup and event observation
can run between passes, so the rank tracks both the pending Expirations and whether the state
still contains anything that Expiration is responsible for clearing.
-/

@[expose] public section

namespace Riftbound

private def needsExpiration (o : Object) : Bool :=
  o.damage != 0 || o.stunned || o.baseMightThisTurn.isSome ||
    o.mightMods.any (·.ends != .never) || o.tempKws.any (·.2 != .never)

private structure ExpirationClear (s : GameState) : Prop where
  facts : s.turnFx = []
  pools : s.pools.isEmpty = true
  objects : ∀ id o, s.obj? id = some o → needsExpiration o = false

private theorem expiration_clear_iff (s : GameState) :
    expirationFrames s = [] ↔ ExpirationClear s := by
  change (if !s.turnFx.isEmpty || !s.pools.isEmpty ||
    s.objects.toList.any (fun (_, o) => needsExpiration o)
    then [Frame.cleanup, Frame.expireTurn] else []) = [] ↔ _
  have objects : s.objects.toList.any (fun (_, o) => needsExpiration o) = false ↔
      ∀ id o, s.obj? id = some o → needsExpiration o = false := by
    rw [List.any_eq_false]
    constructor
    · intro clear id o found
      have member : (id.n, o) ∈ s.objects.toList :=
        Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr found
      simpa using clear _ member
    · intro clear entry member
      obtain ⟨n, o⟩ := entry
      simpa using clear ⟨n⟩ o (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp member)
  have facts : (!s.turnFx.isEmpty) = false ↔ s.turnFx = [] := by
    cases s.turnFx <;> simp
  simp only [ite_eq_right_iff, List.cons_ne_nil, imp_false, Bool.not_eq_true,
    Bool.or_eq_false_iff, facts, objects]
  exact ⟨fun h => ⟨h.1.1, by simpa using h.1.2, h.2⟩,
    fun h => ⟨⟨h.facts, by simpa using h.pools⟩, h.objects⟩⟩

private theorem endTurnObj_clear (o : Object) : needsExpiration (endTurnObj o) = false := by
  unfold needsExpiration endTurnObj healObj
  simp only [List.any_filter, bne, Bool.and_not_self]
  simp

private theorem expiration_reset_clear (s : GameState) (pending : List Frame) :
    ExpirationClear { s.mapObjects endTurnObj with pending, pools := {}, turnFx := [] } := by
  refine ⟨rfl, rfl, ?_⟩
  intro id o found
  change (s.mapObjects endTurnObj).obj? id = some o at found
  rw [GameState.obj?_mapObjects] at found
  obtain ⟨original, _, rfl⟩ := Option.map_eq_some_iff.mp found
  exact endTurnObj_clear original

/-- After the reset that Expiration performs, the raw state has nothing left to expire. -/
theorem expirationFrames_after_reset (s : GameState) (pending : List Frame) :
    expirationFrames { s.mapObjects endTurnObj with pending, pools := {}, turnFx := [] } = [] :=
  (expiration_clear_iff _).mpr (expiration_reset_clear s pending)

private theorem ExpirationClear.modObj {s : GameState} (clear : ExpirationClear s)
    (id : ObjId) (f : Object → Object) (preserves : ∀ o, needsExpiration (f o) = needsExpiration o) :
    ExpirationClear (s.modObj id f) := by
  refine ⟨clear.facts, clear.pools, ?_⟩
  intro other o found
  rcases obj?_modObj_cases s id f other with unchanged | ⟨old, before, after⟩
  · exact clear.objects _ _ (unchanged.symm.trans found)
  · have eq : f old = o := Option.some.inj (after.symm.trans found)
    rw [← eq, preserves]
    exact clear.objects _ _ before

private theorem ExpirationClear.removeObj {s t : GameState} {id : ObjId}
    (clear : ExpirationClear s) (removed : removeObj s id = some t) :
    ExpirationClear t := by
  obtain ⟨z, _, _, rfl⟩ := removeObj_spec removed
  refine ⟨clear.facts, clear.pools, ?_⟩
  intro other o found
  change (s.objects.erase id.n)[other.n]? = some o at found
  rw [Std.ExtTreeMap.getElem?_erase] at found
  split at found
  · contradiction
  · exact clear.objects _ _ found

private theorem ExpirationClear.moveObj {s t : GameState} {id id' : ObjId}
    {dst : Zone} {pos : Pos} (clear : ExpirationClear s)
    (moved : Riftbound.moveObj s id dst pos = some (t, id')) : ExpirationClear t := by
  unfold Riftbound.moveObj at moved
  split at moved
  · dsimp only at moved
    split at moved
    · contradiction
    · split at moved
      · simp only [Option.some.injEq, Prod.mk.injEq] at moved
        obtain ⟨rfl, rfl⟩ := moved
        refine ⟨clear.facts, clear.pools, ?_⟩
        intro other o found
        simp only [GameState.obj?, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase] at found
        split at found
        · cases found
          rfl
        · split at found
          · contradiction
          · exact clear.objects _ _ found
      · simp only [Option.some.injEq, Prod.mk.injEq] at moved
        obtain ⟨rfl, rfl⟩ := moved
        exact ⟨clear.facts, clear.pools, clear.objects⟩
  · contradiction

private theorem ExpirationClear.lethal {s : GameState} (clear : ExpirationClear s) (id : ObjId) :
    s.lethal id = false := by
  unfold GameState.lethal
  cases found : s.obj? id with
  | none => rfl
  | some o =>
    have noDamage := clear.objects id o found
    unfold needsExpiration at noDamage
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at noDamage
    simp [noDamage.1.1.1.1]

private theorem ExpirationClear.deathGroup {s : GameState} (clear : ExpirationClear s) :
    cleanupDeathGroup s = [] := by
  unfold cleanupDeathGroup
  split
  · rfl
  · simp [clear.lethal]

private def neutralEvent (event : Event) : Prop :=
  ∀ s : GameState, s.recordTurnEvent [] event = []

private theorem cleanupStep0_clear {s next : GameState} {events : List Event}
    (clear : ExpirationClear s) (step : cleanupStep0 s = some (next, events)) :
    ExpirationClear next ∧ ∀ event ∈ events, neutralEvent event := by
  unfold cleanupStep0 at step
  have noDeath : s.inPlay.find? (fun u => s.isUnit u && s.lethal u) = none := by
    simp [clear.lethal]
  rw [noDeath] at step
  dsimp only at step
  split at step
  · cases step
    refine ⟨clear.modObj _ _ (fun _ => rfl), ?_⟩
    intro event member
    obtain rfl := List.mem_singleton.mp member
    intro state
    rfl
  · split at step
    · cases step
      exact ⟨clear.modObj _ _ (fun _ => rfl), by simp⟩
    · split at step
      · cases step
        exact ⟨clear.modObj _ _ (fun _ => rfl), by simp⟩
      · contradiction

private theorem cleanupStep_clear {s next : GameState} {events : List Event}
    (clear : ExpirationClear s) (step : cleanupStep s = some (next, events)) :
    ExpirationClear next ∧ ∀ event ∈ events, neutralEvent event := by
  unfold cleanupStep at step
  split at step
  · rename_i result taken
    cases step
    unfold tokenStep at taken
    split at taken
    · obtain ⟨t, removed, equal⟩ := Option.map_eq_some_iff.mp taken
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact ⟨clear.removeObj removed, by simp⟩
    · contradiction
  · split at step
    · rename_i result taken
      cases step
      unfold detachStep at taken
      obtain ⟨id, _, equal⟩ := Option.map_eq_some_iff.mp taken
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact ⟨clear.modObj id _ (fun _ => rfl), by simp⟩
    · cases returned : returnReservedLegendStep s with
      | none => exact cleanupStep0_clear clear (by simpa [returned, Option.orElse] using step)
      | some result =>
        have equal : result = (next, events) := by simpa [returned, Option.orElse] using step
        subst result
        unfold returnReservedLegendStep at returned
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at returned
        obtain ⟨⟨p, id⟩, _, ⟨t, new⟩, moved, result⟩ := returned
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj result)
        refine ⟨clear.moveObj moved, ?_⟩
        intro event member
        obtain rfl := List.mem_singleton.mp member
        intro state
        rfl

private theorem observeCombat_neutral {s : GameState} {pending : List Frame} {event : Event}
    (member : event ∈ (s.observeCombat pending).2) : neutralEvent event := by
  unfold GameState.observeCombat at member
  split at member
  · split at member
    · dsimp only at member
      split at member
      · simp at member
      · obtain rfl := List.mem_singleton.mp member
        intro state
        rfl
    · simp at member
  · split at member
    · split at member
      · obtain rfl := List.mem_singleton.mp member
        intro state
        rfl
      · simp at member
    · simp at member

private theorem continueAfterCleanup_clear {s : GameState} (clear : ExpirationClear s)
    (pending : List Frame) :
    ExpirationClear (continueAfterCleanup s pending).1 ∧
      ∀ event ∈ (continueAfterCleanup s pending).2, neutralEvent event := by
  refine ⟨⟨clear.facts, clear.pools, clear.objects⟩, ?_⟩
  intro event member
  exact observeCombat_neutral member

private theorem cleanupFrame_clear {s : GameState} (clear : ExpirationClear s)
    (rest : List Frame) :
    ExpirationClear (cleanupFrame s rest).1 ∧
      ∀ event ∈ (cleanupFrame s rest).2, neutralEvent event := by
  have choice : cleanupDeathBanishChoice s = none := by
    simp [cleanupDeathBanishChoice, clear.deathGroup]
  have group : cleanupResolveDeathGroup s = none := by
    simp [cleanupResolveDeathGroup, clear.deathGroup]
  unfold cleanupFrame
  cases winner : s.winner with
  | some seat =>
    refine ⟨⟨clear.facts, clear.pools, clear.objects⟩, ?_⟩
    intro event member
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
    intro state
    rfl
  | none =>
    simp only [choice, group]
    cases work : cleanupStep s with
    | some result =>
      obtain ⟨next, events⟩ := result
      have ⟨after, notes⟩ := cleanupStep_clear clear work
      exact ⟨⟨after.facts, after.pools, after.objects⟩, notes⟩
    | none =>
      cases staged : s.stagedShowdowns rest with
      | nil => exact continueAfterCleanup_clear clear rest
      | cons entry later =>
        obtain ⟨bf, player⟩ := entry
        dsimp only
        split
        · exact ⟨⟨clear.facts, clear.pools, clear.objects⟩, by simp⟩
        · exact continueAfterCleanup_clear clear _

private theorem exhaustionEvents_neutral {s t : GameState} {who : Option PlayerId} {event : Event}
    (member : event ∈ s.exhaustionEvents t who) : neutralEvent event := by
  unfold GameState.exhaustionEvents at member
  dsimp only at member
  split at member
  · simp at member
  · obtain rfl := List.mem_singleton.mp member
    intro state
    rfl

private theorem transitionEvents_neutral {s t : GameState} {head : Frame} {rest : List Frame}
    (pending : s.pending = head :: rest) (tracked : head = .cleanup ∨ head = .expireTurn)
    {event : Event} (member : event ∈ s.workTransitionEvents t) : neutralEvent event := by
  have primary {event : Event} (inEvents : event ∈ s.exhaustionEvents t none ++ s.mightyEvents t) :
      neutralEvent event := by
    rcases List.mem_append.mp inEvents with exhausted | mighty
    · exact exhaustionEvents_neutral exhausted
    · intro state
      exact mightyEvents_recordTurnEvent mighty state []
  unfold GameState.workTransitionEvents at member
  rw [pending] at member
  rcases tracked with rfl | rfl
  · simp only [GameState.mightReductionEvents, List.append_nil] at member
    rcases List.mem_append.mp member with normal | linked
    · exact primary normal
    · split at linked <;> try simp only [List.not_mem_nil] at linked
      split at linked
      · obtain rfl := List.mem_singleton.mp linked
        intro state
        rfl
      · simp at linked
  · simp only [GameState.mightReductionEvents, List.append_nil] at member
    exact primary member

private theorem foldl_neutralEvents (s : GameState) (events : List Event)
    (neutral : ∀ event ∈ events, neutralEvent event) : events.foldl s.recordTurnEvent [] = [] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    rw [List.foldl_cons, neutral event List.mem_cons_self s]
    exact ih (fun event member => neutral event (List.mem_cons_of_mem _ member))

private theorem withTriggers_clear {s : GameState} {events : List Event} (clear : ExpirationClear s)
    (neutral : ∀ event ∈ events, neutralEvent event) : ExpirationClear (s.withTriggers events) := by
  obtain ⟨pending, result, woven⟩ := withTriggers_pending s events
  rw [woven]
  refine ⟨?_, clear.pools, clear.objects⟩
  unfold GameState.recordTurnEvents
  dsimp only
  rw [clear.facts, foldl_neutralEvents s events neutral]
  simp

private def isExpiration : Frame → Bool
  | .expireTurn => true
  | _ => false

private theorem withTriggers_expiration_count (s : GameState) (events : List Event) :
    (s.withTriggers events).pending.countP isExpiration ≤ s.pending.countP isExpiration := by
  rcases withTriggers_cases s events with ⟨p, finished, _⟩ | unchanged | ⟨queue, woven, _⟩
  · simp [finished]
  · rw [unchanged]
    exact Nat.le_refl _
  · rw [woven]
    change (insertDetectedTriggers (s.recordTurnEvents events) queue s.pending).countP isExpiration ≤
      s.pending.countP isExpiration
    rw [List.countP_eq_length_filter, insertDetectedTriggers_filter isExpiration
      (fun _ => rfl) (fun _ _ _ _ => rfl), ← List.countP_eq_length_filter]
    exact Nat.le_refl _

private theorem cleanupFrame_expiration_count (s : GameState) (rest : List Frame) :
    (cleanupFrame s rest).1.pending.countP isExpiration ≤ rest.countP isExpiration := by
  unfold cleanupFrame
  split
  · simp
  · split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · split
        · exact Nat.le_refl _
        · split
          · split <;> exact Nat.le_refl _
          · exact Nat.le_refl _

private def expirationBudget (s : GameState) : Nat :=
  2 * s.pending.countP isExpiration + (if (expirationFrames s).isEmpty then 0 else 1)

private def ExpirationWorkLt (next before : GameState) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) MeasLt)
    (expirationBudget next, cleanupWorkRank next)
    (expirationBudget before, cleanupWorkRank before)

private theorem expirationWorkLt_wf : WellFounded ExpirationWorkLt :=
  InvImage.wf (fun s => (expirationBudget s, cleanupWorkRank s))
    ((Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ ⟨_, MeasLt.wf⟩)).wf)

private def inExpirationWork (s : GameState) : Prop :=
  s.pending.head? = some .cleanup ∨ s.pending.head? = some .expireTurn

private theorem cleanup_expirationBudget_le (s : GameState) (rest : List Frame)
    (pending : s.pending = .cleanup :: rest) :
    let raw := cleanupFrame s rest
    let next := raw.1.withTriggers (raw.2 ++ s.workTransitionEvents raw.1)
    expirationBudget next ≤ expirationBudget s := by
  let raw := cleanupFrame s rest
  let next := raw.1.withTriggers (raw.2 ++ s.workTransitionEvents raw.1)
  have count : next.pending.countP isExpiration ≤ s.pending.countP isExpiration := by
    have noNew := Nat.le_trans (withTriggers_expiration_count raw.1
      (raw.2 ++ s.workTransitionEvents raw.1)) (cleanupFrame_expiration_count s rest)
    rw [pending, List.countP_cons_of_neg (show ¬ isExpiration .cleanup = true from by decide)]
    exact noNew
  have remainsClear (clear : expirationFrames s = []) : expirationFrames next = [] := by
    have ⟨rawClear, neutral⟩ := cleanupFrame_clear ((expiration_clear_iff s).mp clear) rest
    apply (expiration_clear_iff next).mpr
    apply withTriggers_clear rawClear
    intro event member
    rcases List.mem_append.mp member with emitted | observed
    · exact neutral event emitted
    · exact transitionEvents_neutral pending (Or.inl rfl) observed
  change expirationBudget next ≤ expirationBudget s
  unfold expirationBudget
  cases items : expirationFrames s with
  | nil =>
    simp [remainsClear items]
    omega
  | cons first later =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
    split <;> omega

private theorem expiration_engine_step (s : GameState) (wf : s.WF) (front : inExpirationWork s) :
    ∃ next events, workStep s = some (next, events) ∧
      (inExpirationWork next → ExpirationWorkLt next s) := by
  cases pending : s.pending with
  | nil => simp [inExpirationWork, pending] at front
  | cons head rest =>
    have tracked : head = .cleanup ∨ head = .expireTurn := by simpa [inExpirationWork, pending] using front
    rcases tracked with rfl | rfl
    · let raw := cleanupFrame s rest
      let next := raw.1.withTriggers (raw.2 ++ s.workTransitionEvents raw.1)
      have step : workStep s = some (next, raw.2) := by
        simp only [workStep, pending, microStep, microStep0, Option.map_some, raw, next]
      refine ⟨next, raw.2, step, ?_⟩
      intro inside
      have fewer := cleanup_workStep_decreases s wf rest pending step inside
      exact Prod.Lex.right' _ (cleanup_expirationBudget_le s rest pending) fewer
    · let raw : GameState := { s.mapObjects endTurnObj with
        pending := expirationFrames s ++ rest, pools := {}, turnFx := [] }
      let next := raw.withTriggers (s.workTransitionEvents raw)
      have step : workStep s = some (next, []) := by
        simp only [workStep, pending, microStep, microStep0, Option.map_some, List.nil_append, raw, next]
      have clears : expirationFrames next = [] := by
        apply (expiration_clear_iff next).mpr
        exact withTriggers_clear (expiration_reset_clear s _)
          (fun _ => transitionEvents_neutral pending (Or.inr rfl))
      have keeps : next.pending.countP isExpiration ≤
          (expirationFrames s ++ rest).countP isExpiration :=
        withTriggers_expiration_count raw (s.workTransitionEvents raw)
      have smaller : expirationBudget next < expirationBudget s := by
        unfold expirationBudget
        rw [clears, pending, List.countP_cons_of_pos (show isExpiration .expireTurn = true from rfl)]
        have schedule : expirationFrames s = [] ∨ expirationFrames s = [.cleanup, .expireTurn] := by
          unfold expirationFrames
          split
          · exact Or.inr rfl
          · exact Or.inl rfl
        rcases schedule with empty | again
        · simp only [empty, List.nil_append] at keeps
          simp only [empty, List.isEmpty_nil, ite_true, Nat.add_zero]
          omega
        · simp only [again, List.countP_append] at keeps
          change next.pending.countP isExpiration ≤ 1 + rest.countP isExpiration at keeps
          simp only [again, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.isEmpty_nil,
            ite_true, Nat.add_zero]
          omega
      exact ⟨next, [], step, fun _ => Prod.Lex.left _ _ smaller⟩

/-- Starting at Cleanup or Expiration, actual engine work reaches a different frame or the end of
the stack in finite time. In particular, Cleanup and Expiration cannot repeat indefinitely on
their own, even while observation queues ordinary triggers behind the current work. -/
theorem advance_expiration_work {s : GameState} (wf : s.WF)
    (pending : s.pending.head? = some .cleanup ∨ s.pending.head? = some .expireTurn) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head? ≠ some .cleanup ∧ t.pending.head? ≠ some .expireTurn := by
  refine expirationWorkLt_wf.induction s (C := fun state => state.WF → inExpirationWork state →
    ∃ t used events, 0 < used ∧ AdvancePrefix state t used events ∧
      t.pending.head? ≠ some .cleanup ∧ t.pending.head? ≠ some .expireTurn) ?_ wf pending
  intro state ih well front
  have current : ∃ frame rest, state.pending = frame :: rest ∧ frame.isWork = true := by
    cases stack : state.pending with
    | nil => simp [inExpirationWork, stack] at front
    | cons head rest =>
      have tracked : head = .cleanup ∨ head = .expireTurn := by
        simpa [inExpirationWork, stack] using front
      rcases tracked with rfl | rfl <;> exact ⟨_, _, rfl, rfl⟩
  obtain ⟨frame, rest, shape, isWork⟩ := current
  obtain ⟨next, events, step, decreases⟩ := expiration_engine_step state well front
  by_cases inside : inExpirationWork next
  · obtain ⟨t, used, later, _, trace, noCleanup, noExpire⟩ :=
      ih next (decreases inside) (workStep_wf well step) inside
    exact ⟨t, used + 1, events ++ later, by omega, trace.prepend shape isWork step, noCleanup, noExpire⟩
  · have done : AdvancePrefix next next 0 [] := by intro fuel before; simp
    exact ⟨next, 1, events, by omega, by simpa using done.prepend shape isWork step,
      fun h => inside (Or.inl h), fun h => inside (Or.inr h)⟩

/-- The turn engine's Ending Phase schedules the first Cleanup and Expiration. The resulting
consecutive work finishes, or hands off to a different kind of work introduced by observation. -/
theorem advance_ending_expiration {s : GameState} {rest : List Frame} (wf : s.WF)
    (pending : s.pending = .phase .ending :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head? ≠ some .cleanup ∧ t.pending.head? ≠ some .expireTurn := by
  let raw := { s with phase := .ending, pending := .cleanup :: .expireTurn :: rest }
  let emitted := [Event.phaseStarted (s.active.getD ⟨0⟩) .ending]
  let next := raw.withTriggers (emitted ++ s.workTransitionEvents raw)
  have step : workStep s = some (next, emitted) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some, raw, next, emitted]
  by_cases inside : inExpirationWork next
  · obtain ⟨t, used, later, _, run, noCleanup, noExpire⟩ :=
      advance_expiration_work (workStep_wf wf step) inside
    exact ⟨t, used + 1, emitted ++ later, by omega, run.prepend pending rfl step, noCleanup, noExpire⟩
  · have done : AdvancePrefix next next 0 [] := by intro fuel before; simp
    exact ⟨next, 1, emitted, by omega, by simpa using done.prepend pending rfl step,
      fun h => inside (Or.inl h), fun h => inside (Or.inr h)⟩

end Riftbound

end
