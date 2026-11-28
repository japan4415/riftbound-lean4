module

public import Riftbound.Invariant.BeginningWork

/-!
# From Beginning to the next decision (I12)
-/

@[expose] public section

namespace Riftbound

private theorem sumMainSpending (p : PlayerId) (turn stamp : Nat)
    (entries : List (Nat × RunePool))
    (unique : entries.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) :
    ((entries.filterMap (fun ((seat, pool) : Nat × RunePool) =>
      if pool.powerSpent == 0 then none else some ({
        who := ⟨seat⟩, turn, stamp, kind := .powerSpentBeforeMain pool.powerSpent } : TurnFx))).filterMap (fun note => note.spendingBeforeMain p turn)).sum =
      ((entries.lookup p.n).getD RunePool.empty).powerSpent := by
  cases p with
  | mk seat =>
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
      obtain ⟨q, pool⟩ := entry
      have nodup := List.pairwise_cons.mp unique
      by_cases same : seat = q
      · subst q
        have missing : entries.lookup seat = none := by
          apply List.lookup_eq_none_iff.mpr
          intro entry member
          have different : seat ≠ entry.1 := by
            intro equal
            exact nodup.1 entry member (by simp [equal])
          simpa using different
        have zero := ih nodup.2
        rw [missing] at zero
        change _ = 0 at zero
        by_cases positive : pool.powerSpent = 0
        · simp [positive] at zero ⊢
          exact zero
        · simp [positive, TurnFx.spendingBeforeMain] at zero ⊢
          exact zero
      · have different : (seat == q) = false := by simpa using same
        have other : (⟨q⟩ : PlayerId) ≠ ⟨seat⟩ := by simp [Ne.symm same]
        by_cases positive : pool.powerSpent = 0
        · simpa [positive, List.lookup_cons, different] using ih nodup.2
        · simpa [positive, List.lookup_cons, different, other, TurnFx.spendingBeforeMain] using ih nodup.2

/-- Main Phase clears available resources and carries every seat's spent Power into the turn history. -/
theorem mainPhase_preserves_spentPower {s next : GameState} {rest : List Frame}
    {events : List Event} (pending : s.pending = .phase .main :: rest)
    (step : microStep0 s = some (next, events)) (p : PlayerId) :
    next.poolOf p = RunePool.empty ∧ next.powerSpentBeforeMain p =
      s.powerSpentBeforeMain p + (s.poolOf p).powerSpent := by
  simp only [microStep0, pending, Option.some.injEq, Prod.mk.injEq] at step
  obtain ⟨rfl, _⟩ := step
  constructor
  · rfl
  · simp only [GameState.mainPhasePowerNotes, GameState.powerSpentBeforeMain,
      List.filterMap_append, List.sum_append, Nat.add_left_cancel_iff]
    rw [sumMainSpending p s.turn s.nextTimestamp _ Std.ExtTreeMap.distinct_keys_toList]
    rw [GameState.poolOf, Std.ExtTreeMap.getD_eq_getD_getElem?]
    congr 2
    cases value : s.pools[p.n]? with
    | none =>
      apply List.lookup_eq_none_iff.mpr
      intro entry present
      obtain ⟨key, pool⟩ := entry
      have different : p.n ≠ key := by
        intro equal
        subst key
        rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at present
        simp [value] at present
      simpa using different
    | some pool =>
      cases found : s.pools.toList.lookup p.n with
      | none =>
        have member := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr value
        simpa using (List.lookup_eq_none_iff.mp found) (p.n, pool) member
      | some foundPool =>
        obtain ⟨before, after, split, _⟩ := List.lookup_eq_some_iff.mp found
        have member : (p.n, foundPool) ∈ s.pools.toList := by simp [split]
        rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, value] at member
        rw [Option.some.inj member]

/-- Ending the turn discards all available resources and both parts of its Power spending history. -/
theorem expiration_clears_spentPower {s next : GameState} {rest : List Frame}
    {events : List Event} (pending : s.pending = .expireTurn :: rest)
    (step : microStep0 s = some (next, events)) (p : PlayerId) :
    next.poolOf p = RunePool.empty ∧ next.powerSpentBeforeMain p = 0 := by
  simp only [microStep0, pending, Option.some.injEq, Prod.mk.injEq] at step
  obtain ⟨rfl, _⟩ := step
  exact ⟨rfl, rfl⟩

/-- Main sets the phase and clears the Rune Pool. The actual dispatcher settles Cleanup,
handles the observed triggers and either finishes the game or reaches a prepared decision. -/
theorem advance_main_to_preparedDecision {s : GameState} {p : PlayerId} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = [.phase .main, .priority p]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      advance used s [] = .ok (t, events) := by
  let rest := [Frame.priority p]
  let raw := { s with
    phase := .main
    pending := .cleanup :: rest
    pools := {}
    turnFx := s.mainPhasePowerNotes }
  let emitted := [Event.phaseStarted (s.active.getD ⟨0⟩) .main]
  have step : microStep0 s = some (raw, emitted) := by
    simp only [microStep0, pending, raw, emitted, rest]
  obtain ⟨mid, used, events, positive, path, midWF, cards, route⟩ :=
    advance_rule_with_adds pending rfl step (microStep_wf0 wf step) rfl reads
  have head : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
    intro f first
    have : f = .priority p := (Option.some.inj first).symm
    subst f
    exact ⟨rfl, by intro q h; cases h⟩
  have insertion (frames : List Frame) (track : TriggerWorkTail rest frames)
      (q : List PendTrigger) (ne : q ≠ []) : TriggerWorkTail rest (insertTriggers q frames) :=
    track.insert head q ne
  suffices completed : ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true by
    obtain ⟨t, count, emitted, ran, trace, ready⟩ := completed
    exact ⟨t, count, emitted, ran, trace, ready,
      by simpa only [List.nil_append] using trace.finish ready []⟩
  have finish (tail : List Frame) (stack : mid.pending = .cleanup :: tail) (track : TriggerWorkTail rest tail) :
      ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
        t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨t, elapsed, later, _, cleanup, stop | ⟨waiting, afterWF, afterCards, nonpriority⟩⟩ :=
      advance_cleanup_with_adds_prepared midWF (cards ▸ reads) stack (TriggerWorkTail rest) track insertion
    · exact ⟨t, used + elapsed, events ++ later, by omega, path.append cleanup, stop⟩
    · rcases waiting with resumed | ⟨queue, nonempty, queued⟩
      · exact (nonpriority p resumed).elim
      · obtain ⟨u, steps, _, _, _, triggers, _, _, decision⟩ :=
          advance_triggers_to_preparedDecision t afterWF queue rest queued
            (afterCards ▸ cards ▸ reads) (Or.inl nonempty)
        exact ⟨u, used + elapsed + steps, _, by omega,
          by simpa only [List.append_nil] using (path.append cleanup).append triggers, decision⟩
  change ObservedWorkStack (.cleanup :: rest) mid.pending at route
  generalize stack : mid.pending = frames at route
  cases route with
  | empty =>
    exact ⟨mid, used, events, positive, path,
      GameState.prepared_idle_of_nonpriority (by rw [stack]; rfl) (by simp [stack])⟩
  | resume => exact finish rest stack (Or.inl rfl)
  | queue q nonempty => exact finish _ stack (insertion rest (Or.inl rfl) q nonempty)

/-- The standard Main transition has a finite prefix ending at an answer or empty stack. -/
theorem advance_main_to_decision {s : GameState} {p : PlayerId} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = [.phase .main, .priority p]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨t, used, events, positive, trace, ready, _⟩ :=
    advance_main_to_preparedDecision wf reads pending
  exact ⟨t, used, events, positive, trace,
    by simpa only [GameState.preparePriority_of_idle ready] using ready⟩

/-- When entering Main leaves only a settled Cleanup followed by neutral priority, the
actual dispatcher returns priority in two work steps and retains Main's phase event. -/
theorem advance_main_to_priority_of_settled {s : GameState} {p : PlayerId} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = [.phase .main, .priority p]) :
    let raw := { s with
      phase := .main
      pending := [.cleanup, .priority p]
      pools := {}
      turnFx := s.mainPhasePowerNotes }
    let event := Event.phaseStarted (s.active.getD ⟨0⟩) .main
    let next := raw.withTriggers (event :: s.workTransitionEvents raw)
    next.pending = [.cleanup, .priority p] → next.Settled →
      next.stagedShowdowns [.priority p] = [] →
      next.turnFx.any (fun f => match f.kind with
        | .linkedDamageDeath .. => true | _ => false) = false →
      advance 2 s [] = .ok ({ next with pending := [.priority p] }, [event]) := by
  intro raw event next stack settled noShowdown noLinks
  have work : workStep s = some (next, [event]) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some, raw, event, next,
      List.cons_append, List.nil_append]
  have cards : next.cards = s.cards := by
    obtain ⟨_, _, unchanged⟩ := withTriggers_pending raw (event :: s.workTransitionEvents raw)
    change (raw.withTriggers _).cards = _
    rw [unchanged]
    rfl
  have noLinked : next.turnFx.any (fun f => match f.kind with
      | .linkedDamageDeath .. => true | _ => false) = false := by
    apply List.any_eq_false.mpr
    intro note member
    have absent := (List.any_eq_false.mp noLinks) note member
    cases kind : note.kind <;> simp_all
  have cleanup := advance_settledCleanup_to_priority (seen := [event])
    (workStep_wf wf work) (cards ▸ reads) stack settled noShowdown noLinked
  have prepared := GameState.preparePriority_of_work pending rfl
  simpa only [advance, prepared, pending, Frame.isWork, ite_true, work, List.nil_append] using cleanup

private def advancesToStack (s : GameState) (rest : List Frame) : Prop :=
  ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
    (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨
      (t.pending = rest ∧ t.WF ∧ t.cards = s.cards))

/-- A remaining part of the standard turn, before the first Main priority. -/
inductive TurnPhaseSuffix : List Frame → Prop where
  /-- Start the Beginning Phase. -/
  | beginning (p : PlayerId) : TurnPhaseSuffix [.phase .beginning, .phase .channel, .phase .draw, .phase .main, .priority p]
  /-- Resume before Hold scoring. -/
  | holds (p : PlayerId) : TurnPhaseSuffix [.scoreHolds, .phase .channel, .phase .draw, .phase .main, .priority p]
  /-- Resume before Channel. -/
  | channel (p : PlayerId) : TurnPhaseSuffix [.phase .channel, .phase .draw, .phase .main, .priority p]
  /-- Resume before the standard Draw Phase. -/
  | draw (p : PlayerId) : TurnPhaseSuffix [.phase .draw, .phase .main, .priority p]
  /-- Start Main with the turn player's priority. -/
  | main (p : PlayerId) : TurnPhaseSuffix [.phase .main, .priority p]

/-- Check the remaining frames against the standard turn phase order. -/
def isTurnPhaseSuffix : List Frame → Bool
  | [.phase .beginning, .phase .channel, .phase .draw, .phase .main, .priority _]
  | [.scoreHolds, .phase .channel, .phase .draw, .phase .main, .priority _]
  | [.phase .channel, .phase .draw, .phase .main, .priority _]
  | [.phase .draw, .phase .main, .priority _]
  | [.phase .main, .priority _] => true
  | _ => false

/-- An accepted phase stack has one of the standard suffixes. -/
theorem isTurnPhaseSuffix_sound {rest : List Frame} (checked : isTurnPhaseSuffix rest = true) :
    TurnPhaseSuffix rest := by
  unfold isTurnPhaseSuffix at checked
  split at checked
  · exact .beginning _
  · exact .holds _
  · exact .channel _
  · exact .draw _
  · exact .main _
  · contradiction

/-- Ordinary triggers can be processed before the first frame in a phase suffix. -/
theorem TurnPhaseSuffix.front {rest : List Frame} (suffix : TurnPhaseSuffix rest) :
    ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
  cases suffix <;> intro f head <;> cases Option.some.inj head <;>
    exact ⟨rfl, by intro q equal; cases equal⟩

private theorem continueTurnWork {s : GameState} {rest : List Frame}
    (segment : advancesToStack s rest) (reads : MightRead.database s.cards)
    (next : ∀ t : GameState, t.pending = rest → t.WF → MightRead.database t.cards →
      ∃ u used events, 0 < used ∧ AdvancePrefix t u used events ∧
        u.preparePriority.pending.head?.all (fun f => !f.isWork) = true) :
    ∃ u used events, 0 < used ∧ AdvancePrefix s u used events ∧
      u.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨t, used, events, positive, path, stop | ⟨atRest, tWF, cards⟩⟩ := segment
  · exact ⟨t, used, events, positive, path, stop⟩
  · obtain ⟨u, later, emitted, _, ran, done⟩ := next t atRest tWF (cards ▸ reads)
    exact ⟨u, used + later, events ++ emitted, by omega, path.append ran, done⟩

/-- Finish the remaining standard phases from the current frame, or stop at a new input. -/
theorem advance_turnPhaseSuffix_to_preparedDecision {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = rest) (suffix : TurnPhaseSuffix rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  let fromMain (state : GameState) (p : PlayerId) (stack : state.pending = [.phase .main, .priority p])
      (safe : state.WF) (known : MightRead.database state.cards) :
      ∃ t used events, 0 < used ∧ AdvancePrefix state t used events ∧
        t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨t, used, events, positive, path, ready, _⟩ :=
      advance_main_to_preparedDecision safe known stack
    exact ⟨t, used, events, positive, path, ready⟩
  let fromDraw (state : GameState) (p : PlayerId)
      (stack : state.pending = [.phase .draw, .phase .main, .priority p])
      (safe : state.WF) (known : MightRead.database state.cards) :=
    continueTurnWork (advance_draw_phase_prepared safe known stack) known
      (fun t pending wf reads => fromMain t p pending wf reads)
  let fromChannel (state : GameState) (p : PlayerId)
      (stack : state.pending = [.phase .channel, .phase .draw, .phase .main, .priority p])
      (safe : state.WF) (known : MightRead.database state.cards) :=
    continueTurnWork (advance_channel_to_draw_prepared safe known stack) known
      (fun t pending wf reads => fromDraw t p pending wf reads)
  let fromHolds (state : GameState) (p : PlayerId)
      (stack : state.pending = [.scoreHolds, .phase .channel, .phase .draw, .phase .main, .priority p])
      (safe : state.WF) (known : MightRead.database state.cards) :=
    continueTurnWork (advance_holds_to_channel_prepared safe known stack) known
      (fun t pending wf reads => fromChannel t p pending wf reads)
  cases suffix with
  | beginning p =>
    exact continueTurnWork (advance_beginning_to_holds_prepared wf reads pending) reads
      (fun t stack safe known => fromHolds t p stack safe known)
  | holds p => exact fromHolds s p pending wf reads
  | channel p => exact fromChannel s p pending wf reads
  | draw p => exact fromDraw s p pending wf reads
  | main p => exact fromMain s p pending wf reads

/-- Execute the normal new turn from Beginning through Hold, Channel, Draw and Main.
The actual engine reaches a decision or the end of the game in finitely many steps. -/
theorem advance_beginning_to_preparedDecision {s : GameState} {p : PlayerId} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = (turnFrames p).drop 1) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      advance used s [] = .ok (t, events) := by
  obtain ⟨t, used, events, positive, path, ready⟩ :=
    advance_turnPhaseSuffix_to_preparedDecision wf reads pending (.beginning p)
  exact ⟨t, used, events, positive, path, ready, by simpa only [List.nil_append] using path.finish ready []⟩

/-- Run the normal automatic turn phases until a decision or the end of the stack. -/
theorem advance_beginning_to_decision {s : GameState} {p : PlayerId} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = (turnFrames p).drop 1) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨t, used, events, positive, path, ready, _⟩ := advance_beginning_to_preparedDecision wf reads pending
  exact ⟨t, used, events, positive, path,
    by simpa only [GameState.preparePriority_of_idle ready] using ready⟩

end Riftbound

end
