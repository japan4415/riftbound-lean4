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

/-- Main sets the new phase, clears the Rune Pool and runs Cleanup. The engine then waits at
priority, a Showdown, an ordinary trigger choice or another decision, or finishes the game. -/
theorem advance_main_to_decision {s : GameState} {p : PlayerId} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = [.phase .main, .priority p]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
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
  have finish (tail : List Frame) (stack : mid.pending = .cleanup :: tail) (track : TriggerWorkTail rest tail) :
      ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
        t.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨t, elapsed, later, _, cleanup, stop | ⟨waiting, afterWF, afterCards⟩⟩ :=
      advance_cleanup_with_adds midWF (cards ▸ reads) stack (TriggerWorkTail rest) track insertion
    · exact ⟨t, used + elapsed, events ++ later, by omega, path.append cleanup, stop⟩
    · obtain ⟨u, queued, triggers, decision | ⟨normal, _, _⟩⟩ :=
        advance_trigger_tail t rest afterWF (afterCards ▸ cards ▸ reads) waiting
      · exact ⟨u, used + elapsed + queued, _, by omega,
          by simpa only [List.append_nil] using (path.append cleanup).append triggers, decision⟩
      · exact ⟨u, used + elapsed + queued, _, by omega,
          by simpa only [List.append_nil] using (path.append cleanup).append triggers, by rw [normal]; rfl⟩
  change ObservedWorkStack (.cleanup :: rest) mid.pending at route
  generalize stack : mid.pending = frames at route
  cases route with
  | empty => exact ⟨mid, used, events, positive, path, by rw [stack]; rfl⟩
  | resume => exact finish rest stack (Or.inl rfl)
  | queue q nonempty => exact finish _ stack (insertion rest (Or.inl rfl) q nonempty)

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
    (t.pending.head?.all (fun f => !f.isWork) = true ∨
      (t.pending = rest ∧ t.WF ∧ t.cards = s.cards))

/-- Execute the normal new turn from Beginning through Hold, Channel, Draw and Main.
The actual engine reaches a decision or the end of the game in finitely many steps. -/
theorem advance_beginning_to_decision {s : GameState} {p : PlayerId} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = (turnFrames p).drop 1) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  have continueFrom {state : GameState} {rest : List Frame}
      (segment : advancesToStack state rest) (known : MightRead.database state.cards)
      (next : ∀ t : GameState, t.pending = rest → t.WF → MightRead.database t.cards →
        ∃ u used events, 0 < used ∧ AdvancePrefix t u used events ∧
          u.pending.head?.all (fun f => !f.isWork) = true) :
      ∃ u used events, 0 < used ∧ AdvancePrefix state u used events ∧
        u.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨t, used, events, positive, path, stop | ⟨atRest, tWF, cards⟩⟩ := segment
    · exact ⟨t, used, events, positive, path, stop⟩
    · obtain ⟨u, later, emitted, _, ran, done⟩ := next t atRest tWF (cards ▸ known)
      exact ⟨u, used + later, events ++ emitted, by omega, path.append ran, done⟩
  refine continueFrom (advance_beginning_to_holds wf reads pending) reads ?_
  intro atHolds ready holdsWF holdsReads
  refine continueFrom (advance_holds_to_channel holdsWF holdsReads ready) holdsReads ?_
  intro atChannel ready channelWF channelReads
  refine continueFrom (advance_channel_to_draw channelWF channelReads ready) channelReads ?_
  intro atDraw ready drawWF drawReads
  refine continueFrom (advance_draw_phase drawWF drawReads ready) drawReads ?_
  intro atMain ready mainWF mainReads
  exact advance_main_to_decision mainWF mainReads ready

end Riftbound

end
