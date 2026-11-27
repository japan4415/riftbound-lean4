module

public import Riftbound.Invariant.Cleanup
public import Riftbound.Invariant.WorkPrefix

/-!
# Finite Cleanup work in the engine (I12)

A Cleanup frame can repeat, return to its continuation, or wait for a decision. This module
uses the board measure through the actual work dispatcher, including event observation.
-/

@[expose] public section

namespace Riftbound

private def isCleanup : Frame → Bool
  | .cleanup => true
  | _ => false

private def isFightAt (field : ObjId) : Frame → Bool
  | .showdown there .. | .endShowdown there => there == field
  | _ => false

private theorem insertTriggers_filter (keep : Frame → Bool)
    (ignores : ∀ queue, keep (.triggers queue) = false)
    (queue : List PendTrigger) (stack : List Frame) :
    (insertTriggers queue stack).filter keep = stack.filter keep := by
  induction stack with
  | nil => simp [insertTriggers, ignores]
  | cons head rest ih =>
    simp only [insertTriggers]
    split
    · simp only [List.filter_cons, ih]
    · cases head <;> simp [ignores]

private theorem insertDetectedTriggers_filter (keep : Frame → Bool)
    (ignoresTriggers : ∀ queue, keep (.triggers queue) = false)
    (ignoresRuns : ∀ p id env effects, keep (.run p id env effects) = false)
    (s : GameState) (queue : List PendTrigger) (stack : List Frame) :
    (insertDetectedTriggers s queue stack).filter keep = stack.filter keep := by
  let arrivals := queue.map (fun t => (t, t.immediateAddFrame s))
  have first : (arrivals.filterMap Prod.snd).filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro f member
    obtain ⟨⟨t, added⟩, inArrivals, got⟩ := List.mem_filterMap.mp member
    obtain ⟨source, _, eq⟩ := List.mem_map.mp inArrivals
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    obtain ⟨p, id, env, effects, rfl⟩ := PendTrigger.immediateAddFrame_run got
    simp only [ignoresRuns, Bool.false_eq_true, not_false_eq_true]
  unfold insertDetectedTriggers
  change ((arrivals.filterMap Prod.snd ++ _).filter keep) = _
  rw [List.filter_append, first, List.nil_append]
  split
  · rfl
  · exact insertTriggers_filter keep ignoresTriggers _ _

private theorem insertTriggers_head_cleanup {queue : List PendTrigger} {stack : List Frame}
    (head : (insertTriggers queue stack).head? = some .cleanup) :
    stack.head? = some .cleanup := by
  cases stack with
  | nil => simp [insertTriggers] at head
  | cons frame rest =>
    simp only [insertTriggers] at head
    split at head
    · simpa using head
    · cases frame <;> simp at head

private theorem insertDetectedTriggers_head_cleanup {s : GameState} {queue : List PendTrigger}
    {stack : List Frame} (head : (insertDetectedTriggers s queue stack).head? = some .cleanup) :
    stack.head? = some .cleanup := by
  let arrivals := queue.map (fun t => (t, t.immediateAddFrame s))
  have onlyRuns {f : Frame} (member : f ∈ arrivals.filterMap Prod.snd) :
      ∃ p id env effects, f = .run p id env effects := by
    obtain ⟨⟨t, added⟩, inArrivals, got⟩ := List.mem_filterMap.mp member
    obtain ⟨source, _, eq⟩ := List.mem_map.mp inArrivals
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact PendTrigger.immediateAddFrame_run got
  unfold insertDetectedTriggers at head
  change ((arrivals.filterMap Prod.snd ++ _).head?) = some .cleanup at head
  cases front : arrivals.filterMap Prod.snd with
  | nil =>
    rw [front, List.nil_append] at head
    split at head
    · exact head
    · exact insertTriggers_head_cleanup head
  | cons frame frames =>
    have member : frame ∈ arrivals.filterMap Prod.snd := by simp [front]
    obtain ⟨_, _, _, _, rfl⟩ := onlyRuns member
    simp [front] at head

private theorem any_eq_of_filter_eq (p : Frame → Bool) {first second : List Frame}
    (eq : first.filter p = second.filter p) : first.any p = second.any p := by
  have test (xs : List Frame) : (xs.filter p).any p = xs.any p := by
    simp only [List.any_filter, Bool.and_self]
  rw [← test first, ← test second, eq]

private theorem cleanupMeasure_eq {s t : GameState} (config : t.config = s.config)
    (cards : t.cards = s.cards) (objects : t.objects = s.objects) (zones : t.zones = s.zones)
    (fighting : ∀ field, t.fightingAt field = s.fightingAt field) :
    t.cleanupMeasure = s.cleanupMeasure := by
  have zone : t.zone = s.zone := by
    funext z
    simp only [GameState.zone, zones]
  have loose : t.looseP = s.looseP := by
    funext gear
    simp only [GameState.looseP, GameState.obj?, objects, GameState.inPlay,
      GameState.players, GameState.playerCount, config, zone]
  simp only [GameState.cleanupMeasure, GameState.pot, GameState.dmgC, GameState.tokC,
    GameState.legendCount, GameState.legendZones, GameState.nbZones, GameState.inPlay,
    GameState.battlefields, GameState.isBattlefield, GameState.players, GameState.playerCount,
    GameState.cLoose, GameState.cLost, GameState.cStale, GameState.cNew, GameState.isTok,
    GameState.lostControl, GameState.staleContest, GameState.newContest, GameState.controlOf,
    GameState.unitsOf, GameState.unitsAt, GameState.isAt, GameState.isControlledBy,
    GameState.isUnit, GameState.printedCardDef?, GameState.obj?,
    fighting, config, cards, objects, zone, loose] <;> rfl

private theorem continuing_observer (s : GameState) (events : List Event)
    (head : (s.withTriggers events).pending.head? = some .cleanup) :
    s.pending.head? = some .cleanup ∧
    (s.withTriggers events).cleanupMeasure = s.cleanupMeasure ∧
    (s.withTriggers events).pending.countP isCleanup = s.pending.countP isCleanup := by
  rcases withTriggers_cases s events with ⟨player, removed, _⟩ | onlyHistory | ⟨queue, woven, _⟩
  · simp [removed] at head
  · rw [onlyHistory] at head ⊢
    exact ⟨head, rfl, rfl⟩
  · rw [woven] at head ⊢
    let observed := s.recordTurnEvents events
    change (insertDetectedTriggers observed queue s.pending).head? = some .cleanup at head
    refine ⟨insertDetectedTriggers_head_cleanup head, cleanupMeasure_eq rfl rfl rfl rfl ?_, ?_⟩
    · intro field
      unfold GameState.fightingAt
      have exactFight := insertDetectedTriggers_filter (isFightAt field) (fun _ => rfl)
        (fun _ _ _ _ => rfl) observed queue s.pending
      have same := any_eq_of_filter_eq _ exactFight
      change (s.combat.any (·.battlefield == field) ||
        (insertDetectedTriggers observed queue s.pending).any (isFightAt field)) =
        (s.combat.any (·.battlefield == field) || s.pending.any (isFightAt field))
      rw [same]
    · have same := insertDetectedTriggers_filter isCleanup (fun _ => rfl)
        (fun _ _ _ _ => rfl) observed queue s.pending
      simp only [List.countP_eq_length_filter]
      exact congrArg List.length same

/-- The end of a segment of Cleanup work in the actual engine. -/
inductive CleanupWorkStop (state : GameState) : Prop where
  /-- The engine returned to a decision, other work, or the end of the game. -/
  | outside (head : state.pending.head? ≠ some .cleanup)
  /-- A simultaneous group completed while keeping a Cleanup frame at the front, with no
  decrease in the board measure. -/
  | deathGroup {before : GameState} {rest : List Frame} {group : GameState × List Event}
      (pending : before.pending = .cleanup :: rest)
      (resolved : cleanupResolveDeathGroup before = some group)
      (step : workStep before = some (state, group.2))
      (head : state.pending.head? = some .cleanup)
      (decrease : ¬ MeasLt state.cleanupMeasure before.cleanupMeasure)

private def cleanupWorkRank (s : GameState) :
    Nat × (Nat × Nat × Nat × Nat × Nat × Nat) :=
  (s.pending.countP isCleanup, s.cleanupMeasure)

private def CleanupWorkLt (next before : GameState) : Prop :=
  Prod.Lex (· < ·) MeasLt (cleanupWorkRank next) (cleanupWorkRank before)

private theorem cleanupWorkLt_wf : WellFounded CleanupWorkLt :=
  InvImage.wf cleanupWorkRank ((Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ ⟨_, MeasLt.wf⟩).wf)

private theorem cleanup_engine_step (s : GameState) (wf : s.WF) (rest : List Frame)
    (pending : s.pending = .cleanup :: rest) :
    ∃ next events, workStep s = some (next, events) ∧
      (CleanupWorkStop next ∨
        (next.pending.head? = some .cleanup ∧ CleanupWorkLt next s)) := by
  let result := cleanupFrame s rest
  let next := result.1.withTriggers (result.2 ++ s.workTransitionEvents result.1)
  have raw : microStep0 s = some result := by simp only [microStep0, pending, result]
  have step : workStep s = some (next, result.2) := by
    simp only [workStep, pending, microStep, raw, Option.map_some, next]
  refine ⟨next, result.2, step, ?_⟩
  by_cases continues : next.pending.head? = some .cleanup
  · obtain ⟨rawHead, measure, count⟩ :=
      continuing_observer result.1 (result.2 ++ s.workTransitionEvents result.1) continues
    have repeated (r : GameState × List Event) (safe : Safe s r.1)
        (route : result = ({ r.1 with pending := .cleanup :: rest }, r.2)) :
        next.cleanupMeasure = r.1.cleanupMeasure ∧
          next.pending.countP isCleanup = s.pending.countP isCleanup := by
      have original : r.1.pending = .cleanup :: rest := safe.same.pending.trans pending
      have reinstalled : { r.1 with pending := .cleanup :: rest } = r.1 := by
        rw [← original]
      have rawState : result.1 = r.1 := by rw [route, reinstalled]
      change next.cleanupMeasure = result.1.cleanupMeasure at measure
      change next.pending.countP isCleanup = result.1.pending.countP isCleanup at count
      exact ⟨measure.trans (congrArg GameState.cleanupMeasure rawState),
        count.trans (congrArg (fun u : GameState => u.pending.countP isCleanup)
          rawState) |>.trans
            (congrArg (List.countP isCleanup) safe.same.pending)⟩
    cases winner : s.winner with
    | some seat => simp [result, cleanupFrame, winner] at rawHead
    | none =>
      cases choice : cleanupDeathBanishChoice s with
      | some decision =>
        obtain ⟨id, player, first, other⟩ := decision
        simp [result, cleanupFrame, winner, choice] at rawHead
      | none =>
        cases group : cleanupResolveDeathGroup s with
        | some r =>
          have route : result = ({ r.1 with pending := .cleanup :: rest }, r.2) := by
            simp [result, cleanupFrame, winner, choice, group]
          obtain ⟨sameMeasure, sameCount⟩ := repeated r (cleanupResolveDeathGroup_safe group) route
          by_cases decreases : MeasLt next.cleanupMeasure s.cleanupMeasure
          · exact Or.inr ⟨continues, Prod.Lex.right' MeasLt (Nat.le_of_eq sameCount) decreases⟩
          · have actual : workStep s = some (next, r.2) := by
              rw [step, route]
            exact Or.inl (.deathGroup pending group actual continues decreases)
        | none =>
          cases single : cleanupStep s with
          | some r =>
            obtain ⟨board, events⟩ := r
            have route : result = ({ board with pending := .cleanup :: rest }, events) := by
              simp [result, cleanupFrame, winner, choice, group, single]
            obtain ⟨sameMeasure, sameCount⟩ := repeated (board, events)
              (cleanupStep_safe (s' := board) (es := events) single) route
            have decreases : MeasLt next.cleanupMeasure s.cleanupMeasure := by
              rw [sameMeasure]
              exact cleanupStep_lt wf single
            exact Or.inr ⟨continues, Prod.Lex.right' MeasLt (Nat.le_of_eq sameCount) decreases⟩
          | none =>
            cases showdowns : s.stagedShowdowns rest with
            | nil =>
              have route : result = continueAfterCleanup s rest := by
                simp [result, cleanupFrame, winner, choice, group, single, showdowns]
              have smaller : next.pending.countP isCleanup < s.pending.countP isCleanup := by
                rw [count, pending, route]
                change rest.countP isCleanup < (Frame.cleanup :: rest).countP isCleanup
                rw [List.countP_cons_of_pos (show isCleanup .cleanup = true from rfl)]
                exact Nat.lt_succ_self _
              exact Or.inr ⟨continues, Prod.Lex.left _ _ smaller⟩
            | cons entry others =>
              obtain ⟨field, player⟩ := entry
              simp only [result, cleanupFrame, winner, choice, group, single, showdowns] at rawHead
              split at rawHead <;> simp [continueAfterCleanup] at rawHead
  · exact Or.inl (.outside continues)

/-- Starting at a Cleanup frame, the real engine runs to other work, a decision, the end of the
game, or a simultaneous death group for which the board measure has not decreased. Repeating
ordinary Cleanup steps consume the board measure even when observers change the turn history
or schedule ordinary triggers beneath the frame. Finishing one of several Cleanup frames
decreases their count. -/
theorem advance_cleanup_work {s : GameState} {rest : List Frame} (wf : s.WF)
    (pending : s.pending = .cleanup :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ CleanupWorkStop t := by
  revert rest
  refine cleanupWorkLt_wf.induction s (C := fun state => state.WF →
    ∀ {rest}, state.pending = .cleanup :: rest →
      ∃ t used events, 0 < used ∧ AdvancePrefix state t used events ∧ CleanupWorkStop t) ?_ wf
  intro state ih well rest stack
  obtain ⟨next, events, step, stop | ⟨front, rank⟩⟩ := cleanup_engine_step state well rest stack
  · have done : AdvancePrefix next next 0 [] := by intro fuel prior; simp
    exact ⟨next, 1, events, by omega, by simpa using done.prepend stack rfl step, stop⟩
  · have nextStack : ∃ tail, next.pending = .cleanup :: tail := by
      cases nextPending : next.pending with
      | nil => simp [nextPending] at front
      | cons frame tail =>
        have eq : frame = .cleanup := by simpa [nextPending] using front
        exact ⟨tail, by rw [eq]⟩
    obtain ⟨tail, shape⟩ := nextStack
    obtain ⟨t, used, later, _, trace, done⟩ :=
      ih next rank (workStep_wf well step) (rest := tail) shape
    exact ⟨t, used + 1, events ++ later, by omega, trace.prepend stack rfl step, done⟩

end Riftbound

end
