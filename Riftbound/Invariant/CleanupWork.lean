module

public import Riftbound.Invariant.CleanupDeathDamage
public import Riftbound.Invariant.WorkPrefix

/-!
# Finite Cleanup work in the engine (I12)

A Cleanup frame can repeat, return to its continuation, or wait for a decision. This module
uses the board measure through the actual work dispatcher, including event observation.
-/

@[expose] public section

namespace Riftbound

/-- Whether the frame is a Cleanup. -/
def Frame.isCleanup : Frame → Bool
  | .cleanup => true
  | _ => false

private def isFightAt (field : ObjId) : Frame → Bool
  | .showdown there .. | .endShowdown there => there == field
  | _ => false

/-- Inserting ordinary triggers preserves the subsequence whose filter ignores trigger frames. -/
theorem insertTriggers_filter (keep : Frame → Bool)
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

/-- Observing triggers preserves the subsequence of frames distinguished from trigger and Run frames. -/
theorem insertDetectedTriggers_filter (keep : Frame → Bool)
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

/-- A head frame other than a trigger queue was already at the head before insertion. -/
theorem insertTriggers_head {queue : List PendTrigger} {stack : List Frame}
    {frame : Frame} (notTrigger : ∀ q, frame ≠ .triggers q)
    (head : (insertTriggers queue stack).head? = some frame) :
    stack.head? = some frame := by
  cases stack with
  | nil => exact False.elim (notTrigger _ (by simpa [insertTriggers] using head.symm))
  | cons first rest =>
    simp only [insertTriggers] at head
    split at head
    · simpa using head
    · split at head <;> exact False.elim (notTrigger _ (by simpa using head.symm))

/-- Observation can leave a pre-existing frame at the head, but cannot introduce there a
frame other than a Run or a trigger queue. -/
private theorem insertDetectedTriggers_head {s : GameState} {queue : List PendTrigger}
    {stack : List Frame} {frame : Frame} (notTrigger : ∀ q, frame ≠ .triggers q)
    (notRun : ∀ p id env effects, frame ≠ .run p id env effects)
    (head : (insertDetectedTriggers s queue stack).head? = some frame) :
    stack.head? = some frame := by
  let arrivals := queue.map (fun t => (t, t.immediateAddFrame s))
  have onlyRuns {f : Frame} (member : f ∈ arrivals.filterMap Prod.snd) :
      ∃ p id env effects, f = .run p id env effects := by
    obtain ⟨⟨t, added⟩, inArrivals, got⟩ := List.mem_filterMap.mp member
    obtain ⟨source, _, eq⟩ := List.mem_map.mp inArrivals
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact PendTrigger.immediateAddFrame_run got
  unfold insertDetectedTriggers at head
  change ((arrivals.filterMap Prod.snd ++ _).head?) = some frame at head
  cases front : arrivals.filterMap Prod.snd with
  | nil =>
    rw [front, List.nil_append] at head
    split at head
    · exact head
    · exact insertTriggers_head notTrigger head
  | cons first rest =>
    have member : first ∈ arrivals.filterMap Prod.snd := by simp [front]
    obtain ⟨p, id, env, effects, rfl⟩ := onlyRuns member
    exact False.elim (notRun p id env effects (by simpa [front] using head.symm))

private theorem any_eq_of_filter_eq (p : Frame → Bool) {first second : List Frame}
    (eq : first.filter p = second.filter p) : first.any p = second.any p := by
  have test (xs : List Frame) : (xs.filter p).any p = xs.any p := by
    simp only [List.any_filter, Bool.and_self]
  rw [← test first, ← test second, eq]

/-- Cleanup's measure depends on the board, the card definitions, and the fields being fought over. -/
theorem cleanupMeasure_eq {s t : GameState} (config : t.config = s.config)
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

/-- Recording an ability use leaves Cleanup's measure unchanged if the same fields are fought over. -/
theorem noteAbilityUse_cleanupMeasure (s : GameState) (source : ObjId) (index : Nat)
    (copy : Option Timestamp) (stack : List Frame)
    (combat : ∀ field, ({ (s.modObj source (fun obj => obj.noteAbilityUse index copy)) with
      pending := stack } : GameState).fightingAt field = s.fightingAt field) :
    let t := { (s.modObj source (fun obj => obj.noteAbilityUse index copy)) with pending := stack }
    t.cleanupMeasure = s.cleanupMeasure := by
  intro t
  have config : t.config = s.config := rfl
  have cards : t.cards = s.cards := rfl
  have zone : t.zone = s.zone := rfl
  have board : t.inPlay = s.inPlay := rfl
  have lookup (id : ObjId) : t.obj? id = (s.obj? id).map
      (if source = id then (fun o => o.noteAbilityUse index copy) else (fun o => o)) := by
    change (s.modObj source _).obj? id = _
    rw [GameState.obj?_modObj]
    by_cases selected : source = id
    · subst id
      simp
    · have different : source.n ≠ id.n := fun h => selected (congrArg ObjId.mk h)
      simp [different, selected]
  have prints : t.printedCardDef? = s.printedCardDef? := by
    funext id
    unfold GameState.printedCardDef?
    rw [lookup, cards]
    split <;> cases s.obj? id <;> rfl
  have unit : t.isUnit = s.isUnit := by
    funext id
    unfold GameState.isUnit
    rw [prints, lookup]
    split <;> cases s.obj? id <;> rfl
  have fields : t.battlefields = s.battlefields := by
    simp only [GameState.battlefields, GameState.isBattlefield, zone, prints]
  have tok : t.isTok = s.isTok := by
    funext id
    unfold GameState.isTok
    rw [lookup]
    split <;> cases s.obj? id <;> rfl
  have loose : t.looseP = s.looseP := by
    funext id
    unfold GameState.looseP
    rw [lookup, board]
    split <;> cases s.obj? id <;> rfl
  have atField : t.unitsAt = s.unitsAt := by
    funext field
    unfold GameState.unitsAt
    rw [zone]
    apply List.filter_congr
    intro id _
    unfold GameState.isAt
    rw [unit, lookup]
    split <;> cases s.obj? id <;> rfl
  have controller (id : ObjId) : (t.obj? id).map Object.controller = (s.obj? id).map Object.controller := by
    rw [lookup]
    split <;> cases s.obj? id <;> rfl
  have players : t.unitsOf = s.unitsOf := by
    funext p field
    simp only [GameState.unitsOf, GameState.isControlledBy, atField, controller]
  have control : t.controlOf = s.controlOf := by
    funext id
    unfold GameState.controlOf
    rw [lookup]
    split <;> cases s.obj? id <;> rfl
  have contest (id : ObjId) : (t.obj? id).bind Object.contested = (s.obj? id).bind Object.contested := by
    rw [lookup]
    split <;> cases s.obj? id <;> rfl
  have damage : t.dmgC = s.dmgC := by
    unfold GameState.dmgC
    rw [board]
    apply List.countP_congr
    intro id _
    rw [lookup]
    split <;> cases s.obj? id <;> rfl
  have fighting : ∀ field, t.fightingAt field = s.fightingAt field := combat
  unfold GameState.cleanupMeasure GameState.cLoose GameState.cLost GameState.cStale GameState.cNew
  have pot : t.pot = s.pot := rfl
  have tokens : t.tokC = s.tokC := by
    simp only [GameState.tokC, GameState.nbZones, GameState.playerCount, config, zone, tok]
  simp only [GameState.lostControl, GameState.staleContest, GameState.newContest, pot, tokens,
    damage, fields, loose, board, control, contest, players, fighting, atField, controller]

private theorem continuing_observer (s : GameState) (events : List Event)
    {frame : Frame} (notTrigger : ∀ q, frame ≠ .triggers q)
    (notRun : ∀ p id env effects, frame ≠ .run p id env effects)
    (head : (s.withTriggers events).pending.head? = some frame) :
    s.pending.head? = some frame ∧
    (s.withTriggers events).cleanupMeasure = s.cleanupMeasure ∧
    (s.withTriggers events).pending.countP Frame.isCleanup = s.pending.countP Frame.isCleanup := by
  rcases withTriggers_cases s events with ⟨player, removed, _⟩ | onlyHistory | ⟨queue, woven, _⟩
  · simp [removed] at head
  · rw [onlyHistory] at head ⊢
    exact ⟨head, rfl, rfl⟩
  · rw [woven] at head ⊢
    let observed := s.recordTurnEvents events
    change (insertDetectedTriggers observed queue s.pending).head? = some frame at head
    refine ⟨insertDetectedTriggers_head notTrigger notRun head, cleanupMeasure_eq rfl rfl rfl rfl ?_, ?_⟩
    · intro field
      unfold GameState.fightingAt
      have exactFight := insertDetectedTriggers_filter (isFightAt field) (fun _ => rfl)
        (fun _ _ _ _ => rfl) observed queue s.pending
      have same := any_eq_of_filter_eq _ exactFight
      change (s.combat.any (·.battlefield == field) ||
        (insertDetectedTriggers observed queue s.pending).any (isFightAt field)) =
        (s.combat.any (·.battlefield == field) || s.pending.any (isFightAt field))
      rw [same]
    · have same := insertDetectedTriggers_filter Frame.isCleanup (fun _ => rfl)
        (fun _ _ _ _ => rfl) observed queue s.pending
      simp only [List.countP_eq_length_filter]
      exact congrArg List.length same

/-- Each Cleanup iteration reduces the number of frames or the Board measure. -/
def cleanupWorkRank (s : GameState) :
    Nat × (Nat × Nat × Nat × Nat × Nat × Nat) :=
  (s.pending.countP Frame.isCleanup, s.cleanupMeasure)

/-- A decrease across a consecutive sequence of Cleanup work. -/
def CleanupWorkLt (next before : GameState) : Prop :=
  Prod.Lex (· < ·) MeasLt (cleanupWorkRank next) (cleanupWorkRank before)

private theorem cleanupWorkLt_wf : WellFounded CleanupWorkLt :=
  InvImage.wf cleanupWorkRank ((Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ ⟨_, MeasLt.wf⟩).wf)

/-- A Cleanup step that keeps processing Cleanup or returns to Expiration decreases the
Cleanup rank. An observer may append ordinary triggers behind pending Cleanup work. -/
theorem cleanup_workStep_decreases (s : GameState) (wf : s.WF) (rest : List Frame)
    (pending : s.pending = .cleanup :: rest) {next : GameState} {events : List Event}
    (h : workStep s = some (next, events))
    (continues : next.pending.head? = some .cleanup ∨ next.pending.head? = some .expireTurn) :
    CleanupWorkLt next s := by
  let result := cleanupFrame s rest
  let observed := result.1.withTriggers (result.2 ++ s.workTransitionEvents result.1)
  have raw : microStep0 s = some result := by simp only [microStep0, pending, result]
  have step : workStep s = some (observed, result.2) := by
    simp only [workStep, pending, microStep, raw, Option.map_some, observed]
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (h.symm.trans step))
  have facts : (result.1.pending.head? = some .cleanup ∨
      result.1.pending.head? = some .expireTurn) ∧
      observed.cleanupMeasure = result.1.cleanupMeasure ∧
      observed.pending.countP Frame.isCleanup = result.1.pending.countP Frame.isCleanup := by
    rcases continues with cleanup | expire
    · obtain ⟨head, measure, count⟩ := continuing_observer result.1
        (result.2 ++ s.workTransitionEvents result.1) (by simp) (by simp) cleanup
      exact ⟨Or.inl head, measure, count⟩
    · obtain ⟨head, measure, count⟩ := continuing_observer result.1
        (result.2 ++ s.workTransitionEvents result.1) (by simp) (by simp) expire
      exact ⟨Or.inr head, measure, count⟩
  obtain ⟨rawHead, measure, count⟩ := facts
  have repeated (r : GameState × List Event) (safe : Safe s r.1)
      (route : result = ({ r.1 with pending := .cleanup :: rest }, r.2)) :
      observed.cleanupMeasure = r.1.cleanupMeasure ∧
        observed.pending.countP Frame.isCleanup = s.pending.countP Frame.isCleanup := by
    have original : r.1.pending = .cleanup :: rest := safe.same.pending.trans pending
    have reinstalled : { r.1 with pending := .cleanup :: rest } = r.1 := by
      rw [← original]
    have rawState : result.1 = r.1 := by rw [route, reinstalled]
    change observed.cleanupMeasure = result.1.cleanupMeasure at measure
    change observed.pending.countP Frame.isCleanup = result.1.pending.countP Frame.isCleanup at count
    exact ⟨measure.trans (congrArg GameState.cleanupMeasure rawState),
      count.trans (congrArg (fun u : GameState => u.pending.countP Frame.isCleanup)
        rawState) |>.trans
          (congrArg (List.countP Frame.isCleanup) safe.same.pending)⟩
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
        have decreases : MeasLt observed.cleanupMeasure s.cleanupMeasure := by
          rw [sameMeasure]
          exact cleanupResolveDeathGroup_decreases wf group
        exact Prod.Lex.right' MeasLt (Nat.le_of_eq sameCount) decreases
      | none =>
        cases single : cleanupStep s with
        | some r =>
          obtain ⟨board, events⟩ := r
          have route : result = ({ board with pending := .cleanup :: rest }, events) := by
            simp [result, cleanupFrame, winner, choice, group, single]
          obtain ⟨sameMeasure, sameCount⟩ := repeated (board, events)
            (cleanupStep_safe (s' := board) (es := events) single) route
          have decreases : MeasLt observed.cleanupMeasure s.cleanupMeasure := by
            rw [sameMeasure]
            exact cleanupStep_lt wf single
          exact Prod.Lex.right' MeasLt (Nat.le_of_eq sameCount) decreases
        | none =>
          cases showdowns : s.stagedShowdowns rest with
          | nil =>
            have route : result = continueAfterCleanup s rest := by
              simp [result, cleanupFrame, winner, choice, group, single, showdowns]
            have smaller : observed.pending.countP Frame.isCleanup < s.pending.countP Frame.isCleanup := by
              rw [count, pending, route]
              change rest.countP Frame.isCleanup < (Frame.cleanup :: rest).countP Frame.isCleanup
              rw [List.countP_cons_of_pos (show Frame.isCleanup .cleanup = true from rfl)]
              exact Nat.lt_succ_self _
            exact Prod.Lex.left _ _ smaller
          | cons entry others =>
            obtain ⟨field, player⟩ := entry
            simp only [result, cleanupFrame, winner, choice, group, single, showdowns] at rawHead
            split at rawHead <;> simp [continueAfterCleanup] at rawHead

private theorem cleanup_engine_step (s : GameState) (wf : s.WF) (rest : List Frame)
    (pending : s.pending = .cleanup :: rest) :
    ∃ next events, workStep s = some (next, events) ∧
      (next.pending.head? ≠ some .cleanup ∨
        (next.pending.head? = some .cleanup ∧ CleanupWorkLt next s)) := by
  let raw := cleanupFrame s rest
  let next := raw.1.withTriggers (raw.2 ++ s.workTransitionEvents raw.1)
  have step : workStep s = some (next, raw.2) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some, raw, next]
  refine ⟨next, raw.2, step, ?_⟩
  by_cases front : next.pending.head? = some .cleanup
  · exact Or.inr ⟨front, cleanup_workStep_decreases s wf rest pending step (Or.inl front)⟩
  · exact Or.inl front

/-- A nonempty segment of consecutive Cleanup work in the real engine always ends.
Ordinary steps, simultaneous deaths and nested replacements use the Board measure even when
observers schedule ordinary triggers. Returning to a continuation consumes a Cleanup frame. -/
theorem advance_cleanup_work {s : GameState} {rest : List Frame} (wf : s.WF)
    (pending : s.pending = .cleanup :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ t.pending.head? ≠ some .cleanup := by
  revert rest
  refine cleanupWorkLt_wf.induction s (C := fun state => state.WF →
    ∀ {rest}, state.pending = .cleanup :: rest →
      ∃ t used events, 0 < used ∧ AdvancePrefix state t used events ∧ t.pending.head? ≠ some .cleanup) ?_ wf
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
