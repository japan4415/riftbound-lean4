module

public import Riftbound.Engine.Step
public import Riftbound.Invariant.TriggerFinalization

/-!
# Observing the automatic finalization of ordinary triggers (I12)

A queue step can put a targetless ability on the Chain or present a decision. Neither exhausts
an object. Any new triggers observed after that work come from crossings of Might thresholds.
-/

@[expose] public section

namespace Riftbound

private def boardObserved (s : GameState) : List ObjId :=
  s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))

private theorem boardObserved_lt {s : GameState} (wf : s.WF) {id : ObjId}
    (member : id ∈ boardObserved s) : id.n < s.nextId := by
  have fromZone {z : Zone} (found : id ∈ s.zone z) : id.n < s.nextId :=
    wf.lt_nextId id (GameState.mem_zoneIds (GameState.zone_valid_of_mem wf found) found)
  simp only [boardObserved, GameState.inPlay, List.mem_append, List.mem_flatMap] at member
  rcases member with (⟨_, _, found⟩ | found) | ⟨_, _, found⟩
  all_goals exact fromZone found

private theorem lookup_addObject_of_lt {s t : GameState} {object : Object} {zone : Zone}
    {pos : Pos} {id query : ObjId} (added : addObject s object zone pos = some (t, id))
    (old : query.n < s.nextId) : t.obj? query = s.obj? query := by
  unfold addObject at added
  split at added
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj added).symm
    have different : compare s.nextId query.n ≠ .eq :=
      fun h => (Nat.ne_of_lt old) (Nat.compare_eq_eq.mp h).symm
    simp only [GameState.obj?, Std.ExtTreeMap.getElem?_insert, different, ite_false]
  · contradiction

private theorem putTrigger_exhaustion {s : GameState} (trigger : PendTrigger) {id : ObjId}
    (old : id.n < s.nextId) :
    ((putTrigger s trigger []).obj? id).map Object.exhausted =
      (s.obj? id).map Object.exhausted := by
  unfold putTrigger
  have noMode : recordTriggerMode s trigger none = s := by
    unfold recordTriggerMode
    split <;> rfl
  rw [noMode]
  dsimp only
  let used := s.modObj trigger.source
    (fun o => (o.noteAbilityUse trigger.idx trigger.copyStamp).noteChose s.turn [])
  change ((match addObject used _ .chain with
    | some r => r.1
    | none => used).obj? id).map Object.exhausted = _
  have same : (used.obj? id).map Object.exhausted = (s.obj? id).map Object.exhausted := by
    unfold used
    rw [GameState.obj?_modObj]
    split
    · rename_i h
      have sameId : trigger.source = id := by
        cases source : trigger.source
        cases id
        simp_all
      rw [sameId]
      cases s.obj? id <;> rfl
    · rfl
  split
  · rename_i r added
    obtain ⟨t, new⟩ := r
    have lookup := lookup_addObject_of_lt (query := id) added (show id.n < used.nextId from old)
    rw [lookup]
    exact same
  · exact same

private theorem triggersStep_noExhaustion (s : GameState) (wf : s.WF)
    (queue : List PendTrigger) (rest : List Frame) :
    let outcome := triggersStep s queue rest
    let next := { outcome.1 with pending := outcome.2 ++ rest }
    s.exhaustionEvents next none = [] := by
  have same (id : ObjId) (member : id ∈ boardObserved s) :
      (((triggersStep s queue rest).1).obj? id).map Object.exhausted =
        (s.obj? id).map Object.exhausted := by
    cases queue with
    | nil => rfl
    | cons trigger others =>
      simp only [triggersStep]
      split
      · exact putTrigger_exhaustion trigger (boardObserved_lt wf member)
      · rfl
  have empty : (boardObserved s).filter (fun id =>
      (s.obj? id).any (fun o => !o.exhausted) &&
        ((triggersStep s queue rest).1.obj? id).any (·.exhausted)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro id member
    have obj := same id member
    cases before : s.obj? id with
    | none => simp
    | some a =>
      rw [before] at obj
      cases after : (triggersStep s queue rest).1.obj? id with
      | none => simp
      | some b =>
        rw [after] at obj
        have sameBit : b.exhausted = a.exhausted := Option.some.inj obj
        simp [sameBit]
  unfold GameState.exhaustionEvents
  change (if ((boardObserved s).filter (fun id => (s.obj? id).any (fun o => !o.exhausted) &&
      ((triggersStep s queue rest).1.obj? id).any (·.exhausted))).isEmpty then [] else _) = []
  rw [empty]
  rfl

private inductive MightNotice : Event → Prop where
  | mighty (id) : MightNotice (.becameMighty id)
  | reached (id threshold) : MightNotice (.mightReached id threshold)

private theorem mightyEvents_notice {s t : GameState} {event : Event}
    (member : event ∈ s.mightyEvents t) : MightNotice event := by
  unfold GameState.mightyEvents at member
  dsimp only at member
  split at member
  · simp at member
  · obtain ⟨id, _, found⟩ := List.mem_flatMap.mp member
    split at found
    · split at found
      · obtain ⟨⟨threshold, watched⟩, _, result⟩ := List.mem_filterMap.mp found
        dsimp only at result
        split at result
        · cases watched <;> simp at result
          · subst event; exact .mighty id
          · subst event; exact .reached id _
        · simp at result
      · simp at found
    · simp at found

/-- Might threshold notices do not record any turn facts. -/
theorem mightyEvents_recordTurnEvent {s t : GameState} {event : Event}
    (member : event ∈ s.mightyEvents t) (current : GameState) (facts : List TurnFx) :
    current.recordTurnEvent facts event = facts := by
  cases mightyEvents_notice member <;> rfl

/-- A Might transition reports either a newly Mighty Unit or a numeric threshold crossing. -/
theorem mightyEvents_cases {s t : GameState} {event : Event}
    (member : event ∈ s.mightyEvents t) :
    (∃ id, event = .becameMighty id) ∨ (∃ id threshold, event = .mightReached id threshold) := by
  cases mightyEvents_notice member with
  | mighty id => exact Or.inl ⟨id, rfl⟩
  | reached id threshold => exact Or.inr ⟨id, threshold, rfl⟩

/-- Keeping the Might of the existing Board objects cannot create a threshold crossing. -/
theorem mightyEvents_eq_nil_of_mightNow {s t : GameState}
    (same : ∀ id ∈ s.inPlay, s.mightNow id = t.mightNow id) : s.mightyEvents t = [] := by
  unfold GameState.mightyEvents
  dsimp only
  split
  · rfl
  apply List.flatMap_eq_nil_iff.mpr
  intro id _
  split
  · rename_i onBoard
    simp only [Bool.and_eq_true] at onBoard
    rw [same id (List.contains_iff_mem.mp onBoard.1)]
    cases might : t.mightNow id with
    | none => rfl
    | some amount =>
      apply List.filterMap_eq_nil_iff.mpr
      rintro ⟨n, event⟩ _
      dsimp only
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      split
      · rename_i crossing
        omega
      · rfl
  · rfl

private theorem foldl_mightNotices {α : Type} (update : α → Event → α)
    (inert : ∀ a e, MightNotice e → update a e = a) (start : α)
    (events : List Event) (notices : ∀ e ∈ events, MightNotice e) :
    events.foldl update start = start := by
  induction events with
  | nil => rfl
  | cons first later ih =>
    rw [List.foldl_cons, inert start first (notices _ List.mem_cons_self)]
    exact ih (fun e mem => notices _ (List.mem_cons_of_mem _ mem))

private theorem recordMightNotices (s : GameState) (events : List Event)
    (notices : ∀ e ∈ events, MightNotice e) : s.recordTurnEvents events = s := by
  have keepPlays := foldl_mightNotices s.recordPlayEvent
    (fun _ _ h => by cases h <;> rfl) s.playLog events notices
  have keepFacts := foldl_mightNotices s.recordTurnEvent
    (fun _ _ h => by cases h <;> rfl) s.turnFx events notices
  unfold GameState.recordTurnEvents
  simp only [keepPlays, keepFacts, ite_self]

private theorem mightNotices_noDelayedPlay (s : GameState) (events : List Event)
    (notices : ∀ e ∈ events, MightNotice e) : s.delayedPlayTriggers events = [] := by
  have noPlays (p : PlayerId) (kind : CardType) : events.filter (s.matchesDelayedPlay p kind) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e mem
    cases notices e mem <;> simp [GameState.matchesDelayedPlay]
  unfold GameState.delayedPlayTriggers
  split
  · rfl
  · apply List.flatMap_eq_nil_iff.mpr
    intro note _
    split
    · simp [noPlays]
    · rfl

private theorem mightNotices_noSuddenDeath (s : GameState) (events : List Event)
    (notices : ∀ e ∈ events, MightNotice e) : s.suddenDeathScorer events = none := by
  unfold GameState.suddenDeathScorer
  cases s.clock with
  | none => rfl
  | some _ =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · apply List.findSome?_eq_none_iff.mpr
      intro e mem
      cases notices e mem <;> rfl
    · rfl

private theorem withMightNotices (s : GameState) (events : List Event)
    (notices : ∀ e ∈ events, MightNotice e) :
    let detected := s.detect events
    s.withTriggers events = if s.phase != .setup && s.pending.all (fun f => !f.isSetup) &&
      !detected.isEmpty then { s with pending := insertDetectedTriggers s detected s.pending } else s := by
  unfold GameState.withTriggers
  rw [recordMightNotices s events notices, mightNotices_noSuddenDeath s events notices]
  dsimp only
  have first : s.firstCardTriggers s = [] := by simp [GameState.firstCardTriggers]
  rw [first, mightNotices_noDelayedPlay s events notices]
  simp only [List.nil_append]
  by_cases active : (s.phase != .setup && s.pending.all (fun f => !f.isSetup)) = true
  · cases s.detect events <;> simp [active]
  · simp [active]

/-- Observing a Might transition only updates the pending stack through the detector. -/
theorem withMightyEvents (before after : GameState) :
    let detected := after.detect (before.mightyEvents after)
    after.withTriggers (before.mightyEvents after) =
      if after.phase != .setup && after.pending.all (fun f => !f.isSetup) && !detected.isEmpty
      then { after with pending := insertDetectedTriggers after detected after.pending } else after :=
  withMightNotices after _ (fun _ h => mightyEvents_notice h)

private theorem triggersStep_transitionEvents (s : GameState) (wf : s.WF)
    (queue : List PendTrigger) (rest : List Frame) (pending : s.pending = .triggers queue :: rest) :
    let outcome := triggersStep s queue rest
    let next := { outcome.1 with pending := outcome.2 ++ rest }
    s.workTransitionEvents next = s.mightyEvents next := by
  intro outcome next
  unfold GameState.workTransitionEvents
  rw [pending]
  change s.exhaustionEvents next none ++ s.mightyEvents next ++ [] ++ [] = _
  have empty : s.exhaustionEvents next none = [] := triggersStep_noExhaustion s wf queue rest
  simp only [empty, List.nil_append, List.append_nil]

/-- An ordinary trigger step can cause new trigger work only through observed Might crossings.
The resulting batch comes from the real detector. These observations neither alter the turn's
history nor award points, and the work step itself emits no events. -/
theorem workStep_triggers_observed (s : GameState) (wf : s.WF) (queue : List PendTrigger)
    (rest : List Frame) (pending : s.pending = .triggers queue :: rest) :
    let outcome := triggersStep s queue rest
    let next := { outcome.1 with pending := outcome.2 ++ rest }
    let detected := next.detect (s.mightyEvents next)
    workStep s = some (if next.phase != .setup && next.pending.all (fun f => !f.isSetup) &&
      !detected.isEmpty then { next with pending := insertDetectedTriggers next detected next.pending }
      else next, ([] : List Event)) := by
  let outcome := triggersStep s queue rest
  let next := { outcome.1 with pending := outcome.2 ++ rest }
  have raw : microStep0 s = some (next, []) := by
    simp only [microStep0, pending, next, outcome]
  have transitions : s.workTransitionEvents next = s.mightyEvents next :=
    triggersStep_transitionEvents s wf queue rest pending
  simp only [workStep, pending, microStep, raw, Option.map_some, transitions, List.nil_append]
  rw [withMightyEvents s next]

/-- If finalizing a trigger crosses no Might threshold, event observation leaves the raw
continuation of the ordinary rules dispatcher in place. -/
theorem workStep_triggers_noMightEvents (s : GameState) (wf : s.WF) (queue : List PendTrigger)
    (rest : List Frame) (pending : s.pending = .triggers queue :: rest)
    (noCrossing : let outcome := triggersStep s queue rest
      s.mightyEvents { outcome.1 with pending := outcome.2 ++ rest } = []) :
    workStep s = microStep0 s := by
  let outcome := triggersStep s queue rest
  let next := { outcome.1 with pending := outcome.2 ++ rest }
  have raw : microStep0 s = some (next, []) := by simp only [microStep0, pending, next, outcome]
  have transitions : s.workTransitionEvents next = [] :=
    (triggersStep_transitionEvents s wf queue rest pending).trans noCrossing
  unfold workStep
  rw [pending]
  simp only [microStep, raw, Option.map_some, transitions, List.nil_append, withTriggers_nil]

/-- When no Might thresholds are being watched, finalizing a trigger creates no new observed
work. The actual step has the same continuation as the ordinary rules dispatcher. -/
theorem workStep_triggers_noMightWatches (s : GameState) (wf : s.WF) (queue : List PendTrigger)
    (rest : List Frame) (pending : s.pending = .triggers queue :: rest)
    (noWatches : s.mightWatches = []) : workStep s = microStep0 s := by
  apply workStep_triggers_noMightEvents s wf queue rest pending
  intro outcome
  let next := { outcome.1 with pending := outcome.2 ++ rest }
  have watches : next.mightWatches = [] := (triggersStep_mightWatches s wf queue rest).trans noWatches
  change s.mightyEvents next = []
  simp [GameState.mightyEvents, watches]

end Riftbound

end
