module

public import Riftbound.Engine.Step

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
  have noExhaust : s.exhaustionEvents next none = [] := triggersStep_noExhaustion s wf queue rest
  have transitions : s.workTransitionEvents next = s.mightyEvents next := by
    unfold GameState.workTransitionEvents
    rw [pending]
    change s.exhaustionEvents next none ++ s.mightyEvents next ++ [] ++ [] = _
    simp only [noExhaust, List.nil_append, List.append_nil]
  simp only [workStep, pending, microStep, raw, Option.map_some, transitions, List.nil_append]
  rw [withMightNotices next (s.mightyEvents next) (fun _ h => mightyEvents_notice h)]

end Riftbound

end
