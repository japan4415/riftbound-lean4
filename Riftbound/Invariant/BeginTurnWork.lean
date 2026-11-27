module

public import Riftbound.Invariant.Step
public import Riftbound.Invariant.TriggerWork

/-!
# Automatic work at the turn boundary

Beginning a turn can reset the inputs to Might. In a checked database, any crossing queues an
ordinary trigger, which requires a decision before Awaken proceeds.
-/

@[expose] public section

namespace Riftbound
private theorem beginTurn_noExhaustion (s : GameState) (rest : List Frame) :
    s.exhaustionEvents (beginTurnStep s rest) none = [] := by
  let next := beginTurnStep s rest
  have lookup (id : ObjId) : (next.obj? id).map Object.exhausted =
      (s.obj? id).map Object.exhausted := by
    rcases beginTurnStep_cases s rest with starts | ⟨_, ends⟩
    · change ((beginTurnStep s rest).obj? id).map _ = _
      rw [starts]
      change ((s.mapObjects clearScored).obj? id).map _ = _
      rw [GameState.obj?_mapObjects]
      cases s.obj? id <;> rfl
    · change ((beginTurnStep s rest).obj? id).map _ = _
      rw [ends]
      rfl
  have noneReadyLost : ((s.inPlay ++ s.players.flatMap (fun q => s.zone (.player q .legendZone))).filter
      (fun id => (s.obj? id).any (fun o => !o.exhausted) && (next.obj? id).any (·.exhausted))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro id _
    have before := lookup id
    cases a : s.obj? id <;> cases b : next.obj? id <;> simp_all
  unfold GameState.exhaustionEvents
  change (if (((s.inPlay ++ s.players.flatMap (fun q => s.zone (.player q .legendZone))).filter
      (fun id => (s.obj? id).any (fun o => !o.exhausted) && (next.obj? id).any (·.exhausted))).isEmpty)
      then [] else _) = []
  rw [noneReadyLost]
  rfl

/-- A new turn can trigger a Might crossing, but its observation queues only ordinary work
in a database checked against the dispatcher. -/
theorem workStep_beginTurn_mightOrdinary (s : GameState) (rest : List Frame)
    (pending : s.pending = .beginTurn :: rest) (database : s.cards.mightTriggersAreOrdinary) :
    let next := beginTurnStep s rest
    let detected := next.detect (s.mightyEvents next)
    workStep s = some (if next.phase != .setup && next.pending.all (fun f => !f.isSetup) &&
      !detected.isEmpty then { next with pending := insertTriggers detected next.pending }
      else next, ([] : List Event)) := by
  intro next detected
  have nextCards : next.cards = s.cards := by
    rcases beginTurnStep_cases s rest with starts | ⟨_, ends⟩
    · change (beginTurnStep s rest).cards = _
      rw [starts]
      rfl
    · change (beginTurnStep s rest).cards = _
      rw [ends]
  have observation : s.workTransitionEvents next = s.mightyEvents next := by
    unfold GameState.workTransitionEvents
    rw [pending]
    change s.exhaustionEvents next none ++ s.mightyEvents next ++ [] ++ [] = _
    rw [beginTurn_noExhaustion s rest, List.nil_append, List.append_nil, List.append_nil]
  simp only [workStep, pending, microStep, microStep0, Option.map_some]
  change some (next.withTriggers ([] ++ s.workTransitionEvents next), []) = _
  rw [List.nil_append, observation, withMightyEvents_ordinary s next (nextCards ▸ database)]

/-- When the clock allows play to continue, the real engine initializes the turn and reaches its
Awaken stack with its card database, or a decision for the ordinary queue that came first. -/
theorem advance_beginTurn_checkpoint {s : GameState} {rest : List Frame} (wf : s.WF)
    (checkedMight : MightRead.database s.cards) (checkedTriggers : s.cards.mightTriggersAreOrdinary)
    (pending : s.pending = .beginTurn :: rest) (clock : s.clockConclusion = none) :
    ∃ t used, 0 < used ∧ AdvancePrefix s t used [] ∧ t.WF ∧
      ((t.pending = turnFrames s.nextTurnPlayer ++ rest ∧ t.active = some s.nextTurnPlayer ∧
        t.turn = s.turn + 1 ∧ t.cards = s.cards) ∨
        t.pending.head?.any (fun f => !f.isWork) = true) := by
  let next := beginTurnStep s rest
  let detected := next.detect (s.mightyEvents next)
  have stack : next.pending = turnFrames s.nextTurnPlayer ++ rest := by
    simp [next, beginTurnStep, clock]
  have cards : next.cards = s.cards := by
    simp [next, beginTurnStep, clock, GameState.mapObjects, GameState.mapObjectsAt]
  let sees := next.phase != .setup && next.pending.all (fun f => !f.isSetup) && !detected.isEmpty
  have step := workStep_beginTurn_mightOrdinary s rest pending checkedTriggers
  change workStep s = some (if sees then { next with pending := insertTriggers detected next.pending }
    else next, []) at step
  by_cases observe : sees = true
  · rw [ite_eq_left observe] at step
    let waiting := { next with pending := insertTriggers detected next.pending }
    have activeStack : waiting.pending = .triggers detected :: (turnFrames s.nextTurnPlayer ++ rest) := by
      change insertTriggers detected next.pending = _
      rw [stack]
      rfl
    have waitingCards : waiting.cards = s.cards := cards
    have nonempty : detected ≠ [] := by
      intro empty
      have observed := observe
      simp [sees, empty] at observed
    obtain ⟨t, used, f, later, _, path, decision, stop, notNeutral⟩ :=
      advance_triggers_to_nonpriorityDecision waiting (workStep_wf wf step) detected _ activeStack
        (waitingCards ▸ checkedMight) (Or.inl nonempty) (by simp [turnFrames])
    have reached : t.WF := by
      have prepared := GameState.preparePriority_of_nonpriority decision notNeutral
      have finish := path.finish (by simp [prepared, decision, stop]) []
      exact advance_wf used (workStep_wf wf step) (by simpa using finish)
    exact ⟨t, used + 1, by omega, by simpa using path.prepend pending rfl step, reached,
      Or.inr (by simp [decision, stop])⟩
  · rw [ite_eq_right observe] at step
    have still : AdvancePrefix next next 0 [] := by intro fuel before; simp
    have started : next.active = some s.nextTurnPlayer ∧ next.turn = s.turn + 1 := by
      simp [next, beginTurnStep, clock]
    exact ⟨next, 1, by decide, still.prepend pending rfl step, workStep_wf wf step,
      Or.inl ⟨stack, started.1, started.2, cards⟩⟩

/-- When the clock allows play to continue, the real engine initializes the turn and reaches its
Awaken stack or a player decision for any nonempty ordinary queue that came first. -/
theorem advance_beginTurn {s : GameState} {rest : List Frame} (wf : s.WF)
    (checkedMight : MightRead.database s.cards) (checkedTriggers : s.cards.mightTriggersAreOrdinary)
    (pending : s.pending = .beginTurn :: rest) (clock : s.clockConclusion = none) :
    ∃ t used, 0 < used ∧ AdvancePrefix s t used [] ∧ t.WF ∧
      ((t.pending = turnFrames s.nextTurnPlayer ++ rest ∧ t.active = some s.nextTurnPlayer ∧
        t.turn = s.turn + 1) ∨
        t.pending.head?.any (fun f => !f.isWork) = true) := by
  obtain ⟨t, used, positive, trace, wellFormed, stop⟩ :=
    advance_beginTurn_checkpoint wf checkedMight checkedTriggers pending clock
  exact ⟨t, used, positive, trace, wellFormed,
    stop.imp_left (fun awake => ⟨awake.1, awake.2.1, awake.2.2.1⟩)⟩

/-- A clock conclusion on the normal turn boundary ends the game in one work step. -/
theorem advance_beginTurn_clock {s : GameState} {result : GameResult}
    (wf : s.WF) (database : MightRead.database s.cards) (pending : s.pending = [.beginTurn])
    (deadline : s.clockConclusion = some result) :
    let done := { s with result := some result, pending := [] }
    AdvancePrefix s done 1 [] ∧ advance 1 s [] = .ok (done, []) := by
  intro done
  have combat : done.combatNow = s.combatNow := by
    unfold GameState.combatNow
    simp only [done, pending, List.findSome?_cons, List.findSome?_nil]
  have reads : SameMightReads s done := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ => rfl,
    rfl, rfl, rfl, rfl, combat, rfl, rfl, rfl, (fun _ => rfl), rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  have mighty : s.mightyEvents done = [] :=
    mightyEvents_eq_nil_of_mightNow (fun _ member => (reads.mightNow_eq wf database
      (old_inPlay wf member)).symm)
  have clockStep : beginTurnStep s [] = done := by simp [beginTurnStep, deadline, done]
  have exhausted : s.exhaustionEvents done none = [] := clockStep ▸ beginTurn_noExhaustion s []
  have quiet : s.workTransitionEvents done = [] := by
    simp only [GameState.workTransitionEvents, pending, exhausted, mighty,
      GameState.mightReductionEvents, List.nil_append]
  have work : workStep s = some (done, []) := by
    simp only [workStep, pending, microStep, microStep0, beginTurnStep, deadline, Option.map_some,
      List.nil_append]
    change some (done.withTriggers (s.workTransitionEvents done), []) = _
    rw [quiet, withTriggers_nil]
  have same : AdvancePrefix done done 0 [] := by intro fuel before; simp
  have path : AdvancePrefix s done 1 [] := same.prepend pending rfl work
  exact ⟨path, path.finish rfl []⟩

/-- The blank Battlefield added after a concession cannot add a Might observer. -/
theorem CardDB.mightTriggersAreOrdinary_withConcessionBattlefield {db : CardDB}
    (checked : db.mightTriggersAreOrdinary) : db.withConcessionBattlefield.mightTriggersAreOrdinary := by
  unfold CardDB.withConcessionBattlefield
  split
  · exact checked
  · change (db.cards ++ [concessionBattlefieldToken]).all CardDef.mightTriggersAreOrdinary = true
    have blank : concessionBattlefieldToken.mightTriggersAreOrdinary = true := rfl
    change db.cards.all CardDef.mightTriggersAreOrdinary = true at checked
    simp only [List.all_append, List.all_cons, List.all_nil, blank, checked, Bool.and_self]

end Riftbound

end
