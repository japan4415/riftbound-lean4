module

public import Riftbound.Invariant.CleanupWork
public import Riftbound.Invariant.AwakenWork
public import Riftbound.Invariant.ObservedAddWork
public import Riftbound.Invariant.TurnPhaseWork

/-!
# Finite turn Expiration and Cleanup work

Expiration clears the state that would call for another pass. Cleanup and event observation
can run between passes. In the normal Ending continuation, immediate Add batches also run
between passes. The rank accounts for their resource changes alongside board changes and
the remaining Cleanup and Expiration frames.
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
  rcases List.mem_append.mp member with member | member
  · unfold GameState.showdownOpeningEvents at member
    split at member
    · split at member
      · obtain rfl := List.mem_singleton.mp member
        intro state
        rfl
      · simp at member
    · simp at member
  · exact observeCombat_neutral member

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

private theorem withTriggers_cards (s : GameState) (events : List Event) :
    (s.withTriggers events).cards = s.cards := by
  obtain ⟨_, _, eq⟩ := withTriggers_pending s events
  rw [eq]
  rfl

private theorem expirationStep_cards {s t : GameState} {events : List Event}
    (tracked : inExpirationWork s) (step : workStep s = some (t, events)) : t.cards = s.cards := by
  cases stack : s.pending with
  | nil => simp [inExpirationWork, stack] at tracked
  | cons head rest =>
    have kind : head = .cleanup ∨ head = .expireTurn := by simpa [inExpirationWork, stack] using tracked
    rcases kind with rfl | rfl
    · simp only [workStep, stack, microStep, microStep0, Option.map_some] at step
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj step).symm
      exact (withTriggers_cards _ _).trans (cleanupFrame_cards s rest)
    · simp only [workStep, stack, microStep, microStep0, Option.map_some] at step
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj step).symm
      exact withTriggers_cards _ _

/-- The Ending Phase can reach a decision, start the next turn, or hand off to an immediate Add
that was scheduled by observing an actual event. -/
inductive EndingWorkStop : Option Frame → Prop where
  /-- The game has no further frames. -/
  | empty : EndingWorkStop none
  /-- A player decision stops the current `advance`. -/
  | decision {frame} : frame.isWork = false → EndingWorkStop (some frame)
  /-- The next turn's work is at the top of the stack. -/
  | beginTurn : EndingWorkStop (some .beginTurn)
  /-- An event observer scheduled the resolution of an immediate Add. -/
  | immediateAdd {frame} (observed : GameState) (trigger : PendTrigger) :
      trigger.immediateAddFrame observed = some frame → EndingWorkStop (some frame)

private inductive EndingFrame : Frame → Prop where
  | cleanup : EndingFrame .cleanup
  | expire : EndingFrame .expireTurn
  | queued (q : List PendTrigger) : q ≠ [] → EndingFrame (.triggers q)
  | stop {frame} : EndingWorkStop (some frame) → EndingFrame frame

/-- The generated frames are tracked together with the position of the original Begin Turn.
Generic continuations can omit the latter check. -/
private structure EndingStack (checkTurn : Bool) (frames : List Frame) : Prop where
  allowed : ∀ f ∈ frames, EndingFrame f
  turnLast : checkTurn = true → frames.Pairwise (fun f _ => f ≠ .beginTurn)

private theorem EndingStack.empty (checkTurn : Bool) : EndingStack checkTurn [] :=
  ⟨(fun _ member => nomatch member), fun _ => List.Pairwise.nil⟩

private theorem EndingStack.tail {checkTurn : Bool} {f : Frame} {rest : List Frame}
    (stack : EndingStack checkTurn (f :: rest)) : EndingStack checkTurn rest :=
  ⟨fun task h => stack.allowed task (List.mem_cons_of_mem _ h),
    fun check => (stack.turnLast check).tail⟩

private theorem EndingStack.push {checkTurn : Bool} {f : Frame} {rest : List Frame}
    (stack : EndingStack checkTurn rest) (allowed : EndingFrame f) (other : f ≠ .beginTurn) :
    EndingStack checkTurn (f :: rest) := by
  constructor
  · intro task member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact allowed
    · exact stack.allowed _ inRest
  · intro check
    exact .cons (fun _ _ => other) (stack.turnLast check)

private theorem EndingStack.prepend {checkTurn : Bool} (addedFrames : List Frame) {rest : List Frame}
    (stack : EndingStack checkTurn rest)
    (added : ∀ f ∈ addedFrames, EndingFrame f ∧ f ≠ .beginTurn) :
    EndingStack checkTurn (addedFrames ++ rest) := by
  induction addedFrames with
  | nil => exact stack
  | cons first later ih =>
    have head := added first List.mem_cons_self
    exact (ih (fun f member => added f (List.mem_cons_of_mem _ member))).push head.1 head.2

private theorem insertTriggers_ending {checkTurn : Bool} (queue : List PendTrigger) (nonempty : queue ≠ [])
    (stack : List Frame) (allowed : EndingStack checkTurn stack) :
    EndingStack checkTurn (insertTriggers queue stack) := by
  induction stack with
  | nil => exact allowed.push (.queued _ nonempty) (by intro h; cases h)
  | cons head rest ih =>
    unfold insertTriggers
    split
    · rename_i resolution
      have other : head ≠ .beginTurn := by
        rintro rfl
        contradiction
      exact (ih allowed.tail).push (allowed.allowed _ List.mem_cons_self) other
    · split
      · exact allowed.tail.push (.queued _ (fun h => nonempty (List.append_eq_nil_iff.mp h).2))
          (by intro h; cases h)
      · exact allowed.push (.queued _ nonempty) (by intro h; cases h)

private theorem insertDetectedTriggers_ending {checkTurn : Bool} (s : GameState) (queue : List PendTrigger)
    (stack : List Frame) (allowed : EndingStack checkTurn stack) :
    EndingStack checkTurn (insertDetectedTriggers s queue stack) := by
  unfold insertDetectedTriggers
  dsimp only
  apply EndingStack.prepend
  · split
    · exact allowed
    · rename_i scheduled
      refine insertTriggers_ending _ ?_ stack allowed
      intro empty
      rw [empty] at scheduled
      exact scheduled rfl
  · intro f add
    obtain ⟨⟨_, _⟩, found, eq⟩ := List.mem_filterMap.mp add
    obtain ⟨trigger, _, candidateEq⟩ := List.mem_map.mp found
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj candidateEq
    refine ⟨.stop (.immediateAdd s trigger eq), ?_⟩
    obtain ⟨_, _, _, _, rfl⟩ := PendTrigger.immediateAddFrame_run eq
    intro h
    cases h

private theorem withTriggers_ending {checkTurn : Bool} (s : GameState) (events : List Event)
    (allowed : EndingStack checkTurn s.pending) : EndingStack checkTurn (s.withTriggers events).pending := by
  rcases withTriggers_cases s events with ⟨_, eq, _⟩ | eq | ⟨queue, eq, _⟩
  · rw [eq]
    exact .empty _
  · rw [eq]
    exact allowed
  · rw [eq]
    exact insertDetectedTriggers_ending _ queue _ allowed

private theorem cleanupFrame_ending {checkTurn : Bool} (s : GameState) (rest : List Frame)
    (allowed : EndingStack checkTurn rest) : EndingStack checkTurn (cleanupFrame s rest).1.pending := by
  have cleanup : EndingStack checkTurn (.cleanup :: rest) :=
    allowed.push .cleanup (by intro h; cases h)
  rcases cleanupFrame_cases s rest with ⟨_, eq⟩ | ⟨_, _, _, _, eq⟩ | ⟨_, _, eq⟩ | ⟨_, _, eq⟩ | ⟨_, _, _, eq⟩ | eq <;>
    rw [eq]
  · exact .empty _
  · exact cleanup.push (.stop (.decision rfl)) (by intro h; cases h)
  · exact cleanup
  · exact cleanup.push (.stop (.decision rfl)) (by intro h; cases h)
  · exact allowed.push (.stop (.decision rfl)) (by intro h; cases h)
  · exact allowed

private theorem expirationStep_ending {checkTurn : Bool} {s t : GameState} {events : List Event}
    (tracked : inExpirationWork s) (step : workStep s = some (t, events))
    (allowed : EndingStack checkTurn s.pending) : EndingStack checkTurn t.pending := by
  cases stack : s.pending with
  | nil => simp [inExpirationWork, stack] at tracked
  | cons head rest =>
    have kind : head = .cleanup ∨ head = .expireTurn := by simpa [inExpirationWork, stack] using tracked
    have restAllowed : EndingStack checkTurn rest := (stack ▸ allowed).tail
    rcases kind with rfl | rfl
    · simp only [workStep, stack, microStep, microStep0, Option.map_some] at step
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj step).symm
      exact withTriggers_ending _ _ (cleanupFrame_ending _ _ restAllowed)
    · simp only [workStep, stack, microStep, microStep0, Option.map_some] at step
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj step).symm
      apply withTriggers_ending
      change EndingStack checkTurn (expirationFrames s ++ rest)
      unfold expirationFrames
      split
      · exact (restAllowed.push .expire (by intro h; cases h)).push .cleanup (by intro h; cases h)
      · exact restAllowed

private theorem advance_expiration_checkpoint (checkTurn : Bool) {s : GameState} (wf : s.WF) (pending : inExpirationWork s) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ t.WF ∧ t.cards = s.cards ∧
      ¬inExpirationWork t ∧
      (EndingStack checkTurn s.pending → EndingStack checkTurn t.pending) := by
  refine expirationWorkLt_wf.induction s (C := fun state => state.WF → inExpirationWork state →
    ∃ t used events, 0 < used ∧ AdvancePrefix state t used events ∧ t.WF ∧ t.cards = state.cards ∧
      ¬inExpirationWork t ∧
      (EndingStack checkTurn state.pending → EndingStack checkTurn t.pending)) ?_ wf pending
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
  have nextWF := workStep_wf well step
  have cards := expirationStep_cards front step
  have allowed := expirationStep_ending (checkTurn := checkTurn) front step
  by_cases inside : inExpirationWork next
  · obtain ⟨last, used, later, _, trace, lastWF, lastCards, outside, keep⟩ :=
      ih next (decreases inside) nextWF inside
    exact ⟨last, used + 1, events ++ later, by omega, trace.prepend shape isWork step,
      lastWF, lastCards.trans cards, outside, fun valid => keep (allowed valid)⟩
  · have done : AdvancePrefix next next 0 [] := by intro fuel before; simp
    exact ⟨next, 1, events, by omega, by simpa using done.prepend shape isWork step,
      nextWF, cards, inside, allowed⟩

/-- Starting at Cleanup or Expiration, actual engine work reaches a different frame or the end of
the stack in finite time. In particular, Cleanup and Expiration cannot repeat indefinitely on
their own, even while observation queues ordinary triggers behind the current work. -/
theorem advance_expiration_work {s : GameState} (wf : s.WF)
    (pending : s.pending.head? = some .cleanup ∨ s.pending.head? = some .expireTurn) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head? ≠ some .cleanup ∧ t.pending.head? ≠ some .expireTurn := by
  obtain ⟨t, used, events, positive, path, _, _, outside, _⟩ := advance_expiration_checkpoint false wf pending
  exact ⟨t, used, events, positive, path, fun same => outside (Or.inl same), fun same => outside (Or.inr same)⟩

private theorem advance_ending_checkpoint (checkTurn : Bool) {s : GameState} {rest : List Frame} (wf : s.WF)
    (pending : s.pending = .phase .ending :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ t.WF ∧ t.cards = s.cards ∧
      ¬inExpirationWork t ∧ (EndingStack checkTurn rest → EndingStack checkTurn t.pending) := by
  let raw := { s with phase := .ending, pending := .cleanup :: .expireTurn :: rest }
  let emitted := [Event.phaseStarted (s.active.getD ⟨0⟩) .ending]
  let next := raw.withTriggers (emitted ++ s.workTransitionEvents raw)
  have step : workStep s = some (next, emitted) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some, raw, next, emitted]
  have nextWF := workStep_wf wf step
  have nextCards : next.cards = s.cards := withTriggers_cards raw _
  have allowed (tail : EndingStack checkTurn rest) : EndingStack checkTurn next.pending :=
    withTriggers_ending _ _
      ((tail.push .expire (by intro h; cases h)).push .cleanup (by intro h; cases h))
  by_cases inside : inExpirationWork next
  · obtain ⟨t, used, later, _, run, lastWF, lastCards, outside, keep⟩ :=
      advance_expiration_checkpoint checkTurn nextWF inside
    exact ⟨t, used + 1, emitted ++ later, by omega, run.prepend pending rfl step, lastWF,
      lastCards.trans nextCards, outside, fun valid => keep (allowed valid)⟩
  · have done : AdvancePrefix next next 0 [] := by intro fuel before; simp
    exact ⟨next, 1, emitted, by omega, by simpa using done.prepend pending rfl step,
      nextWF, nextCards, inside, allowed⟩

/-- The turn engine's Ending Phase schedules the first Cleanup and Expiration. The resulting
consecutive work finishes, or hands off to a different kind of work introduced by observation. -/
theorem advance_ending_expiration {s : GameState} {rest : List Frame} (wf : s.WF)
    (pending : s.pending = .phase .ending :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head? ≠ some .cleanup ∧ t.pending.head? ≠ some .expireTurn := by
  obtain ⟨t, used, events, positive, path, _, _, outside, _⟩ := advance_ending_checkpoint false wf pending
  exact ⟨t, used, events, positive, path, fun same => outside (Or.inl same), fun same => outside (Or.inr same)⟩

private theorem advance_ending_handoff {checkTurn : Bool} {s : GameState} {rest : List Frame}
    (wf : s.WF) (database : MightRead.database s.cards) (pending : s.pending = .phase .ending :: rest)
    (continuation : EndingStack checkTurn rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ EndingWorkStop t.pending.head? ∧
      (t.pending.head? = some .beginTurn →
        t.WF ∧ t.cards = s.cards ∧ (checkTurn = true → t.pending = [.beginTurn])) := by
  obtain ⟨mid, elapsed, events, positive, path, midWF, cards, outside, keep⟩ :=
    advance_ending_checkpoint checkTurn wf pending
  cases stack : mid.pending with
  | nil =>
    exact ⟨mid, elapsed, events, positive, path, by rw [stack]; exact .empty, by simp [stack]⟩
  | cons first later =>
    have tracked := keep continuation
    have allowed := tracked.allowed first (stack ▸ List.mem_cons_self)
    cases allowed with
    | cleanup => exact False.elim (outside (Or.inl (stack ▸ rfl)))
    | expire => exact False.elim (outside (Or.inr (stack ▸ rfl)))
    | stop stop =>
      refine ⟨mid, elapsed, events, positive, path, by rw [stack]; exact stop, ?_⟩
      intro front
      have firstIsBegin : first = .beginTurn := by simpa [stack] using front
      subst first
      refine ⟨midWF, cards, fun check => ?_⟩
      have order := List.pairwise_cons.mp (stack ▸ tracked.turnLast check)
      cases later with
      | nil => exact stack
      | cons f fs => exact False.elim (order.1 f List.mem_cons_self rfl)
    | queued queue nonempty =>
      obtain ⟨t, used, f, tail, _, observed, done, decision⟩ :=
        advance_triggers_to_decision mid midWF queue later stack (cards ▸ database) (Or.inl nonempty)
      refine ⟨t, elapsed + used, events, by omega, by simpa using path.append observed,
        by rw [done]; exact .decision decision, ?_⟩
      intro front
      have isBegin : f = .beginTurn := by simpa [done] using front
      subst f
      contradiction

/-- The actual Ending Phase runs its Cleanup and Expiration steps and any leading ordinary
trigger queue. A nonempty queue reaches a player decision; other routes are the next turn,
the end of the stack, a decision reached during Cleanup, or a witnessed triggered Add. -/
theorem advance_ending_through_triggers {s : GameState} {rest : List Frame} (wf : s.WF)
    (database : MightRead.database s.cards) (pending : s.pending = .phase .ending :: rest)
    (continuation : ∀ f ∈ rest, EndingWorkStop (some f)) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ EndingWorkStop t.pending.head? := by
  obtain ⟨t, used, events, positive, path, stop, _⟩ := advance_ending_handoff wf database pending
    (checkTurn := false) ⟨fun f member => .stop (continuation f member), by intro h; cases h⟩
  exact ⟨t, used, events, positive, path, stop⟩

private inductive CycleFrame : Frame → Prop where
  | cleanup : CycleFrame .cleanup
  | expire : CycleFrame .expireTurn
  | turn : CycleFrame .beginTurn
  | queue (pending : List PendTrigger) : CycleFrame (.triggers pending)
  | choice (p : PlayerId) (src : ObjId) (env : Env) (a b : Effect) (more : EffectList) :
      CycleFrame (.eitherDo p src env a b more)

private structure CycleStack (frames : List Frame) : Prop where
  ending : EndingStack true frames
  safe : ∀ f ∈ frames, CycleFrame f

private theorem CycleStack.empty : CycleStack [] := ⟨.empty true, fun _ member => nomatch member⟩

private theorem CycleStack.beginTurn : CycleStack [.beginTurn] :=
  ⟨⟨fun _ member => (List.mem_singleton.mp member).symm ▸ EndingFrame.stop .beginTurn,
      fun _ => .cons (fun _ impossible => nomatch impossible) .nil⟩,
    fun _ member => (List.mem_singleton.mp member).symm ▸ CycleFrame.turn⟩

private theorem CycleStack.tail {f : Frame} {rest : List Frame} (stack : CycleStack (f :: rest)) :
    CycleStack rest := ⟨stack.ending.tail, fun f h => stack.safe f (List.mem_cons_of_mem _ h)⟩

private theorem CycleStack.push {f : Frame} {rest : List Frame} (later : CycleStack rest)
    (frame : EndingFrame f) (safe : CycleFrame f) (other : f ≠ .beginTurn) : CycleStack (f :: rest) := by
  refine ⟨later.ending.push frame other, ?_⟩
  intro task member
  rcases List.mem_cons.mp member with rfl | inside
  · exact safe
  · exact later.safe _ inside

private theorem CycleStack.cleanup {rest : List Frame} (later : CycleStack rest) :
    CycleStack (.cleanup :: rest) := later.push .cleanup .cleanup (by intro h; cases h)

private theorem CycleStack.expire {rest : List Frame} (later : CycleStack rest) :
    CycleStack (.expireTurn :: rest) := later.push .expire .expire (by intro h; cases h)

private theorem CycleStack.noPriority {s : GameState} {rest : List Frame} (ok : CycleStack rest) :
    s.stagedShowdowns rest = [] := by
  cases rest with
  | nil => rfl
  | cons first later =>
    have safe := ok.safe first List.mem_cons_self
    cases safe <;> rfl

private theorem CycleStack.ordinary {s : GameState} (triggers : List PendTrigger) {rest : List Frame}
    (ok : CycleStack rest) : CycleStack (ordinaryTriggerContinuation s triggers rest) := by
  unfold ordinaryTriggerContinuation
  dsimp only
  split
  · exact ok
  · rename_i nonempty
    refine ⟨insertTriggers_ending _ (fun h => nonempty (by rw [h]; rfl)) rest ok.ending, ?_⟩
    intro f found
    rcases insertTriggers_mem _ _ found with before | ⟨_, rfl⟩
    · exact ok.safe _ before
    · exact .queue _

private def combatObservationFrame : Frame → Bool
  | .showdown .. | .endShowdown .. | .combatResolve .. | .combatResult ..
  | .combatControl .. | .combatFinish .. => true
  | _ => false

private theorem CycleStack.noCombat {stack : List Frame} (ok : CycleStack stack) :
    ∀ f ∈ stack, combatObservationFrame f = false := by
  intro f member
  have safe := ok.safe f member
  cases safe <;> rfl

private theorem observeCombat_idle (s : GameState) (stack : List Frame)
    (quiet : ∀ f ∈ stack, combatObservationFrame f = false) :
    s.observeCombat stack = (s.combat, []) := by
  unfold GameState.observeCombat
  cases active : s.combat with
  | some c =>
    have none : stack.any (fun
        | .showdown bf .. | .endShowdown bf | .combatResolve bf _ | .combatResult bf |
          .combatControl bf | .combatFinish bf => bf == c.battlefield
        | _ => false) = false := by
      apply List.any_eq_false.mpr
      intro f member
      have silent := quiet f member
      cases f <;> simp [combatObservationFrame] at silent ⊢
    dsimp only
    rw (config := { transparency := .all }) [none]
    simp only [Bool.false_eq_true, ↓reduceIte]
  | none =>
    have none : stack.findSome? (fun
      | .showdown bf p _ => some (bf, p)
      | _ => none) = none := by
      apply List.findSome?_eq_none_iff.mpr
      intro f member
      have silent := quiet f member
      cases f <;> simp [combatObservationFrame] at silent ⊢
    dsimp only
    rw (config := { transparency := .all }) [none]

private theorem fightingAt_idle (s : GameState) (stack : List Frame)
    (quiet : ∀ f ∈ stack, combatObservationFrame f = false) (field : ObjId) :
    ({ s with pending := stack } : GameState).fightingAt field =
      s.combat.any (fun c => c.battlefield == field) := by
  have none : stack.any (fun
      | .showdown bf .. | .endShowdown bf => bf == field
      | _ => false) = false := by
    apply List.any_eq_false.mpr
    intro f member
    have silent := quiet f member
    cases f <;> simp [combatObservationFrame] at silent ⊢
  change (s.combat.any (fun c => c.battlefield == field) || stack.any (fun
      | .showdown bf .. | .endShowdown bf => bf == field
      | _ => false)) = s.combat.any (fun c => c.battlefield == field)
  rw [none, Bool.or_false]

private theorem expiration_cleanupMeasure (s : GameState) (pending : List Frame)
    (combat : ∀ field, ({ s.mapObjects endTurnObj with pending, pools := {}, turnFx := [] } : GameState).fightingAt field =
      s.fightingAt field) :
    let t := { s.mapObjects endTurnObj with pending, pools := {}, turnFx := [] }
    t.cleanupMeasure = s.cleanupMeasure ∨ MeasLt t.cleanupMeasure s.cleanupMeasure := by
  intro t
  have config : t.config = s.config := rfl
  have cards : t.cards = s.cards := rfl
  have zone : t.zone = s.zone := rfl
  have board : t.inPlay = s.inPlay := rfl
  have lookup (id : ObjId) : t.obj? id = (s.obj? id).map endTurnObj := GameState.obj?_mapObjects ..
  have prints : t.printedCardDef? = s.printedCardDef? := by
    funext id
    unfold GameState.printedCardDef?
    rw [lookup, cards]
    cases s.obj? id <;> rfl
  have unit : t.isUnit = s.isUnit := by
    funext id
    unfold GameState.isUnit
    rw [prints, lookup]
    cases s.obj? id <;> rfl
  have fields : t.battlefields = s.battlefields := by
    simp only [GameState.battlefields, GameState.isBattlefield, zone, prints]
  have tok : t.isTok = s.isTok := by
    funext id
    unfold GameState.isTok
    rw [lookup]
    cases s.obj? id <;> rfl
  have loose : t.looseP = s.looseP := by
    funext id
    unfold GameState.looseP
    rw [lookup, board]
    cases s.obj? id <;> rfl
  have atField : t.unitsAt = s.unitsAt := by
    funext field
    unfold GameState.unitsAt
    rw [zone]
    apply List.filter_congr
    intro id _
    unfold GameState.isAt
    rw [unit, lookup]
    cases s.obj? id <;> rfl
  have controller (id : ObjId) : (t.obj? id).map Object.controller = (s.obj? id).map Object.controller := by
    rw [lookup]
    cases s.obj? id <;> rfl
  have players : t.unitsOf = s.unitsOf := by
    funext p field
    simp only [GameState.unitsOf, GameState.isControlledBy, atField, controller]
  have control : t.controlOf = s.controlOf := by
    funext id
    unfold GameState.controlOf
    rw [lookup]
    cases s.obj? id <;> rfl
  have contest (id : ObjId) : (t.obj? id).bind Object.contested = (s.obj? id).bind Object.contested := by
    rw [lookup]
    cases s.obj? id <;> rfl
  have healed : t.dmgC = 0 := by
    unfold GameState.dmgC
    apply List.countP_eq_zero.mpr
    intro id _
    rw [lookup]
    cases s.obj? id <;> simp [endTurnObj, healObj]
  have fighting : ∀ field, t.fightingAt field = s.fightingAt field := combat
  have sameMeasure :
      t.cleanupMeasure = (s.pot, s.tokC, s.cLoose, s.cLost, s.cStale, s.cNew) := by
    unfold GameState.cleanupMeasure GameState.cLoose GameState.cLost GameState.cStale GameState.cNew
    have pot : t.pot = s.pot := rfl
    have tokens : t.tokC = s.tokC := by
      simp only [GameState.tokC, GameState.nbZones, GameState.playerCount, config, zone, tok]
    simp only [GameState.lostControl, GameState.staleContest, GameState.newContest, pot, tokens,
      healed, Nat.add_zero, fields, loose, board, control, contest, players, fighting, atField, controller]
  rw [sameMeasure]
  by_cases damage : s.dmgC = 0
  · left
    simp [GameState.cleanupMeasure, damage]
  · right
    exact MeasLt.at2 rfl (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero damage))

private theorem ordinary_filter (keep : Frame → Bool) (ignores : ∀ q, keep (.triggers q) = false)
    (state : GameState) (triggers : List PendTrigger) (rest : List Frame) :
    (ordinaryTriggerContinuation state triggers rest).filter keep = rest.filter keep := by
  unfold ordinaryTriggerContinuation
  dsimp only
  split
  · rfl
  · exact insertTriggers_filter keep ignores _ rest

private theorem ordinary_head {state : GameState} {triggers : List PendTrigger} {rest : List Frame}
    {head : Frame} (notTrigger : ∀ q, head ≠ .triggers q)
    (found : (ordinaryTriggerContinuation state triggers rest).head? = some head) :
    rest.head? = some head := by
  unfold ordinaryTriggerContinuation at found
  dsimp only at found
  split at found
  · exact found
  · exact insertTriggers_head notTrigger found

private theorem CycleStack.sameMeasure {s t : GameState} (old : CycleStack s.pending)
    (next : CycleStack t.pending)
    (config : t.config = s.config) (cards : t.cards = s.cards) (objects : t.objects = s.objects)
    (zones : t.zones = s.zones) (combat : t.combat = s.combat) :
    t.cleanupMeasure = s.cleanupMeasure := by
  apply cleanupMeasure_eq config cards objects zones
  intro field
  have oldFight := fightingAt_idle s s.pending old.noCombat field
  have newFight := fightingAt_idle t t.pending next.noCombat field
  have eta (state : GameState) : { state with pending := state.pending } = state := by cases state; rfl
  rw [eta s] at oldFight
  rw [eta t] at newFight
  rw [oldFight, newFight, combat]

private theorem resolve_cycle_observation (raw : GameState) (notices : List Event)
    (wf : raw.WF) (database : MightRead.database raw.cards) (allowed : CycleStack raw.pending) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.WF ∧ t.cards = raw.cards ∧ CycleStack t.pending ∧
      (inExpirationWork t →
        (inExpirationWork raw ∧ t.cleanupMeasure = raw.cleanupMeasure ∧
          t.pending.countP isExpiration = raw.pending.countP isExpiration ∧
          t.pending.countP Frame.isCleanup = raw.pending.countP Frame.isCleanup)) := by
  rcases withTriggers_cases raw notices with ⟨winner, finished, _⟩ | unchanged | ⟨queue, woven, _⟩
  · let done := raw.withTriggers notices
    have stop : done.pending = [] := congrArg GameState.pending finished
    refine ⟨done, 0, [], by intro fuel past; simp [done], withTriggers_wf notices wf, withTriggers_cards raw _,
      stop ▸ CycleStack.empty, by simp [inExpirationWork, stop]⟩
  · let next := raw.withTriggers notices
    have projected := congrArg GameState.pending unchanged
    have stack : next.pending = raw.pending := projected
    have measure : next.cleanupMeasure = raw.cleanupMeasure := by
      change (raw.withTriggers notices).cleanupMeasure = _
      rw [unchanged]
      exact allowed.sameMeasure allowed rfl rfl rfl rfl rfl
    refine ⟨next, 0, [], by intro fuel past; simp [next], withTriggers_wf notices wf, withTriggers_cards raw _,
      stack ▸ allowed, ?_⟩
    intro inside
    exact ⟨by simpa only [inExpirationWork, stack] using inside, measure,
      congrArg (List.countP isExpiration) stack, congrArg (List.countP Frame.isCleanup) stack⟩
  · let ready := raw.recordTurnEvents notices
    let continuation := ordinaryTriggerContinuation ready queue raw.pending
    have keeps : CycleStack continuation := CycleStack.ordinary queue allowed
    obtain ⟨board, used, events, path, wellFormed, cards, measure⟩ :=
      advance_insertDetectedTriggers_adds_measured ready queue raw.pending
        (wf.congr rfl rfl rfl rfl) database
    let next := { board with pending := continuation }
    have rawMeasure : ({ ready with pending := continuation } : GameState).cleanupMeasure = raw.cleanupMeasure :=
      allowed.sameMeasure keeps rfl rfl rfl rfl rfl
    refine ⟨next, used, events, by rw [woven]; exact path, wellFormed.congr rfl rfl rfl rfl,
      cards, keeps, ?_⟩
    intro inside
    refine ⟨?_, (measure continuation).trans rawMeasure, ?_, ?_⟩
    · rcases inside with clean | expire
      · exact Or.inl (ordinary_head (fun q h => by cases h) clean)
      · exact Or.inr (ordinary_head (fun q h => by cases h) expire)
    · change continuation.countP isExpiration = _
      rw [List.countP_eq_length_filter, ordinary_filter isExpiration (fun _ => rfl), ← List.countP_eq_length_filter]
    · change continuation.countP Frame.isCleanup = _
      rw [List.countP_eq_length_filter, ordinary_filter Frame.isCleanup (fun _ => rfl), ← List.countP_eq_length_filter]

private def expirationDirty (s : GameState) : Nat :=
  if (expirationFrames s).isEmpty then 0 else 1

/-- Compare Expiration count first, then board changes, then clearing turn state and consuming Cleanup. -/
private def EndingCycleLt (next before : GameState) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex MeasLt (Prod.Lex (· < ·) (· < ·)))
    (next.pending.countP isExpiration, next.cleanupMeasure, expirationDirty next,
      next.pending.countP Frame.isCleanup)
    (before.pending.countP isExpiration, before.cleanupMeasure, expirationDirty before,
      before.pending.countP Frame.isCleanup)

private theorem endingCycleLt_wf : WellFounded EndingCycleLt := by
  unfold EndingCycleLt
  exact InvImage.wf (fun s : GameState => (s.pending.countP isExpiration, s.cleanupMeasure, expirationDirty s,
    s.pending.countP Frame.isCleanup))
    ((Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ (Prod.lex ⟨_, MeasLt.wf⟩
      (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ ⟨_, Nat.lt_wfRel.wf⟩))).wf)

private theorem cleanup_cycle_routes (s : GameState) (rest : List Frame) (wf : s.WF)
    (pending : s.pending = .cleanup :: rest) (suffix : CycleStack rest) :
    let raw := cleanupFrame s rest
    CycleStack raw.1.pending ∧
      (¬inExpirationWork raw.1 ∨
        (raw.1.pending = .cleanup :: rest ∧ MeasLt raw.1.cleanupMeasure s.cleanupMeasure) ∨
        raw = ({ s with pending := rest }, [])) := by
  unfold cleanupFrame
  cases winner : s.winner with
  | some p => exact ⟨.empty, Or.inl (by simp [inExpirationWork])⟩
  | none =>
    cases decision : cleanupDeathBanishChoice s with
    | some answer =>
      obtain ⟨src, p, a, b⟩ := answer
      exact ⟨suffix.cleanup.push (.stop (.decision rfl)) (.choice ..) (by intro h; cases h),
        Or.inl (by simp [inExpirationWork])⟩
    | none =>
      have keep (next : GameState) (safe : Safe s next) :
          { next with pending := .cleanup :: rest } = next := by
        have same := safe.same.pending.trans pending
        rw [← same]
      cases group : cleanupResolveDeathGroup s with
      | some r =>
        change CycleStack (.cleanup :: rest) ∧
          (¬inExpirationWork { r.1 with pending := .cleanup :: rest } ∨
            (.cleanup :: rest = .cleanup :: rest ∧
              MeasLt ({ r.1 with pending := .cleanup :: rest } : GameState).cleanupMeasure s.cleanupMeasure) ∨ _)
        exact ⟨suffix.cleanup, Or.inr (Or.inl ⟨rfl, by
          rw [keep r.1 (cleanupResolveDeathGroup_safe group)]
          exact cleanupResolveDeathGroup_decreases wf group⟩)⟩
      | none =>
        cases one : cleanupStep s with
        | some r =>
          obtain ⟨next, events⟩ := r
          have safe := cleanupStep_safe (s' := next) (es := events) one
          dsimp only
          exact ⟨suffix.cleanup, Or.inr (Or.inl ⟨rfl, by rw [keep next safe]; exact cleanupStep_lt wf one⟩)⟩
        | none =>
          have noOpening : s.showdownOpeningEvents rest = [] := by
            cases rest with
            | nil => rfl
            | cons first _ =>
              have silent := suffix.noCombat first (by simp)
              cases first <;> simp [combatObservationFrame, GameState.showdownOpeningEvents] at silent ⊢
          have idle : continueAfterCleanup s rest = ({ s with pending := rest }, []) := by
            unfold continueAfterCleanup
            rw [observeCombat_idle s rest suffix.noCombat, noOpening]
            simp
          exact ⟨by simpa only [suffix.noPriority (s := s), idle] using suffix,
            Or.inr (Or.inr (by simp only [suffix.noPriority (s := s), idle]))⟩

private theorem settled_cleanup_pending (s : GameState) (rest : List Frame) (wf : s.WF)
    (database : MightRead.database s.cards) (pending : s.pending = .cleanup :: rest) :
    let raw := { s with pending := rest }
    (raw.withTriggers (s.workTransitionEvents raw)).pending = rest := by
  intro raw
  have combat : raw.combatNow = s.combatNow := by
    unfold GameState.combatNow
    rw [pending]
    rfl
  have reads : SameMightReads s raw := (SameMightReads.refl s).replacePending rest combat
  have mighty : s.mightyEvents raw = [] :=
    mightyEvents_eq_nil_of_mightNow (fun _ member =>
      (reads.mightNow_eq wf database (old_inPlay wf member)).symm)
  have exhaust : s.exhaustionEvents raw none = [] := by
    have none : ((s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))).filter
        (fun id => (s.obj? id).any (fun o => !o.exhausted) && (s.obj? id).any (·.exhausted))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro id _
      cases found : s.obj? id <;> simp
    unfold GameState.exhaustionEvents
    have lookup : raw.obj? = s.obj? := rfl
    dsimp only
    rw [lookup, none]
    rfl
  simp only [GameState.workTransitionEvents, pending, exhaust, mighty, GameState.mightReductionEvents,
    List.nil_append]
  split
  · rw [withTriggers_nil]
  · rw [withTriggers_nil]
  · split
    · rw [linkedCleanup_withTriggers_recorded raw]
      rfl
    · rw [withTriggers_nil]
  · rw [withTriggers_nil]

private theorem advance_cycle_cleanup (s : GameState) (rest : List Frame) (wf : s.WF)
    (database : MightRead.database s.cards) (pending : s.pending = .cleanup :: rest)
    (shape : CycleStack s.pending) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.WF ∧ t.cards = s.cards ∧ CycleStack t.pending ∧
      (inExpirationWork t → EndingCycleLt t s) := by
  let raw := cleanupFrame s rest
  let notices := raw.2 ++ s.workTransitionEvents raw.1
  let observed := raw.1.withTriggers notices
  have step : workStep s = some (observed, raw.2) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some, raw, observed, notices]
  have suffix : CycleStack rest := (pending ▸ shape).tail
  have known := cleanupFrame_cards s rest
  obtain ⟨allowed, route | ⟨pendingSame, smaller⟩ | settled⟩ := cleanup_cycle_routes s rest wf pending suffix
  · obtain ⟨t, n, added, ran, nextWF, cards, nextShape, facts⟩ :=
      resolve_cycle_observation raw.1 notices (cleanupFrame_preservesBoard s rest wf).1 (known ▸ database) allowed
    exact ⟨t, n + 1, raw.2 ++ added, by omega, ran.prepend pending rfl step,
      nextWF, cards.trans known, nextShape, fun inside => False.elim (route (facts inside).1)⟩
  · obtain ⟨t, n, added, ran, nextWF, cards, nextShape, facts⟩ :=
      resolve_cycle_observation raw.1 notices (cleanupFrame_preservesBoard s rest wf).1 (known ▸ database) allowed
    refine ⟨t, n + 1, raw.2 ++ added, by omega, ran.prepend pending rfl step,
      nextWF, cards.trans known, nextShape, ?_⟩
    intro inside
    obtain ⟨_, measure, count, _⟩ := facts inside
    have sameCount : t.pending.countP isExpiration = s.pending.countP isExpiration := by rw [count, pendingSame, pending]
    unfold EndingCycleLt
    rw [sameCount, measure]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ smaller)
  · let simple := { s with pending := rest }
    have settledRaw : raw = (simple, []) := settled
    have stack : observed.pending = rest := by
      change (raw.1.withTriggers (raw.2 ++ s.workTransitionEvents raw.1)).pending = rest
      rw [settledRaw, List.nil_append]
      exact settled_cleanup_pending s rest wf database pending
    have finalShape : CycleStack observed.pending := stack ▸ suffix
    have same : observed.cleanupMeasure = s.cleanupMeasure := by
      obtain ⟨_, _, woven⟩ := withTriggers_pending raw.1 notices
      apply shape.sameMeasure finalShape <;> dsimp only [observed] <;> rw [woven, settledRaw] <;> rfl
    have nonincrease : expirationDirty observed ≤ expirationDirty s := by
      unfold expirationDirty
      split
      · omega
      · split
        · rename_i dirty clear
          have valid := (expiration_clear_iff s).mp (List.isEmpty_iff.mp clear)
          have clears := withTriggers_clear (s := raw.1) (events := notices)
            (by rw [settledRaw]; exact ⟨valid.facts, valid.pools, valid.objects⟩)
            (fun e found => by
              rcases List.mem_append.mp found with emitted | noticed
              · rw [settledRaw] at emitted
                contradiction
              · exact transitionEvents_neutral pending (Or.inl rfl) noticed)
          exact False.elim (dirty (List.isEmpty_iff.mpr ((expiration_clear_iff observed).mpr clears)))
        · omega
    have path : AdvancePrefix s observed 1 raw.2 := by
      have zero : AdvancePrefix observed observed 0 [] := by intro fuel past; simp
      simpa only [List.append_nil] using zero.prepend pending rfl step
    refine ⟨observed, 1, raw.2, by decide, path, workStep_wf wf step, (withTriggers_cards _ _).trans known,
      finalShape, ?_⟩
    intro _
    have expCount : observed.pending.countP isExpiration = s.pending.countP isExpiration := by
      rw [stack, pending]
      rw [List.countP_cons_of_neg (show ¬ isExpiration .cleanup = true from by decide)]
    have cleanCount : observed.pending.countP Frame.isCleanup < s.pending.countP Frame.isCleanup := by
      rw [stack, pending]
      rw [List.countP_cons_of_pos (show Frame.isCleanup .cleanup = true from rfl)]
      exact Nat.lt_succ_self _
    unfold EndingCycleLt
    rw [expCount, same]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right' _ nonincrease cleanCount))

private theorem advance_cycle_expire (s : GameState) (rest : List Frame) (wf : s.WF)
    (ordinaryMight : s.cards.mightTriggersAreOrdinary) (pending : s.pending = .expireTurn :: rest)
    (shape : CycleStack s.pending) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.WF ∧ t.cards = s.cards ∧ CycleStack t.pending ∧
      (inExpirationWork t → EndingCycleLt t s) := by
  let raw := { s.mapObjects endTurnObj with
    pending := expirationFrames s ++ rest, pools := {}, turnFx := [] }
  let detected := raw.detect (s.mightyEvents raw)
  let detects := raw.phase != .setup && raw.pending.all (fun f => !f.isSetup) && !detected.isEmpty
  let next := if detects then { raw with pending := insertTriggers detected raw.pending } else raw
  have step : workStep s = some (next, []) := workStep_expireTurn_mightOrdinary s rest pending ordinaryMight
  have suffix : CycleStack rest := (pending ▸ shape).tail
  have schedule : expirationFrames s = [] ∨ expirationFrames s = [.cleanup, .expireTurn] := by
    unfold expirationFrames
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have rawShape : CycleStack raw.pending := by
    change CycleStack (expirationFrames s ++ rest)
    rcases schedule with empty | renew
    · simpa only [empty, List.nil_append] using suffix
    · simpa only [renew, List.cons_append, List.nil_append] using suffix.expire.cleanup
  have clearRaw : ExpirationClear raw := expiration_reset_clear s _
  have properties : CycleStack next.pending ∧ next.cards = s.cards ∧
      expirationFrames next = [] ∧ next.cleanupMeasure = raw.cleanupMeasure ∧
      next.pending.countP isExpiration = raw.pending.countP isExpiration := by
    unfold next
    split
    · rename_i observes
      have nonempty : detected ≠ [] := by
        intro empty
        simp [detects, empty] at observes
      have inserted : CycleStack (insertTriggers detected raw.pending) := by
        refine ⟨insertTriggers_ending detected nonempty raw.pending rawShape.ending, ?_⟩
        intro f member
        rcases insertTriggers_mem _ _ member with before | ⟨_, rfl⟩
        · exact rawShape.safe _ before
        · exact .queue _
      refine ⟨inserted, rfl, (expiration_clear_iff _).mpr ⟨clearRaw.facts, clearRaw.pools, clearRaw.objects⟩,
        rawShape.sameMeasure inserted rfl rfl rfl rfl rfl, ?_⟩
      change (insertTriggers detected raw.pending).countP isExpiration = _
      rw [List.countP_eq_length_filter, insertTriggers_filter isExpiration (fun _ => rfl), ← List.countP_eq_length_filter]
    · exact ⟨rawShape, rfl, (expiration_clear_iff _).mpr clearRaw, rfl, rfl⟩
  obtain ⟨nextShape, cards, clear, measure, count⟩ := properties
  have path : AdvancePrefix s next 1 [] := by
    have zero : AdvancePrefix next next 0 [] := by intro fuel past; simp
    exact zero.prepend pending rfl step
  refine ⟨next, 1, [], by decide, path, workStep_wf wf step, cards, nextShape, ?_⟩
  intro _
  have rawCount : raw.pending.countP isExpiration =
      (expirationFrames s ++ rest).countP isExpiration := rfl
  unfold EndingCycleLt
  rw [count, rawCount, pending]
  rcases schedule with empty | renew
  · rw [empty, List.nil_append, List.countP_cons_of_pos (show isExpiration .expireTurn = true from rfl)]
    exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
  · have sameCount : ([Frame.cleanup, Frame.expireTurn] ++ rest).countP isExpiration =
        (Frame.expireTurn :: rest).countP isExpiration :=
      List.countP_cons_of_neg (show ¬ isExpiration .cleanup = true from by decide)
    rw [renew, sameCount, measure]
    apply Prod.Lex.right
    have fights (field : ObjId) : raw.fightingAt field = s.fightingAt field := by
      have oldFight := fightingAt_idle s s.pending shape.noCombat field
      have newFight := fightingAt_idle raw raw.pending rawShape.noCombat field
      have eta (state : GameState) : { state with pending := state.pending } = state := by cases state; rfl
      rw [eta s] at oldFight
      rw [eta raw] at newFight
      exact newFight.trans oldFight.symm
    rcases expiration_cleanupMeasure s raw.pending fights with same | less
    · change raw.cleanupMeasure = s.cleanupMeasure at same
      rw [same]
      exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [expirationDirty, clear, renew]))
    · exact Prod.Lex.left _ _ less

private theorem advance_cycle_run (s : GameState) (wf : s.WF) (database : MightRead.database s.cards)
    (ordinaryMight : s.cards.mightTriggersAreOrdinary) (shape : CycleStack s.pending) :
    ∃ t used events, AdvancePrefix s t used events ∧ t.WF ∧
      t.cards = s.cards ∧ CycleStack t.pending ∧ ¬inExpirationWork t := by
  revert wf database ordinaryMight shape
  apply endingCycleLt_wf.induction s
  intro state ih wellFormed reads ordinary stack
  by_cases inside : inExpirationWork state
  · have stepBatch : ∃ next used events, 0 < used ∧ AdvancePrefix state next used events ∧
        next.WF ∧ next.cards = state.cards ∧ CycleStack next.pending ∧
        (inExpirationWork next → EndingCycleLt next state) := by
      cases frames : state.pending with
      | nil => simp [inExpirationWork, frames] at inside
      | cons first rest =>
        have kind : first = .cleanup ∨ first = .expireTurn := by
          simpa [inExpirationWork, frames] using inside
        rcases kind with rfl | rfl
        · exact advance_cycle_cleanup state rest wellFormed reads frames stack
        · exact advance_cycle_expire state rest wellFormed ordinary frames stack
    obtain ⟨next, used, events, _, path, nextWF, cards, nextShape, smaller⟩ := stepBatch
    by_cases again : inExpirationWork next
    · obtain ⟨t, later, emitted, run, lastWF, lastCards, lastShape, outside⟩ :=
        ih next (smaller again) nextWF (cards ▸ reads) (cards ▸ ordinary) nextShape
      exact ⟨t, used + later, events ++ emitted, path.append run, lastWF,
        lastCards.trans cards, lastShape, outside⟩
    · exact ⟨next, used, events, path, nextWF, cards, nextShape, again⟩
  · exact ⟨state, 0, [], by intro fuel past; simp, wellFormed, rfl, stack, inside⟩

private theorem EndingFrame.queue_nonempty {queue : List PendTrigger}
    (allowed : EndingFrame (.triggers queue)) : queue ≠ [] := by
  cases allowed with
  | queued _ nonempty => exact nonempty
  | stop boundary =>
    cases boundary with
    | decision decision => contradiction
    | immediateAdd _ _ add =>
      obtain ⟨_, _, _, _, impossible⟩ := PendTrigger.immediateAddFrame_run add
      contradiction

private theorem advance_turn_boundary_work (raw : GameState) (notices : List Event) (wf : raw.WF)
    (database : MightRead.database raw.cards) (ordinaryMight : raw.cards.mightTriggersAreOrdinary)
    (pending : raw.pending = [.cleanup, .expireTurn, .beginTurn]) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      (t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true ∨
        (t.pending = [.beginTurn] ∧ t.WF ∧ t.cards = raw.cards)) := by
  obtain ⟨mid, adds, added, runAdds, midWF, midCards, midShape, _⟩ :=
    resolve_cycle_observation raw notices wf database
      (pending.symm ▸ CycleStack.beginTurn.expire.cleanup)
  obtain ⟨t, later, events, run, lastWF, lastCards, shape, outside⟩ :=
    advance_cycle_run mid midWF (midCards ▸ database) (midCards ▸ ordinaryMight) midShape
  have initial := runAdds.append run
  have cards : t.cards = raw.cards := lastCards.trans midCards
  cases stack : t.pending with
  | nil => exact ⟨t, _, _, initial, Or.inl (GameState.prepared_idle_of_empty stack)⟩
  | cons first rest =>
    have frame := shape.safe first (stack ▸ List.mem_cons_self)
    cases frame with
    | cleanup => exact False.elim (outside (Or.inl (stack ▸ rfl)))
    | expire => exact False.elim (outside (Or.inr (stack ▸ rfl)))
    | turn =>
      have order := List.pairwise_cons.mp (stack ▸ shape.ending.turnLast rfl)
      cases rest with
      | nil => exact ⟨t, _, _, initial, Or.inr ⟨stack, lastWF, cards⟩⟩
      | cons f fs => exact False.elim (order.1 f List.mem_cons_self rfl)
    | choice =>
      have ready := GameState.prepared_idle_of_nonpriority (s := t)
        (by simp [stack, Frame.isWork]) (by intro p tail equal; rw [stack] at equal; cases equal)
      exact ⟨t, _, _, initial, Or.inl ready⟩
    | queue queued =>
      have nonempty := (shape.ending.allowed _ (stack ▸ List.mem_cons_self)).queue_nonempty
      obtain ⟨done, used, _, _, _, resolved, _, _, ready⟩ :=
        advance_triggers_to_preparedDecision t lastWF queued rest stack (cards ▸ database) (Or.inl nonempty)
      refine ⟨done, adds + later + used, _, initial.append resolved, ?_⟩
      exact Or.inl ready

/-- Ending resolves the immediate Adds detected at phase entry and during Cleanup, including
any Expiration passes their effects require. It reaches a player decision, an empty stack, or
the normal Begin Turn continuation. -/
theorem advance_ending_with_adds_prepared {s : GameState} (wf : s.WF) (database : MightRead.database s.cards)
    (ordinaryMight : s.cards.mightTriggersAreOrdinary) (pending : s.pending = [.phase .ending, .beginTurn]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true ∨
        (t.pending = [.beginTurn] ∧ t.WF ∧ t.cards = s.cards)) := by
  let raw := { s with phase := .ending, pending := [.cleanup, .expireTurn, .beginTurn] }
  let emitted := [Event.phaseStarted (s.active.getD ⟨0⟩) .ending]
  let notices := emitted ++ s.workTransitionEvents raw
  have step : workStep s = some (raw.withTriggers notices, emitted) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some, raw, emitted, notices]
  obtain ⟨t, used, events, path, next⟩ :=
    advance_turn_boundary_work raw notices (wf.congr rfl rfl rfl rfl) database ordinaryMight rfl
  exact ⟨t, used + 1, emitted ++ events, by omega, path.prepend pending rfl step, next⟩

/-- Finish Ending's automatic work, or reach the next turn. -/
theorem advance_ending_with_adds {s : GameState} (wf : s.WF) (database : MightRead.database s.cards)
    (ordinaryMight : s.cards.mightTriggersAreOrdinary) (pending : s.pending = [.phase .ending, .beginTurn]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true ∨
        (t.pending = [.beginTurn] ∧ t.WF ∧ t.cards = s.cards)) := by
  obtain ⟨t, used, events, positive, path, ready | continues⟩ :=
    advance_ending_with_adds_prepared wf database ordinaryMight pending
  · exact ⟨t, used, events, positive, path,
      Or.inl (by simpa only [GameState.preparePriority_of_idle ready] using ready)⟩
  · exact ⟨t, used, events, positive, path, Or.inr continues⟩

/-- From the Ending Phase, automatic work can finish, ask for a decision, reach the next turn's
Awaken stack, or enter an immediate Add that was scheduled by event observation. -/
inductive TurnBoundaryStop (s : GameState) : Prop where
  /-- The game has no further frames. -/
  | empty : s.pending = [] → TurnBoundaryStop s
  /-- The engine needs a player decision. -/
  | decision {frame : Frame} {rest : List Frame} :
      s.pending = frame :: rest → frame.isWork = false → TurnBoundaryStop s
  /-- The next turn has been initialized, including its active player and phase frames. -/
  | awaken (p : PlayerId) :
      s.pending = turnFrames p → s.active = some p → TurnBoundaryStop s
  /-- A triggered Add still needs to resolve. -/
  | immediateAdd {frame : Frame} {rest : List Frame} (observed : GameState) (trigger : PendTrigger) :
      s.pending = frame :: rest → trigger.immediateAddFrame observed = some frame → TurnBoundaryStop s

private theorem advance_beginTurn_to_awaken_checkpoint {s : GameState} (wf : s.WF)
    (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (pending : s.pending = [.beginTurn]) :
    ∃ t used, AdvancePrefix s t used [] ∧
      (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨
        ∃ p, t.pending = turnFrames p ∧ t.active = some p ∧ t.WF ∧ t.cards = s.cards) := by
  cases clock : s.clockConclusion with
  | some result =>
    obtain ⟨finish, _⟩ := advance_beginTurn_clock wf database pending clock
    exact ⟨_, 1, finish, Or.inl rfl⟩
  | none =>
    obtain ⟨t, elapsed, _, start, wellFormed, boundary⟩ :=
      advance_beginTurn_prepared_checkpoint wf database ordinaryMight pending clock
    refine ⟨t, elapsed, start, ?_⟩
    rcases boundary with awakened | choice
    · exact Or.inr ⟨_, by simpa only [List.append_nil] using awakened.1,
        awakened.2.1, wellFormed, awakened.2.2.2⟩
    · exact Or.inl choice.2

private theorem advance_ending_to_awaken_checkpoint {s : GameState} (wf : s.WF) (database : MightRead.database s.cards)
    (ordinaryMight : s.cards.mightTriggersAreOrdinary) (pending : s.pending = [.phase .ending, .beginTurn]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨
        ∃ p, t.pending = turnFrames p ∧ t.active = some p ∧ t.WF ∧ t.cards = s.cards) := by
  obtain ⟨mid, used, events, positive, path, stop | ⟨normal, midWF, cards⟩⟩ :=
    advance_ending_with_adds_prepared wf database ordinaryMight pending
  · exact ⟨mid, used, events, positive, path, Or.inl stop⟩
  · obtain ⟨t, elapsed, start, boundary⟩ :=
      advance_beginTurn_to_awaken_checkpoint midWF (cards ▸ database) (cards ▸ ordinaryMight) normal
    refine ⟨t, used + elapsed, events, by omega, by simpa using path.append start, ?_⟩
    rcases boundary with stop | ⟨p, stack, active, tWF, tCards⟩
    · exact Or.inl stop
    · exact Or.inr ⟨p, stack, active, tWF, tCards.trans cards⟩

/-- Follow the real Ending Phase across the normal turn boundary. After resolving Ending's
immediate Adds, the engine processes the clock and any ordinary triggers before Awaken. -/
theorem advance_ending_to_awaken {s : GameState} (wf : s.WF) (database : MightRead.database s.cards)
    (ordinaryMight : s.cards.mightTriggersAreOrdinary) (pending : s.pending = [.phase .ending, .beginTurn]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ TurnBoundaryStop t := by
  obtain ⟨t, used, events, positive, path, stopped | ⟨p, awakened, active, _, _⟩⟩ :=
    advance_ending_to_awaken_checkpoint wf database ordinaryMight pending
  · refine ⟨t, used, events, positive, path, ?_⟩
    have unchanged := GameState.preparePriority_of_idle stopped
    cases stack : t.pending with
    | nil => exact .empty stack
    | cons f rest => exact .decision stack (by simpa [unchanged, stack] using stopped)
  · exact ⟨t, used, events, positive, path, .awaken p awakened active⟩

/-- An observed Ending and Awaken prefix can stop at a decision, at the Beginning stack, or
at an immediate Add scheduled earlier in Ending. -/
inductive AwakenWorkStop (cards : CardDB) (s : GameState) : Prop where
  /-- The game has finished or is waiting for an answer. -/
  | stopped : s.pending.head?.all (fun frame => !frame.isWork) = true → AwakenWorkStop cards s
  /-- Beginning is next, with the rest of the turn's frames and the original card database. -/
  | beginning (p : PlayerId) :
      s.pending = (turnFrames p).drop 1 → s.WF → s.cards = cards → AwakenWorkStop cards s
  /-- An immediate Add scheduled during Ending must resolve before the new turn. -/
  | immediateAdd {frame : Frame} {rest : List Frame} (observed : GameState) (trigger : PendTrigger) :
      s.pending = frame :: rest → trigger.immediateAddFrame observed = some frame → AwakenWorkStop cards s

private theorem advance_awaken_to_beginning_checkpoint {s : GameState} {p : PlayerId} (wf : s.WF)
    (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary) (pending : s.pending = turnFrames p) :
    ∃ t used events, AdvancePrefix s t used events ∧
      (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨
        (t.pending = (turnFrames p).drop 1 ∧ t.WF ∧ t.cards = s.cards)) := by
  obtain ⟨t, used, events, _, work, after⟩ :=
    advance_awaken_prepared wf database ordinaryMight ordinaryAwaken pending
  refine ⟨t, used, events, work, ?_⟩
  rcases after with next | ⟨_, _, _, _, ready⟩
  · exact Or.inr next
  · exact Or.inl ready

private theorem advance_ending_through_awaken_checkpoint {s : GameState} (wf : s.WF)
    (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary) (pending : s.pending = [.phase .ending, .beginTurn]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨
        ∃ p, t.pending = (turnFrames p).drop 1 ∧ t.WF ∧ t.cards = s.cards) := by
  obtain ⟨mid, used, events, positive, path, stop | ⟨p, stack, _, midWF, cards⟩⟩ :=
    advance_ending_to_awaken_checkpoint wf database ordinaryMight pending
  · exact ⟨mid, used, events, positive, path, Or.inl stop⟩
  · obtain ⟨t, elapsed, later, awake, after⟩ :=
      advance_awaken_to_beginning_checkpoint midWF (cards ▸ database) (cards ▸ ordinaryMight)
        (cards ▸ ordinaryAwaken) stack
    refine ⟨t, used + elapsed, events ++ later, by omega, path.append awake, ?_⟩
    rcases after with done | ⟨continues, wellFormed, preserved⟩
    · exact Or.inl done
    · exact Or.inr ⟨p, continues, wellFormed, preserved.trans cards⟩

/-- Follow Ending and Awaken to Beginning or an earlier player decision or the end of the stack. -/
theorem advance_ending_through_awaken {s : GameState} (wf : s.WF) (database : MightRead.database s.cards)
    (ordinaryMight : s.cards.mightTriggersAreOrdinary) (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary)
    (pending : s.pending = [.phase .ending, .beginTurn]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ AwakenWorkStop s.cards t := by
  obtain ⟨t, used, events, positive, path, stop | ⟨p, beginning, tWF, cards⟩⟩ :=
    advance_ending_through_awaken_checkpoint wf database ordinaryMight ordinaryAwaken pending
  · exact ⟨t, used, events, positive, path, .stopped (by simpa only [GameState.preparePriority_of_idle stop] using stop)⟩
  · exact ⟨t, used, events, positive, path, .beginning p beginning tWF cards⟩

/-- The standard turn transition from Ending reaches a prepared decision in finite fuel. -/
theorem advance_ending_to_preparedDecision {s : GameState} (wf : s.WF) (database : MightRead.database s.cards)
    (ordinaryMight : s.cards.mightTriggersAreOrdinary) (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary)
    (pending : s.pending = [.phase .ending, .beginTurn]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      advance used s [] = .ok (t, events) := by
  obtain ⟨t, used, events, positive, path, ready | ⟨p, beginning, tWF, cards⟩⟩ :=
    advance_ending_through_awaken_checkpoint wf database ordinaryMight ordinaryAwaken pending
  · exact ⟨t, used, events, positive, path, ready,
      by simpa only [List.nil_append] using path.finish ready []⟩
  · obtain ⟨u, later, emitted, _, rest, ready, _⟩ :=
      advance_beginning_to_preparedDecision tWF (cards ▸ database) beginning
    have turn := path.append rest
    exact ⟨u, used + later, events ++ emitted, by omega, turn, ready,
      by simpa only [List.nil_append] using turn.finish ready []⟩

/-- The standard automatic turn transition ends at a decision or the end of the game. -/
theorem advance_ending_to_decision {s : GameState} (wf : s.WF) (database : MightRead.database s.cards)
    (ordinaryMight : s.cards.mightTriggersAreOrdinary) (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary)
    (pending : s.pending = [.phase .ending, .beginTurn]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨t, used, events, positive, path, ready, _⟩ :=
    advance_ending_to_preparedDecision wf database ordinaryMight ordinaryAwaken pending
  exact ⟨t, used, events, positive, path,
    by simpa only [GameState.preparePriority_of_idle ready] using ready⟩

/-- Begin the new turn and run Awaken. If the clock or an ordinary trigger stops the
dispatcher before Beginning, the work already done suffices for a successful advance. -/
theorem advance_beginTurn_through_awaken {s : GameState} (wf : s.WF)
    (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary) (pending : s.pending = [.beginTurn]) :
    ∃ t used events, AdvancePrefix s t used events ∧
      ((t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
          advance used s [] = .ok (t, events)) ∨
        ∃ p, t.pending = (turnFrames p).drop 1 ∧ t.WF ∧ t.cards = s.cards) := by
  obtain ⟨start, elapsed, beginWork, boundary⟩ :=
    advance_beginTurn_to_awaken_checkpoint wf database ordinaryMight pending
  rcases boundary with stop | ⟨p, stack, _, startWF, startCards⟩
  · exact ⟨start, elapsed, [], beginWork, Or.inl ⟨stop, beginWork.finish stop []⟩⟩
  obtain ⟨awake, more, emitted, awakenWork, after⟩ :=
    advance_awaken_to_beginning_checkpoint startWF (startCards ▸ database) (startCards ▸ ordinaryMight)
      (startCards ▸ ordinaryAwaken) stack
  have awakePath : AdvancePrefix s awake (elapsed + more) emitted := by
    simpa only [List.nil_append] using beginWork.append awakenWork
  rcases after with done | ⟨continues, awakeWF, awakeCards⟩
  · exact ⟨awake, elapsed + more, emitted, awakePath,
      Or.inl ⟨done, by simpa only [List.nil_append] using awakePath.finish done []⟩⟩
  · exact ⟨awake, elapsed + more, emitted, awakePath,
      Or.inr ⟨p, continues, awakeWF, awakeCards.trans startCards⟩⟩

/-- Begin a turn directly, including the opening turn after the last Mulligan. The actual
dispatcher returns a prepared decision or an empty stack with finite fuel. -/
theorem advance_beginTurn_to_preparedDecision {s : GameState} (wf : s.WF)
    (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary) (pending : s.pending = [.beginTurn]) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      advance used s [] = .ok (t, events) := by
  obtain ⟨t, used, events, work, ⟨ready, done⟩ | ⟨p, begins, tWF, cards⟩⟩ :=
    advance_beginTurn_through_awaken wf database ordinaryMight ordinaryAwaken pending
  · exact ⟨t, used, events, work, ready, done⟩
  obtain ⟨u, later, emitted, _, next, ready, _⟩ :=
    advance_beginning_to_preparedDecision tWF (cards ▸ database) begins
  have turn := work.append next
  exact ⟨u, used + later, events ++ emitted, turn, ready,
    by simpa only [List.nil_append] using turn.finish ready []⟩

/-- Begin a turn directly, including the opening turn after the last Mulligan. The actual
dispatcher reaches a decision continuation or the empty stack. -/
theorem advance_beginTurn_to_decision {s : GameState} (wf : s.WF)
    (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary) (pending : s.pending = [.beginTurn]) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨t, used, events, path, ready, _⟩ :=
    advance_beginTurn_to_preparedDecision wf database ordinaryMight ordinaryAwaken pending
  exact ⟨t, used, events, path, by simpa only [GameState.preparePriority_of_idle ready] using ready⟩

/-- Resume the observed turn boundary directly at Cleanup and Expiration, as when the turn
player concedes in War. The clock and all phases of the next turn use the same dispatcher. -/
theorem advance_observed_turn_boundary_to_preparedDecision (raw : GameState) (notices : List Event) (wf : raw.WF)
    (database : MightRead.database raw.cards) (ordinaryMight : raw.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : raw.cards.awakenTriggersAreOrdinary)
    (pending : raw.pending = [.cleanup, .expireTurn, .beginTurn]) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨mid, used, events, work, ready | ⟨begin, midWF, cards⟩⟩ :=
    advance_turn_boundary_work raw notices wf database ordinaryMight pending
  · exact ⟨mid, used, events, work, ready⟩
  obtain ⟨t, more, later, next, ready, _⟩ :=
    advance_beginTurn_to_preparedDecision midWF (cards ▸ database) (cards ▸ ordinaryMight)
      (cards ▸ ordinaryAwaken) begin
  exact ⟨t, used + more, events ++ later, work.append next, ready⟩

/-- Follow the observed Cleanup, Expiration and new turn to a decision. -/
theorem advance_observed_turn_boundary_to_decision (raw : GameState) (notices : List Event) (wf : raw.WF)
    (database : MightRead.database raw.cards) (ordinaryMight : raw.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : raw.cards.awakenTriggersAreOrdinary)
    (pending : raw.pending = [.cleanup, .expireTurn, .beginTurn]) :
    ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨t, used, events, path, ready⟩ :=
    advance_observed_turn_boundary_to_preparedDecision raw notices wf database ordinaryMight ordinaryAwaken pending
  exact ⟨t, used, events, path, by simpa only [GameState.preparePriority_of_idle ready] using ready⟩

private theorem priorityPass_reads {s : GameState} {p : PlayerId} {rest : List Frame}
    (before : s.pending = .priority p :: rest) :
    SameMightReads s (({ s with pending := .phase .ending :: .beginTurn :: rest }).setPool p (s.poolOf p)) := by
  have combat : (({ s with pending := .phase .ending :: .beginTurn :: rest }).setPool p (s.poolOf p)).combatNow =
      s.combatNow := by
    unfold GameState.combatNow
    simp only [GameState.setPool, before, List.findSome?_cons]
    rfl
  have pools : (({ s with pending := .phase .ending :: .beginTurn :: rest }).setPool p (s.poolOf p)).poolOf =
      s.poolOf := by
    funext q
    by_cases who : q = p
    · subst q
      exact GameState.poolOf_setPool_self _ _ _
    · exact GameState.poolOf_setPool_ne _ who _
  exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, combat, rfl,
    rfl, rfl, (by intro q; rw [pools]), rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

private theorem priorityPass_observations {s : GameState} {p : PlayerId} {rest : List Frame}
    (wf : s.WF) (database : MightRead.database s.cards) (pending : s.pending = .priority p :: rest) :
    let next := ({ s with pending := .phase .ending :: .beginTurn :: rest }).setPool p (s.poolOf p)
    s.actionTransitionEvents next ⟨.player p, .pass⟩ = [] := by
  intro next
  have reads : SameMightReads s next := priorityPass_reads pending
  have exhausted : s.exhaustionEvents next (some p) = [] := by
    have empty : ((s.inPlay ++ s.players.flatMap (fun q => s.zone (.player q .legendZone))).filter
        (fun id => (s.obj? id).any (fun o => !o.exhausted) && (s.obj? id).any (·.exhausted))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro id _
      cases lookup : s.obj? id <;> simp
    unfold GameState.exhaustionEvents
    dsimp only
    have sameObjects : next.obj? = s.obj? := rfl
    rw [sameObjects, empty]
    rfl
  have mighty : s.mightyEvents next = [] :=
    mightyEvents_eq_nil_of_mightNow (fun _ onBoard => (reads.mightNow_eq wf database (old_inPlay wf onBoard)).symm)
  have reduction : s.mightReductionEvents next (some p) = [] := by
    simp only [GameState.mightReductionEvents]
    split
    · apply List.filterMap_eq_nil_iff.mpr
      intro id member
      have old : id.n < s.nextId := old_inPlay wf (show id ∈ s.inPlay from member)
      split
      · rfl
      · rw [reads.mightNow_eq wf database old]
        cases s.mightNow id <;> simp
    · rfl
  simp only [GameState.actionTransitionEvents, pending, exhausted, mighty, reduction, List.nil_append]

/-- Passing at ordinary priority enters the Ending Phase and schedules the next turn without
creating an event observation along the way. -/
theorem applyDeclaredAction_priorityPass {s : GameState} {p : PlayerId} {rest : List Frame}
    (wf : s.WF) (database : MightRead.database s.cards) (pending : s.pending = .priority p :: rest) :
    applyDeclaredAction s ⟨.player p, .pass⟩ =
      some (({ s with pending := .phase .ending :: .beginTurn :: rest }).setPool p (s.poolOf p), []) := by
  unfold applyDeclaredAction
  simp only [GameState.actionDeathCostChoice, pending, GameState.actionKillCosts,
    GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  unfold applyAction applyFrame applyFrame0
  simp only [pending]
  let next := ({ s with pending := .phase .ending :: .beginTurn :: rest }).setPool p (s.poolOf p)
  have events : s.actionTransitionEvents next ⟨.player p, .pass⟩ = [] := priorityPass_observations wf database pending
  simp [extraEvents, GameState.paySurcharge, GameState.paidDeflectPool, GameState.deflectInPayment,
    Action.targetsOf, Action.spellSource,
    GameState.deflectCost, RunePool.takeN, RunePool.recordDeflectDebit, GameState.poolOf]
  change next.withTriggers (s.actionTransitionEvents next ⟨.player p, .pass⟩) = next
  rw [events, withTriggers_nil]

private theorem priority_pass_prefix {s initial t : GameState} {p : PlayerId} {used : Nat}
    {events : List Event} (legal : Legal s ⟨.player p, .pass⟩)
    (applyPass : applyDeclaredAction s ⟨.player p, .pass⟩ = some (initial, []))
    (path : AdvancePrefix initial t used events) :
    (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  constructor
  · intro fuel
    simp only [step, ite_eq_left legal, applyPass]
    simpa only [List.nil_append] using path fuel []
  · intro boundary
    simp only [step, ite_eq_left legal, applyPass]
    simpa only [List.nil_append] using path.finish boundary []

/-- Starting from the normal single priority frame, the player's Pass reaches the next Ending
boundary, even when Cleanup queues ordinary triggers before the next turn. The remaining fuel
continues from that boundary with all the events emitted so far. If there is no further automatic
work before a decision, the steps used are sufficient for a successful `step` result. -/
theorem step_priority_pass_ending {s : GameState} {p : PlayerId}
    (wf : s.WF) (database : MightRead.database s.cards) (pending : s.pending = [.priority p])
    (legal : Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ EndingWorkStop t.pending.head? ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  let initial := ({ s with pending := [.phase .ending, .beginTurn] }).setPool p (s.poolOf p)
  have applyPass : applyDeclaredAction s ⟨.player p, .pass⟩ = some (initial, []) :=
    applyDeclaredAction_priorityPass wf database pending
  obtain ⟨t, used, events, positive, path, stop⟩ :=
    advance_ending_through_triggers (s := initial) (wf.congr rfl rfl rfl rfl) database rfl (by
      intro f member
      obtain rfl := List.mem_singleton.mp member
      exact .beginTurn)
  exact ⟨t, used, events, positive, stop, priority_pass_prefix legal applyPass path⟩

/-- The normal Pass resolves all immediate Adds during Ending and performs any required
Cleanup and Expiration before the next decision or Begin Turn. -/
theorem step_priority_pass_ending_with_adds {s : GameState} {p : PlayerId}
    (wf : s.WF) (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (pending : s.pending = [.priority p]) (legal : Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true ∨ t.pending = [.beginTurn]) ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  let initial := ({ s with pending := [.phase .ending, .beginTurn] }).setPool p (s.poolOf p)
  have applyPass : applyDeclaredAction s ⟨.player p, .pass⟩ = some (initial, []) :=
    applyDeclaredAction_priorityPass wf database pending
  obtain ⟨t, used, events, positive, path, boundary | ⟨normal, _, _⟩⟩ :=
    advance_ending_with_adds (s := initial) (wf.congr rfl rfl rfl rfl) database ordinaryMight rfl
  · exact ⟨t, used, events, positive, Or.inl boundary, priority_pass_prefix legal applyPass path⟩
  · exact ⟨t, used, events, positive, Or.inr normal, priority_pass_prefix legal applyPass path⟩

/-- The ordinary Pass advances through the turn boundary when Ending reaches it. The remaining
fuel resumes at Awaken or at the work or decision introduced before it. -/
theorem step_priority_pass_to_awaken {s : GameState} {p : PlayerId}
    (wf : s.WF) (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (pending : s.pending = [.priority p]) (legal : Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ TurnBoundaryStop t ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  let initial := ({ s with pending := [.phase .ending, .beginTurn] }).setPool p (s.poolOf p)
  have applyPass : applyDeclaredAction s ⟨.player p, .pass⟩ = some (initial, []) :=
    applyDeclaredAction_priorityPass wf database pending
  obtain ⟨t, used, events, positive, path, stop⟩ :=
    advance_ending_to_awaken (s := initial) (wf.congr rfl rfl rfl rfl) database ordinaryMight rfl
  exact ⟨t, used, events, positive, stop, priority_pass_prefix legal applyPass path⟩

/-- A legal ordinary Pass proceeds through Ending and Awaken to Beginning or an earlier
decision or the end of the stack. The remaining fuel starts at the reached boundary. -/
theorem step_priority_pass_through_awaken {s : GameState} {p : PlayerId}
    (wf : s.WF) (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary)
    (pending : s.pending = [.priority p]) (legal : Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ AwakenWorkStop s.cards t ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  let initial := ({ s with pending := [.phase .ending, .beginTurn] }).setPool p (s.poolOf p)
  have applyPass : applyDeclaredAction s ⟨.player p, .pass⟩ = some (initial, []) :=
    applyDeclaredAction_priorityPass wf database pending
  obtain ⟨t, used, events, positive, path, stop⟩ :=
    advance_ending_through_awaken (s := initial) (wf.congr rfl rfl rfl rfl) database
      ordinaryMight ordinaryAwaken rfl
  exact ⟨t, used, events, positive, stop, priority_pass_prefix legal applyPass path⟩

/-- With ordinary Might and Awaken triggers, the standard Pass reaches the continuation
of the next prepared decision or game end with finite fuel. -/
theorem step_priority_pass_to_preparedDecision {s : GameState} {p : PlayerId}
    (wf : s.WF) (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary)
    (pending : s.pending = [.priority p]) (legal : Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ extra, step (used + extra) s ⟨.player p, .pass⟩ = advance extra t events) ∧
      step used s ⟨.player p, .pass⟩ = .ok (t, events) := by
  let initial := ({ s with pending := [.phase .ending, .beginTurn] }).setPool p (s.poolOf p)
  have applyPass : applyDeclaredAction s ⟨.player p, .pass⟩ = some (initial, []) :=
    applyDeclaredAction_priorityPass wf database pending
  obtain ⟨t, used, events, positive, path, ready, _⟩ :=
    advance_ending_to_preparedDecision (s := initial) (wf.congr rfl rfl rfl rfl) database
      ordinaryMight ordinaryAwaken rfl
  obtain ⟨run, finish⟩ := priority_pass_prefix legal applyPass path
  exact ⟨t, used, events, positive, ready, run, finish ready⟩

/-- A legal ordinary Pass has a finite prefix up to the next decision or the empty stack. -/
theorem step_priority_pass_to_decision {s : GameState} {p : PlayerId}
    (wf : s.WF) (database : MightRead.database s.cards) (ordinaryMight : s.cards.mightTriggersAreOrdinary)
    (ordinaryAwaken : s.cards.awakenTriggersAreOrdinary)
    (pending : s.pending = [.priority p]) (legal : Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .pass⟩ = advance extra t events := by
  obtain ⟨t, used, events, positive, ready, run, _⟩ :=
    step_priority_pass_to_preparedDecision wf database ordinaryMight ordinaryAwaken pending legal
  exact ⟨t, used, events, positive,
    by simpa only [GameState.preparePriority_of_idle ready] using ready, run⟩

end Riftbound

end
