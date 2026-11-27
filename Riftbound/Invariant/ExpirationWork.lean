module

public import Riftbound.Invariant.CleanupWork
public import Riftbound.Invariant.TriggerWork

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

private theorem cleanupFrame_cards (s : GameState) (rest : List Frame) :
    (cleanupFrame s rest).1.cards = s.cards := by
  rcases cleanupFrame_cases s rest with
    ⟨_, eq⟩ | ⟨_, _, _, _, eq⟩ | ⟨_, safe, eq⟩ | ⟨_, _, eq⟩ | ⟨_, _, _, eq⟩ | eq <;>
    rw [eq] <;> try rfl
  have metadata := safe.same
  unfold SameMeta at metadata
  have projected := congrArg GameState.cards metadata
  exact projected

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

private theorem insertTriggers_ending (queue : List PendTrigger) (nonempty : queue ≠ [])
    (stack : List Frame) (allowed : ∀ f ∈ stack, EndingFrame f) :
    ∀ f ∈ insertTriggers queue stack, EndingFrame f := by
  induction stack with
  | nil =>
    intro f member
    obtain rfl := List.mem_singleton.mp member
    exact .queued _ nonempty
  | cons head rest ih =>
    have oldRest (f) (member : f ∈ rest) := allowed f (List.mem_cons_of_mem _ member)
    intro f member
    unfold insertTriggers at member
    split at member
    · rcases List.mem_cons.mp member with eq | later
      · exact allowed f (List.mem_cons.mpr (Or.inl eq))
      · exact ih oldRest f later
    · split at member
      · rcases List.mem_cons.mp member with rfl | later
        · exact .queued _ (fun h => nonempty (List.append_eq_nil_iff.mp h).2)
        · exact oldRest f later
      · rcases List.mem_cons.mp member with rfl | later
        · exact .queued _ nonempty
        · exact allowed f later

private theorem insertDetectedTriggers_ending (s : GameState) (queue : List PendTrigger)
    (stack : List Frame) (allowed : ∀ f ∈ stack, EndingFrame f) :
    ∀ f ∈ insertDetectedTriggers s queue stack, EndingFrame f := by
  intro f member
  unfold insertDetectedTriggers at member
  dsimp only at member
  rcases List.mem_append.mp member with add | ordinary
  · obtain ⟨⟨_, _⟩, found, eq⟩ := List.mem_filterMap.mp add
    obtain ⟨trigger, _, candidateEq⟩ := List.mem_map.mp found
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj candidateEq
    exact .stop (.immediateAdd s trigger eq)
  · split at ordinary
    · exact allowed f ordinary
    · rename_i scheduled
      refine insertTriggers_ending _ ?_ stack allowed f ordinary
      intro empty
      rw [empty] at scheduled
      exact scheduled rfl

private theorem withTriggers_ending (s : GameState) (events : List Event)
    (allowed : ∀ f ∈ s.pending, EndingFrame f) : ∀ f ∈ (s.withTriggers events).pending, EndingFrame f := by
  rcases withTriggers_cases s events with ⟨_, eq, _⟩ | eq | ⟨queue, eq, _⟩
  · rw [eq]
    intro _ impossible
    contradiction
  · rw [eq]
    exact allowed
  · rw [eq]
    exact insertDetectedTriggers_ending _ queue _ allowed

private theorem ending_cons {f : Frame} {rest : List Frame} (top : EndingFrame f)
    (later : ∀ task ∈ rest, EndingFrame task) : ∀ task ∈ f :: rest, EndingFrame task := by
  intro task member
  rcases List.mem_cons.mp member with rfl | inRest
  · exact top
  · exact later _ inRest

private theorem cleanupFrame_ending (s : GameState) (rest : List Frame)
    (allowed : ∀ f ∈ rest, EndingFrame f) : ∀ f ∈ (cleanupFrame s rest).1.pending, EndingFrame f := by
  rcases cleanupFrame_cases s rest with ⟨_, eq⟩ | ⟨_, _, _, _, eq⟩ | ⟨_, _, eq⟩ | ⟨_, _, eq⟩ | ⟨_, _, _, eq⟩ | eq <;>
    rw [eq]
  · intro _ member; contradiction
  · exact ending_cons (.stop (.decision rfl)) (ending_cons .cleanup allowed)
  · exact ending_cons .cleanup allowed
  · exact ending_cons (.stop (.decision rfl)) (ending_cons .cleanup allowed)
  · exact ending_cons (.stop (.decision rfl)) allowed
  · exact allowed

private theorem expirationStep_ending {s t : GameState} {events : List Event}
    (tracked : inExpirationWork s) (step : workStep s = some (t, events))
    (allowed : ∀ f ∈ s.pending, EndingFrame f) : ∀ f ∈ t.pending, EndingFrame f := by
  cases stack : s.pending with
  | nil => simp [inExpirationWork, stack] at tracked
  | cons head rest =>
    have kind : head = .cleanup ∨ head = .expireTurn := by simpa [inExpirationWork, stack] using tracked
    have restAllowed (f) (member : f ∈ rest) : EndingFrame f :=
      allowed f (stack ▸ List.mem_cons_of_mem head member)
    rcases kind with rfl | rfl
    · simp only [workStep, stack, microStep, microStep0, Option.map_some] at step
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj step).symm
      exact withTriggers_ending _ _ (cleanupFrame_ending _ _ restAllowed)
    · simp only [workStep, stack, microStep, microStep0, Option.map_some] at step
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj step).symm
      apply withTriggers_ending
      change ∀ f ∈ expirationFrames s ++ rest, EndingFrame f
      unfold expirationFrames
      split
      · exact ending_cons .cleanup (ending_cons .expire restAllowed)
      · exact restAllowed

private theorem advance_expiration_checkpoint {s : GameState} (wf : s.WF) (pending : inExpirationWork s) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ t.WF ∧ t.cards = s.cards ∧
      ¬inExpirationWork t ∧
      ((∀ f ∈ s.pending, EndingFrame f) → ∀ f ∈ t.pending, EndingFrame f) := by
  refine expirationWorkLt_wf.induction s (C := fun state => state.WF → inExpirationWork state →
    ∃ t used events, 0 < used ∧ AdvancePrefix state t used events ∧ t.WF ∧ t.cards = state.cards ∧
      ¬inExpirationWork t ∧
      ((∀ f ∈ state.pending, EndingFrame f) → ∀ f ∈ t.pending, EndingFrame f)) ?_ wf pending
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
  have allowed := expirationStep_ending front step
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
  obtain ⟨t, used, events, positive, path, _, _, outside, _⟩ := advance_expiration_checkpoint wf pending
  exact ⟨t, used, events, positive, path, fun same => outside (Or.inl same), fun same => outside (Or.inr same)⟩

private theorem advance_ending_checkpoint {s : GameState} {rest : List Frame} (wf : s.WF)
    (pending : s.pending = .phase .ending :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ t.WF ∧ t.cards = s.cards ∧
      ¬inExpirationWork t ∧ ((∀ f ∈ rest, EndingFrame f) → ∀ f ∈ t.pending, EndingFrame f) := by
  let raw := { s with phase := .ending, pending := .cleanup :: .expireTurn :: rest }
  let emitted := [Event.phaseStarted (s.active.getD ⟨0⟩) .ending]
  let next := raw.withTriggers (emitted ++ s.workTransitionEvents raw)
  have step : workStep s = some (next, emitted) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some, raw, next, emitted]
  have nextWF := workStep_wf wf step
  have nextCards : next.cards = s.cards := withTriggers_cards raw _
  have allowed (tail : ∀ f ∈ rest, EndingFrame f) : ∀ f ∈ next.pending, EndingFrame f :=
    withTriggers_ending _ _ (ending_cons .cleanup (ending_cons .expire tail))
  by_cases inside : inExpirationWork next
  · obtain ⟨t, used, later, _, run, lastWF, lastCards, outside, keep⟩ :=
      advance_expiration_checkpoint nextWF inside
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
  obtain ⟨t, used, events, positive, path, _, _, outside, _⟩ := advance_ending_checkpoint wf pending
  exact ⟨t, used, events, positive, path, fun same => outside (Or.inl same), fun same => outside (Or.inr same)⟩

/-- The actual Ending Phase runs its Cleanup and Expiration steps and any leading ordinary
trigger queue. A nonempty queue reaches a player decision; other routes are the next turn,
the end of the stack, a decision reached during Cleanup, or a witnessed triggered Add. -/
theorem advance_ending_through_triggers {s : GameState} {rest : List Frame} (wf : s.WF)
    (database : MightRead.database s.cards) (pending : s.pending = .phase .ending :: rest)
    (continuation : ∀ f ∈ rest, EndingWorkStop (some f)) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ EndingWorkStop t.pending.head? := by
  obtain ⟨mid, elapsed, events, positive, path, midWF, cards, outside, keep⟩ :=
    advance_ending_checkpoint wf pending
  cases stack : mid.pending with
  | nil => exact ⟨mid, elapsed, events, positive, path, by rw [stack]; exact .empty⟩
  | cons first later =>
    have allowed := keep (fun f member => .stop (continuation f member)) first
      (stack ▸ List.mem_cons_self)
    cases allowed with
    | cleanup => exact False.elim (outside (Or.inl (stack ▸ rfl)))
    | expire => exact False.elim (outside (Or.inr (stack ▸ rfl)))
    | stop stop => exact ⟨mid, elapsed, events, positive, path, by rw [stack]; exact stop⟩
    | queued queue nonempty =>
      obtain ⟨t, used, f, tail, _, observed, done, decision⟩ :=
        advance_triggers_to_decision mid midWF queue later stack (cards ▸ database) (Or.inl nonempty)
      exact ⟨t, elapsed + used, events, by omega, by simpa using path.append observed,
        by rw [done]; exact .decision decision⟩

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
    rfl, rfl, pools, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

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
  simp [extraEvents, GameState.paySurcharge, GameState.deflectInPayment, Action.targetsOf, Action.spellSource,
    GameState.deflectCost, RunePool.takeN, GameState.poolOf]
  change next.withTriggers (s.actionTransitionEvents next ⟨.player p, .pass⟩) = next
  rw [events, withTriggers_nil]

/-- Starting from the normal single priority frame, the player's Pass reaches the next Ending
boundary, even when Cleanup queues ordinary triggers before the next turn. The remaining fuel
continues from that boundary with all the events emitted so far. If there is no further automatic
work before a decision, the steps used are sufficient for a successful `step` result. -/
theorem step_priority_pass_ending {s : GameState} {p : PlayerId}
    (wf : s.WF) (database : MightRead.database s.cards) (pending : s.pending = [.priority p])
    (legal : Legal s ⟨.player p, .pass⟩) :
    ∃ t used events, 0 < used ∧ EndingWorkStop t.pending.head? ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  let initial := ({ s with pending := [.phase .ending, .beginTurn] }).setPool p (s.poolOf p)
  have applyPass : applyDeclaredAction s ⟨.player p, .pass⟩ = some (initial, []) :=
    applyDeclaredAction_priorityPass wf database pending
  obtain ⟨t, used, events, positive, path, stop⟩ :=
    advance_ending_through_triggers (s := initial) (wf.congr rfl rfl rfl rfl) database rfl (by
      intro f member
      obtain rfl := List.mem_singleton.mp member
      exact .beginTurn)
  refine ⟨t, used, events, positive, stop, ?_, ?_⟩
  · intro fuel
    simp only [step, ite_eq_left legal, applyPass]
    simpa only [List.nil_append] using path fuel []
  · intro boundary
    simp only [step, ite_eq_left legal, applyPass]
    simpa only [List.nil_append] using path.finish boundary []

end Riftbound

end
