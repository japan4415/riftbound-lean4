module

public import Riftbound.Invariant.RunWork

/-!
# Finite deferred Spell declarations (I12)

Funding and finalization either reach a decision, consume an instruction, or remove the
queued Spell and advance to the next item on the Chain.
-/

@[expose] public section

namespace Riftbound

/-- Limited Spell funding always includes cancellation as its last option. -/
private theorem fundLimitedOptions_last (s : GameState) (p : PlayerId) (card : ObjId)
    (plan : EffectSpellPlay) (adds : List EffectAdd) (policy : EffectAddPolicy) :
    ∃ earlier, fundLimitedOptions s p card plan adds policy =
      earlier ++ [.cancelLimitedSpell card] := by
  unfold fundLimitedOptions
  dsimp only
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨[], rfl⟩
  · exact ⟨[], rfl⟩

private theorem pendingSpell_mem {s : GameState} {card : ObjId} {play : PendingSpellPlay}
    (pending : s.pendingSpell card = some play) : card ∈ s.zone .chain := by
  unfold GameState.pendingSpell at pending
  split at pending
  · next member => exact List.contains_iff_mem.mp member
  · contradiction

/-- A successful cancellation removes its item from the Chain before scheduling the next item. -/
private theorem cancelLimitedStep_routes (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (card : ObjId) (more : EffectList) (wf : s.WF) :
    let result := cancelLimitedStep s p src env card more
    result = (s, [.run p src env more], []) ∨
      ((result.1.zone .chain).length < (s.zone .chain).length ∧
        result.2.1 = afterItem result.1 ++ [.run p src env more]) := by
  unfold cancelLimitedStep
  dsimp only
  cases pending : s.pendingSpell card with
  | none => exact Or.inl rfl
  | some play =>
    let index := play.preceding.countP (fun id => (s.zone play.origin).contains id)
    cases moved : moveObj s card play.origin (.atIndex index) with
    | none =>
      simp only [show moveObj s card play.origin (.atIndex (play.preceding.countP
        (fun id => (s.zone play.origin).contains id))) = none from moved, true_or]
    | some movedCard =>
      obtain ⟨t, restored⟩ := movedCard
      have member := pendingSpell_mem pending
      obtain ⟨source, dest, shape⟩ := moveObj_spec moved
      have locate := GameState.locate_eq wf (GameState.zone_valid_of_mem wf member) member
      have chainSource : source = .chain := Option.some.inj (shape.locate.symm.trans locate)
      have zone := shape.zone_src
      rw [chainSource] at zone
      have decreases : (t.zone .chain).length < (s.zone .chain).length := by
        rw [zone, List.length_erase_of_mem member]
        have nonempty := List.length_pos_of_mem member
        omega
      simp only [show moveObj s card play.origin (.atIndex (play.preceding.countP
        (fun id => (s.zone play.origin).contains id))) = some (t, restored) from moved]
      exact Or.inr ⟨decreases, trivial⟩

/-- A deferred declaration leaves a finite list of plans, consumes a missing item,
or cancels and removes an item before starting the next one. -/
private theorem finalizeLimitedStep_routes (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (card : ObjId) (more : EffectList) (wf : s.WF) :
    let result := finalizeLimitedStep s p src env card more effectAddPolicy
    result = (s, [.run p src env more], []) ∨
      (((result.1.zone .chain).length < (s.zone .chain).length) ∧
        result.2.1 = afterItem result.1 ++ [.run p src env more]) ∨
      ∃ plans : List (EffectSpellPlay × Bool), plans ≠ [] ∧
        result = (s, [.run p src env (.cons (.eitherOf (EffectList.ofList
          (plans.map (fun (plan, hasAdds) =>
            if hasAdds then Effect.fundLimitedSpell card plan [] else .finishLimitedSpell card plan [])))) more)], []) := by
  unfold finalizeLimitedStep
  dsimp only
  cases pending : s.pendingSpell card with
  | none => exact Or.inl rfl
  | some play =>
    cases plans : limitedSpellChoices s p card play.price effectAddPolicy with
    | nil =>
      rcases cancelLimitedStep_routes s p src env card more wf with resume | removed
      · exact Or.inl (by simpa only [plans] using resume)
      · exact Or.inr (Or.inl (by simpa only [plans] using removed))
    | cons first rest =>
      refine Or.inr (Or.inr ⟨first :: rest, List.cons_ne_nil _ _, ?_⟩)
      simp only [plans]

private def limitedPlans (card : ObjId) (plans : List (EffectSpellPlay × Bool)) : List Effect :=
  plans.map (fun (plan, hasAdds) =>
    if hasAdds then Effect.fundLimitedSpell card plan [] else .finishLimitedSpell card plan [])

private inductive LimitedInstruction : Nat → Effect → Prop where
  | finalize (card : ObjId) : LimitedInstruction 4 (.finalizeLimitedSpell card)
  | plans (card : ObjId) (plans : List (EffectSpellPlay × Bool)) :
      LimitedInstruction 3 (.eitherOf (EffectList.ofList (limitedPlans card plans)))
  | fund (card : ObjId) (plan : EffectSpellPlay) (adds : List EffectAdd) :
      LimitedInstruction 2 (.fundLimitedSpell card plan adds)
  | commit (card : ObjId) (plan : EffectSpellPlay) (adds : List EffectAdd) :
      LimitedInstruction 2 (.finishLimitedSpell card plan adds)
  | funding (card : ObjId) (others : List Effect) :
      LimitedInstruction 1 (.eitherOf (EffectList.ofList (others ++ [.cancelLimitedSpell card])))
  | cancel (card : ObjId) : LimitedInstruction 0 (.cancelLimitedSpell card)

/-- Cancellation decreases the Chain length. Without cancellation, each automatic
instruction advances to a lower stage within the same declaration. -/
private def limitedRank (s : GameState) (height : Nat) : Nat :=
  5 * (s.zone .chain).length + height

private inductive LimitedRoute (s : GameState) (height : Nat) (p : PlayerId)
    (src : ObjId) (env : Env) (rest : List Frame) (raw : GameState) : Prop where
  | decision : NonNeutralDecision raw.pending →
      LimitedRoute s height p src env rest raw
  | resume : raw.pending = .run p src env .nil :: rest →
      LimitedRoute s height p src env rest raw
  | next (nextHeight : Nat) (effect : Effect) (q : PlayerId) (card : ObjId) (live : Env)
      (tail : List Frame) :
      raw.pending = .run q card live (.cons effect .nil) :: tail →
      LimitedInstruction nextHeight effect →
      (tail = rest ∨ tail = .run p src env .nil :: rest) →
      limitedRank raw nextHeight < limitedRank s height →
      LimitedRoute s height p src env rest raw

private theorem limited_cancel_route {s raw : GameState} {height : Nat} {p : PlayerId}
    {src : ObjId} {env : Env} {rest : List Frame}
    (shorter : (raw.zone .chain).length < (s.zone .chain).length)
    (stack : raw.pending = afterItem raw ++ (.run p src env .nil :: rest)) :
    LimitedRoute s height p src env rest raw := by
  cases opened : (raw.zone .chain).head? with
  | none => exact .resume (by simpa only [afterItem, opened, List.nil_append] using stack)
  | some card =>
    by_cases deferred : (raw.pendingSpell card).isSome = true
    · let controller := ((raw.obj? card).map (·.controller)).getD (raw.active.getD ⟨0⟩)
      refine .next 4 (.finalizeLimitedSpell card) controller card {} (.run p src env .nil :: rest)
        ?_ (.finalize card) (Or.inr rfl) (by unfold limitedRank; omega)
      simpa only [afterItem, opened, deferred, ite_true, List.cons_append, List.nil_append, controller] using stack
    · have passes : raw.pending = .chainPass raw.chainPrioritySeat 0 :: .run p src env .nil :: rest := by
        simpa only [afterItem, opened, ite_eq_right deferred, List.cons_append, List.nil_append] using stack
      exact .decision (by rw [passes]; rfl)

private theorem limited_cancel_result {s : GameState} {p : PlayerId} {src card : ObjId}
    {env : Env} {rest : List Frame} (height : Nat) (wf : s.WF) :
    let result := cancelLimitedStep s p src env card .nil
    LimitedRoute s height p src env rest { result.1 with pending := result.2.1 ++ rest } := by
  let result := cancelLimitedStep s p src env card .nil
  change LimitedRoute s height p src env rest { result.1 with pending := result.2.1 ++ rest }
  rcases cancelLimitedStep_routes s p src env card .nil wf with resume | ⟨shrinks, ready⟩
  · change result = _ at resume
    rw [resume]
    exact .resume rfl
  · refine limited_cancel_route shrinks ?_
    have sameItem : afterItem { result.1 with pending := result.2.1 ++ rest } = afterItem result.1 := rfl
    change result.2.1 ++ rest = afterItem { result.1 with pending := result.2.1 ++ rest } ++ _
    rw [sameItem]
    change result.2.1 = _ at ready
    rw [ready, List.append_assoc]
    rfl

private theorem limited_offer_route (s : GameState) (p : PlayerId) (src : ObjId)
    (env : Env) (rest : List Frame) (options : List Effect) (height : Nat)
    (single : ∀ instruction, options = [instruction] →
      ∃ lower, LimitedInstruction lower instruction ∧ lower < height) :
    let result := runEffect s p src env (.eitherOf (EffectList.ofList options)) .nil effectAddPolicy
    LimitedRoute s height p src env rest { result.1 with pending := result.2.1 ++ rest } := by
  cases options with
  | nil => exact .resume rfl
  | cons first remaining =>
    cases remaining with
    | nil =>
      obtain ⟨lower, stage, smaller⟩ := single first rfl
      exact .next lower first p src env rest rfl stage (Or.inl rfl) (by
        change 5 * (s.zone .chain).length + lower < 5 * (s.zone .chain).length + height
        omega)
    | cons second tail =>
      cases tail <;> exact .decision rfl

private theorem limited_route (s : GameState) (p : PlayerId) (src : ObjId)
    (env : Env) (rest : List Frame) {height : Nat} {effect : Effect}
    (stage : LimitedInstruction height effect) (wf : s.WF) :
    let result := runEffect s p src env effect .nil effectAddPolicy
    LimitedRoute s height p src env rest { result.1 with pending := result.2.1 ++ rest } := by
  cases stage with
  | cancel card => exact limited_cancel_result 0 wf
  | finalize card =>
    let result := finalizeLimitedStep s p src env card .nil effectAddPolicy
    change LimitedRoute s 4 p src env rest { result.1 with pending := result.2.1 ++ rest }
    rcases finalizeLimitedStep_routes s p src env card .nil wf with resume | ⟨shrinks, ready⟩ | ⟨plans, _, begins⟩
    · change result = _ at resume
      rw [resume]
      exact .resume rfl
    · refine limited_cancel_route shrinks ?_
      have sameItem : afterItem { result.1 with pending := result.2.1 ++ rest } = afterItem result.1 := rfl
      change result.2.1 ++ rest = afterItem { result.1 with pending := result.2.1 ++ rest } ++ _
      rw [sameItem]
      change result.2.1 = _ at ready
      rw [ready, List.append_assoc]
      rfl
    · change result = _ at begins
      rw [begins]
      exact .next 3 _ p src env rest rfl (.plans card plans) (Or.inl rfl)
        (by change 5 * (s.zone .chain).length + 3 < 5 * (s.zone .chain).length + 4; omega)
  | plans card plans =>
    apply limited_offer_route
    intro instruction exactlyOne
    cases plans with
    | nil => contradiction
    | cons head rest =>
      obtain ⟨plan, hasAdds⟩ := head
      have first := (List.cons.inj exactlyOne).1
      cases hasAdds with
      | true => exact ⟨2, first ▸ LimitedInstruction.fund card plan [], by decide⟩
      | false => exact ⟨2, first ▸ LimitedInstruction.commit card plan [], by decide⟩
  | fund card plan adds =>
    obtain ⟨others, offered⟩ := fundLimitedOptions_last s p card plan adds effectAddPolicy
    let next := EffectList.cons (.eitherOf (EffectList.ofList (fundLimitedOptions s p card plan adds effectAddPolicy))) .nil
    change LimitedRoute s 2 p src env rest { s with pending := Frame.run p src env next :: rest }
    dsimp only [next]
    rw [offered]
    exact .next 1 _ p src env rest rfl (.funding card others) (Or.inl rfl)
      (by change 5 * (s.zone .chain).length + 1 < 5 * (s.zone .chain).length + 2; omega)
  | funding card others =>
    apply limited_offer_route
    intro instruction exactlyOne
    cases others with
    | nil =>
      have only := List.mem_singleton.mp (show Effect.cancelLimitedSpell card ∈ [instruction] by
        rw [← exactlyOne]; exact List.mem_singleton_self _)
      exact ⟨0, only ▸ LimitedInstruction.cancel card, by decide⟩
    | cons first rest =>
      have length := congrArg List.length exactlyOne
      simp only [List.length_append, List.length_cons, List.length_nil] at length
      omega
  | commit card plan adds =>
    simp only [runEffect, Effect.pickSel?, runEffect1]
    cases replacement : (s.playDeathCost card plan.targets plan.pick).bind
        (fun unit => s.deathReplacementChoice unit) with
    | some details =>
      obtain ⟨_, _, _, _⟩ := details
      exact .decision rfl
    | none =>
      cases paid : commitLimitedSpell s p card plan adds effectAddPolicy with
      | some result => exact .decision rfl
      | none => exact limited_cancel_result 2 wf

private def LimitedTail (keeps : List Frame → Prop) (stack : List Frame) : Prop :=
  ∃ owed : List Frame, (∀ f ∈ owed, f.FiniteRun) ∧ ResolutionPrefix owed keeps stack

private theorem LimitedTail.prepend {keeps : List Frame → Prop} {stack : List Frame}
    (tracked : LimitedTail keeps stack) (p : PlayerId) (src : ObjId) (env : Env) :
    LimitedTail keeps (.run p src env .nil :: stack) := by
  obtain ⟨owed, finite, tail, rfl, kept⟩ := tracked
  refine ⟨.run p src env .nil :: owed, ?_, tail, rfl, kept⟩
  intro f found
  rcases List.mem_cons.mp found with rfl | earlier
  · exact ⟨p, src, env, .nil, rfl, .nil⟩
  · exact finite f earlier

private theorem LimitedTail.insert {keeps : List Frame → Prop} {stack : List Frame}
    (tracked : LimitedTail keeps stack) (q : List PendTrigger) (ne : q ≠ [])
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    LimitedTail keeps (insertTriggers q stack) := by
  obtain ⟨frames, finite, waiting⟩ := tracked
  exact ⟨frames, finite, waiting.insert (fun f member => (finite f member).isResolution) inserted q ne⟩

private theorem LimitedTail.advance {s : GameState} {keeps : List Frame → Prop}
    (tracked : LimitedTail keeps s.pending) (wf : s.WF) (reads : MightRead.database s.cards)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  obtain ⟨frames, finite, waiting⟩ := tracked
  exact advance_run_frames wf reads waiting finite inserted

private theorem advance_limited_work (keeps : List Frame → Prop)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail))
    (s : GameState) (height : Nat) (effect : Effect) (p : PlayerId) (src : ObjId) (env : Env)
    (rest : List Frame) (wf : s.WF) (reads : MightRead.database s.cards)
    (stage : LimitedInstruction height effect) (pending : s.pending = .run p src env (.cons effect .nil) :: rest)
    (kept : LimitedTail keeps rest) : AdvanceTo s keeps := by
  let live := env.withMight s.mightTable
  let result := runEffect s p src live effect .nil effectAddPolicy
  let raw := { result.1 with pending := result.2.1 ++ rest }
  have rule : microStep0 s = some (raw, result.2.2) := by simp only [microStep0, pending, live, raw, result]
  have known : raw.cards = s.cards := by
    have db := congrArg GameState.cards (runEffect_safe s p src live effect .nil effectAddPolicy).same
    exact db
  obtain ⟨mid, used, events, _, path, midWF, cards, observation, zones⟩ :=
    advance_rule_with_adds_geometry pending rfl rule (microStep_wf0 wf rule) known reads
  have midReads : MightRead.database mid.cards := cards ▸ reads
  have emptyStop (stack : mid.pending = []) : AdvanceTo s keeps :=
    ⟨mid, used, events, path, Or.inl (GameState.prepared_idle_of_empty stack)⟩
  have thenFrom (reached : AdvanceTo mid keeps) : AdvanceTo s keeps := by
    obtain ⟨t, later, more, done, outcome⟩ := reached
    exact ⟨t, used + later, events ++ more, path.append done,
      outcome.imp_right (fun ⟨tail, tWF, tCards⟩ => ⟨tail, tWF, tCards.trans cards⟩)⟩
  have route : LimitedRoute s height p src live rest raw := limited_route s p src live rest stage wf
  cases route with
  | decision ready =>
    obtain ⟨t, elapsed, run, stop⟩ := advance_observed_nonNeutralDecision mid raw.pending midWF midReads observation ready
    exact ⟨t, used + elapsed, events, by simpa only [List.append_nil] using path.append run, Or.inl stop⟩
  | resume ready =>
    rw [ready] at observation
    have restored := kept.prepend p src live
    generalize stack : mid.pending = observed at observation
    cases observation with
    | empty => exact emptyStop stack
    | resume => exact thenFrom ((stack.symm ▸ restored).advance midWF midReads inserted)
    | queue q ne => exact thenFrom ((stack.symm ▸ restored.insert q ne inserted).advance midWF midReads inserted)
  | next nextHeight nextEffect nextPlayer item nextEnv tail ready nextStage tailShape smaller =>
    have tracked : LimitedTail keeps tail := by
      rcases tailShape with rfl | rfl
      · exact kept
      · exact kept.prepend p src live
    have midRank : limitedRank mid nextHeight = limitedRank raw nextHeight := by
      unfold limitedRank GameState.zone
      rw [zones]
    have decreases : limitedRank mid nextHeight < limitedRank s height := midRank ▸ smaller
    rw [ready] at observation
    generalize stack : mid.pending = observed at observation
    cases observation with
    | empty => exact emptyStop stack
    | resume =>
      exact thenFrom (advance_limited_work keeps inserted mid nextHeight nextEffect nextPlayer item
        nextEnv tail midWF midReads nextStage stack tracked)
    | queue q ne =>
      exact thenFrom (advance_limited_work keeps inserted mid nextHeight nextEffect nextPlayer item
        nextEnv (insertTriggers q tail) midWF midReads nextStage stack (tracked.insert q ne inserted))
termination_by limitedRank s height

/-- Run a queued Spell declaration, including consecutive cancellations, until a decision or
the tracked continuation. Ordinary triggers stay in dispatcher order. -/
theorem advance_limited_finalization {s : GameState} {p : PlayerId} {src card : ObjId} {env : Env}
    {rest : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons (.finalizeLimitedSpell card) .nil) :: rest)
    (keeps : List Frame → Prop) (base : keeps rest)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps :=
  advance_limited_work keeps inserted s 4 (.finalizeLimitedSpell card) p src env rest wf reads
    (.finalize card) pending ⟨[], by simp, rest, rfl, base⟩

/-- Finalize deferred declarations, retaining the original continuation if no new decision opens. -/
theorem advance_limited_until_decision {s : GameState} {p : PlayerId} {src card : ObjId} {env : Env}
    {rest original : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons (.finalizeLimitedSpell card) .nil) :: rest)
    (queued : TriggerWorkTail original rest)
    (front : ∀ f, original.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q) :
    AdvanceTo s (· = original) :=
  (advance_limited_finalization wf reads pending (TriggerWorkTail original) queued
    (fun _ tail q ne => tail.insert front q ne)).then reads
      (fun _ safe known tail => advance_trigger_tail_until_decision safe known tail)

/-- A deferred declaration above a decision stack reaches a decision or ends the game. -/
theorem advance_limited_to_decision {s : GameState} {p : PlayerId} {src card : ObjId} {env : Env}
    {rest original : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons (.finalizeLimitedSpell card) .nil) :: rest)
    (queued : TriggerWorkTail original rest)
    (front : ∀ f, original.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : original.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true :=
  (advance_limited_until_decision wf reads pending queued front).atDecision decision

end Riftbound

end
