module

public import Riftbound.Invariant.ObservedCleanupWork
public import Riftbound.Invariant.Priority
public import Riftbound.Invariant.LimitedSpellWork

/-!
# Observed Chain resolution work (I12)
-/

@[expose] public section

namespace Riftbound

/-- After the final Chain pass the engine schedules the newest item's Run frames before Finish.
Observer-introduced immediate Adds resolve without consuming those frames. -/
theorem advance_resolve_chain_with_adds {s : GameState} {item : ObjId} {older : List ObjId}
    {rest : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .resolveChain :: rest) (chain : s.zone .chain = item :: older) :
    ∃ body t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.WF ∧ t.cards = s.cards ∧
      (∀ f ∈ body, ∃ p src env effects, f = .run p src env effects) ∧
      ObservedWorkStack (body ++ (Frame.finishSpell item :: rest)) t.pending := by
  obtain ⟨body, step, runs⟩ := microStep0_resolveNewest pending chain
  obtain ⟨t, used, events, positive, path, afterWF, cards, route⟩ :=
    advance_rule_with_adds pending rfl step (microStep_wf0 wf step) rfl reads
  exact ⟨body, t, used, events, positive, path, afterWF, cards, runs, route⟩

/-- Finish the Chain item and all immediate Adds that leaving the Chain observed. -/
theorem advance_finish_chain_item_with_adds {s : GameState} {item : ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .finishSpell item :: rest) :
    let result := finishItem s item
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.WF ∧ t.cards = s.cards ∧
      ObservedWorkStack (finishedItemFrames result.1 ++ rest) t.pending := by
  let result := finishItem s item
  let raw := { result.1 with pending := finishedItemFrames result.1 ++ rest }
  have step : microStep0 s = some (raw, result.2) := by
    simp only [microStep0, pending, raw, result]
  have known : raw.cards = s.cards := by
    have cards := congrArg GameState.cards (finishItem_sameMeta s item)
    exact cards
  exact advance_rule_with_adds pending rfl step (microStep_wf0 wf step) known reads

/-- After a final legal Chain pass, run its first work step and resolve observed immediate Adds
before the item's Run frames. -/
theorem step_chainPass_last_with_adds {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    {item : ObjId} {older : List ObjId}
    (wf : s.WF) (reads : MightRead.database s.cards) (ongoing : s.result = none)
    (pending : s.pending = .chainPass p passes :: rest) (last : s.participatingCount ≤ passes + 1)
    (chain : s.zone .chain = item :: older) :
    ∃ body t used events, 0 < used ∧ t.WF ∧ t.cards = s.cards ∧
      (∀ f ∈ body, ∃ player src env effects, f = .run player src env effects) ∧
      ObservedWorkStack (body ++ (Frame.finishSpell item :: rest)) t.pending ∧
      ∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events := by
  let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
  obtain ⟨body, t, used, events, positive, path, wellFormed, cards, runs, route⟩ :=
    advance_resolve_chain_with_adds (s := initial) (wf.congr rfl rfl rfl rfl) reads rfl chain
  refine ⟨body, t, used, events, positive, wellFormed, cards, runs, route, fun fuel => ?_⟩
  rw [step_chainPass_last _ ongoing pending last]
  simpa only [List.nil_append] using path fuel []

/-- Remove the Chain item, run Cleanup, and keep the continuation with any ordinary triggers
observed along the way. -/
theorem advance_finished_item_until {s : GameState} {item : ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .finishSpell item :: rest)
    (keeps : List Frame → Prop) (base : keeps (afterItem (finishItem s item).1 ++ rest))
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  let next := afterItem (finishItem s item).1 ++ rest
  let result := finishItem s item
  let raw := { result.1 with pending := finishedItemFrames result.1 ++ rest }
  let cleanupContinuation := ResolutionPrefix [.cleanup] keeps
  have step : microStep0 s = some (raw, result.2) := by simp only [microStep0, pending, raw, result]
  have cards : raw.cards = s.cards := by
    have known := congrArg GameState.cards (finishItem_sameMeta s item)
    exact known
  have advanceCleanup {state : GameState} (stateWF : state.WF) (stateReads : MightRead.database state.cards)
      (reached : cleanupContinuation state.pending) : AdvanceTo state keeps := by
    obtain ⟨tail, stack, tracked⟩ := reached
    obtain ⟨t, used, events, _, path, stop⟩ :=
      advance_cleanup_with_adds_prepared stateWF stateReads stack keeps tracked inserted
    exact ⟨t, used, events, path,
      stop.imp_right (fun ⟨waiting, safe, known, _⟩ => ⟨waiting, safe, known⟩)⟩
  have insertCleanup : ∀ tail, cleanupContinuation tail → ∀ q, q ≠ [] →
      cleanupContinuation (insertTriggers q tail) :=
    fun _ tracked q ne => tracked.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) inserted q ne
  have rawWF := microStep_wf0 wf step
  have entered : AdvanceTo s cleanupContinuation :=
    .rule pending rfl step rawWF cards reads ⟨next, rfl, base⟩ insertCleanup
  exact entered.then reads (fun _ => advanceCleanup)

/-- Resolving the newest Chain item reaches a decision or an already queued limited Spell. -/
inductive ChainWorkEnd (s : GameState) : Prop where
  /-- The game is waiting for an answer, or has no remaining frames. -/
  | decision : s.pending.head?.all (fun frame => !frame.isWork) = true → ChainWorkEnd s
  /-- A Spell played by an effect is still waiting to finalize. -/
  | limited (p : PlayerId) (card : ObjId) (rest : List Frame) :
      s.pending = .run p card {} (.cons (.finalizeLimitedSpell card) .nil) :: rest → ChainWorkEnd s

/-- Finish an item and resolve deferred declarations before reaching the next decision. -/
theorem advance_finish_chain_to_decision {s : GameState} {item : ObjId}
    {rest original : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .finishSpell item :: rest) (tracks : TriggerWorkTail original rest)
    (front : ∀ f, original.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (waits : original.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix s t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  let finished := (finishItem s item).1
  have reaches (base : List Frame) (waiting : TriggerWorkTail base (afterItem finished ++ rest))
      (nonresolution : ∀ f, base.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
      (decision : base.head?.all (fun f => !f.isWork) = true) :
      ∃ t used events, AdvancePrefix s t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨mid, used, events, path, stop | ⟨queued, midWF, cards⟩⟩ :=
      advance_finished_item_until wf reads pending (TriggerWorkTail base) waiting
        (fun _ route q ne => route.insert nonresolution q ne)
    · exact ⟨mid, used, events, path, GameState.idle_of_prepared stop⟩
    · obtain ⟨t, elapsed, resolved, outcome⟩ := advance_trigger_tail mid base midWF (cards ▸ reads) queued
      refine ⟨t, used + elapsed, events, by simpa only [List.append_nil] using path.append resolved, ?_⟩
      rcases outcome with choice | ⟨resume, _, _⟩
      · exact choice
      · exact resume.symm ▸ decision
  cases nextCard : (finished.zone .chain).head? with
  | none =>
    apply reaches original _ front waits
    simpa only [afterItem, nextCard, List.nil_append] using tracks
  | some card =>
    by_cases deferred : (finished.pendingSpell card).isSome = true
    · let p := ((finished.obj? card).map (·.controller)).getD (finished.active.getD ⟨0⟩)
      let frame := Frame.run p card {} (.cons (.finalizeLimitedSpell card) .nil)
      let keeps := ResolutionPrefix [frame] (TriggerWorkTail original)
      have base : keeps (afterItem finished ++ rest) := by
        refine ⟨rest, ?_, tracks⟩
        simp only [afterItem, nextCard, deferred, ite_true, frame, p]
      obtain ⟨t, used, events, path, stop | ⟨⟨tail, stack, queued⟩, tWF, cards⟩⟩ :=
        advance_finished_item_until wf reads pending keeps base (fun _ route q ne => route.insert
          (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl)
          (fun _ waiting added ne' => waiting.insert front added ne') q ne)
      · exact ⟨t, used, events, path, GameState.idle_of_prepared stop⟩
      · obtain ⟨u, later, emitted, done, stop⟩ :=
          advance_limited_to_decision tWF (cards ▸ reads) stack queued front waits
        exact ⟨u, used + later, events ++ emitted, path.append done, stop⟩
    · let base := .chainPass finished.chainPrioritySeat 0 :: rest
      have exactBase : afterItem finished ++ rest = base := by
        simp only [afterItem, nextCard, ite_eq_right deferred, base, List.cons_append, List.nil_append]
      apply reaches base (Or.inl exactBase) ?_ rfl
      intro f head
      obtain rfl := Option.some.inj head
      exact ⟨rfl, by intro q h; cases h⟩

/-- Finish an item above its decision continuation and any ordinary trigger queue. -/
theorem advance_finish_chain_to_boundary {s : GameState} {item : ObjId}
    {rest original : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .finishSpell item :: rest) (tracks : TriggerWorkTail original rest)
    (front : ∀ f, original.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (waits : original.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix s t used events ∧ ChainWorkEnd t := by
  obtain ⟨t, used, events, path, stop⟩ :=
    advance_finish_chain_to_decision wf reads pending tracks front waits
  exact ⟨t, used, events, path, .decision stop⟩

/-- Run the certified programs above an item's Finish and follow the remaining Chain work. -/
theorem advance_chain_runs_to_decision {s : GameState} {item : ObjId} {body original : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : ResolutionPrefix body (ResolutionPrefix [.finishSpell item] (TriggerWorkTail original)) s.pending)
    (finite : ∀ f ∈ body, Frame.FiniteRun f)
    (front : ∀ f, original.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : original.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix s t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨mid, used, events, path, stop | ⟨⟨tail, ready, queued⟩, midWF, cards⟩⟩ :=
    advance_run_frames wf reads pending finite (fun _ tracked q ne => tracked.insert
      (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl)
      (fun _ kept added nonempty => kept.insert front added nonempty) q ne)
  · exact ⟨mid, used, events, path, GameState.idle_of_prepared stop⟩
  · obtain ⟨t, later, emitted, finished, stop⟩ :=
      advance_finish_chain_to_decision midWF (cards ▸ reads) ready queued front decision
    exact ⟨t, used + later, events ++ emitted, path.append finished, stop⟩

/-- The top item's effects, Finish, optional Recycle and Cleanup are finite when its Run frames
terminate under observation. Resolve subsequent deferred declarations before returning. -/
theorem advance_chain_resolution_to_decision {s : GameState} {item : ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .resolveChain :: rest)
    (finite : ∃ body, resolveFrames s rest = body ++ (Frame.finishSpell item :: rest) ∧
      ∀ f ∈ body, Frame.FiniteRun f)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨body, frames, runs⟩ := finite
  let raw := { s with pending := body ++ (Frame.finishSpell item :: rest) }
  have step : microStep0 s = some (raw, []) := by simp only [microStep0, pending, frames, raw]
  obtain ⟨mid, used, events, positive, path, midWF, cards, route⟩ :=
    advance_rule_with_adds pending rfl step (microStep_wf0 wf step) rfl reads
  let finishes := ResolutionPrefix [.finishSpell item] (TriggerWorkTail rest)
  have inserts (tail : List Frame) (tracked : finishes tail) (q : List PendTrigger) (ne : q ≠ []) :
      finishes (insertTriggers q tail) :=
    tracked.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl)
      (fun _ kept q' ne' => kept.insert front q' ne') q ne
  have base : ResolutionPrefix body finishes raw.pending := ⟨_, rfl, ⟨rest, rfl, Or.inl rfl⟩⟩
  have finish (tracks : ResolutionPrefix body finishes mid.pending) :
      ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ t.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨t, more, emitted, resolved, stop⟩ :=
      advance_chain_runs_to_decision midWF (cards ▸ reads) tracks runs front decision
    exact ⟨t, used + more, events ++ emitted, by omega, path.append resolved, stop⟩
  generalize stack : mid.pending = pendingFrames at route
  cases route with
  | empty => exact ⟨mid, used, events, positive, path, by rw [stack]; rfl⟩
  | resume => exact finish (stack.symm ▸ base)
  | queue q ne =>
    exact finish (stack.symm ▸ base.insert (fun f member => (runs f member).isResolution) inserts q ne)

/-- The top item's effects, Finish, optional Recycle and Cleanup are finite when its Run frames
terminate under observation. Earlier decisions and deferred Spell declarations remain explicit. -/
theorem advance_chain_resolution {s : GameState} {item : ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .resolveChain :: rest)
    (finite : ∃ body, resolveFrames s rest = body ++ (Frame.finishSpell item :: rest) ∧
      ∀ f ∈ body, Frame.FiniteRun f)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ ChainWorkEnd t := by
  obtain ⟨t, used, events, positive, path, stop⟩ :=
    advance_chain_resolution_to_decision wf reads pending finite front decision
  exact ⟨t, used, events, positive, path, .decision stop⟩

/-- Lift certified Chain resolution to the actual final Pass, including any Cleanup
required before offering neutral priority. -/
theorem step_chainPass_last_certified_to_decision {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    {item : ObjId} (wf : s.WF) (reads : MightRead.database s.cards) (ongoing : s.result = none)
    (pending : s.pending = .chainPass p passes :: rest) (last : s.participatingCount ≤ passes + 1)
    (finite : let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
      ∃ body, resolveFrames initial rest = body ++ (Frame.finishSpell item :: rest) ∧
        ∀ f ∈ body, Frame.FiniteRun f)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, 0 < used ∧ t.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      step used s ⟨.player p, .pass⟩ = advance 0 t events := by
  let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
  obtain ⟨t, used, events, positive, path, stop⟩ :=
    advance_chain_resolution_to_decision (s := initial) (wf.congr rfl rfl rfl rfl) reads rfl finite front decision
  refine ⟨t, used, events, positive, stop, ?_, ?_⟩
  · intro fuel
    rw [step_chainPass_last _ ongoing pending last]
    simpa only [List.nil_append] using path fuel []
  · rw [step_chainPass_last _ ongoing pending last]
    simpa only [List.nil_append, Nat.add_zero] using path 0 []

/-- Lift certified Chain resolution to the actual final Pass. A prepared decision
can be returned without further work. -/
theorem step_chainPass_last_certified {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    {item : ObjId} (wf : s.WF) (reads : MightRead.database s.cards) (ongoing : s.result = none)
    (pending : s.pending = .chainPass p passes :: rest) (last : s.participatingCount ≤ passes + 1)
    (finite : let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
      ∃ body, resolveFrames initial rest = body ++ (Frame.finishSpell item :: rest) ∧
        ∀ f ∈ body, Frame.FiniteRun f)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, 0 < used ∧ ChainWorkEnd t ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  obtain ⟨t, used, events, positive, stopped, continues, finishes⟩ :=
    step_chainPass_last_certified_to_decision wf reads ongoing pending last finite front decision
  refine ⟨t, used, events, positive, .decision stopped, continues, fun ready => finishes.trans ?_⟩
  let here : AdvancePrefix t t 0 [] := by intro fuel seen; simp
  simpa using here.finish ready events

/-- Whether the frame contains a Run program. -/
def isRunFrame : Frame → Bool
  | .run .. => true
  | _ => false

/-- Whether the frame is a Run whose complete program is supported. -/
def runFrameSupported : Frame → Bool
  | .run _ _ _ program => program.observedWorkSupported
  | _ => false

/-- Check the actual Run instructions generated for the newest Chain item at this final Pass. -/
def chainPassWorkSupported (s : GameState) (p : PlayerId) (rest : List Frame) : Bool :=
  let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
  ((resolveFrames initial rest).takeWhile isRunFrame).all runFrameSupported

/-- Every accepted Run frame carries the observed termination proof for its program. -/
theorem runFrameSupported_finite {f : Frame} (supported : runFrameSupported f = true) :
    f.FiniteRun := by
  cases f <;> try (simp [runFrameSupported] at supported; done)
  exact ⟨_, _, _, _, rfl, EffectList.observedFinite_of_supported _ supported⟩

private theorem takeWhile_ChainRuns (body : List Frame) (item : ObjId) (rest : List Frame)
    (onlyRuns : ∀ f ∈ body, ∃ p src env program, f = .run p src env program) :
    (body ++ (.finishSpell item :: rest)).takeWhile isRunFrame = body := by
  induction body with
  | nil => rfl
  | cons first later ih =>
    obtain ⟨p, src, env, program, rfl⟩ := onlyRuns first List.mem_cons_self
    simp only [List.cons_append, List.takeWhile_cons, isRunFrame, ite_true,
      ih (fun f member => onlyRuns f (List.mem_cons_of_mem _ member))]

/-- A final Chain Pass checks the current program only, then follows the observed dispatcher
through deferred declarations to the next decision. -/
theorem step_chainPass_last_checked_to_decision {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (ongoing : s.result = none)
    (pending : s.pending = .chainPass p passes :: rest) (last : s.participatingCount ≤ passes + 1)
    (checked : chainPassWorkSupported s p rest = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, 0 < used ∧ t.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      step used s ⟨.player p, .pass⟩ = advance 0 t events := by
  let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
  cases chain : s.zone .chain with
  | cons item older =>
    have present : initial.zone .chain = item :: older := chain
    obtain ⟨body, frames, onlyRuns⟩ := resolveFrames_newest present rest
    have programs : body.all runFrameSupported = true := by
      change ((resolveFrames initial rest).takeWhile isRunFrame).all runFrameSupported = true at checked
      rw [frames, takeWhile_ChainRuns body item rest onlyRuns] at checked
      exact checked
    exact step_chainPass_last_certified_to_decision wf reads ongoing pending last
      ⟨body, frames, fun f member => runFrameSupported_finite (List.all_eq_true.mp programs f member)⟩ front decision
  | nil =>
    let raw := { initial with pending := rest }
    have noChain : initial.zone .chain = [] := chain
    have starts : initial.pending = .resolveChain :: rest := rfl
    have stepRule : microStep0 initial = some (raw, []) := by
      simp only [microStep0, starts, resolveFrames, noChain, raw]
    have initialWF : initial.WF := wf.congr rfl rfl rfl rfl
    obtain ⟨mid, used, events, positive, path, midWF, cards, route⟩ :=
      advance_rule_with_adds starts rfl stepRule (microStep_wf0 initialWF stepRule) rfl reads
    obtain ⟨t, more, resolved, stop⟩ := advance_observed_decision mid rest midWF (cards ▸ reads) route decision
    have full : AdvancePrefix initial t (used + more) events := by
      simpa only [List.append_nil] using path.append resolved
    refine ⟨t, used + more, events, by omega, stop, ?_, ?_⟩
    · intro fuel
      rw [step_chainPass_last _ ongoing pending last]
      simpa only [List.nil_append] using full fuel []
    · rw [step_chainPass_last _ ongoing pending last]
      simpa only [List.nil_append, Nat.add_zero] using full 0 []

/-- A final Chain Pass checks the current program only, then follows the observed dispatcher
to the next decision or a queued limited Spell. -/
theorem step_chainPass_last_checked {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (ongoing : s.result = none)
    (pending : s.pending = .chainPass p passes :: rest) (last : s.participatingCount ≤ passes + 1)
    (checked : chainPassWorkSupported s p rest = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, 0 < used ∧ ChainWorkEnd t ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  obtain ⟨t, used, events, positive, stopped, continues, finishes⟩ :=
    step_chainPass_last_checked_to_decision wf reads ongoing pending last checked front decision
  refine ⟨t, used, events, positive, .decision stopped, continues, fun ready => finishes.trans ?_⟩
  let here : AdvancePrefix t t 0 [] := by intro fuel seen; simp
  simpa using here.finish ready events

end Riftbound

end
