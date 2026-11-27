module

public import Riftbound.Invariant.ObservedCleanupWork
public import Riftbound.Invariant.Priority
public import Riftbound.Invariant.RunWork

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
      ObservedWorkStack (finishedItemFrames s item result ++ rest) t.pending := by
  let result := finishItem s item
  let raw := { result.1 with pending := finishedItemFrames s item result ++ rest }
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

/-- Finishing a Chain item starts Cleanup, preceded by one recycle instruction if required. -/
theorem finishedItemFrames_recycle_cases (s : GameState) (item : ObjId) (rest : List Frame) :
    let result := finishItem s item
    let continuation := .cleanup :: (afterItem result.1 ++ rest)
    finishedItemFrames s item result ++ rest = continuation ∨
      ∃ p src, finishedItemFrames s item result ++ rest =
        .run p src {} (.cons (.prim (.recycle .self)) .nil) :: continuation := by
  unfold finishedItemFrames
  dsimp only
  cases found : s.obj? item with
  | none => exact Or.inl rfl
  | some object =>
    simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    split
    · exact Or.inl rfl
    · let tail := .cleanup :: (afterItem (finishItem s item).1 ++ rest)
      let frame := fun id => Frame.run object.owner id {} (.cons (.prim (.recycle .self)) .nil)
      have shape (moved : Option ObjId) :
          moved.toList.map frame ++ tail = tail ∨
            ∃ p src, moved.toList.map frame ++ tail =
              .run p src {} (.cons (.prim (.recycle .self)) .nil) :: tail := by
        cases moved with
        | none => exact Or.inl rfl
        | some src => exact Or.inr ⟨object.owner, src, rfl⟩
      simp only [List.append_assoc, List.cons_append]
      exact shape _

/-- Remove the Chain item, run its optional Recycle and Cleanup, and keep the continuation
with any ordinary triggers observed along the way. -/
theorem advance_finished_item_until {s : GameState} {item : ObjId} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .finishSpell item :: rest)
    (keeps : List Frame → Prop) (base : keeps (afterItem (finishItem s item).1 ++ rest))
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  let next := afterItem (finishItem s item).1 ++ rest
  let result := finishItem s item
  let raw := { result.1 with pending := finishedItemFrames s item result ++ rest }
  let cleanupContinuation := ResolutionPrefix [.cleanup] keeps
  have step : microStep0 s = some (raw, result.2) := by simp only [microStep0, pending, raw, result]
  have cards : raw.cards = s.cards := by
    have known := congrArg GameState.cards (finishItem_sameMeta s item)
    exact known
  have advanceCleanup {state : GameState} (stateWF : state.WF) (stateReads : MightRead.database state.cards)
      (reached : cleanupContinuation state.pending) : AdvanceTo state keeps := by
    obtain ⟨tail, stack, tracked⟩ := reached
    obtain ⟨t, used, events, _, path, stop⟩ :=
      advance_cleanup_with_adds stateWF stateReads stack keeps tracked inserted
    exact ⟨t, used, events, path, stop⟩
  have insertCleanup : ∀ tail, cleanupContinuation tail → ∀ q, q ≠ [] →
      cleanupContinuation (insertTriggers q tail) :=
    fun _ tracked q ne => tracked.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) inserted q ne
  have rawWF := microStep_wf0 wf step
  rcases finishedItemFrames_recycle_cases s item rest with normal | ⟨p, src, recycle⟩
  · have entered : AdvanceTo s cleanupContinuation :=
      .rule pending rfl step rawWF cards reads ⟨next, normal, base⟩ insertCleanup
    exact entered.then reads (fun _ => advanceCleanup)
  · let program := EffectList.cons (.prim (.recycle .self)) .nil
    let recycleFrame := Frame.run p src {} program
    have entered : AdvanceTo s (ResolutionPrefix [recycleFrame] cleanupContinuation) := by
      refine .rule pending rfl step rawWF cards reads ⟨.cleanup :: next, recycle, ⟨next, rfl, base⟩⟩ ?_
      exact fun _ route q ne => route.insert
        (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) insertCleanup q ne
    apply entered.then reads
    intro mid midWF midReads staged
    obtain ⟨tail, stack, scheduled⟩ := staged
    exact (advance_run_program midWF midReads stack (.cons Effect.SingleRun.recycleSelf.observed .nil)
      cleanupContinuation scheduled insertCleanup).then midReads (fun _ => advanceCleanup)

/-- Resolving the newest Chain item reaches a decision or an already queued limited Spell. -/
inductive ChainWorkEnd (s : GameState) : Prop where
  /-- The game is waiting for an answer, or has no remaining frames. -/
  | decision : s.pending.head?.all (fun frame => !frame.isWork) = true → ChainWorkEnd s
  /-- A Spell played by an effect is still waiting to finalize. -/
  | limited (p : PlayerId) (card : ObjId) (rest : List Frame) :
      s.pending = .run p card {} (.cons (.finalizeLimitedSpell card) .nil) :: rest → ChainWorkEnd s

/-- Finish an item above its decision continuation and any ordinary trigger queue. -/
theorem advance_finish_chain_to_boundary {s : GameState} {item : ObjId}
    {rest original : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .finishSpell item :: rest) (tracks : TriggerWorkTail original rest)
    (front : ∀ f, original.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (waits : original.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, AdvancePrefix s t used events ∧ ChainWorkEnd t := by
  let finished := (finishItem s item).1
  have reaches (base : List Frame) (waiting : TriggerWorkTail base (afterItem finished ++ rest))
      (nonresolution : ∀ f, base.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
      (decision : base.head?.all (fun f => !f.isWork) = true) :
      ∃ t used events, AdvancePrefix s t used events ∧ ChainWorkEnd t := by
    obtain ⟨mid, used, events, path, stop | ⟨queued, midWF, cards⟩⟩ :=
      advance_finished_item_until wf reads pending (TriggerWorkTail base) waiting
        (fun _ route q ne => route.insert nonresolution q ne)
    · exact ⟨mid, used, events, path, .decision stop⟩
    · obtain ⟨t, elapsed, resolved, outcome⟩ := advance_trigger_tail mid base midWF (cards ▸ reads) queued
      refine ⟨t, used + elapsed, events, by simpa only [List.append_nil] using path.append resolved, .decision ?_⟩
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
      let keeps := ResolutionPrefix [frame] (fun _ => True)
      have base : keeps (afterItem finished ++ rest) := by
        refine ⟨rest, ?_, trivial⟩
        simp only [afterItem, nextCard, deferred, ite_true, frame, p]
      obtain ⟨t, used, events, path, stop | ⟨⟨tail, stack, _⟩, _, _⟩⟩ :=
        advance_finished_item_until wf reads pending keeps base (fun _ route q ne => route.insert
          (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) (fun _ _ _ _ => trivial) q ne)
      · exact ⟨t, used, events, path, .decision stop⟩
      · exact ⟨t, used, events, path, .limited p card tail stack⟩
    · let base := .chainPass finished.chainPrioritySeat 0 :: rest
      have exactBase : afterItem finished ++ rest = base := by
        simp only [afterItem, nextCard, ite_eq_right deferred, base, List.cons_append, List.nil_append]
      apply reaches base (Or.inl exactBase) ?_ rfl
      intro f head
      obtain rfl := Option.some.inj head
      exact ⟨rfl, by intro q h; cases h⟩

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
      ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ ChainWorkEnd t := by
    obtain ⟨t, more, emitted, resolved, stop | ⟨⟨tail, finishStack, seen⟩, tWF, tCards⟩⟩ :=
      advance_run_frames midWF (cards ▸ reads) tracks runs inserts
    · exact ⟨t, used + more, events ++ emitted, by omega, path.append resolved, .decision stop⟩
    · obtain ⟨u, elapsed, _, settled, stop⟩ :=
        advance_finish_chain_to_boundary tWF (tCards ▸ cards ▸ reads) finishStack seen front decision
      exact ⟨u, used + more + elapsed, _, by omega, (path.append resolved).append settled, stop⟩
  generalize stack : mid.pending = pendingFrames at route
  cases route with
  | empty => exact ⟨mid, used, events, positive, path, .decision (by rw [stack]; rfl)⟩
  | resume => exact finish (stack.symm ▸ base)
  | queue q ne =>
    exact finish (stack.symm ▸ base.insert (fun f member => (runs f member).isResolution) inserts q ne)

/-- Lift certified Chain resolution to the actual final Pass. At a decision the amount of
fuel used suffices for a successful step. -/
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
      (t.pending.head?.all (fun f => !f.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
  obtain ⟨t, used, events, positive, path, stop⟩ :=
    advance_chain_resolution (s := initial) (wf.congr rfl rfl rfl rfl) reads rfl finite front decision
  refine ⟨t, used, events, positive, stop, ?_, ?_⟩
  · intro fuel
    rw [step_chainPass_last _ ongoing pending last]
    simpa only [List.nil_append] using path fuel []
  · intro reached
    rw [step_chainPass_last _ ongoing pending last]
    simpa only [List.nil_append] using path.finish reached []

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

private theorem runFrameSupported_finite {f : Frame} (supported : runFrameSupported f = true) :
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
to the next decision or a queued limited Spell. -/
theorem step_chainPass_last_checked {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (ongoing : s.result = none)
    (pending : s.pending = .chainPass p passes :: rest) (last : s.participatingCount ≤ passes + 1)
    (checked : chainPassWorkSupported s p rest = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, 0 < used ∧ ChainWorkEnd t ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.pending.head?.all (fun f => !f.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
  cases chain : s.zone .chain with
  | cons item older =>
    have present : initial.zone .chain = item :: older := chain
    obtain ⟨body, frames, onlyRuns⟩ := resolveFrames_newest present rest
    have programs : body.all runFrameSupported = true := by
      change ((resolveFrames initial rest).takeWhile isRunFrame).all runFrameSupported = true at checked
      rw [frames, takeWhile_ChainRuns body item rest onlyRuns] at checked
      exact checked
    exact step_chainPass_last_certified wf reads ongoing pending last
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
    refine ⟨t, used + more, events, by omega, .decision stop, ?_, ?_⟩
    · intro fuel
      rw [step_chainPass_last _ ongoing pending last]
      simpa only [List.nil_append] using full fuel []
    · intro _
      rw [step_chainPass_last _ ongoing pending last]
      simpa only [List.nil_append] using full.finish stop []

end Riftbound

end
