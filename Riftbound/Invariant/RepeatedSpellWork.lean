module

public import Riftbound.Invariant.ChainWork
public import Riftbound.Invariant.Resources

/-!
# Repeat executions under the observed dispatcher (I12)
-/

@[expose] public section

namespace Riftbound

/-- One dynamically generated repeated execution is finite when the currently selected body is. -/
theorem spellExecutionFrames_finite (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (pick : SpellPick) (targets : List ObjId)
    (body : ∀ definition, (s.cardDef? src).bind (·.spellForPick pick) = some definition →
      definition.body.ObservedFinite) :
    ∀ f ∈ spellExecutionFrames s p src env pick targets, f.FiniteRun := by
  intro f found
  unfold spellExecutionFrames at found
  dsimp only at found
  split at found
  · rename_i _ definition chosen
    change f ∈ [_] at found
    obtain rfl := List.mem_singleton.mp found
    exact ⟨_, _, _, _, rfl, definition.recheckTargetGroup_observed s p src targets
      (.cons (body definition chosen) .nil)⟩
  · contradiction

/-- Execute the actual dynamic Repeat frame and recheck its locked targets using the current state. -/
theorem advance_spell_execution {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {pick : SpellPick} {targets : List ObjId} {more : EffectList} {rest : List Frame}
    {keeps : List Frame → Prop} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons (.resolveSpellExecution pick targets) more) :: rest)
    (body : ∀ definition, (s.cardDef? src).bind (·.spellForPick pick) = some definition →
      definition.body.ObservedFinite)
    (base : keeps rest) (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s (RunContinuation p src more keeps) := by
  let live := env.withMight s.mightTable
  let generated := spellExecutionFrames s p src live pick targets
  let resumes := RunContinuation p src more keeps
  have finite : ∀ f ∈ generated, f.FiniteRun :=
    spellExecutionFrames_finite s p src live pick targets body
  have enters : AdvanceTo s (ResolutionPrefix generated resumes) := by
    refine advance_run_rule wf reads pending ?_ ?_
    · change ResolutionPrefix generated resumes ((generated ++ [.run p src live more]) ++ rest)
      rw [List.append_assoc]
      exact ⟨_, rfl, ⟨live, rest, rfl, base⟩⟩
    · exact fun _ route q ne => route.insert (fun f member => (finite f member).isResolution)
        (fun _ tracked q' ne' => tracked.insert inserted q' ne') q ne
  exact enters.then reads (fun _ safe checked staged =>
    advance_run_frames safe checked staged finite (fun _ route q ne => route.insert inserted q ne))

/-- Check the body selected for this execution in the current game state.
An absent definition leaves no body to execute. -/
def spellExecutionWorkSupported (s : GameState) (src : ObjId) (pick : SpellPick) : Bool :=
  ((s.cardDef? src).bind (·.spellForPick pick)).all (·.body.observedWorkSupported)

/-- A sequence of Repeat executions reaches the ordinary Chain boundary or the first
execution whose currently selected body lacks an observed termination proof. -/
inductive RepeatedSpellEnd (s : GameState) : Prop where
  /-- The Chain is waiting for a player decision or limited Spell declaration, or has ended. -/
  | chain : ChainWorkEnd s → RepeatedSpellEnd s
  /-- The next Repeat execution needs additional effect rules in the proof. -/
  | unsupported (p : PlayerId) (src : ObjId) (env : Env) (pick : SpellPick)
      (targets : List ObjId) (rest : List Frame) :
      s.pending = .run p src env (.cons (.resolveSpellExecution pick targets) .nil) :: rest →
      spellExecutionWorkSupported s src pick = false →
      RepeatedSpellEnd s

/-- The current Repeat execution has reached a body that the work checker does not support. -/
def RepeatWorkUnsupported (s : GameState) : Prop :=
  ∃ p src env pick targets rest,
    s.pending = .run p src env (.cons (.resolveSpellExecution pick targets) .nil) :: rest ∧
    spellExecutionWorkSupported s src pick = false

private def repeatedFrames (p : PlayerId) (src : ObjId) (env : Env)
    (executions : List (SpellPick × List ObjId)) : List Frame :=
  executions.map (fun (pick, targets) =>
    .run p src env (.cons (.resolveSpellExecution pick targets) .nil))

private theorem repeatedFrames_resolution {p : PlayerId} {src : ObjId} {env : Env}
    {executions : List (SpellPick × List ObjId)} {f : Frame} (member : f ∈ repeatedFrames p src env executions) :
    f.isResolution = true := by
  obtain ⟨⟨pick, targets⟩, _, rfl⟩ := List.mem_map.mp member
  rfl

private theorem advance_repeated_executions {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {keeps : List Frame → Prop} (executions : List (SpellPick × List ObjId))
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : ResolutionPrefix (repeatedFrames p src env executions) keeps s.pending)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    ∃ t used events, AdvancePrefix s t used events ∧
      ((t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨ RepeatWorkUnsupported t) ∨
        keeps t.pending ∧ t.WF ∧ t.cards = s.cards) := by
  induction executions generalizing s with
  | nil =>
    obtain ⟨rest, stack, kept⟩ := pending
    exact ⟨s, 0, [], by intro fuel prior; simp, Or.inr ⟨stack.symm ▸ kept, wf, rfl⟩⟩
  | cons execution later ih =>
    obtain ⟨pick, targets⟩ := execution
    obtain ⟨rest, exactStack, kept⟩ := pending
    let remaining := repeatedFrames p src env later
    let continuations := ResolutionPrefix remaining keeps
    have stack : s.pending = .run p src env (.cons (.resolveSpellExecution pick targets) .nil) ::
        (remaining ++ rest) := exactStack
    cases checked : spellExecutionWorkSupported s src pick with
    | false =>
      exact ⟨s, 0, [], by intro fuel prior; simp, Or.inl (Or.inr ⟨p, src, env, pick, targets, _, stack, checked⟩)⟩
    | true =>
      have body (definition : EffectDef)
          (selected : (s.cardDef? src).bind (·.spellForPick pick) = some definition) :
          definition.body.ObservedFinite := by
        unfold spellExecutionWorkSupported at checked
        rw [selected] at checked
        exact definition.body.observedFinite_of_supported checked
      have insertRest : ∀ tail, continuations tail → ∀ q, q ≠ [] → continuations (insertTriggers q tail) :=
        fun _ valid q ne => valid.insert (fun _ member => repeatedFrames_resolution member) inserted q ne
      have enters := advance_spell_execution wf reads stack body
        (keeps := continuations) ⟨rest, rfl, kept⟩ insertRest
      have run : AdvanceTo s continuations := by
        apply enters.then reads
        intro t tWF tReads tracked
        obtain ⟨nextEnv, tail, atEnd, known⟩ := tracked
        exact advance_run_program tWF tReads atEnd .nil continuations known insertRest
      obtain ⟨mid, used, events, path, stop | ⟨tracked, midWF, cards⟩⟩ := run
      · exact ⟨mid, used, events, path, Or.inl (Or.inl stop)⟩
      · obtain ⟨t, elapsed, emitted, resolved, outcome⟩ := ih midWF (cards ▸ reads) tracked
        exact ⟨t, used + elapsed, events ++ emitted, path.append resolved,
          outcome.imp_right (fun ⟨active, finalWF, finalCards⟩ => ⟨active, finalWF, finalCards.trans cards⟩)⟩

private theorem advance_repeated_chain_until_decision {s : GameState} {item : ObjId} {older : List ObjId}
    {object : Object} {definition : CardDef} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .resolveChain :: rest)
    (chain : s.zone .chain = item :: older) (found : s.obj? item = some object)
    (printed : s.cardDef? item = some definition) (repeated : object.spellPick.hasExecutionChoices = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      ((t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨ RepeatWorkUnsupported t) ∨
        t.pending = rest ∧ t.WF ∧ t.cards = s.cards) := by
  let ctx : Env := { hiddenPlayLocation := object.hiddenAt, shownOff := object.shownOff }
  let executions := object.spellPick.executions object.targets
  let frames := repeatedFrames object.controller item ctx executions
  let raw := { s with pending := frames ++ (Frame.finishSpell item :: rest) }
  have step : microStep0 s = some (raw, []) := by
    simp only [microStep0, pending, resolveFrames_execution_slots chain found printed repeated,
      frames, repeatedFrames, ctx, executions, raw]
  obtain ⟨mid, used, events, positive, path, midWF, cards, route⟩ :=
    advance_rule_with_adds pending rfl step (microStep_wf0 wf step) rfl reads
  let finish := ResolutionPrefix [.finishSpell item] (TriggerWorkTail rest)
  have insertFinish : ∀ tail, finish tail → ∀ q, q ≠ [] → finish (insertTriggers q tail) :=
    fun _ known q ne => known.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl)
      (fun _ after q' ne' => after.insert front q' ne') q ne
  have rawStack : ResolutionPrefix frames finish raw.pending := ⟨_, rfl, ⟨rest, rfl, Or.inl rfl⟩⟩
  have finishExecution (tracks : ResolutionPrefix frames finish mid.pending) :
      ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
        ((t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨ RepeatWorkUnsupported t) ∨
          t.pending = rest ∧ t.WF ∧ t.cards = s.cards) := by
    obtain ⟨t, elapsed, later, work, stop | ⟨⟨tail, ready, tailRoute⟩, tWF, tCards⟩⟩ :=
      advance_repeated_executions executions midWF (cards ▸ reads) tracks insertFinish
    · exact ⟨t, used + elapsed, events ++ later, by omega, path.append work, Or.inl stop⟩
    · obtain ⟨u, closing, emitted, completed, stop | ⟨resumed, safe, known⟩⟩ :=
        advance_finish_chain_until_decision tWF (tCards ▸ cards ▸ reads) ready tailRoute front
      · exact ⟨u, used + elapsed + closing, (events ++ later) ++ emitted, by omega,
          (path.append work).append completed, Or.inl (Or.inl stop)⟩
      · exact ⟨u, used + elapsed + closing, (events ++ later) ++ emitted, by omega,
          (path.append work).append completed, Or.inr ⟨resumed, safe, (known.trans tCards).trans cards⟩⟩
  generalize stack : mid.pending = framesAfter at route
  cases route with
  | empty => exact ⟨mid, used, events, positive, path, Or.inl (Or.inl (GameState.prepared_idle_of_empty stack))⟩
  | resume => exact finishExecution (stack.symm ▸ rawStack)
  | queue q ne =>
    exact finishExecution (stack.symm ▸ rawStack.insert
      (fun _ member => repeatedFrames_resolution member) insertFinish q ne)

/-- Resolve the Repeat executions generated by the actual Chain rule, checking each body
after the preceding executions have updated the game. -/
theorem advance_repeated_chain_resolution {s : GameState} {item : ObjId} {older : List ObjId}
    {object : Object} {definition : CardDef} {rest : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards) (pending : s.pending = .resolveChain :: rest)
    (chain : s.zone .chain = item :: older) (found : s.obj? item = some object)
    (printed : s.cardDef? item = some definition) (repeated : object.spellPick.hasExecutionChoices = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧ RepeatedSpellEnd t := by
  obtain ⟨t, used, events, positive, path, (ready | unsupported) | ⟨resumed, _, _⟩⟩ :=
    advance_repeated_chain_until_decision wf reads pending chain found printed repeated front
  · exact ⟨t, used, events, positive, path, .chain (.decision (GameState.idle_of_prepared ready))⟩
  · obtain ⟨p, src, env, pick, targets, tail, stack, missing⟩ := unsupported
    exact ⟨t, used, events, positive, path, .unsupported p src env pick targets tail stack missing⟩
  · exact ⟨t, used, events, positive, path, .chain (.decision (resumed.symm ▸ decision))⟩

/-- Follow the real final Pass through every supported Repeat execution, reporting either
a Chain boundary or the current execution with an unsupported body. -/
theorem step_chainPass_last_repeated {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    {item : ObjId} {older : List ObjId} {object : Object} {definition : CardDef}
    (wf : s.WF) (reads : MightRead.database s.cards) (ongoing : s.result = none)
    (pending : s.pending = .chainPass p passes :: rest) (last : s.participatingCount ≤ passes + 1)
    (chain : s.zone .chain = item :: older) (found : s.obj? item = some object)
    (printed : s.cardDef? item = some definition) (repeated : object.spellPick.hasExecutionChoices = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ t used events, 0 < used ∧ RepeatedSpellEnd t ∧
      (∀ fuel, step (used + fuel) s ⟨.player p, .pass⟩ = advance fuel t events) ∧
      (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true →
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) := by
  let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
  have initialWF : initial.WF := wf.congr rfl rfl rfl rfl
  obtain ⟨t, used, events, positive, path, stop⟩ :=
    advance_repeated_chain_resolution (s := initial) initialWF reads rfl chain found printed repeated front decision
  refine ⟨t, used, events, positive, stop, ?_, ?_⟩
  · intro fuel
    rw [step_chainPass_last _ ongoing pending last]
    simpa only [List.nil_append] using path fuel []
  · intro reached
    rw [step_chainPass_last _ ongoing pending last]
    simpa only [List.nil_append] using path.finish reached []

/-- A final Repeat pass reaches a prepared decision or the first unsupported execution. -/
theorem step_chainPass_last_repeated_to_preparedDecision {s : GameState} {p : PlayerId} {passes : Nat}
    {rest : List Frame} {item : ObjId} {older : List ObjId} {object : Object} {definition : CardDef}
    (wf : s.WF) (reads : MightRead.database s.cards) (ongoing : s.result = none)
    (pending : s.pending = .chainPass p passes :: rest) (last : s.participatingCount ≤ passes + 1)
    (chain : s.zone .chain = item :: older) (found : s.obj? item = some object)
    (printed : s.cardDef? item = some definition) (repeated : object.spellPick.hasExecutionChoices = true)
    (front : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (decision : rest.head?.all (fun f => !f.isWork) = true)
    (quiet : ∀ owner tail, rest = .priority owner :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, 0 < used ∧
      (∀ extra, step (used + extra) s ⟨.player p, .pass⟩ = advance extra t events) ∧
      ((t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
        step used s ⟨.player p, .pass⟩ = .ok (t, events)) ∨ RepeatWorkUnsupported t) := by
  let initial := ({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)
  have finishes {t : GameState} {used : Nat} {events : List Event} (positive : 0 < used)
      (path : AdvancePrefix initial t used events)
      (stop : t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨ RepeatWorkUnsupported t) :
      ∃ t used events, 0 < used ∧
        (∀ extra, step (used + extra) s ⟨.player p, .pass⟩ = advance extra t events) ∧
        ((t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∧
          step used s ⟨.player p, .pass⟩ = .ok (t, events)) ∨ RepeatWorkUnsupported t) := by
    refine ⟨t, used, events, positive, ?_, stop.imp_left (fun ready => ⟨ready, ?_⟩)⟩
    · intro extra
      rw [step_chainPass_last _ ongoing pending last]
      simpa only [List.nil_append] using path extra []
    · rw [step_chainPass_last _ ongoing pending last]
      simpa only [List.nil_append] using path.finish ready []
  obtain ⟨mid, used, events, positive, path, stop | ⟨resumed, safe, cards⟩⟩ :=
    advance_repeated_chain_until_decision (s := initial) (wf.congr rfl rfl rfl rfl)
      reads rfl chain found printed repeated front
  · exact finishes positive path stop
  · obtain ⟨t, more, emitted, resumedPath, ready⟩ :=
      advance_waiting_to_preparedDecision safe (cards ▸ reads) (resumed.symm ▸ decision)
        (fun owner tail priority => quiet owner tail (resumed.symm.trans priority))
    exact finishes (by omega) (path.append resumedPath) (Or.inl ready)

end Riftbound

end
