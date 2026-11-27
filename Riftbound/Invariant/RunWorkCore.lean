module

public import Riftbound.Invariant.ObservedWork
public import Riftbound.Invariant.TurnDrawWork

/-!
# Effect programs under the work dispatcher (I12)
-/

@[expose] public section

namespace Riftbound

/-- Executing this effect consumes one instruction without creating a new work or decision
frame before the remaining instructions. -/
def Effect.SingleRun (effect : Effect) : Prop :=
  ∀ s p src env more, ∃ board emitted,
    runEffect s p src env effect more effectAddPolicy = (board, [.run p src env more], emitted)

/-- Remaining instructions for the same invocation, with its current environment and tail. -/
def RunContinuation (p : PlayerId) (src : ObjId) (program : EffectList)
    (keeps : List Frame → Prop) (stack : List Frame) : Prop :=
  ∃ env rest, stack = .run p src env program :: rest ∧ keeps rest

/-- Ordinary trigger insertion preserves the next Run frame. -/
theorem RunContinuation.insert {p : PlayerId} {src : ObjId} {program : EffectList}
    {keeps : List Frame → Prop} {stack : List Frame}
    (before : RunContinuation p src program keeps stack)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail))
    (q : List PendTrigger) (ne : q ≠ []) :
    RunContinuation p src program keeps (insertTriggers q stack) := by
  obtain ⟨env, rest, rfl, kept⟩ := before
  exact ⟨env, _, rfl, inserted rest kept q ne⟩

/-- One instruction terminates when it yields to a decision or reaches the rest of the invocation
under the actual observer and any immediate Adds it schedules. -/
def Effect.ObservedFinite (effect : Effect) : Prop :=
  ∀ (s : GameState) p src env more rest (keeps : List Frame → Prop),
    s.WF → MightRead.database s.cards → s.pending = .run p src env (.cons effect more) :: rest →
    keeps rest → (∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) →
    AdvanceTo s (RunContinuation p src more keeps)

/-- Each instruction in the program is finite under actual observation. -/
inductive EffectList.ObservedFinite : EffectList → Prop where
  /-- The program has no instructions. -/
  | nil : EffectList.ObservedFinite .nil
  /-- The first instruction and the rest terminate in order. -/
  | cons {effect : Effect} {more : EffectList} :
      effect.ObservedFinite → more.ObservedFinite → EffectList.ObservedFinite (.cons effect more)

/-- Dispatch the instruction and account for all immediate Adds and ordinary trigger insertion. -/
theorem advance_run_rule {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {effect : Effect} {more : EffectList} {rest : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons effect more) :: rest)
    (base : let result := runEffect s p src (env.withMight s.mightTable) effect more effectAddPolicy
      keeps (result.2.1 ++ rest))
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  let result := runEffect s p src (env.withMight s.mightTable) effect more effectAddPolicy
  let raw := { result.1 with pending := result.2.1 ++ rest }
  have rule : microStep0 s = some (raw, result.2.2) := by simp only [microStep0, pending, raw, result]
  have cards : raw.cards = s.cards := by
    have same := congrArg GameState.cards (runEffect_safe s p src (env.withMight s.mightTable)
      effect more effectAddPolicy).same
    exact same
  exact AdvanceTo.rule pending rfl rule (microStep_wf0 wf rule) cards reads base inserted

/-- An instruction that performs its work in one Run transition terminates through the observer. -/
theorem Effect.SingleRun.observed {effect : Effect} (single : effect.SingleRun) :
    effect.ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
  obtain ⟨board, emitted, rule⟩ := single s p src (env.withMight s.mightTable) more
  dsimp only
  rw [rule]
  exact ⟨_, rest, rfl, base⟩

/-- Consume the certified prefix and leave the still-owed Run instructions at the front. -/
theorem EffectList.ObservedFinite.advance_appended {program : EffectList} (finite : program.ObservedFinite)
    {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {more : EffectList}
    {rest : List Frame} {keeps : List Frame → Prop} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (program.append more) :: rest)
    (base : keeps rest) (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s (RunContinuation p src more keeps) := by
  induction finite generalizing s env rest with
  | nil => exact .resume wf ⟨env, rest, pending, base⟩
  | @cons effect moreProgram head remaining ih =>
    apply AdvanceTo.then (head s p src env (moreProgram.append more) rest keeps wf reads pending base inserted) reads
    intro t tWF tReads reached
    obtain ⟨env, rest, stack, tracked⟩ := reached
    exact ih tWF tReads stack tracked

private theorem effectList_append_nil : ∀ es : EffectList, es.append .nil = es
  | .nil => rfl
  | .cons e es => by simp only [EffectList.append, effectList_append_nil es]

/-- Run a certified program and remove its empty Run frame before resuming the continuation. -/
theorem advance_run_program {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {program : EffectList} {rest : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env program :: rest) (finite : program.ObservedFinite)
    (keeps : List Frame → Prop) (base : keeps rest)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  have full : s.pending = .run p src env (program.append .nil) :: rest := by
    simpa only [effectList_append_nil] using pending
  apply (finite.advance_appended wf reads full base inserted).then reads
  intro t tWF tReads reached
  obtain ⟨env, tail, stack, tracked⟩ := reached
  let raw := { t with pending := tail }
  have rule : microStep0 t = some (raw, []) := by simp only [microStep0, stack, raw]
  exact .rule stack rfl rule (microStep_wf0 tWF rule) rfl tReads tracked inserted

private theorem Effect.ObservedFinite.ofPrograms {effect : Effect}
    (programs : ∀ s p src env more, ∃ program : EffectList, program.ObservedFinite ∧
      (runEffect s p src env effect more effectAddPolicy).2.1 = [.run p src env (program.append more)]) :
    effect.ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  obtain ⟨program, finite, starts⟩ := programs s p src (env.withMight s.mightTable) more
  have enter : AdvanceTo s (RunContinuation p src (program.append more) keeps) := by
    apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
    dsimp only
    rw [starts]
    exact ⟨_, rest, rfl, base⟩
  apply enter.then reads
  intro t tWF tReads reached
  obtain ⟨env, tail, stack, tracked⟩ := reached
  exact finite.advance_appended tWF tReads stack tracked inserted

/-- Nested sequences run their certified instructions before the remaining invocation. -/
theorem Effect.ObservedFinite.seq {program : EffectList} (finite : program.ObservedFinite) :
    (Effect.seq program).ObservedFinite :=
  .ofPrograms (fun _ _ _ _ _ => ⟨program, finite, rfl⟩)

private theorem Effect.ObservedFinite.replicate {body : Effect} (finite : body.ObservedFinite) (n : Nat) :
    (EffectList.replicate n body).ObservedFinite := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons finite ih

/-- A runtime repetition consumes a finite number of certified body invocations. -/
theorem Effect.ObservedFinite.repeatN {amount : Amount} {body : Effect} (finite : body.ObservedFinite) :
    (Effect.repeatN amount body).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  cases count : amount.evalS s p src env with
  | none => exact ⟨.nil, .nil, by simp only [runEffect, Effect.pickSel?, runEffect1, count]; rfl⟩
  | some n => exact ⟨_, finite.replicate n, by simp only [runEffect, Effect.pickSel?, runEffect1, count]⟩

/-- A conditional follows the branch selected by the live state and refreshed Might. -/
theorem Effect.ObservedFinite.ifThen {test : Condition} {yes no : Effect}
    (onYes : yes.ObservedFinite) (onNo : no.ObservedFinite) :
    (Effect.ifThen test yes no).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  cases result : test.eval s p src (env.withMight s.mightTable) with
  | none =>
    exact ⟨.nil, .nil, by simp only [runEffect, Effect.pickSel?, runEffect1, result]; rfl⟩
  | some selected =>
    have branch : (if selected then yes else no).ObservedFinite := by cases selected <;> assumption
    exact ⟨.cons (if selected then yes else no) .nil, .cons branch .nil,
      by simp only [runEffect, Effect.pickSel?, runEffect1, result, EffectList.append]⟩

/-- A Run frame whose instruction list terminates under actual observation. -/
def Frame.FiniteRun (frame : Frame) : Prop :=
  ∃ p src env program, frame = .run p src env program ∧ program.ObservedFinite

/-- Certified Run frames are resolution work. -/
theorem Frame.FiniteRun.isResolution {frame : Frame} (finite : Frame.FiniteRun frame) :
    frame.isResolution = true := by
  obtain ⟨_, _, _, _, rfl, _⟩ := finite
  rfl

/-- Execute a list of certified Run frames, preserving the order of ordinary triggers queued
behind those frames. -/
theorem advance_run_frames {s : GameState} {frames : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : ResolutionPrefix frames keeps s.pending)
    (finite : ∀ f ∈ frames, Frame.FiniteRun f)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  induction frames generalizing s with
  | nil =>
    obtain ⟨tail, ready, tracked⟩ := pending
    exact .resume wf (ready.symm ▸ tracked)
  | cons first later ih =>
    obtain ⟨p, src, env, program, rfl, active⟩ := finite first List.mem_cons_self
    obtain ⟨tail, ready, tracked⟩ := pending
    have remaining (f : Frame) (inLater : f ∈ later) : Frame.FiniteRun f :=
      finite f (List.mem_cons_of_mem _ inLater)
    have begins : s.pending = .run p src env program :: (later ++ tail) := ready
    let waits := ResolutionPrefix later keeps
    have work := advance_run_program wf reads begins active waits ⟨tail, rfl, tracked⟩
      (fun _ keep q ne => keep.insert (fun f member => (remaining f member).isResolution) inserted q ne)
    exact work.then reads (fun state safe checked keep => ih safe checked keep remaining)

private theorem Effect.ObservedFinite.ofForks {effect : Effect}
    (forks : ∀ s p src env more, ∃ frames,
      (runEffect s p src env effect more effectAddPolicy).2.1 = frames ++ [.run p src env more] ∧
      ∀ f ∈ frames, Frame.FiniteRun f) :
    effect.ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  obtain ⟨frames, scheduled, finite⟩ := forks s p src (env.withMight s.mightTable) more
  let resumes := RunContinuation p src more keeps
  have entered : AdvanceTo s (ResolutionPrefix frames resumes) := by
    refine advance_run_rule wf reads pending ?_ ?_
    · dsimp only
      rw [scheduled, List.append_assoc]
      exact ⟨_, rfl, ⟨_, rest, rfl, base⟩⟩
    · exact fun _ route q ne => route.insert (fun f member => (finite f member).isResolution)
        (fun _ resume q' ne' => resume.insert inserted q' ne') q ne
  exact entered.then reads (fun state safe checked queued =>
    advance_run_frames safe checked queued finite (fun _ resume q ne => resume.insert inserted q ne))

/-- A binding runs the certified body in the derived environment. -/
theorem Effect.ObservedFinite.bind {name : VarId} {amount : Amount} {body : Effect}
    (finite : body.ObservedFinite) : (Effect.bind name amount body).ObservedFinite := by
  apply Effect.ObservedFinite.ofForks
  intro s p src env more
  cases value : amount.evalS s p src env with
  | none => exact ⟨[], by simp [runEffect, Effect.pickSel?, runEffect1, value], by simp⟩
  | some n =>
    refine ⟨[.run p src (env.bind name (.int n)) (.cons body .nil)], ?_, ?_⟩
    · simp [runEffect, Effect.pickSel?, runEffect1, value]
    · intro f member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_, _, _, _, rfl, .cons finite .nil⟩

/-- A finite selection gives a finite list of body invocations. -/
theorem Effect.ObservedFinite.forEach {sel : Selector} {body : Effect}
    (finite : body.ObservedFinite) : (Effect.forEach sel body).ObservedFinite := by
  apply Effect.ObservedFinite.ofForks
  intro s p src env more
  cases selected : sel.eval s p src env with
  | none => exact ⟨[], by simp [runEffect, Effect.pickSel?, runEffect1, selected], by simp⟩
  | some objects =>
    refine ⟨objects.map (fun id => .run p src { env with it := some id } (.cons body .nil)), ?_, ?_⟩
    · simp [runEffect, Effect.pickSel?, runEffect1, selected]
    · intro f member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      exact ⟨_, _, _, _, rfl, .cons finite .nil⟩

/-- Each selected player receives a terminating body with the appropriate controller. -/
theorem Effect.ObservedFinite.eachPlayer {who : PlayerSel} {body : Effect}
    (finite : body.ObservedFinite) : (Effect.eachPlayer who body).ObservedFinite := by
  apply Effect.ObservedFinite.ofForks
  intro s p src env more
  let seats : Option (List PlayerId) := match who with
    | .controllerOf i =>
      match env.slots[i]? with
      | some (.obj o) => (s.obj? o).bind fun x =>
        if s.departures.seats.contains x.controller then none else some [x.controller]
      | _ => none
    | _ => who.resolve s p env
  let playerEnv := { env with effectController := env.effectController <|> some p }
  have rule : (runEffect s p src env (.eachPlayer who body) more effectAddPolicy).2.1 =
      match seats with
      | some qs => qs.map (fun q => .run q src playerEnv (.cons body .nil)) ++ [.run p src env more]
      | none => [.run p src env more] := by
    unfold runEffect Effect.pickSel? runEffect1
    change (match seats with
      | some qs => (s, qs.map (fun q => Frame.run q src playerEnv (.cons body .nil)) ++ [Frame.run p src env more], [])
      | none => (s, [Frame.run p src env more], [Event.skipped src])).2.1 = _
    cases seats <;> rfl
  cases selected : seats with
  | none => exact ⟨[], by rw [rule, selected]; rfl, by simp⟩
  | some players =>
    refine ⟨players.map (fun q => .run q src playerEnv (.cons body .nil)), by rw [rule, selected], ?_⟩
    intro f member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    exact ⟨_, _, _, _, rfl, .cons finite .nil⟩

/-- Resolve a Run instruction that immediately presents a decision, including its observer. -/
theorem advance_run_decision {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {effect : Effect} {more : EffectList} {rest : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons effect more) :: rest)
    (waits : let result := runEffect s p src (env.withMight s.mightTable) effect more effectAddPolicy
      (result.2.1 ++ rest).head?.all (fun f => !f.isWork) = true) :
    AdvanceTo s keeps := by
  let result := runEffect s p src (env.withMight s.mightTable) effect more effectAddPolicy
  let raw := { result.1 with pending := result.2.1 ++ rest }
  have step : microStep0 s = some (raw, result.2.2) := by simp only [microStep0, pending, raw, result]
  have cards : raw.cards = s.cards := by
    have db := congrArg GameState.cards (runEffect_safe s p src (env.withMight s.mightTable)
      effect more effectAddPolicy).same
    exact db
  obtain ⟨mid, used, events, _, path, midWF, midCards, route⟩ :=
    advance_rule_with_adds pending rfl step (microStep_wf0 wf step) cards reads
  obtain ⟨t, later, remaining, stop⟩ :=
    advance_observed_decision mid raw.pending midWF (midCards ▸ reads) route waits
  exact ⟨t, used + later, events, by simpa only [List.append_nil] using path.append remaining, Or.inl stop⟩

/-- A feasible optional instruction yields to its decision before running its body. -/
theorem Effect.ObservedFinite.may (body : Effect) : (Effect.may body).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  by_cases possible : mayAvailable s p src live body effectAddPolicy = true
  · apply advance_run_decision wf reads pending
    simp only [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl,
      possible, ite_true]
    rfl
  · apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
    simp only [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl,
      ite_eq_right possible]
    exact ⟨live, rest, rfl, base⟩

/-- An empty alternative list is skipped, a singleton runs, and larger lists ask for a decision. -/
theorem Effect.ObservedFinite.eitherOf {options : EffectList} (finite : options.ObservedFinite) :
    (Effect.eitherOf options).ObservedFinite := by
  cases finite with
  | nil => exact Effect.SingleRun.observed (fun s p src env more => ⟨s, [.skipped src], rfl⟩)
  | @cons first rest firstFinite _ =>
    cases rest with
    | nil =>
      exact .ofPrograms (fun _ _ _ _ _ => ⟨.cons first .nil, .cons firstFinite .nil, rfl⟩)
    | cons other later =>
      intro s p src env more tail keeps wf reads pending _ _
      apply advance_run_decision wf reads pending
      cases later <;> rfl

/-- Resolve a prefix of draws, preserving the tracked continuation and ordinary trigger order. -/
theorem advance_draw_frames {s : GameState} {frames : List Frame}
    {keeps : List Frame → Prop} (count : Nat) (draws : ∀ f ∈ frames, ∃ p, f = .draw p count)
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : ResolutionPrefix frames keeps s.pending)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s keeps := by
  induction frames generalizing s with
  | nil =>
    obtain ⟨tail, ready, tracked⟩ := pending
    exact .resume wf (ready.symm ▸ tracked)
  | cons first frames ih =>
    obtain ⟨p, rfl⟩ := draws first List.mem_cons_self
    obtain ⟨tail, ready, tracked⟩ := pending
    have following f (member : f ∈ frames) := draws f (List.mem_cons_of_mem _ member)
    have resolution : ∀ f ∈ frames, f.isResolution = true := by
      intro f member
      obtain ⟨_, rfl⟩ := following f member
      rfl
    let tracks := ResolutionPrefix frames keeps
    have work : AdvanceTo s tracks := by
      obtain ⟨t, used, events, _, path, outcome⟩ :=
        advance_draw_until wf reads ready tracks ⟨tail, rfl, tracked⟩
          (fun _ route q ne => route.insert resolution inserted q ne)
      exact ⟨t, used, events, path, outcome⟩
    exact work.then reads (fun _ safe checked kept => ih following safe checked kept)

/-- Draw instructions finish their generated batches, or stop at Burn Out or another decision. -/
theorem Effect.ObservedFinite.draw (who : PlayerSel) (amount : Amount) :
    (Effect.prim (.draw who amount)).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  let resumes := RunContinuation p src more keeps
  have enter (players : List PlayerId) (count : Nat)
      (work : (runEffect s p src live (.prim (.draw who amount)) more effectAddPolicy).2.1 =
        players.map (fun q => Frame.draw q count) ++ [.run p src live more]) :
      AdvanceTo s resumes := by
    let draws := players.map (fun q => Frame.draw q count)
    have resolution : ∀ f ∈ draws, f.isResolution = true := by
      intro frame member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      rfl
    have head : AdvanceTo s (ResolutionPrefix draws resumes) := by
      refine advance_run_rule wf reads pending ?_ ?_
      · dsimp only
        rw [work, List.append_assoc]
        exact ⟨_, rfl, ⟨live, rest, rfl, base⟩⟩
      · exact fun _ route q ne => route.insert resolution
          (fun _ keep q' ne' => keep.insert inserted q' ne') q ne
    exact head.then reads (fun state safe checked tracked =>
      advance_draw_frames count
        (fun frame member => by
          obtain ⟨q, _, h⟩ := List.mem_map.mp member
          exact ⟨q, h.symm⟩)
        safe checked tracked (fun _ keep q ne => keep.insert inserted q ne))
  cases players : who.resolve s p live with
  | none => exact enter [] 0 (by simp only [runEffect, Effect.pickSel?, Prim.pickSel?,
      runEffect1, runPrimEffect, players]; rfl)
  | some targets =>
    cases amountRead : amount.evalS s p src live with
    | none => exact enter [] 0 (by simp only [runEffect, Effect.pickSel?, Prim.pickSel?,
        runEffect1, runPrimEffect, players, amountRead]; rfl)
    | some count => exact enter targets count (by simp only [runEffect, Effect.pickSel?, Prim.pickSel?,
        runEffect1, runPrimEffect, players, amountRead])

/-- A no-op consumes one Run step. -/
theorem Effect.SingleRun.nop : Effect.nop.SingleRun := by
  intro s p src env more
  exact ⟨s, [], rfl⟩

/-- Gaining XP consumes one Run step. -/
theorem Effect.SingleRun.gainXP (who : PlayerSel) (amount : Amount) :
    (Effect.prim (.gainXP who amount)).SingleRun := by
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
    effectDamageBatch?, permanentPlayEffects, applyPrim]
  by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;>
    cases who.resolve s p env <;> cases amount.evalS s p src env <;> exact ⟨_, _, rfl⟩

/-- A permission to inspect facedown cards consumes one Run step. -/
theorem Effect.SingleRun.allowFacedownInspection (whose : PlayerSel) :
    (Effect.prim (.allowFacedownInspection whose)).SingleRun := by
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
    effectDamageBatch?, permanentPlayEffects, applyPrim]
  by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;>
    cases whose.resolve s p env <;> exact ⟨_, _, rfl⟩

private def noAttachments (events : List Event) : Prop :=
  ∀ gear unit, Event.attached gear unit ∉ events

private theorem noAttachments.append {a b : List Event}
    (first : noAttachments a) (second : noAttachments b) : noAttachments (a ++ b) := by
  intro gear unit found
  rcases List.mem_append.mp found with l | r
  · exact first gear unit l
  · exact second gear unit r

private theorem recycleOne_noAttachments (s : GameState) (id : ObjId) :
    noAttachments (recycleOne s id).2 := by
  unfold recycleOne
  split
  · dsimp only
    split
    · simp [noAttachments]
    · split <;> simp [noAttachments]
  · simp [noAttachments]

private theorem applyEach_noAttachments (f : GameState → ObjId → GameState × List Event)
    (noAttachmentsOne : ∀ s id, noAttachments (f s id).2) (s : GameState) (ids : List ObjId) :
    noAttachments (applyEach f s ids).2 := by
  induction ids generalizing s with
  | nil => simp [applyEach, noAttachments]
  | cons first more ih =>
    exact (noAttachmentsOne s first).append (ih (f s first).1)

private theorem spellCompletion_noAttachments (s : GameState) (src : ObjId) (events : List Event) :
    noAttachments (spellCompletion s src events true) := by
  unfold spellCompletion
  simp only [ite_true]
  split
  · split
    · split <;> simp [noAttachments]
    · simp [noAttachments]
  · simp [noAttachments]

private theorem recycle_noAttachments {s t : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {events : List Event} (outcome : applyPrim s p src env (.recycle sel) = some (t, events)) :
    noAttachments events := by
  unfold applyPrim at outcome
  cases selected : Selector.eval s p src env sel with
  | none => simp [selected] at outcome
  | some ids =>
    simp only [selected, Option.map_some] at outcome
    have eventsEq := (Prod.mk.inj (Option.some.inj outcome)).2
    rw [← eventsEq]
    apply noAttachments.append
    · apply (applyEach_noAttachments recycleOne recycleOne_noAttachments s ids).append
      split <;> simp [noAttachments]
    · split
      · exact spellCompletion_noAttachments s src _
      · simp [noAttachments]

private theorem attachments_empty (s : GameState) {events : List Event} (h : noAttachments events) :
    attachmentReplacementFrames s events = [] := by
  unfold attachmentReplacementFrames
  apply List.flatMap_eq_nil_iff.mpr
  intro event found
  cases event <;> try rfl
  exact False.elim (h _ _ found)

private def directPrimResult (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (pr : Prim)
    (more : EffectList) : GameState × List Frame × List Event :=
  match applyPrim s p src env pr with
  | some r => (r.1, attachmentReplacementFrames r.1 r.2 ++ [.run p src env more], r.2)
  | none => (s, [.run p src env more], [Event.skipped src])

private theorem Effect.SingleRun.directPrim (pr : Prim)
    (dispatch : ∀ s p src env more,
      runEffect s p src env (.prim pr) more effectAddPolicy = directPrimResult s p src env pr more)
    (plainEvents : ∀ {s t p src env events},
      applyPrim s p src env pr = some (t, events) → noAttachments events) :
    (Effect.prim pr).SingleRun := by
  intro s p src env more
  rw [dispatch]
  unfold directPrimResult
  split
  · rename_i r applied
    rw [attachments_empty _ (plainEvents applied), List.nil_append]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

private theorem Effect.SingleRun.directRecycle (sel : Selector)
    (direct : sel = .self ∨ (∃ i, sel = .slot i) ∨ ∃ side, sel = .revealedDeck side) :
    (Effect.prim (.recycle sel)).SingleRun := by
  refine .directPrim (.recycle sel) ?_ recycle_noAttachments
  intro s p src env more
  rcases direct with rfl | ⟨i, rfl⟩ | ⟨side, rfl⟩ <;>
    simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
      effectDamageBatch?, permanentPlayEffects] <;>
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl

/-- A Limited Spell's recycle instruction creates no attachment-replacement work. -/
theorem Effect.SingleRun.recycleSelf : (Effect.prim (.recycle .self)).SingleRun :=
  .directRecycle .self (Or.inl rfl)

/-- Recycle uses the previously chosen slot and leaves the remaining instructions. -/
theorem Effect.SingleRun.recycleSlot (i : Nat) : (Effect.prim (.recycle (.slot i))).SingleRun :=
  .directRecycle (.slot i) (Or.inr (Or.inl ⟨i, rfl⟩))

/-- Recycle the selected cards from a reveal, then resume the program. -/
theorem Effect.SingleRun.recycleRevealed (side : Side) : (Effect.prim (.recycle (.revealedDeck side))).SingleRun :=
  .directRecycle (.revealedDeck side) (Or.inr (Or.inr ⟨side, rfl⟩))

private theorem drawLookedCard_noAttachments (p : PlayerId) (looked : List ObjId) (s : GameState) (id : ObjId) :
    noAttachments (drawLookedCard p looked s id).2 := by
  unfold drawLookedCard
  split
  · split <;> simp [noAttachments]
  · simp [noAttachments]

/-- Draw cards selected from a reveal without generating additional resolution frames. -/
theorem Effect.SingleRun.drawRevealed (side : Side) : (Effect.prim (.drawLooked (.revealedDeck side))).SingleRun := by
  apply Effect.SingleRun.directPrim
  · intro s p src env more
    simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
      effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro s t p src env events applied
    simp only [applyPrim, onSelected] at applied
    obtain ⟨ids, _, shape⟩ := Option.map_eq_some_iff.mp applied
    rw [← (Prod.mk.inj shape).2]
    exact applyEach_noAttachments _ (drawLookedCard_noAttachments p env.lookedCards) s ids

private theorem retainTargetSetFrame_cases (p : PlayerId) (src : ObjId) (env : Env)
    (groups : List (List ObjId)) (more : EffectList) :
    (∃ newEnv, retainTargetSetFrame p src env groups more = .run p src newEnv more) ∨
      (retainTargetSetFrame p src env groups more).isWork = false := by
  unfold retainTargetSetFrame
  dsimp only
  split
  · exact Or.inr rfl
  · exact Or.inl ⟨_, rfl⟩

/-- Target rechecking either keeps the final subset or asks which subset to keep. -/
theorem Effect.ObservedFinite.retainTargetSet (groups : List (List ObjId)) :
    (Effect.retainTargetSet groups).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  rcases retainTargetSetFrame_cases p src live groups more with ⟨retained, resumes⟩ | choice
  · refine advance_run_rule wf reads pending ?_ (fun _ route q ne => route.insert inserted q ne)
    change RunContinuation p src more keeps ([retainTargetSetFrame p src live groups more] ++ rest)
    rw [resumes]
    exact ⟨retained, rest, rfl, base⟩
  · apply advance_run_decision wf reads pending
    change (!(retainTargetSetFrame p src live groups more).isWork) = true
    rw [choice]
    rfl

/-- Any instruction that rechecks a target group is finite if its unchanged body is finite. -/
theorem EffectDef.recheckTargetGroup_observed (e : EffectDef) (s : GameState) (p : PlayerId)
    (src : ObjId) (targets : List ObjId) {program : EffectList} (finite : program.ObservedFinite) :
    (e.recheckTargetGroup s p src targets program).ObservedFinite := by
  unfold EffectDef.recheckTargetGroup
  split
  · split <;> first
      | exact finite
      | exact .cons (Effect.ObservedFinite.retainTargetSet _) finite
      | dsimp only
        split
        · exact finite
        · exact .cons (Effect.ObservedFinite.retainTargetSet _) finite
  · exact finite

/-- A dispatcher instruction with a direct continuation or a choice is finite in either case. -/
private theorem Effect.ObservedFinite.ofDecisionOrRun {effect : Effect}
    (routes : ∀ s p src env more, let frames := (runEffect s p src env effect more effectAddPolicy).2.1
      frames = [.run p src env more] ∨ ∃ f tail, frames = f :: tail ∧ f.isWork = false) :
    effect.ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  rcases routes s p src live more with resumes | ⟨f, tail, choice, decision⟩
  · refine advance_run_rule wf reads pending ?_ (fun _ route q ne => route.insert inserted q ne)
    dsimp only
    rw [resumes]
    exact ⟨live, rest, rfl, base⟩
  · apply advance_run_decision wf reads pending
    dsimp only
    rw [choice]
    simp [decision]

/-- Choosing an object either skips an unavailable choice or asks the player. -/
theorem Effect.ObservedFinite.chooseObject (side : Side) (place : Place) (filters : FilterList)
    (body : Effect) : (Effect.chooseObject side place filters body).ObservedFinite := by
  apply Effect.ObservedFinite.ofDecisionOrRun
  intro s p src env more
  let effect := Effect.chooseObject side place filters body
  let selected := requiredPlayCandidates s p src env effect effectAddPolicy <|>
    s.pickCandidates p src env side place filters (!effect.isLinkedCost)
  let frames : List Frame := match selected with
    | some [o] => [.pickDo p src env o [] effect.withPick more]
    | some (o :: other :: rest) => [.pickDo p src env o (other :: rest) effect.withPick more]
    | _ => [.run p src env more]
  have same : (runEffect s p src env effect more effectAddPolicy).2.1 = frames := by
    change (match selected with
      | some [o] => (s, [Frame.pickDo p src env o [] effect.withPick more], [])
      | some (o :: other :: rest) => (s, [.pickDo p src env o (other :: rest) effect.withPick more], [])
      | _ => (s, [.run p src env more], [Event.skipped src])).2.1 = frames
    unfold frames
    cases selected with
    | none => rfl
    | some objects =>
      cases objects with
      | nil => rfl
      | cons head rest => cases rest <;> rfl
  dsimp only
  rw [← show effect = Effect.chooseObject side place filters body from rfl, same]
  unfold frames
  cases selected with
  | none => exact Or.inl rfl
  | some objects =>
    cases objects with
    | nil => exact Or.inl rfl
    | cons first rest =>
      cases rest with
      | nil => exact Or.inr ⟨.pickDo p src env first [] effect.withPick more, [], rfl, rfl⟩
      | cons other tail => exact Or.inr ⟨.pickDo p src env first (other :: tail) effect.withPick more, [], rfl, rfl⟩

/-- Discard either skips an invalid instruction or waits for the first selected player. -/
theorem Effect.ObservedFinite.discard (who : PlayerSel) (amount : Amount) :
    (Effect.prim (.discard who amount)).ObservedFinite := by
  apply Effect.ObservedFinite.ofDecisionOrRun
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect]
  cases selected : who.resolve s p env with
  | none => exact Or.inl rfl
  | some players =>
    cases count : amount.evalS s p src env with
    | none => exact Or.inl rfl
    | some n =>
      cases players with
      | nil => exact Or.inl rfl
      | cons first rest => exact Or.inr ⟨_, _, rfl, rfl⟩

/-- An alternative with at least two branches yields before it executes a branch. -/
theorem Effect.ObservedFinite.eitherChoice (first second : Effect) (rest : EffectList) :
    (Effect.eitherOf (.cons first (.cons second rest))).ObservedFinite := by
  intro s p src env more tail keeps wf reads pending _ _
  apply advance_run_decision wf reads pending
  cases rest <;> rfl

end Riftbound

end
