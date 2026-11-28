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

/-- Each member of a list supplies the certificate for its place in the Run program. -/
theorem EffectList.ObservedFinite.ofList {effects : List Effect}
    (finite : ∀ effect ∈ effects, effect.ObservedFinite) : (EffectList.ofList effects).ObservedFinite := by
  induction effects with
  | nil => exact .nil
  | cons first later ih =>
    exact .cons (finite first List.mem_cons_self) (ih fun e mem => finite e (List.mem_cons_of_mem _ mem))

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

/-- A scheduled, finite prefix of the same Run executes before its original suffix. -/
theorem Effect.ObservedFinite.ofPrograms {effect : Effect}
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

/-- Follow the certified Runs scheduled before the original invocation. -/
private theorem advance_run_forks {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {effect : Effect} {more : EffectList} {rest frames : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons effect more) :: rest)
    (scheduled : (runEffect s p src (env.withMight s.mightTable) effect more effectAddPolicy).2.1 =
      frames ++ [.run p src (env.withMight s.mightTable) more])
    (finite : ∀ f ∈ frames, Frame.FiniteRun f) (base : keeps rest)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s (RunContinuation p src more keeps) := by
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

private theorem Effect.ObservedFinite.ofForks {effect : Effect}
    (forks : ∀ s p src env more, ∃ frames,
      (runEffect s p src env effect more effectAddPolicy).2.1 = frames ++ [.run p src env more] ∧
      ∀ f ∈ frames, Frame.FiniteRun f) :
    effect.ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  obtain ⟨frames, scheduled, finite⟩ := forks s p src (env.withMight s.mightTable) more
  exact advance_run_forks wf reads pending scheduled finite base inserted

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
      NonNeutralDecision (result.2.1 ++ rest)) :
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
    advance_observed_nonNeutralDecision mid raw.pending midWF (midCards ▸ reads) route waits
  exact ⟨t, used + later, events, by simpa only [List.append_nil] using path.append remaining, Or.inl stop⟩

/-- A runtime instruction either waits for a decision or schedules certified Runs before its suffix. -/
theorem Effect.ObservedFinite.ofDecisionOrForks {effect : Effect}
    (routes : ∀ s p src env more,
      let frames := (runEffect s p src env effect more effectAddPolicy).2.1
      (∃ forks, frames = forks ++ [.run p src env more] ∧ ∀ f ∈ forks, f.FiniteRun) ∨
        (∃ f tail, frames = f :: tail ∧ NonNeutralDecision (f :: tail))) : effect.ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  rcases routes s p src (env.withMight s.mightTable) more with ⟨forks, stack, finite⟩ | ⟨f, tail, choice, idle⟩
  · exact advance_run_forks wf reads pending stack finite base inserted
  · apply advance_run_decision wf reads pending
    dsimp only
    rw [choice]
    exact idle

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
        advance_draw_until_prepared wf reads ready tracks ⟨tail, rfl, tracked⟩
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

/-- Events that cannot schedule attachment replacements. -/
def NoAttach (events : List Event) : Prop :=
  ∀ gear unit, Event.attached gear unit ∉ events

theorem NoAttach.nil : NoAttach [] := by
  intro gear unit
  simp

theorem NoAttach.append {first other : List Event} (left : NoAttach first)
    (right : NoAttach other) : NoAttach (first ++ other) := by
  intro gear unit
  simp [left gear unit, right gear unit]

theorem NoAttach.replacementFrames {events : List Event} (noAttach : NoAttach events)
    (s : GameState) : attachmentReplacementFrames s events = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro e member
  cases e <;> try rfl
  rename_i gear unit
  exact False.elim (noAttach gear unit member)

theorem sendObj_noAttach (k : ZoneKind) (s : GameState) (id : ObjId) :
    NoAttach (sendObj k s id).2 := by
  unfold sendObj
  split
  · dsimp only
    split
    · intro gear unit
      unfold Object.ownerMoveEvents
      split <;> simp
    · exact .nil
  · exact .nil

theorem banishCardEvents_noAttach (p : PlayerId) (s : GameState) (id : ObjId)
    (moves : List Event) : NoAttach (banishCardEvents p s id moves) := by
  intro gear unit member
  unfold banishCardEvents at member
  split at member
  · obtain ⟨e, _, h⟩ := List.mem_filterMap.mp member
    split at h <;> cases h
  · contradiction

private theorem recycleOne_noAttachments (s : GameState) (id : ObjId) :
    NoAttach (recycleOne s id).2 := by
  unfold recycleOne
  split
  · dsimp only
    split
    · simp [NoAttach]
    · split <;> simp [NoAttach]
  · simp [NoAttach]

theorem applyEach_noAttach {α : Type} (g : GameState → α → GameState × List Event)
    (trusted : ∀ s a, NoAttach (g s a).2) (s : GameState) (items : List α) :
    NoAttach (applyEach g s items).2 := by
  induction items generalizing s with
  | nil => exact .nil
  | cons first next ih =>
    exact (trusted s first).append (ih (g s first).1)

private theorem spellCompletion_noAttachments (s : GameState) (src : ObjId) (events : List Event)
    (inPlace : Bool) : NoAttach (spellCompletion s src events inPlace) := by
  cases inPlace
  all_goals
    unfold spellCompletion
    simp only [Bool.false_eq_true, ite_false, ite_true]
    split
    · split
      · split <;> simp [NoAttach]
      · exact .nil
    · exact .nil

private theorem recycle_noAttachments {s t : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {events : List Event} (outcome : applyPrim s p src env (.recycle sel) = some (t, events)) :
    NoAttach events := by
  unfold applyPrim at outcome
  cases selected : Selector.eval s p src env sel with
  | none => simp [selected] at outcome
  | some ids =>
    simp only [selected, Option.map_some] at outcome
    have eventsEq := (Prod.mk.inj (Option.some.inj outcome)).2
    rw [← eventsEq]
    apply NoAttach.append
    · apply (applyEach_noAttach recycleOne recycleOne_noAttachments s ids).append
      split <;> simp [NoAttach]
    · split
      · exact spellCompletion_noAttachments s src _ true
      · simp [NoAttach]

private def directPrimResult (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (pr : Prim)
    (more : EffectList) : GameState × List Frame × List Event :=
  match applyPrim s p src env pr with
  | some r => (r.1, attachmentReplacementFrames r.1 r.2 ++ [.run p src env more], r.2)
  | none => (s, [.run p src env more], [Event.skipped src])

private theorem Effect.SingleRun.directPrim (pr : Prim)
    (dispatch : ∀ s p src env more,
      runEffect s p src env (.prim pr) more effectAddPolicy = directPrimResult s p src env pr more)
    (plainEvents : ∀ {s t p src env events},
      applyPrim s p src env pr = some (t, events) → NoAttach events) :
    (Effect.prim pr).SingleRun := by
  intro s p src env more
  rw [dispatch]
  unfold directPrimResult
  split
  · rename_i r applied
    rw [(plainEvents applied).replacementFrames _, List.nil_append]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

private theorem Effect.SingleRun.bin (sel : Selector) (direct : (Effect.prim (.bin sel)).pickSel? = none) :
    (Effect.prim (.bin sel)).SingleRun := by
  refine .directPrim (.bin sel) ?_ ?_
  · intro s p src env more
    simp only [runEffect, direct, runEffect1, runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro s t p src env events applied
    simp only [applyPrim, onSelected] at applied
    cases selected : sel.eval s p src env with
    | none => simp [selected] at applied
    | some ids =>
      simp only [selected, Option.map_some, Option.some.injEq] at applied
      rw [← (Prod.mk.inj applied).2]
      exact (applyEach_noAttach _ (sendObj_noAttach .trash) s ids).append
        (spellCompletion_noAttachments s src _ false)

private theorem Effect.SingleRun.castInline (sel : Selector)
    (direct : (Effect.prim (.castInline sel)).pickSel? = none) : (Effect.prim (.castInline sel)).SingleRun := by
  intro s p src env more
  simp only [runEffect, direct, runEffect1, runPrimEffect, castInlineStep]
  split
  · unfold castLimitedStep
    dsimp only
    split
    · exact ⟨_, _, rfl⟩
    · split <;> exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

private theorem Effect.SingleRun.selectedPrim (pr : Prim) (selector : Selector)
    (changeObject : PlayerId → Env → GameState → ObjId → GameState × List Event)
    (direct : (Effect.prim pr).pickSel? = none)
    (dispatch : ∀ s p src env more,
      runPrimEffect s p src env pr more effectAddPolicy = directPrimResult s p src env pr more)
    (targets : ∀ s p src env,
      applyPrim s p src env pr = onSelected s p src env selector (changeObject p env))
    (plain : ∀ p env s id, NoAttach (changeObject p env s id).2) :
    (Effect.prim pr).SingleRun := by
  apply Effect.SingleRun.directPrim pr
  · intro s p src env more
    simp only [runEffect, direct]
    exact dispatch s p src env more
  · intro s t p src env events outcome
    rw [targets] at outcome
    unfold onSelected at outcome
    cases selected : selector.eval s p src env with
    | none => simp [selected] at outcome
    | some ids =>
      simp only [selected, Option.map_some, Option.some.injEq] at outcome
      rw [← (Prod.mk.inj outcome).2]
      exact applyEach_noAttach _ (plain p env) s ids

theorem setExhausted_noAttach (exhausted : Bool) (s : GameState) (id : ObjId) :
    NoAttach (setExhausted exhausted s id).2 := by
  unfold setExhausted
  split
  · cases exhausted <;> split <;> simp [NoAttach]
  · simp [NoAttach]

private theorem replaceChosenHarm_noAttach (env : Env)
    (changeObject : GameState → ObjId → GameState × List Event)
    (plain : ∀ s id, NoAttach (changeObject s id).2) (s : GameState) (id : ObjId) :
    NoAttach (replaceChosenHarm env changeObject s id).2 := by
  unfold replaceChosenHarm
  split
  · split
    · exact .nil
    · exact plain s id
  · exact plain s id

private theorem Effect.SingleRun.ready (sel : Selector) (direct : (Effect.prim (.ready sel)).pickSel? = none) :
    (Effect.prim (.ready sel)).SingleRun := by
  refine .selectedPrim (.ready sel) sel (fun _ _ => readyEffect) direct ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro _ _ s id
    unfold readyEffect
    split
    · simp [NoAttach]
    · exact setExhausted_noAttach false s id

private theorem Effect.SingleRun.exhaust (sel : Selector) (direct : (Effect.prim (.exhaust sel)).pickSel? = none) :
    (Effect.prim (.exhaust sel)).SingleRun := by
  refine .selectedPrim (.exhaust sel) sel (fun _ _ => setExhausted true) direct ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro _ _ s id
    exact setExhausted_noAttach true s id

private theorem Effect.SingleRun.buff (sel : Selector) (direct : (Effect.prim (.buff sel)).pickSel? = none) :
    (Effect.prim (.buff sel)).SingleRun := by
  refine .selectedPrim (.buff sel) sel (fun p _ s id => buffObj s id (some p)) direct
    ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro p _ s id
    unfold buffObj
    dsimp only
    split
    · split
      · simp [NoAttach]
      · split <;> simp [NoAttach]
    · simp [NoAttach]

private theorem Effect.SingleRun.stun (sel : Selector) (direct : (Effect.prim (.stun sel)).pickSel? = none) :
    (Effect.prim (.stun sel)).SingleRun := by
  refine .selectedPrim (.stun sel) sel (fun p env s id => stunObj s id env (some p)) direct
    ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro p env s id
    unfold stunObj
    split
    · exact replaceChosenHarm_noAttach env _ (fun _ _ => by simp [NoAttach]) s id
    · exact .nil

private theorem Effect.SingleRun.returnToHand (sel : Selector)
    (direct : (Effect.prim (.returnToHand sel)).pickSel? = none) :
    (Effect.prim (.returnToHand sel)).SingleRun := by
  refine .selectedPrim (.returnToHand sel) sel (fun _ env => replaceChosenHarm env (sendObj .hand)) direct
    ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro _ env s id
    exact replaceChosenHarm_noAttach env (sendObj .hand) (sendObj_noAttach .hand) s id

private theorem Effect.SingleRun.banish (sel : Selector) (direct : (Effect.prim (.banish sel)).pickSel? = none) :
    (Effect.prim (.banish sel)).SingleRun := by
  refine .selectedPrim (.banish sel) sel (fun p _ => banishObj p) direct ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro p _ s id
    exact (sendObj_noAttach .banishment s id).append (banishCardEvents_noAttach p s id _)

private theorem Effect.SingleRun.topdeck (sel : Selector) (direct : (Effect.prim (.topdeck sel)).pickSel? = none) :
    (Effect.prim (.topdeck sel)).SingleRun := by
  refine .selectedPrim (.topdeck sel) sel (fun _ _ => sendObj .mainDeck) direct ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro _ _ s id
    exact sendObj_noAttach .mainDeck s id

private theorem Effect.SingleRun.empower (sel : Selector) (direct : (Effect.prim (.empower sel)).pickSel? = none) :
    (Effect.prim (.empower sel)).SingleRun := by
  refine .selectedPrim (.empower sel) sel (fun p _ => empowerObj p) direct ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro p _ s id
    unfold empowerObj
    split
    · split <;> simp [NoAttach]
    · exact .nil

private theorem Effect.SingleRun.disempower (sel : Selector)
    (direct : (Effect.prim (.disempower sel)).pickSel? = none) : (Effect.prim (.disempower sel)).SingleRun := by
  refine .selectedPrim (.disempower sel) sel (fun _ _ => disempowerObj) direct ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro _ _ _ _
    exact .nil

private theorem Effect.SingleRun.spendBuff (sel : Selector)
    (direct : (Effect.prim (.spendBuff sel)).pickSel? = none) : (Effect.prim (.spendBuff sel)).SingleRun := by
  refine .selectedPrim (.spendBuff sel) sel (fun _ _ => unbuffObj) direct ?_ (fun _ _ _ _ => rfl) ?_
  · intro s p src env more
    simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro _ _ s id
    unfold unbuffObj
    dsimp only
    split
    · split <;> simp [NoAttach]
    · exact .nil

/-- A turn effect records its note before resuming the Run, including the hidden-play events. -/
theorem Effect.SingleRun.turnEffect (effect : TurnEffect) : (Effect.prim (.turnEffect effect)).SingleRun := by
  refine .directPrim (.turnEffect effect) ?_ ?_
  · intro s p src env more
    simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
      effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro s t p src env events applied
    simp only [applyPrim, Option.some.injEq, Prod.mk.injEq] at applied
    rw [← applied.2]
    split
    · split <;> simp [NoAttach]
    · exact .nil

/-- Hiding a selected card moves it without scheduling an additional attachment action. -/
theorem Effect.SingleRun.hideAt (cards battlefields : Selector) : (Effect.prim (.hideAt cards battlefields)).SingleRun := by
  refine .directPrim (.hideAt cards battlefields) ?_ ?_
  · intro s p src env more
    simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
      effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro s t p src env events applied
    simp only [applyPrim] at applied
    split at applied
    · rename_i field _ _
      unfold onSelected at applied
      cases selected : cards.eval s p src env with
      | none => simp [selected] at applied
      | some ids =>
        simp only [selected, Option.map_some, Option.some.injEq] at applied
        rw [← (Prod.mk.inj applied).2]
        apply applyEach_noAttach (hideObj field) ?_ s ids
        intro board id
        unfold hideObj
        split
        · split
          · exact .nil
          · split <;> simp [NoAttach]
        · exact .nil
    · contradiction

private theorem Effect.pickSel_one {effect : Effect} {selector : Selector}
    (pick : effect.pickSel? = some selector) :
    ∃ side place filters, selector = .pick .one side place filters := by
  unfold Effect.pickSel? at pick
  split at pick
  all_goals
    first
    | contradiction
    | obtain rfl := Option.some.inj pick
      exact ⟨_, _, _, rfl⟩
    | split at pick
      · obtain rfl := Option.some.inj pick
        exact ⟨_, _, _, rfl⟩
      · contradiction

/-- An instruction can resolve its direct or bound effect, skip, or ask about a resolution pick. -/
theorem Effect.ObservedFinite.withResolutionPick (effect : Effect)
    (direct : effect.pickSel? = none → effect.ObservedFinite) (bound : effect.withPick.ObservedFinite)
    (automatic : ∀ side place filters body, effect ≠ .chooseObject side place filters body) :
    effect.ObservedFinite := by
  cases pick : effect.pickSel? with
  | none => exact direct pick
  | some selector =>
    obtain ⟨side, place, filters, rfl⟩ := Effect.pickSel_one pick
    intro s p src env more rest keeps wf reads pending base inserted
    let live := env.withMight s.mightTable
    let selected := requiredPlayCandidates s p src live effect effectAddPolicy <|>
      s.pickCandidates p src live side place filters (!effect.isLinkedCost)
    let frames : List Frame := match selected with
      | some [o] => [.run p src (live.bindPick o (effect.pickIsTarget s o)) (.cons effect.withPick more)]
      | some (o :: other :: rest) => [.pickDo p src live o (other :: rest) effect.withPick more]
      | _ => [.run p src live more]
    have single (o : ObjId) :
        (match effect with
        | .chooseObject .. => (s, [Frame.pickDo p src live o [] effect.withPick more], [])
        | _ => (s, [.run p src (live.bindPick o (effect.pickIsTarget s o)) (.cons effect.withPick more)],
            effect.pickEvents s p src o)) =
          (s, [.run p src (live.bindPick o (effect.pickIsTarget s o)) (.cons effect.withPick more)],
            effect.pickEvents s p src o) := by
      cases effect <;> try rfl
      case chooseObject who where_ fs body =>
        exact False.elim (automatic who where_ fs body rfl)
    have route : (runEffect s p src live effect more effectAddPolicy).2.1 = frames := by
      unfold runEffect
      rw [pick]
      change (match selected with
        | some [o] =>
          match effect with
          | .chooseObject .. => (s, [Frame.pickDo p src live o [] effect.withPick more], [])
          | _ => (s, [.run p src (live.bindPick o (effect.pickIsTarget s o)) (.cons effect.withPick more)],
              effect.pickEvents s p src o)
        | some (o :: other :: rest) => (s, [.pickDo p src live o (other :: rest) effect.withPick more], [])
        | _ => (s, [.run p src live more], [Event.skipped src])).2.1 = frames
      unfold frames
      cases selected with
      | none => rfl
      | some objects =>
        cases objects with
        | nil => rfl
        | cons first rest =>
          cases rest with
          | nil => exact congrArg (fun result => result.2.1) (single first)
          | cons other later => rfl
    have resumes (sel : frames = [.run p src live more]) :
        AdvanceTo s (RunContinuation p src more keeps) := by
      apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
      change RunContinuation p src more keeps ((runEffect s p src live effect more effectAddPolicy).2.1 ++ rest)
      rw [route, sel]
      exact ⟨live, rest, rfl, base⟩
    cases candidates : selected with
    | none => exact resumes (by simp [frames, candidates])
    | some objects =>
      cases objects with
      | nil => exact resumes (by simp [frames, candidates])
      | cons first others =>
        cases others with
        | nil =>
          let boundProgram := EffectList.cons effect.withPick more
          have firstRun : AdvanceTo s (RunContinuation p src boundProgram keeps) := by
            apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
            change RunContinuation p src boundProgram keeps
              ((runEffect s p src live effect more effectAddPolicy).2.1 ++ rest)
            rw [route]
            exact ⟨live.bindPick first (effect.pickIsTarget s first), rest, by simp [frames, candidates, boundProgram], base⟩
          apply firstRun.then reads
          intro t safe checked continued
          obtain ⟨chosen, tail, stack, kept⟩ := continued
          exact bound t p src chosen more tail keeps safe checked stack kept inserted
        | cons another later =>
          have waiting : NonNeutralDecision (frames ++ rest) := by simp [frames, candidates, NonNeutralDecision, Frame.isWork]
          apply advance_run_decision wf reads pending
          change NonNeutralDecision ((runEffect s p src live effect more effectAddPolicy).2.1 ++ rest)
          rwa [route]

private theorem Effect.ObservedFinite.selectedPrimitive (pr : Prim)
    (direct : (Effect.prim pr).pickSel? = none → (Effect.prim pr).SingleRun)
    (bound : (Effect.prim pr).withPick.SingleRun) : (Effect.prim pr).ObservedFinite :=
  .withResolutionPick _ (fun h => (direct h).observed) bound.observed
    (fun _ _ _ _ impossible => by cases impossible)

private theorem Effect.SingleRun.copyAttachedFrom (sel : Selector)
    (direct : (Effect.prim (.copyAttachedFrom sel)).pickSel? = none) :
    (Effect.prim (.copyAttachedFrom sel)).SingleRun := by
  refine .directPrim (.copyAttachedFrom sel) ?_ ?_
  · intro s p src env more
    simp only [runEffect, direct, runEffect1, runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro s t p src env events applied
    simp only [applyPrim, onSelected] at applied
    cases selected : sel.eval s p src env with
    | none => simp [selected] at applied
    | some models =>
      simp only [selected, Option.map_some, Option.some.injEq] at applied
      rw [← (Prod.mk.inj applied).2]
      apply applyEach_noAttach (copyAttachedUnit src) (fun board model => ?_) s models
      unfold copyAttachedUnit
      split
      · split <;> exact .nil
      · exact .nil

private theorem Effect.SingleRun.detach (sel : Selector)
    (direct : (Effect.prim (.detach sel)).pickSel? = none) :
    (Effect.prim (.detach sel)).SingleRun := by
  refine .selectedPrim (.detach sel) sel (fun _ _ => detachObj) direct ?_
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => .nil)
  intro s p src env more
  simp only [runPrimEffect, effectDamageBatch?, permanentPlayEffects]
  by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl

/-- Removing an attachment also goes through the observed target-selection rules. -/
theorem Effect.ObservedFinite.detach (sel : Selector) : (Effect.prim (.detach sel)).ObservedFinite :=
  .selectedPrimitive (.detach sel) (Effect.SingleRun.detach sel) (Effect.SingleRun.detach (.var pickVar) rfl)

/-- Copying a model for attached Equipment can wait for a target, or copy a bound target
and continue without creating another attachment replacement. -/
theorem Effect.ObservedFinite.copyAttachedFrom (sel : Selector) :
    (Effect.prim (.copyAttachedFrom sel)).ObservedFinite :=
  .selectedPrimitive (.copyAttachedFrom sel) (Effect.SingleRun.copyAttachedFrom sel)
    (Effect.SingleRun.copyAttachedFrom (.var pickVar) rfl)

/-- Applying a linked copy changes the selected tokens without another attachment replacement. -/
theorem Effect.ObservedFinite.becomeCopy (targets source : Selector) :
    (Effect.prim (.becomeCopy targets source)).ObservedFinite := by
  apply Effect.SingleRun.observed
  refine .directPrim (.becomeCopy targets source) ?_ ?_
  · intro s p src env more
    simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
      effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro s t p src env events applied
    simp only [applyPrim] at applied
    split at applied
    · rename_i model _ _
      unfold onSelected at applied
      cases selected : targets.eval s p src env with
      | none => simp [selected] at applied
      | some objects =>
        simp only [selected, Option.map_some, Option.some.injEq] at applied
        rw [← (Prod.mk.inj applied).2]
        apply applyEach_noAttach (becomeCopyOf model) (fun board id => ?_) s objects
        unfold becomeCopyOf
        split <;> exact .nil
    · contradiction

/-- Binning selected objects also records completion of any resolving Spell. -/
theorem Effect.ObservedFinite.bin (sel : Selector) : (Effect.prim (.bin sel)).ObservedFinite :=
  .selectedPrimitive (.bin sel) (Effect.SingleRun.bin sel) (Effect.SingleRun.bin (.var pickVar) rfl)

/-- Casting a Spell through the deferred declaration rule resumes the originating effect. -/
theorem Effect.ObservedFinite.castInline (sel : Selector) : (Effect.prim (.castInline sel)).ObservedFinite :=
  .selectedPrimitive (.castInline sel) (Effect.SingleRun.castInline sel)
    (Effect.SingleRun.castInline (.var pickVar) rfl)

/-- The primitive costs handled directly by the linked-action Run rule. -/
def Prim.linkedCostSupported : Prim → Bool
  | .banish _ | .disempower _ | .exhaust _ | .spendBuff _ => true
  | _ => false

private theorem Effect.ObservedFinite.linkedCostDirect (cost : Prim) {body : Effect}
    (supported : cost.linkedCostSupported = true)
    (direct : (Effect.doThen (.prim cost) body).pickSel? = none) (finite : body.ObservedFinite) :
    (Effect.doThen (.prim cost) body).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  have runs : (runEffect s p src env (.doThen (.prim cost) body) more effectAddPolicy).2.1 =
      [.run p src env (if (linkedAction s p src env cost).2.1 then .cons body more else more)] := by
    simp only [runEffect, direct]
    cases cost <;> first | rfl | (simp [Prim.linkedCostSupported] at supported)
  rw [runs]
  cases paid : (linkedAction s p src env cost).2.1
  · exact ⟨.nil, .nil, rfl⟩
  · exact ⟨.cons body .nil, .cons finite .nil, rfl⟩

/-- The linked follow-up runs only if the cost actually happened. A resolution choice,
when the rule offers one, is an intermediate stopping point. -/
theorem Effect.ObservedFinite.linkedCost (cost : Prim) {body : Effect}
    (supported : cost.linkedCostSupported = true) (finite : body.ObservedFinite) :
    (Effect.doThen (.prim cost) body).ObservedFinite := by
  apply Effect.ObservedFinite.withResolutionPick
  · exact fun direct => Effect.ObservedFinite.linkedCostDirect cost supported direct finite
  · change (Effect.doThen (.prim (cost.withSel (.var pickVar))) body).ObservedFinite
    refine Effect.ObservedFinite.linkedCostDirect _ ?_ ?_ finite
    · cases cost <;> simp_all [Prim.linkedCostSupported, Prim.withSel]
    · cases cost <;> simp_all [Prim.linkedCostSupported, Prim.withSel, Effect.pickSel?]
  · intro _ _ _ _ impossible
    cases impossible

/-- Readying selected objects stops at any resolution choice or resumes the program. -/
theorem Effect.ObservedFinite.ready (sel : Selector) : (Effect.prim (.ready sel)).ObservedFinite :=
  .selectedPrimitive (.ready sel) (Effect.SingleRun.ready sel) (Effect.SingleRun.ready (.var pickVar) rfl)

/-- Exhausting selected objects stops at any resolution choice or resumes the program. -/
theorem Effect.ObservedFinite.exhaust (sel : Selector) : (Effect.prim (.exhaust sel)).ObservedFinite :=
  .selectedPrimitive (.exhaust sel) (Effect.SingleRun.exhaust sel) (Effect.SingleRun.exhaust (.var pickVar) rfl)

/-- Buffing selected objects stops at any resolution choice or resumes the program. -/
theorem Effect.ObservedFinite.buff (sel : Selector) : (Effect.prim (.buff sel)).ObservedFinite :=
  .selectedPrimitive (.buff sel) (Effect.SingleRun.buff sel) (Effect.SingleRun.buff (.var pickVar) rfl)

/-- Stunning selected objects stops at any resolution choice or resumes the program. -/
theorem Effect.ObservedFinite.stun (sel : Selector) : (Effect.prim (.stun sel)).ObservedFinite :=
  .selectedPrimitive (.stun sel) (Effect.SingleRun.stun sel) (Effect.SingleRun.stun (.var pickVar) rfl)

/-- Returning selected objects to their owners' hands reaches a choice or the next instruction. -/
theorem Effect.ObservedFinite.returnToHand (sel : Selector) : (Effect.prim (.returnToHand sel)).ObservedFinite :=
  .selectedPrimitive (.returnToHand sel) (Effect.SingleRun.returnToHand sel)
    (Effect.SingleRun.returnToHand (.var pickVar) rfl)

/-- Banishing selected objects reaches a choice or the next instruction. -/
theorem Effect.ObservedFinite.banish (sel : Selector) : (Effect.prim (.banish sel)).ObservedFinite :=
  .selectedPrimitive (.banish sel) (Effect.SingleRun.banish sel) (Effect.SingleRun.banish (.var pickVar) rfl)

/-- Putting selected objects on top of their owners' decks reaches a choice or the next instruction. -/
theorem Effect.ObservedFinite.topdeck (sel : Selector) : (Effect.prim (.topdeck sel)).ObservedFinite :=
  .selectedPrimitive (.topdeck sel) (Effect.SingleRun.topdeck sel) (Effect.SingleRun.topdeck (.var pickVar) rfl)

/-- Empower follows the selected objects or stops for a choice during resolution. -/
theorem Effect.ObservedFinite.empower (sel : Selector) : (Effect.prim (.empower sel)).ObservedFinite :=
  .selectedPrimitive (.empower sel) (Effect.SingleRun.empower sel) (Effect.SingleRun.empower (.var pickVar) rfl)

/-- Removing Empower follows the selected objects or stops for a choice during resolution. -/
theorem Effect.ObservedFinite.disempower (sel : Selector) : (Effect.prim (.disempower sel)).ObservedFinite :=
  .selectedPrimitive (.disempower sel) (Effect.SingleRun.disempower sel) (Effect.SingleRun.disempower (.var pickVar) rfl)

/-- Spending a Buff follows the selected objects or stops for a choice during resolution. -/
theorem Effect.ObservedFinite.spendBuff (sel : Selector) : (Effect.prim (.spendBuff sel)).ObservedFinite :=
  .selectedPrimitive (.spendBuff sel) (Effect.SingleRun.spendBuff sel) (Effect.SingleRun.spendBuff (.var pickVar) rfl)

/-- Awarding points consumes one Run step before any resulting win is observed. -/
theorem Effect.SingleRun.score (who : PlayerSel) (amount : Amount) :
    (Effect.prim (.score who amount)).SingleRun := by
  refine .directPrim (.score who amount) ?_ ?_
  · intro s p src env more
    simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
      effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro s t p src env events outcome gear unit attached
    cases selected : who.resolve s p env <;> cases count : amount.evalS s p src env <;>
      simp only [applyPrim, selected, count, Option.bind_none, Option.bind_some,
        Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at outcome
    rw [← outcome.2] at attached
    split at attached
    · exact List.not_mem_nil attached
    · obtain ⟨_, _, impossible⟩ := List.mem_map.mp attached
      cases impossible

/-- A declared win consumes one Run step before the observer clears the unfinished work. -/
theorem Effect.SingleRun.win (who : PlayerSel) : (Effect.prim (.win who)).SingleRun := by
  refine .directPrim (.win who) ?_ ?_
  · intro s p src env more
    simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
      effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro s t p src env events outcome gear unit attached
    cases selected : who.resolve s p env with
    | none => simp [applyPrim, selected] at outcome
    | some candidates =>
      simp only [applyPrim, selected, Option.map_some, Option.some.injEq, Prod.mk.injEq] at outcome
      rw [← outcome.2] at attached
      obtain ⟨_, _, side⟩ := List.mem_flatMap.mp attached
      obtain ⟨_, _, impossible⟩ := List.mem_map.mp side
      cases impossible

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
    NoAttach (drawLookedCard p looked s id).2 := by
  unfold drawLookedCard
  split
  · split <;> simp [NoAttach]
  · simp [NoAttach]

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
    exact applyEach_noAttach _ (drawLookedCard_noAttachments p env.lookedCards) s ids

private theorem retainTargetSetFrame_cases (p : PlayerId) (src : ObjId) (env : Env)
    (groups : List (List ObjId)) (more : EffectList) :
    (∃ newEnv, retainTargetSetFrame p src env groups more = .run p src newEnv more) ∨
      NonNeutralDecision [retainTargetSetFrame p src env groups more] := by
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
    exact choice

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
      (∃ nextEnv, frames = [.run p src nextEnv more]) ∨
        ∃ f tail, frames = f :: tail ∧ NonNeutralDecision (f :: tail)) :
    effect.ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  rcases routes s p src live more with ⟨nextEnv, resumes⟩ | ⟨f, tail, choice, decision⟩
  · refine advance_run_rule wf reads pending ?_ (fun _ route q ne => route.insert inserted q ne)
    dsimp only
    rw [resumes]
    exact ⟨nextEnv, rest, rfl, base⟩
  · apply advance_run_decision wf reads pending
    dsimp only
    rw [choice]
    exact decision

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
  | none => exact Or.inl ⟨env, rfl⟩
  | some objects =>
    cases objects with
    | nil => exact Or.inl ⟨env, rfl⟩
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
  | none => exact Or.inl ⟨env, rfl⟩
  | some players =>
    cases count : amount.evalS s p src env with
    | none => exact Or.inl ⟨env, rfl⟩
    | some n =>
      cases players with
      | nil => exact Or.inl ⟨env, rfl⟩
      | cons first rest => exact Or.inr ⟨_, _, rfl, rfl⟩

/-- An alternative with at least two branches yields before it executes a branch. -/
theorem Effect.ObservedFinite.eitherChoice (first second : Effect) (rest : EffectList) :
    (Effect.eitherOf (.cons first (.cons second rest))).ObservedFinite := by
  intro s p src env more tail keeps wf reads pending _ _
  apply advance_run_decision wf reads pending
  cases rest <;> rfl

/-- Declining is always offered. If it is the only option, execute it directly. -/
private theorem Effect.ObservedFinite.eitherWithDecline (options : List Effect) :
    (Effect.eitherOf (EffectList.ofList (options ++ [.nop]))).ObservedFinite := by
  cases options with
  | nil => exact .eitherOf (.cons Effect.SingleRun.nop.observed .nil)
  | cons first rest =>
    cases rest with
    | nil => exact .eitherChoice first .nop .nil
    | cons second later => exact .eitherChoice first second (EffectList.ofList (later ++ [.nop]))

/-- An unfunded finalization rechecks its plan, can wait for a death replacement, and binds
the identifier of the permanent that enters play on success. -/
theorem Effect.ObservedFinite.finishReducedPermanent (card : ObjId) (terms : EffectPlayTerms)
    (plan : ReducedPermanentPlay) : (Effect.finishReducedPermanent card terms plan).ObservedFinite := by
  apply Effect.ObservedFinite.ofDecisionOrRun
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, runEffect1]
  by_cases valid : (permanentPlayPlans s p card terms).contains plan = true
  · rw [ite_eq_left valid]
    cases pendingCost : permanentDeathCostChoice s card plan with
    | none =>
      cases applied : applyReducedPermanent s p card plan with
      | none => exact Or.inl ⟨env, rfl⟩
      | some result =>
        obtain ⟨next, entered, events⟩ := result
        exact Or.inl ⟨env.bind pickVar (.obj entered), rfl⟩
    | some replacement =>
      obtain ⟨victim, controller, first, other⟩ := replacement
      exact Or.inr ⟨_, _, rfl, rfl⟩
  · rw [ite_eq_right valid]
    exact Or.inl ⟨env, rfl⟩

/-- The funded finalization either waits at the same replacement decision or evaluates the
atomic payment and play, preserving the caller's program. -/
theorem Effect.ObservedFinite.finishFundedPermanent (card : ObjId) (terms : EffectPlayTerms)
    (plan : ReducedPermanentPlay) (adds : List EffectAdd) :
    (Effect.finishFundedPermanent card terms plan adds).ObservedFinite := by
  apply Effect.ObservedFinite.ofDecisionOrRun
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, runEffect1]
  cases pendingCost : permanentDeathCostChoice s card plan with
  | none =>
    cases applied : finishFundedPermanentPlay s p card terms plan adds effectAddPolicy with
    | none => exact Or.inl ⟨env, rfl⟩
    | some result =>
      obtain ⟨next, entered, events⟩ := result
      exact Or.inl ⟨env.bind pickVar (.obj entered), rfl⟩
  | some replacement =>
    obtain ⟨victim, controller, first, other⟩ := replacement
    exact Or.inr ⟨_, _, rfl, rfl⟩

/-- The ordinary permanent planner executes its only available plan or waits at a choice. -/
theorem Effect.ObservedFinite.planPermanentPlay (card : ObjId) (terms : EffectPlayTerms) :
    (Effect.planPermanentPlay card terms).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  cases plans : permanentPlayPlans s p card terms with
  | nil => exact ⟨.nil, .nil, by simp [runEffect, Effect.pickSel?, runEffect1, plans, EffectList.append]⟩
  | cons first rest =>
    let plans' := first :: rest
    let options := plans'.map (Effect.finishReducedPermanent card terms)
    let decline := if plans'.all (fun plan => !plan.battlefieldFees.isEmpty) then [Effect.nop] else []
    have finite : (EffectList.ofList (options ++ decline)).ObservedFinite := by
      apply EffectList.ObservedFinite.ofList
      intro effect present
      rcases List.mem_append.mp present with allowed | declined
      · obtain ⟨plan, _, rfl⟩ := List.mem_map.mp allowed
        exact .finishReducedPermanent card terms plan
      · dsimp only [decline] at declined
        split at declined
        · obtain rfl := List.mem_singleton.mp declined
          exact Effect.SingleRun.nop.observed
        · contradiction
    exact ⟨.cons (.eitherOf (EffectList.ofList (options ++ decline))) .nil, .cons (.eitherOf finite) .nil,
      by simp [runEffect, Effect.pickSel?, runEffect1, plans, plans', options, decline, EffectList.append]⟩

/-- A projected funding action never executes a second projection automatically. Decline is
always available, so asking about another Add needs a decision even if it is the only Add. -/
theorem Effect.ObservedFinite.fundPermanentFromEffect (card : ObjId) (terms : EffectPlayTerms)
    (plan : ReducedPermanentPlay) (adds : List EffectAdd) :
    (Effect.fundPermanentFromEffect card terms plan adds).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  let options := fundPermanentOptions s p card terms plan adds effectAddPolicy
  have includesDecline : ∃ later, options = later ++ [.nop] := by
    unfold options fundPermanentOptions
    split
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨[], rfl⟩
    · exact ⟨[], rfl⟩
  obtain ⟨later, offered⟩ := includesDecline
  refine ⟨.cons (.eitherOf (EffectList.ofList options)) .nil, ?_, rfl⟩
  rw [offered]
  exact .cons (.eitherWithDecline later) .nil

/-- Offering an already fundable play reaches its required choice or proceeds with the
single certified option. -/
theorem fundedPermanentOptions_observedFinite (s : GameState) (p : PlayerId) (card : ObjId)
    (terms : EffectPlayTerms) (funding : EffectAddPolicy) :
    (fundedPermanentOptions s p card terms funding).ObservedFinite := by
  unfold fundedPermanentOptions
  apply Effect.ObservedFinite.eitherOf
  apply EffectList.ObservedFinite.ofList
  intro effect present
  rcases List.mem_append.mp present with offered | declined
  · obtain ⟨⟨plan, needsAdds⟩, _, rfl⟩ := List.mem_map.mp offered
    cases needsAdds
    · exact .finishFundedPermanent card terms plan []
    · exact .fundPermanentFromEffect card terms plan []
  · split at declined
    · obtain rfl := List.mem_singleton.mp declined
      exact Effect.SingleRun.nop.observed
    · contradiction

/-- A permanent previously Banished by an effect uses the certified funding options. -/
theorem Effect.ObservedFinite.planBanishReplay (card : ObjId) (location : Option ObjId) :
    (Effect.planBanishReplay card location).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  let terms : EffectPlayTerms := {
    price := .ignoreBase
    requirements := [none :: location.toList.map some] ++ env.hiddenPlayRequirements }
  let options := fundedPermanentOptions s p card terms effectAddPolicy
  exact ⟨.cons options .nil, .cons (fundedPermanentOptions_observedFinite s p card terms _) .nil, rfl⟩

private theorem EffectList.ObservedFinite.permanentPlans (cards : List ObjId) (terms : EffectPlayTerms) :
    (EffectList.ofList (cards.map (Effect.planPermanentPlay · terms))).ObservedFinite := by
  apply EffectList.ObservedFinite.ofList
  intro e included
  obtain ⟨card, _, rfl⟩ := List.mem_map.mp included
  exact .planPermanentPlay card terms

private theorem Effect.ObservedFinite.playAtBaseDirect (sel : Selector)
    (direct : (Effect.prim (.playAtBase sel)).pickSel? = none) :
    (Effect.prim (.playAtBase sel)).ObservedFinite := by
  apply Effect.ObservedFinite.ofForks
  intro s p src env more
  let terms : EffectPlayTerms := { price := .ignoreBase, requirements := [none] :: env.hiddenPlayRequirements }
  let program := EffectList.ofList (((sel.eval s p src env).getD []).map (Effect.planPermanentPlay · terms))
  refine ⟨[.run p src env program], ?_, ?_⟩
  · simp only [runEffect, direct, runEffect1, runPrimEffect, effectDamageBatch?, permanentPlayEffects]
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;> rfl
  · intro frame member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, _, _, _, rfl, .permanentPlans _ terms⟩

/-- Playing at the Base uses the permanent planner, including a resolution pick if needed. -/
theorem Effect.ObservedFinite.playAtBase (sel : Selector) : (Effect.prim (.playAtBase sel)).ObservedFinite :=
  .withResolutionPick _ (.playAtBaseDirect sel) (.playAtBaseDirect (.var pickVar) rfl)
    (fun _ _ _ _ impossible => by cases impossible)

/-- An actual Play whose current dispatch neither asks to pick an object nor enters the
Spell-specific route can run its permanent plans and resume its caller. -/
theorem advance_run_playPermanent {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {more : EffectList} {rest : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons (.prim (.play sel)) more) :: rest)
    (direct : (Effect.prim (.play sel)).pickSel? = none)
    (noSpell : playSpellStep s p src (env.withMight s.mightTable) sel more effectAddPolicy = none)
    (base : keeps rest) (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s (RunContinuation p src more keeps) := by
  let live := env.withMight s.mightTable
  have noInline : playSpellStep s p src live sel more effectAddPolicy = none := noSpell
  cases planned : permanentPlayEffects s p src live (.play sel) with
  | none =>
    apply advance_run_rule wf reads pending ?_ (fun _ track q ne => track.insert inserted q ne)
    change RunContinuation p src more keeps
      ((runEffect s p src live (.prim (.play sel)) more effectAddPolicy).2.1 ++ rest)
    simp only [runEffect, direct, runEffect1, runPrimEffect, noInline, planned]
    split <;> exact ⟨live, rest, rfl, base⟩
  | some program =>
    obtain ⟨context, instructions⟩ := program
    have finite : instructions.ObservedFinite := by
      unfold permanentPlayEffects at planned
      dsimp only at planned
      split at planned
      · rw [← (Prod.mk.inj (Option.some.inj planned)).2]
        exact .permanentPlans _ _
      · contradiction
    apply advance_run_forks (frames := [.run p src context instructions]) wf reads pending ?_ ?_ base inserted
    · change (runEffect s p src live (.prim (.play sel)) more effectAddPolicy).2.1 =
        [.run p src context instructions] ++ [.run p src live more]
      simp only [runEffect, direct, runEffect1, runPrimEffect, noInline, planned, List.cons_append, List.nil_append]
    · intro f member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_, _, _, _, rfl, finite⟩

/-- Paying a cost takes the unique payment or waits for a choice among several payments. -/
theorem Effect.ObservedFinite.payThen (cost : Cost) (gearPower : Bool) {body : Effect}
    (finite : body.ObservedFinite) : (Effect.payThen cost body gearPower).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  cases payments : resolutionPayments s p src cost gearPower with
  | nil => exact ⟨.nil, .nil, by simp [runEffect, Effect.pickSel?, runEffect1, payments, EffectList.append]⟩
  | cons first rest =>
    cases rest with
    | nil =>
      obtain ⟨symbols, pool⟩ := first
      exact ⟨.cons body .nil, .cons finite .nil,
        by simp [runEffect, Effect.pickSel?, runEffect1, payments, EffectList.append]⟩
    | cons second later =>
      let one := Effect.paySelected first.1 body gearPower
      let two := Effect.paySelected second.1 body gearPower
      let rest := EffectList.ofList (later.map (fun plan => Effect.paySelected plan.1 body gearPower))
      exact ⟨.cons (.eitherOf (.cons one (.cons two rest))) .nil, .cons (.eitherChoice one two rest) .nil,
        by simp [runEffect, Effect.pickSel?, runEffect1, payments, EffectList.append, EffectList.ofList, one, two, rest]⟩

/-- Resolving a selected payment either executes the checked body or skips it if payment fails. -/
theorem Effect.ObservedFinite.paySelected (cost : Cost) (gearPower : Bool) {body : Effect}
    (finite : body.ObservedFinite) : (Effect.paySelected cost body gearPower).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  cases payment : spendResolutionPayment s p src cost gearPower with
  | none => exact ⟨.nil, .nil, by simp [runEffect, Effect.pickSel?, runEffect1, payment, EffectList.append]⟩
  | some pool => exact ⟨.cons body .nil, .cons finite .nil,
      by simp [runEffect, Effect.pickSel?, runEffect1, payment, EffectList.append]⟩

end Riftbound

end
