module

public import Riftbound.Invariant.WorkPrefix

/-!
# Termination of effect control flow (I12)

These lemmas describe finite paths through the actual effect dispatcher. Arbitrary counts and
selections may duplicate a terminating body. Sequential composition preserves the pending
continuation and every emitted event.
-/

@[expose] public section

namespace Riftbound

/-- Every invocation consumes this effect and leaves the remaining instructions and stack.
The cached Might is refreshed by the dispatcher. -/
def Effect.ControlTerminates (e : Effect) : Prop :=
  ∀ (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (more : EffectList) (rest : List Frame),
    ∃ (t : GameState) (n : Nat) (events : List Event) (might : List (ObjId × Int)),
      RawWorkPrefix { s with pending := .run p src env (.cons e more) :: rest }
        { t with pending := .run p src (env.withMight might) more :: rest } n events

/-- Every invocation of this sequence consumes its instructions, keeping the continuation. -/
def EffectList.ControlTerminates (program : EffectList) : Prop :=
  ∀ (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (more : EffectList) (rest : List Frame),
    ∃ (t : GameState) (n : Nat) (events : List Event) (might : List (ObjId × Int)),
      RawWorkPrefix { s with pending := .run p src env (program.append more) :: rest }
        { t with pending := .run p src (env.withMight might) more :: rest } n events

private theorem rawEffectStep {s t : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {e : Effect} {more : EffectList} {rest frames : List Frame} {events : List Event}
    (rule : let start := { s with pending := .run p src env (.cons e more) :: rest }
      runEffect start p src (env.withMight start.mightTable) e more effectAddPolicy =
        (t, frames, events)) :
    RawWorkPrefix { s with pending := .run p src env (.cons e more) :: rest }
      { t with pending := frames ++ rest } 1 events := by
  let start := { s with pending := .run p src env (.cons e more) :: rest }
  change runEffect start p src (env.withMight start.mightTable) e more effectAddPolicy = _ at rule
  have pending : start.pending = .run p src env (.cons e more) :: rest := rfl
  have step : microStep0 start = some ({ t with pending := frames ++ rest }, events) := by
    simp only [microStep0, pending, rule]
  exact .single pending rfl step

private theorem rawRun {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {e : Effect} {more : EffectList} {rest frames : List Frame} {events : List Event}
    (rule : let start := { s with pending := .run p src env (.cons e more) :: rest }
      runEffect start p src (env.withMight start.mightTable) e more effectAddPolicy =
        (start, frames, events)) :
    RawWorkPrefix { s with pending := .run p src env (.cons e more) :: rest }
      { s with pending := frames ++ rest } 1 events :=
  rawEffectStep (t := { s with pending := .run p src env (.cons e more) :: rest }) rule

private theorem rawForkRun {s : GameState} {p : PlayerId} {src : ObjId} {env refreshed : Env}
    {e : Effect} {more : EffectList} {rest frames : List Frame}
    (rule : let start := { s with pending := .run p src env (.cons e more) :: rest }
      runEffect start p src (env.withMight start.mightTable) e more effectAddPolicy =
        (start, frames ++ [.run p src refreshed more], [])) :
    RawWorkPrefix { s with pending := .run p src env (.cons e more) :: rest }
      { s with pending := frames ++ (.run p src refreshed more :: rest) } 1 [] := by
  have step := rawRun rule
  rw [List.append_assoc] at step
  exact step

private theorem popRun (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (rest : List Frame) :
    RawWorkPrefix { s with pending := .run p src env .nil :: rest }
      { s with pending := rest } 1 [] := by
  exact .single (frame := .run p src env .nil) (rest := rest) rfl rfl rfl

private theorem refreshAgain (env : Env) (prior after : List (ObjId × Int)) :
    (env.withMight prior).withMight after = env.withMight after := rfl

/-- The empty sequence leaves the continuation ready immediately. -/
theorem EffectList.ControlTerminates.nil : EffectList.nil.ControlTerminates := by
  intro s p src env more rest
  refine ⟨s, 0, [], env.passMight, ?_⟩
  have refresh : env.withMight env.passMight = env := by cases env; rfl
  simpa only [EffectList.append, refresh] using
    RawWorkPrefix.done { s with pending := .run p src env more :: rest }

/-- Finite effect prefixes compose even when an earlier effect refreshes the cached Might. -/
theorem EffectList.ControlTerminates.cons {e : Effect} {program : EffectList}
    (first : e.ControlTerminates) (later : program.ControlTerminates) :
    (EffectList.cons e program).ControlTerminates := by
  intro s p src env more rest
  obtain ⟨t, n, events, might, h⟩ := first s p src env (program.append more) rest
  obtain ⟨u, m, extra, afterMight, h'⟩ := later t p src (env.withMight might) more rest
  exact ⟨u, n + m, events ++ extra, afterMight, by
    simpa only [EffectList.append, refreshAgain] using h.append h'⟩

private theorem replicateControl {body : Effect} (h : body.ControlTerminates) (n : Nat) :
    (EffectList.replicate n body).ControlTerminates := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons h ih

private theorem forksControl {α : Type} (s : GameState) (src : ObjId) {body : Effect}
    (h : body.ControlTerminates) (context : α → PlayerId × Env) (inputs : List α)
    (rest : List Frame) :
    ∃ (t : GameState) (n : Nat) (events : List Event), RawWorkPrefix
      { s with pending := inputs.map (fun a =>
          .run (context a).1 src (context a).2 (.cons body .nil)) ++ rest }
      { t with pending := rest } n events := by
  induction inputs generalizing s with
  | nil => exact ⟨s, 0, [], .done _⟩
  | cons a inputs ih =>
    let tail := inputs.map (fun i => Frame.run (context i).1 src (context i).2 (.cons body .nil)) ++ rest
    obtain ⟨t, n, events, might, headRun⟩ := h s (context a).1 src (context a).2 .nil tail
    have done := popRun t (context a).1 src ((context a).2.withMight might) tail
    obtain ⟨u, m, extra, tailRun⟩ := ih t
    exact ⟨u, n + 1 + m, (events ++ []) ++ extra, (headRun.append done).append tailRun⟩

/-- A no-op consumes one work step. -/
theorem Effect.ControlTerminates.nop : Effect.nop.ControlTerminates := by
  intro s p src env more rest
  let start := { s with pending := .run p src env (.cons .nop more) :: rest }
  exact ⟨s, 1, [], start.mightTable,
    rawRun (frames := [.run p src (env.withMight start.mightTable) more]) rfl⟩

/-- Entering a sequence takes one step, after which it runs before the unchanged suffix. -/
theorem Effect.ControlTerminates.seq {program : EffectList} (h : program.ControlTerminates) :
    (Effect.seq program).ControlTerminates := by
  intro s p src env more rest
  let start := { s with pending := .run p src env (.cons (.seq program) more) :: rest }
  let refreshed := env.withMight start.mightTable
  have enter := rawRun (s := s) (env := env) (rest := rest)
    (frames := [.run p src refreshed (program.append more)]) (events := []) (e := .seq program)
    (more := more) rfl
  obtain ⟨t, n, events, might, run⟩ := h s p src refreshed more rest
  exact ⟨t, 1 + n, [] ++ events, might, by simpa only [refreshAgain, refreshed] using enter.append run⟩

/-- Runtime repetition terminates for every evaluated count when the body terminates. -/
theorem Effect.ControlTerminates.repeatN {amount : Amount} {body : Effect}
    (h : body.ControlTerminates) : (Effect.repeatN amount body).ControlTerminates := by
  intro s p src env more rest
  let start := { s with pending := .run p src env (.cons (.repeatN amount body) more) :: rest }
  let refreshed := env.withMight start.mightTable
  cases count : amount.evalS start p src refreshed with
  | none =>
    exact ⟨s, 1, [.skipped src], start.mightTable,
      rawRun (frames := [.run p src refreshed more]) (by
        change runEffect start p src refreshed (.repeatN amount body) more effectAddPolicy = _
        simp only [runEffect, Effect.pickSel?, runEffect1, count] <;> rfl)⟩
  | some n =>
    have enter : RawWorkPrefix start
        { s with pending := .run p src refreshed ((EffectList.replicate n body).append more) :: rest }
        1 [] := by
      apply rawRun (frames := [.run p src refreshed ((EffectList.replicate n body).append more)])
      change runEffect start p src refreshed (.repeatN amount body) more effectAddPolicy = _
      simp only [runEffect, Effect.pickSel?, runEffect1, count] <;> rfl
    obtain ⟨t, m, events, might, run⟩ := (replicateControl h n) s p src refreshed more rest
    exact ⟨t, 1 + m, [] ++ events, might, by simpa only [refreshAgain, refreshed] using enter.append run⟩

private theorem appendNil : ∀ (es : EffectList), es.append .nil = es
  | .nil => rfl
  | .cons e es => by simp only [EffectList.append, appendNil es]

/-- Once a finite sequence has run, its empty frame is popped and the previous stack resumes. -/
theorem EffectList.ControlTerminates.frame {program : EffectList} (h : program.ControlTerminates)
    (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (rest : List Frame) :
    ∃ (t : GameState) (n : Nat) (events : List Event), RawWorkPrefix { s with pending := .run p src env program :: rest }
      { t with pending := rest } n events := by
  obtain ⟨t, n, events, might, run⟩ := h s p src env .nil rest
  exact ⟨t, n + 1, events, by
    simpa only [appendNil, List.append_nil] using
      run.append (popRun t p src (env.withMight might) rest)⟩

/-- Either branch of a condition can use an arbitrary terminating body. -/
theorem Effect.ControlTerminates.ifThen {test : Condition} {yes no : Effect}
    (onYes : yes.ControlTerminates) (onNo : no.ControlTerminates) :
    (Effect.ifThen test yes no).ControlTerminates := by
  intro s p src env more rest
  let start := { s with pending := .run p src env (.cons (.ifThen test yes no) more) :: rest }
  let refreshed := env.withMight start.mightTable
  cases result : test.eval start p src refreshed with
  | none =>
    refine ⟨s, 1, [.skipped src], start.mightTable, rawRun (frames := [.run p src refreshed more]) ?_⟩
    change runEffect start p src refreshed (.ifThen test yes no) more effectAddPolicy = _
    simp only [runEffect, Effect.pickSel?, runEffect1, refreshed, refreshAgain] <;>
      rw [show test.eval start p src (env.withMight start.mightTable) = none from result] <;> rfl
  | some answer =>
    have branch : (if answer then yes else no).ControlTerminates := by
      cases answer
      · exact onNo
      · exact onYes
    have enter : RawWorkPrefix start
        { s with pending := .run p src refreshed (.cons (if answer then yes else no) more) :: rest }
        1 [] := by
      apply rawRun (frames := [.run p src refreshed (.cons (if answer then yes else no) more)])
      change runEffect start p src refreshed (.ifThen test yes no) more effectAddPolicy = _
      simp only [runEffect, Effect.pickSel?, runEffect1, refreshed, refreshAgain] <;>
        rw [show test.eval start p src (env.withMight start.mightTable) = some answer from result] <;> rfl
    obtain ⟨t, n, events, might, run⟩ := branch s p src refreshed more rest
    exact ⟨t, 1 + n, [] ++ events, might, by simpa only [refreshAgain, refreshed] using enter.append run⟩

/-- Binding a value runs a terminating body in the derived environment, preserving the environment
of the continuation. -/
theorem Effect.ControlTerminates.bind {name : VarId} {amount : Amount} {body : Effect}
    (h : body.ControlTerminates) : (Effect.bind name amount body).ControlTerminates := by
  intro s p src env more rest
  let start := { s with pending := .run p src env (.cons (.bind name amount body) more) :: rest }
  let refreshed := env.withMight start.mightTable
  cases result : amount.evalS start p src refreshed with
  | none =>
    refine ⟨s, 1, [.skipped src], start.mightTable, rawRun (frames := [.run p src refreshed more]) ?_⟩
    change runEffect start p src refreshed (.bind name amount body) more effectAddPolicy = _
    simp only [runEffect, Effect.pickSel?, runEffect1, result] <;> rfl
  | some value =>
    let inner := refreshed.bind name (.int value)
    let resume := .run p src refreshed more :: rest
    have enter : RawWorkPrefix start { s with pending := .run p src inner (.cons body .nil) :: resume }
        1 [] := by
      apply rawRun (frames := [.run p src inner (.cons body .nil), .run p src refreshed more])
      change runEffect start p src refreshed (.bind name amount body) more effectAddPolicy = _
      simp only [runEffect, Effect.pickSel?, runEffect1, result] <;> rfl
    obtain ⟨t, n, events, run⟩ :=
      (EffectList.ControlTerminates.cons h .nil).frame s p src inner resume
    exact ⟨t, 1 + n, [] ++ events, start.mightTable, enter.append run⟩

/-- A terminating body can be run once for every object in a finite selection. -/
theorem Effect.ControlTerminates.forEach {sel : Selector} {body : Effect}
    (h : body.ControlTerminates) : (Effect.forEach sel body).ControlTerminates := by
  intro s p src env more rest
  let start := { s with pending := .run p src env (.cons (.forEach sel body) more) :: rest }
  let refreshed := env.withMight start.mightTable
  cases result : sel.eval start p src refreshed with
  | none =>
    refine ⟨s, 1, [.skipped src], start.mightTable, rawRun (frames := [.run p src refreshed more]) ?_⟩
    change runEffect start p src refreshed (.forEach sel body) more effectAddPolicy = _
    simp only [runEffect, Effect.pickSel?, runEffect1, result] <;> rfl
  | some ids =>
    let context (id : ObjId) : PlayerId × Env := (p, { refreshed with it := some id })
    let frames := ids.map (fun id => Frame.run p src (context id).2 (.cons body .nil))
    let resume := .run p src refreshed more :: rest
    have enter : RawWorkPrefix start { s with pending := frames ++ resume } 1 [] := by
      apply rawForkRun (frames := frames)
      change runEffect start p src refreshed (.forEach sel body) more effectAddPolicy = _
      simp only [runEffect, Effect.pickSel?, runEffect1, result] <;> rfl
    obtain ⟨t, n, events, run⟩ := forksControl s src h context ids resume
    exact ⟨t, 1 + n, [] ++ events, start.mightTable, enter.append run⟩

/-- The same control bound holds for each seat selected at runtime, retaining the original
effect controller in each seat's instructions. -/
theorem Effect.ControlTerminates.eachPlayer {who : PlayerSel} {body : Effect}
    (h : body.ControlTerminates) : (Effect.eachPlayer who body).ControlTerminates := by
  intro s p src env more rest
  let start := { s with pending := .run p src env (.cons (.eachPlayer who body) more) :: rest }
  let refreshed := env.withMight start.mightTable
  let selected : Option (List PlayerId) := match who with
    | .controllerOf i =>
      match refreshed.slots[i]? with
      | some (.obj o) => (start.obj? o).bind fun x =>
        if start.departures.seats.contains x.controller then none else some [x.controller]
      | _ => none
    | _ => who.resolve start p refreshed
  cases result : selected with
  | none =>
    refine ⟨s, 1, [.skipped src], start.mightTable, rawRun (frames := [.run p src refreshed more]) ?_⟩
    change runEffect start p src refreshed (.eachPlayer who body) more effectAddPolicy = _
    simp only [runEffect, Effect.pickSel?, runEffect1]
    change (match selected with
      | some qs =>
        (start, qs.map (fun q => Frame.run q src
          { refreshed with effectController := refreshed.effectController <|> some p }
          (.cons body .nil)) ++ [Frame.run p src refreshed more], [])
      | none => (start, [Frame.run p src refreshed more], [Event.skipped src])) = _
    rw [result]
  | some players =>
    let playerEnv := { refreshed with effectController := refreshed.effectController <|> some p }
    let context (q : PlayerId) : PlayerId × Env := (q, playerEnv)
    let frames := players.map (fun q => Frame.run q src playerEnv (.cons body .nil))
    let resume := .run p src refreshed more :: rest
    have enter : RawWorkPrefix start { s with pending := frames ++ resume } 1 [] := by
      apply rawForkRun (frames := frames)
      change runEffect start p src refreshed (.eachPlayer who body) more effectAddPolicy = _
      simp only [runEffect, Effect.pickSel?, runEffect1]
      change (match selected with
        | some qs => (start, qs.map (fun q => Frame.run q src playerEnv (.cons body .nil)) ++
            [Frame.run p src refreshed more], [])
        | none => (start, [Frame.run p src refreshed more], [Event.skipped src])) = _
      rw [result]
    obtain ⟨t, n, events, run⟩ := forksControl s src h context players resume
    exact ⟨t, 1 + n, [] ++ events, start.mightTable, enter.append run⟩

/-- A state-changing effect qualifies when its dispatcher always returns precisely its continuation. -/
theorem Effect.ControlTerminates.ofSingleRun {effect : Effect}
    (rule : ∀ s p src env more, ∃ (t : GameState) (events : List Event),
      runEffect s p src env effect more effectAddPolicy =
        (t, [.run p src env more], events)) : effect.ControlTerminates := by
  intro s p src env more rest
  let start := { s with pending := .run p src env (.cons effect more) :: rest }
  let refreshed := env.withMight start.mightTable
  obtain ⟨t, events, executed⟩ := rule start p src refreshed more
  exact ⟨t, 1, events, start.mightTable, rawEffectStep (frames := [.run p src refreshed more]) executed⟩

private theorem controlOfPrimitive {pr : Prim}
    (rule : ∀ s p src env more,
      runEffect s p src env (.prim pr) more effectAddPolicy =
        match applyPrim s p src env pr with
        | some (t, events) => (t, [.run p src env more], events)
        | none => (s, [.run p src env more], [.skipped src])) :
    (Effect.prim pr).ControlTerminates := by
  apply Effect.ControlTerminates.ofSingleRun
  intro s p src env more
  cases applied : applyPrim s p src env pr with
  | none => exact ⟨s, [.skipped src], by rw [rule, applied]⟩
  | some r => exact ⟨r.1, r.2, by cases r; rw [rule, applied]⟩

/-- The marker that records an immediate Add's use consumes one work step. -/
theorem Effect.ControlTerminates.markTriggeredAdd (index : Nat) :
    (Effect.markTriggeredAdd index).ControlTerminates := by
  apply ofSingleRun
  intro s p src env more
  exact ⟨s.modObj src (fun o => o.noteAbilityUse index env.abilityCopyStamp), [], rfl⟩

/-- Gaining XP consumes one step and keeps the updated balance. -/
theorem Effect.ControlTerminates.gainXP (who : PlayerSel) (amount : Amount) :
    (Effect.prim (.gainXP who amount)).ControlTerminates := by
  apply controlOfPrimitive
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
    effectDamageBatch?, permanentPlayEffects, applyPrim]
  by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;>
    cases who.resolve s p env <;> cases amount.evalS s p src env <;> rfl

/-- Adding regular Energy consumes one step. -/
theorem Effect.ControlTerminates.addEnergy (who : PlayerSel) (amount : Amount) :
    (Effect.prim (.addEnergy who amount none)).ControlTerminates := by
  apply controlOfPrimitive
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
    effectDamageBatch?, permanentPlayEffects, applyPrim]
  by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;>
    cases who.resolve s p env <;> cases amount.evalS s p src env <;> rfl

/-- Adding Energy restricted to Unit plays consumes one step. -/
theorem Effect.ControlTerminates.addUnitEnergy (who : PlayerSel) (amount : Amount) :
    (Effect.prim (.addUnitEnergy who amount)).ControlTerminates := by
  apply controlOfPrimitive
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
    effectDamageBatch?, permanentPlayEffects, applyPrim]
  by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;>
    cases who.resolve s p env <;> cases amount.evalS s p src env <;> rfl

/-- Adding Energy restricted to Spell plays consumes one step. -/
theorem Effect.ControlTerminates.addSpellEnergy (who : PlayerSel) (amount : Amount) :
    (Effect.prim (.addSpellEnergy who amount)).ControlTerminates := by
  apply controlOfPrimitive
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
    effectDamageBatch?, permanentPlayEffects, applyPrim]
  by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;>
    cases who.resolve s p env <;> cases amount.evalS s p src env <;> rfl

/-- Adding unrestricted Power, of a fixed or unspecified domain, consumes one step. -/
theorem Effect.ControlTerminates.addPower (who : PlayerSel) (amount : Amount)
    (domain : Option Domain) : (Effect.prim (.addPower who amount domain none)).ControlTerminates := by
  apply controlOfPrimitive
  intro s p src env more
  cases domain <;> (simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
    effectDamageBatch?, permanentPlayEffects, applyPrim]) <;>
    by_cases small : s.turnFx.length < 2 <;> simp only [small, ite_true, ite_false] <;>
    cases who.resolve s p env <;> cases amount.evalS s p src env <;> rfl

end Riftbound

end
