module

public import Riftbound.Invariant.ControlWork

/-!
# Finite work from immediate Add triggers (I12)

The engine only schedules an immediate Add for a small accepted effect language. The bound
covers that exact language and the marker placed before the effect by the trigger dispatcher.
-/

@[expose] public section

namespace Riftbound

private theorem addPrimitiveControl (pr : Prim) (h : (Effect.prim pr).isTriggerAdd = true) :
    (Effect.prim pr).ControlTerminates := by
  cases pr with
  | addEnergy who n only =>
    cases only with
    | none => exact .addEnergy who n
    | some act => cases who <;> simp [Effect.isTriggerAdd] at h
  | addUnitEnergy who n => exact .addUnitEnergy who n
  | addSpellEnergy who n => exact .addSpellEnergy who n
  | addPower who n domain only =>
    cases only with
    | none => exact .addPower who n domain
    | some act => cases who <;> simp [Effect.isTriggerAdd] at h
  | _ => simp [Effect.isTriggerAdd] at h

mutual

/-- Every effect the trigger dispatcher accepts as an immediate Add has finite rule work. -/
theorem Effect.isTriggerAdd_control (effect : Effect) (h : effect.isTriggerAdd = true) :
    effect.ControlTerminates := by
  cases effect with
  | prim pr => exact addPrimitiveControl pr h
  | seq program =>
    cases program with
    | nil => simp [Effect.isTriggerAdd] at h
    | cons first rest =>
      simp only [Effect.isTriggerAdd, Bool.and_eq_true] at h
      exact .seq (.cons (Effect.isTriggerAdd_control first h.1)
        (EffectList.areTriggerAdds_control rest h.2))
  | ifThen condition yes no =>
    cases no with
    | nop => exact .ifThen (Effect.isTriggerAdd_control yes (by simpa only [Effect.isTriggerAdd] using h)) .nop
    | _ => simp [Effect.isTriggerAdd] at h
  | _ => simp [Effect.isTriggerAdd] at h
termination_by structural effect

/-- A sequence of immediate Add instructions has finite rule work. -/
theorem EffectList.areTriggerAdds_control (effects : EffectList) (h : effects.areTriggerAdds = true) :
    effects.ControlTerminates := by
  cases effects with
  | nil => exact .nil
  | cons first rest =>
    simp only [EffectList.areTriggerAdds, Bool.and_eq_true] at h
    exact .cons (Effect.isTriggerAdd_control first h.1) (EffectList.areTriggerAdds_control rest h.2)
termination_by structural effects

end

/-- The work generated for an immediate Add, including the bookkeeping marker, runs to the
supplied continuation under the rule dispatcher. -/
theorem PendTrigger.immediateAddFrame_bound {s : GameState} {trigger : PendTrigger} {frame : Frame}
    (scheduled : trigger.immediateAddFrame s = some frame) (current : GameState) (rest : List Frame) :
    ∃ (t : GameState) (used : Nat) (events : List Event),
      RawWorkPrefix { current with pending := frame :: rest } { t with pending := rest } used events := by
  unfold PendTrigger.immediateAddFrame at scheduled
  split at scheduled
  · split at scheduled
    · rename_i effectRule
      simp only [Bool.and_eq_true] at effectRule
      obtain rfl := Option.some.inj scheduled
      exact (EffectList.ControlTerminates.cons (.markTriggeredAdd _)
        (.cons (Effect.isTriggerAdd_control _ effectRule.2) .nil)).frame _ _ _ _ _
    · contradiction
  · contradiction

private theorem immediateAdds_bound (detected : GameState) (triggers : List PendTrigger)
    (current : GameState) (rest : List Frame) :
    ∃ (t : GameState) (used : Nat) (events : List Event),
      RawWorkPrefix
        { current with pending := triggers.filterMap (·.immediateAddFrame detected) ++ rest }
        { t with pending := rest } used events := by
  induction triggers generalizing current with
  | nil => exact ⟨current, 0, [], .done _⟩
  | cons first triggers ih =>
    cases scheduled : first.immediateAddFrame detected with
    | none =>
      simpa only [List.filterMap_cons, scheduled] using ih current
    | some frame =>
      let tail := triggers.filterMap (·.immediateAddFrame detected) ++ rest
      obtain ⟨t, n, events, run⟩ := first.immediateAddFrame_bound scheduled current tail
      obtain ⟨u, m, more, remaining⟩ := ih t
      exact ⟨u, n + m, events ++ more, by
        simpa only [List.filterMap_cons, scheduled, List.cons_append] using run.append remaining⟩

/-- The stack left for ordinary triggers and other work after the immediate Adds have run. -/
def ordinaryTriggerContinuation (s : GameState) (triggers : List PendTrigger)
    (rest : List Frame) : List Frame :=
  let ordinary := triggers.filterMap (fun t =>
    if (t.immediateAddFrame s).isNone then some t else none)
  if ordinary.isEmpty then rest else insertTriggers ordinary rest

/-- All immediate Adds queued by event observation finish their rule work before the ordinary
triggers and the original stack. Each Add receives the state produced by its predecessors. -/
theorem insertDetectedTriggers_addWork (s : GameState) (triggers : List PendTrigger)
    (rest : List Frame) :
    ∃ (t : GameState) (used : Nat) (events : List Event),
      RawWorkPrefix { s with pending := insertDetectedTriggers s triggers rest }
        { t with pending := ordinaryTriggerContinuation s triggers rest } used events := by
  unfold ordinaryTriggerContinuation insertDetectedTriggers
  simp only [List.filterMap_map, Function.comp_def]
  exact immediateAdds_bound s triggers s _

end Riftbound

end
