module

public import Riftbound.Engine.Step

/-!
# Finite prefixes of automatic work (I12)

The work dispatcher has a rule transition followed by event observers. A finite path through the
rule transitions gives a bound up to the same continuation or up to the first observer change.
-/

@[expose] public section

namespace Riftbound

/-- A finite sequence of work transitions before the event observers are applied. -/
inductive RawWorkPrefix : GameState → GameState → Nat → List Event → Prop where
  /-- Stop at the supplied continuation. -/
  | done (s : GameState) : RawWorkPrefix s s 0 []
  /-- Perform one work transition and continue. -/
  | next {s t u : GameState} {n : Nat} {events more : List Event}
      {frame : Frame} {rest : List Frame} (pending : s.pending = frame :: rest)
      (work : frame.isWork = true) (raw : microStep0 s = some (t, events))
      (tail : RawWorkPrefix t u n more) :
      RawWorkPrefix s u (n + 1) (events ++ more)

namespace RawWorkPrefix

/-- A single rule transition through a work frame. -/
theorem single {s t : GameState} {events : List Event} {frame : Frame} {rest : List Frame}
    (pending : s.pending = frame :: rest) (work : frame.isWork = true)
    (raw : microStep0 s = some (t, events)) : RawWorkPrefix s t 1 events := by
  simpa only [List.append_nil] using RawWorkPrefix.next pending work raw (.done t)

/-- Join two prefixes, adding their lengths and keeping their events in order. -/
theorem append {s t u : GameState} {n m : Nat} {events more : List Event}
    (first : RawWorkPrefix s t n events) (second : RawWorkPrefix t u m more) :
    RawWorkPrefix s u (n + m) (events ++ more) := by
  induction first with
  | done => simpa using second
  | @next s t v n events later frame rest pending work raw _ ih =>
    simpa only [List.append_assoc, Nat.succ_add] using .next pending work raw (ih second)

end RawWorkPrefix

/-- Consume exactly these work steps and events before passing the remaining fuel to the suffix. -/
def AdvancePrefix (s t : GameState) (n : Nat) (events : List Event) : Prop :=
  ∀ fuel before, advance (n + fuel) s before = advance fuel t (before ++ events)

/-- Prepend one observed work step to a known continuation of the engine. -/
theorem AdvancePrefix.prepend {s next t : GameState} {frame : Frame} {rest : List Frame}
    {n : Nat} {events more : List Event} (pending : s.pending = frame :: rest)
    (work : frame.isWork = true) (step : workStep s = some (next, events))
    (path : AdvancePrefix next t n more) : AdvancePrefix s t (n + 1) (events ++ more) := by
  intro fuel prior
  rw [show n + 1 + fuel = n + fuel + 1 by omega]
  simp only [advance, GameState.preparePriority_of_work pending work, pending, work, ite_true, step]
  rw [path]
  simp only [List.append_assoc]

/-- Run two observed work segments in order and keep their events in order. -/
theorem AdvancePrefix.append {s t u : GameState} {n m : Nat} {first second : List Event}
    (initial : AdvancePrefix s t n first) (later : AdvancePrefix t u m second) :
    AdvancePrefix s u (n + m) (first ++ second) := by
  intro fuel seen
  rw [Nat.add_assoc, initial, later, List.append_assoc]

/-- At the end of the stack or at a decision, the steps used so far are enough for `advance`. -/
theorem AdvancePrefix.finish {s t : GameState} {n : Nat} {events : List Event}
    (path : AdvancePrefix s t n events)
    (boundary : t.preparePriority.pending.head?.all (fun frame => !frame.isWork) = true)
    (before : List Event) : advance n s before = .ok (t, before ++ events) := by
  rw [← Nat.add_zero n, path]
  have unchanged := GameState.preparePriority_of_idle boundary
  rw [unchanged] at boundary
  cases stack : t.pending with
  | nil => simp [advance, unchanged, stack]
  | cons frame rest =>
    have choice : frame.isWork = false := by simpa [stack] using boundary
    simp only [advance, unchanged, stack, choice, Bool.false_eq_true, ↓reduceIte]

/-- The rule transition produced `expected` and applying its event observers changed that state. -/
def WorkObserverChange (before expected actual : GameState) : Prop :=
  actual ≠ expected ∧ ∃ events, microStep0 before = some (expected, events) ∧
    actual = expected.withTriggers (events ++ before.workTransitionEvents expected)

/-- While following a raw prefix, the engine either reaches its planned continuation or reaches
the first state changed by an observer. The second bound includes the step that produced it. -/
theorem RawWorkPrefix.observe {s t : GameState} {n : Nat} {events : List Event}
    (path : RawWorkPrefix s t n events) :
    AdvancePrefix s t n events ∨
      ∃ before expected actual used emitted,
        WorkObserverChange before expected actual ∧ 0 < used ∧ used ≤ n ∧
        AdvancePrefix s actual used emitted ∧ emitted <+: events := by
  induction path with
  | done s =>
    exact Or.inl (by intro fuel prior; simp)
  | @next s mid t n events later frame rest pending work raw _ ih =>
    let observed := mid.withTriggers (events ++ s.workTransitionEvents mid)
    have step : workStep s = some (observed, events) := by
      unfold workStep
      split
      · rename_i _ _ locked
        simp only [microStep0, locked] at raw
        contradiction
      · unfold microStep
        rw [raw]
        rfl
    by_cases unchanged : observed = mid
    · rw [← unchanged] at ih
      rcases ih with reaches |
        ⟨before, expected, actual, used, emitted, changed, positive, bound, reaches, eventPrefix⟩
      · exact Or.inl (reaches.prepend pending work step)
      · obtain ⟨laterEvents, h⟩ := eventPrefix
        exact Or.inr ⟨before, expected, actual, used + 1, events ++ emitted,
          changed, by omega, by omega, reaches.prepend pending work step,
          ⟨laterEvents, by rw [List.append_assoc, h]⟩⟩
    · have one : AdvancePrefix observed observed 0 [] := by
        intro fuel prior
        simp
      refine Or.inr ⟨s, mid, observed, 1, events, ⟨unchanged, events, raw, rfl⟩,
        by omega, by omega, ?_, ⟨later, rfl⟩⟩
      simpa using one.prepend pending work step

end Riftbound

end
