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
        AdvancePrefix s actual used emitted := by
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
    have liftPrefix {target : GameState} {used : Nat} {emitted : List Event}
        (h : AdvancePrefix observed target used emitted) :
        AdvancePrefix s target (used + 1) (events ++ emitted) := by
      intro fuel prior
      rw [show used + 1 + fuel = used + fuel + 1 by omega]
      simp only [advance, pending, work, ite_true, step]
      rw [h]
      simp only [List.append_assoc]
    by_cases unchanged : observed = mid
    · rw [← unchanged] at ih
      rcases ih with reaches | ⟨before, expected, actual, used, emitted, changed, positive, bound, reaches⟩
      · exact Or.inl (liftPrefix reaches)
      · exact Or.inr ⟨before, expected, actual, used + 1, events ++ emitted,
          changed, by omega, by omega, liftPrefix reaches⟩
    · have one : AdvancePrefix observed observed 0 [] := by
        intro fuel prior
        simp
      refine Or.inr ⟨s, mid, observed, 1, events, ⟨unchanged, events, raw, rfl⟩, by omega, by omega, ?_⟩
      simpa using liftPrefix one

end Riftbound

end
