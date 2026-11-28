module

public import Riftbound.Engine.Step

/-! # Recording card faces during engine steps -/

@[expose] public section

namespace Riftbound

/-- A disclosure within one answer. The index refers to the corresponding event in the
answer's event list. A missing seat means every player saw the disclosure. -/
structure CardDisclosure where
  /-- Zero-based position in the answer's events. -/
  eventIndex : Nat
  /-- The inspecting seat, or none for a public disclosure. -/
  onlyFor : Option PlayerId
  /-- The faces shown in event order. -/
  cards : List CardId
deriving DecidableEq, Repr

/-- A public reveal is visible to all players. A private look is visible to its viewer. -/
def CardDisclosure.visibleTo (viewer : PlayerId) (d : CardDisclosure) : Bool :=
  d.onlyFor.all (· == viewer)

/-- No other player receives the face of a privately inspected card. -/
theorem CardDisclosure.private_hidden {viewer seat : PlayerId} (different : viewer ≠ seat)
    (i : Nat) (cards : List CardId) :
    (CardDisclosure.mk i (some seat) cards).visibleTo viewer = false := by
  simp [CardDisclosure.visibleTo, Ne.symm different]

/-- Read known faces from the transition that emitted an event. Reveal and Look use the current
object identifier, which can disappear during a later work frame in the same answer. -/
def CardDisclosure.capture (before after : GameState) (offset : Nat) (events : List Event) :
    List CardDisclosure :=
  let face (id : ObjId) :=
    ((before.obj? id).bind (·.kind.cardId?)) <|> ((after.obj? id).bind (·.kind.cardId?))
  let disclosures (i : Nat) (seat : Option PlayerId) (ids : List ObjId) :=
    { eventIndex := i, onlyFor := seat, cards := ids.filterMap face }
  (events.zipIdx offset).filterMap fun
    | (.lookedAt p card, i) => some (disclosures i (some p) [card])
    | (.revealed _ card, i) => some (disclosures i none [card])
    | (.handRevealed _ cards, i) => some (disclosures i none cards)
    | _ => none

/-- Work through the same frames as `advance`, capturing disclosures at each transition. -/
def advanceWithDisclosures : Nat → GameState → List Event → List CardDisclosure →
    Except RuleError ((GameState × List Event) × List CardDisclosure)
  | 0, s, es, seen =>
    let prepared := s.preparePriority
    match prepared.pending with
    | f :: _ => if f.isWork then .error .fuelExhausted else .ok ((prepared, es), seen)
    | [] => .ok ((prepared, es), seen)
  | n + 1, s, es, seen =>
    let prepared := s.preparePriority
    match prepared.pending with
    | f :: _ =>
      if f.isWork then
        match workStep prepared with
        | some (s', es') => advanceWithDisclosures n s' (es ++ es')
            (seen ++ CardDisclosure.capture prepared s' es.length es')
        | none => .error (.internal "microStep")
      else .ok ((prepared, es), seen)
    | [] => .ok ((prepared, es), seen)

/-- Capturing disclosures preserves the result, the events and any errors from `advance`. -/
theorem advanceWithDisclosures_erase (fuel : Nat) (s : GameState) (es : List Event)
    (seen : List CardDisclosure) :
    (advanceWithDisclosures fuel s es seen).map Prod.fst = advance fuel s es := by
  induction fuel generalizing s es seen with
  | zero =>
    cases h : s.preparePriority.pending with
    | nil => simp [advanceWithDisclosures, advance, h] <;> rfl
    | cons f rest => by_cases work : f.isWork <;> simp [advanceWithDisclosures, advance, h, work] <;> rfl
  | succ n ih =>
    cases h : s.preparePriority.pending with
    | nil => simp [advanceWithDisclosures, advance, h] <;> rfl
    | cons f rest =>
      by_cases work : f.isWork
      · cases hw : workStep s.preparePriority with
        | none => simp [advanceWithDisclosures, advance, h, work, hw] <;> rfl
        | some transition =>
          obtain ⟨next, events⟩ := transition
          simpa [advanceWithDisclosures, advance, h, work, hw] using
            ih next (es ++ events) (seen ++ CardDisclosure.capture s.preparePriority next es.length events)
      · simp [advanceWithDisclosures, advance, h, work] <;> rfl

/-- Take an ordinary answer and record any card faces it shows before the next decision. -/
def stepWithDisclosures (fuel : Nat) (s : GameState) (a : Action) :
    Except RuleError ((GameState × List Event) × List CardDisclosure) :=
  if Legal s a then
    match applyDeclaredAction s a with
    | some (next, events) =>
      advanceWithDisclosures fuel next events (CardDisclosure.capture s next 0 events)
    | none => .error (.internal "applyAction")
  else .error .illegal

/-- The observed transition implements exactly the same decision contract as `step`. -/
theorem stepWithDisclosures_erase (fuel : Nat) (s : GameState) (a : Action) :
    (stepWithDisclosures fuel s a).map Prod.fst = step fuel s a := by
  by_cases legal : Legal s a
  · cases h : applyDeclaredAction s a with
    | none => simp [stepWithDisclosures, step, legal, h] <;> rfl
    | some transition =>
      obtain ⟨next, events⟩ := transition
      simpa [stepWithDisclosures, step, legal, h] using
        advanceWithDisclosures_erase fuel next events (CardDisclosure.capture s next 0 events)
  · simp [stepWithDisclosures, step, legal] <;> rfl

/-- A successful run captures the same disclosures when the caller offers more fuel. -/
theorem advanceWithDisclosures_ok_add_fuel {fuel : Nat} {s : GameState} {events : List Event}
    {seen : List CardDisclosure} {result : (GameState × List Event) × List CardDisclosure}
    (done : advanceWithDisclosures fuel s events seen = .ok result) (extra : Nat) :
    advanceWithDisclosures (fuel + extra) s events seen = .ok result := by
  induction fuel generalizing s events seen with
  | zero =>
    cases stack : s.preparePriority.pending with
    | nil => cases extra <;> simpa [advanceWithDisclosures, stack] using done
    | cons frame rest =>
      by_cases work : frame.isWork
      · simp [advanceWithDisclosures, stack, work] at done
      · cases extra <;> simpa [advanceWithDisclosures, stack, work] using done
  | succ fuel ih =>
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
    cases stack : s.preparePriority.pending with
    | nil => simpa [advanceWithDisclosures, stack] using done
    | cons frame rest =>
      by_cases work : frame.isWork
      · cases workStepEq : workStep s.preparePriority with
        | none => simp [advanceWithDisclosures, stack, work, workStepEq] at done
        | some transition =>
          obtain ⟨next, emitted⟩ := transition
          have short := (show advanceWithDisclosures fuel next (events ++ emitted)
              (seen ++ CardDisclosure.capture s.preparePriority next events.length emitted) = .ok result by
            simpa [advanceWithDisclosures, stack, work, workStepEq] using done)
          simpa [advanceWithDisclosures, stack, work, workStepEq] using ih short
      · simpa [advanceWithDisclosures, stack, work] using done

/-- More fuel preserves the state, event list and card disclosures of a successful answer. -/
theorem stepWithDisclosures_ok_add_fuel {fuel : Nat} {s : GameState} {a : Action}
    {result : (GameState × List Event) × List CardDisclosure}
    (done : stepWithDisclosures fuel s a = .ok result) (extra : Nat) :
    stepWithDisclosures (fuel + extra) s a = .ok result := by
  by_cases legal : Legal s a
  · cases applied : applyDeclaredAction s a with
    | none => simp [stepWithDisclosures, legal, applied] at done
    | some transition =>
      obtain ⟨next, events⟩ := transition
      have short := (show advanceWithDisclosures fuel next events
          (CardDisclosure.capture s next 0 events) = .ok result by
        simpa [stepWithDisclosures, legal, applied] using done)
      simpa [stepWithDisclosures, legal, applied] using advanceWithDisclosures_ok_add_fuel short extra
  · simp [stepWithDisclosures, legal] at done

/-- If the ordinary engine reaches its next input, the observing engine reaches the same
state with the same events and returns the card disclosures, for all additional fuel. -/
theorem stepWithDisclosures_of_step_ok {fuel : Nat} {s : GameState} {a : Action}
    {t : GameState} {events : List Event} (done : step fuel s a = .ok (t, events)) :
    ∃ disclosures, ∀ extra,
      stepWithDisclosures (fuel + extra) s a = .ok ((t, events), disclosures) := by
  rw [← stepWithDisclosures_erase fuel s a] at done
  cases observed : stepWithDisclosures fuel s a with
  | error e => simp [observed, Except.map] at done
  | ok result =>
    obtain ⟨stateAndEvents, disclosures⟩ := result
    have agrees : stateAndEvents = (t, events) := by
      simpa [observed, Except.map] using done
    rw [agrees] at observed
    exact ⟨disclosures, stepWithDisclosures_ok_add_fuel observed⟩

/-- More fuel preserves an ordinary answer's successful state and event list. -/
theorem step_ok_add_fuel {fuel : Nat} {s : GameState} {a : Action}
    {t : GameState} {events : List Event} (done : step fuel s a = .ok (t, events)) (extra : Nat) :
    step (fuel + extra) s a = .ok (t, events) := by
  obtain ⟨disclosures, stable⟩ := stepWithDisclosures_of_step_ok done
  rw [← stepWithDisclosures_erase, stable extra]
  rfl

end Riftbound

end
