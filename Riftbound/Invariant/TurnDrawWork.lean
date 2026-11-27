module

public import Riftbound.Invariant.ObservedWork

/-!
# Channel and observed draw work (I12)

Immediate Adds resolve as their events are observed. Ordinary abilities wait until the
outstanding draws finish or a decision needs to be made.
-/

@[expose] public section

namespace Riftbound

/-- The Channel Phase finishes its Rune movements, resolves immediate Adds and either reaches
Draw or waits for a decision from an ordinary trigger. -/
theorem advance_channel_to_draw {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = .phase .channel :: .phase .draw :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true ∨
        (t.pending = .phase .draw :: rest ∧ t.WF ∧ t.cards = s.cards)) := by
  let p := s.active.getD ⟨0⟩
  let result := channelEx p s.channelCount 0 s
  let raw := { result.1 with phase := .channel, pending := .phase .draw :: rest }
  let notices := result.2 ++ s.workTransitionEvents raw
  have step : workStep s = some (raw.withTriggers notices, result.2) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some, raw, p, result, notices]
  have safe := channelEx_safe p s.channelCount 0 s
  have known : raw.cards = s.cards := by
    have cards := congrArg GameState.cards safe.same
    exact cards
  have rawWF : raw.WF := (safe.wf wf).congr rfl rfl rfl rfl
  have before : ∀ f, raw.pending.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
    intro f head
    have : f = .phase .draw := (Option.some.inj head).symm
    subst f
    exact ⟨rfl, by intro q mismatch; cases mismatch⟩
  obtain ⟨t, n, events, path, stop | ⟨after, lastWF, cards⟩⟩ :=
    advance_observed_to_boundary raw notices rawWF (known ▸ reads) before
  · exact ⟨t, n + 1, result.2 ++ events, by omega, path.prepend pending rfl step, Or.inl stop⟩
  · exact ⟨t, n + 1, result.2 ++ events, by omega, path.prepend pending rfl step,
      Or.inr ⟨after, lastWF, cards.trans known⟩⟩

/-- The rule's continuation after one draw operation, before ordinary triggers are inserted. -/
private inductive DrawContinuation (p : PlayerId) (rest : List Frame) : Nat → List Frame → Prop where
  /-- The batch's last frame publishes its group event. -/
  | done : DrawContinuation p rest 0 rest
  /-- An exhausted Main Deck yields to a chance answer. -/
  | burnOut (n : Nat) (hand : Option Nat) :
      DrawContinuation p rest (n + 1) (.chanceBurnOut p :: .draw p (n + 1) hand :: rest)
  /-- One card was drawn and the remainder of the batch is still pending. -/
  | next (n : Nat) (hand : Option Nat) :
      DrawContinuation p rest (n + 1) (.draw p n hand :: rest)

/-- One draw operation executes its immediate Adds and reports how ordinary triggers were placed
relative to the draw continuation. -/
private theorem advance_draw_step_with_adds {s : GameState} {p : PlayerId} {count : Nat} {hand : Option Nat}
    {rest : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .draw p count hand :: rest) :
    ∃ t used events frames, 0 < used ∧ AdvancePrefix s t used events ∧
      t.WF ∧ t.cards = s.cards ∧ DrawContinuation p rest count frames ∧
      ObservedWorkStack frames t.pending := by
  have perform (raw : GameState) (emitted : List Event)
      (rule : microStep0 s = some (raw, emitted)) (wellFormed : raw.WF)
      (known : raw.cards = s.cards) (next : DrawContinuation p rest count raw.pending) :
      ∃ t used events frames, 0 < used ∧ AdvancePrefix s t used events ∧
        t.WF ∧ t.cards = s.cards ∧ DrawContinuation p rest count frames ∧
        ObservedWorkStack frames t.pending := by
    obtain ⟨t, used, events, positive, path, afterWF, cards, stack⟩ :=
      advance_rule_with_adds pending rfl rule wellFormed known reads
    exact ⟨t, used, events, raw.pending, positive, path, afterWF, cards, next, stack⟩
  cases count with
  | zero =>
    let raw := { s with pending := rest }
    have step : microStep0 s = some (raw, hand.toList.map (.drewGroup p)) := by
      simp only [microStep0, pending, raw]
    exact perform raw _ step (wf.congr rfl rfl rfl rfl) rfl .done
  | succ n =>
    cases drawn : drawOne s p with
    | none =>
      let raw := { s with pending := .chanceBurnOut p :: .draw p (n + 1) hand :: rest }
      have step : microStep0 s = some (raw, []) := by simp only [microStep0, pending, drawn, raw]
      exact perform raw _ step (wf.congr rfl rfl rfl rfl) rfl (.burnOut n hand)
    | some r =>
      obtain ⟨board, emitted⟩ := r
      let initial := hand <|> some ((s.zone (.player p .hand)).length)
      let raw := { board.noteDraw p with pending := .draw p n initial :: rest }
      have step : microStep0 s = some (raw, emitted ++ [.drew p]) := by
        simp only [microStep0, pending, drawn, raw, initial]
      have known : raw.cards = s.cards := by
        have same := congrArg GameState.cards (drawOne_meta drawn)
        exact same
      exact perform raw _ step ((drawOne_wf wf drawn).congr rfl rfl rfl rfl) known (.next n initial)

/-- Finish a draw batch and its immediate Adds, or reach a decision. Ordinary triggers can
be inserted into the continuation behind the remaining draw frames. -/
theorem advance_draw_until {s : GameState} {p : PlayerId} {count : Nat} {hand : Option Nat}
    {queued : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .draw p count hand :: queued) (keeps : List Frame → Prop)
    (tail : keeps queued)
    (insertion : ∀ frames, keeps frames → ∀ q, q ≠ [] → keeps (insertTriggers q frames)) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true ∨
        (keeps t.pending ∧ t.WF ∧ t.cards = s.cards)) := by
  induction count generalizing s hand queued with
  | zero =>
    obtain ⟨t, used, events, frames, positive, path, nextWF, cards, route, observed⟩ :=
      advance_draw_step_with_adds wf reads pending
    cases route
    generalize stack : t.pending = pendingFrames at observed
    cases observed with
    | empty => exact ⟨t, used, events, positive, path, Or.inl (by rw [stack]; rfl)⟩
    | resume => exact ⟨t, used, events, positive, path, Or.inr ⟨stack.symm ▸ tail, nextWF, cards⟩⟩
    | queue q nonempty =>
      exact ⟨t, used, events, positive, path, Or.inr ⟨stack.symm ▸ insertion queued tail q nonempty, nextWF, cards⟩⟩
  | succ n ih =>
    obtain ⟨t, used, events, frames, positive, path, nextWF, cards, route, observed⟩ :=
      advance_draw_step_with_adds wf reads pending
    generalize stack : t.pending = pendingFrames at observed
    cases route with
    | burnOut _ captured =>
      cases observed with
      | empty => exact ⟨t, used, events, positive, path, Or.inl (by rw [stack]; rfl)⟩
      | resume => exact ⟨t, used, events, positive, path, Or.inl (by rw [stack]; rfl)⟩
      | queue qs nonempty =>
        have waiting : t.pending = .triggers qs :: .chanceBurnOut p :: .draw p (n + 1) captured :: queued := stack
        obtain ⟨u, later, _, _, _, resolved, decisionStack, decision⟩ :=
          advance_triggers_to_decision t nextWF qs _ waiting (cards ▸ reads) (Or.inl nonempty)
        exact ⟨u, used + later, events, by omega,
          by simpa only [List.append_nil] using path.append resolved, Or.inl (by simp [decisionStack, decision])⟩
    | next _ captured =>
      have nextStep (nextTail : List Frame) (nextDraw : t.pending = .draw p n captured :: nextTail)
          (tracks : keeps nextTail) :
          ∃ u steps emitted, 0 < steps ∧ AdvancePrefix s u steps emitted ∧
            (u.pending.head?.all (fun frame => !frame.isWork) = true ∨
              (keeps u.pending ∧ u.WF ∧ u.cards = s.cards)) := by
        obtain ⟨u, later, emitted, _, resolved, stop | ⟨endFrames, lastWF, lastCards⟩⟩ :=
          ih (s := t) nextWF (cards ▸ reads) nextDraw tracks
        · exact ⟨u, used + later, events ++ emitted, by omega, path.append resolved, Or.inl stop⟩
        · exact ⟨u, used + later, events ++ emitted, by omega, path.append resolved,
            Or.inr ⟨endFrames, lastWF, lastCards.trans cards⟩⟩
      cases observed with
      | empty => exact ⟨t, used, events, positive, path, Or.inl (by rw [stack]; rfl)⟩
      | resume => exact nextStep queued stack tail
      | queue qs nonempty => exact nextStep (insertTriggers qs queued) stack (insertion queued tail qs nonempty)

/-- Resolve the batch and its immediate Adds. The ordinary triggers queued during the
batch get their decision before the supplied non-resolution continuation. -/
theorem advance_draw_with_adds {s : GameState} {p : PlayerId} {count : Nat} {hand : Option Nat}
    {rest queued : List Frame} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .draw p count hand :: queued) (tail : TriggerWorkTail rest queued)
    (head : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true ∨
        (t.pending = rest ∧ t.WF ∧ t.cards = s.cards)) := by
  obtain ⟨t, used, events, positive, path, stop | ⟨route, nextWF, cards⟩⟩ :=
    advance_draw_until wf reads pending (TriggerWorkTail rest) tail (fun _ valid q nonempty => valid.insert head q nonempty)
  · exact ⟨t, used, events, positive, path, Or.inl stop⟩
  · obtain ⟨u, elapsed, queue, decision | ⟨resumed, lastWF, lastCards⟩⟩ :=
      advance_trigger_tail t rest nextWF (cards ▸ reads) route
    · exact ⟨u, used + elapsed, events, by omega, by simpa only [List.append_nil] using path.append queue, Or.inl decision⟩
    · exact ⟨u, used + elapsed, events, by omega, by simpa only [List.append_nil] using path.append queue,
        Or.inr ⟨resumed, lastWF, lastCards.trans cards⟩⟩

/-- The normal Draw Phase either skips its draw, stops for a decision, or completes it
and reaches the original Main continuation. -/
theorem advance_draw_phase {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = .phase .draw :: .phase .main :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun frame => !frame.isWork) = true ∨
        (t.pending = .phase .main :: rest ∧ t.WF ∧ t.cards = s.cards)) := by
  let p := s.active.getD ⟨0⟩
  let continuation := .phase .main :: rest
  have head : ∀ f, continuation.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
    intro f whereAt
    have : f = .phase .main := (Option.some.inj whereAt).symm
    subst f
    exact ⟨rfl, by intro q h; cases h⟩
  by_cases skip : s.hasControlledMod p .skipDrawPhase = true
  · let raw := { s with pending := continuation }
    have rule : microStep0 s = some (raw, []) := by
      simp only [microStep0, pending, (show s.hasControlledMod (s.active.getD ⟨0⟩) .skipDrawPhase = true
        from skip), ite_true, raw, continuation]
    obtain ⟨t, used, events, positive, path, afterWF, cards, route⟩ :=
      advance_rule_with_adds pending rfl rule (wf.congr rfl rfl rfl rfl) rfl reads
    have tail : ObservedWorkStack continuation t.pending := route
    generalize stack : t.pending = frames at tail
    cases tail with
    | empty => exact ⟨t, used, events, positive, path, Or.inl (by rw [stack]; rfl)⟩
    | resume => exact ⟨t, used, events, positive, path, Or.inr ⟨stack, afterWF, cards⟩⟩
    | queue q nonempty =>
      have queueStack := stack.trans (insertTriggers_front q continuation head)
      obtain ⟨u, elapsed, _, _, _, run, decisionStack, decision⟩ :=
        advance_triggers_to_decision t afterWF q continuation queueStack (cards ▸ reads) (Or.inl nonempty)
      exact ⟨u, used + elapsed, events, by omega, by simpa only [List.append_nil] using path.append run,
        Or.inl (by simp [decisionStack, decision])⟩
  · let raw := { s with phase := .draw, pending := .draw p s.drawCount :: continuation }
    have rule : microStep0 s = some (raw, []) := by
      have takes := Bool.eq_false_iff.mpr skip
      simp only [microStep0, pending, (show s.hasControlledMod (s.active.getD ⟨0⟩) .skipDrawPhase = false
        from takes), Bool.false_eq_true, ↓reduceIte, raw, continuation, p]
    obtain ⟨t, used, events, positive, path, afterWF, cards, route⟩ :=
      advance_rule_with_adds pending rfl rule (wf.congr rfl rfl rfl rfl) rfl reads
    have finish (tail : List Frame) (draw : t.pending = .draw p s.drawCount :: tail)
        (queued : TriggerWorkTail continuation tail) :
        ∃ u steps emitted, 0 < steps ∧ AdvancePrefix s u steps emitted ∧
          (u.pending.head?.all (fun frame => !frame.isWork) = true ∨
            (u.pending = .phase .main :: rest ∧ u.WF ∧ u.cards = s.cards)) := by
      obtain ⟨u, elapsed, later, _, ran, stop | ⟨last, finalWF, finalCards⟩⟩ :=
        advance_draw_with_adds afterWF (cards ▸ reads) draw queued head
      · exact ⟨u, used + elapsed, events ++ later, by omega, path.append ran, Or.inl stop⟩
      · exact ⟨u, used + elapsed, events ++ later, by omega, path.append ran,
          Or.inr ⟨last, finalWF, finalCards.trans cards⟩⟩
    change ObservedWorkStack (.draw p s.drawCount :: continuation) t.pending at route
    generalize stack : t.pending = frames at route
    cases route with
    | empty => exact ⟨t, used, events, positive, path, Or.inl (by rw [stack]; rfl)⟩
    | resume => exact finish continuation stack (Or.inl rfl)
    | queue q nonempty => exact finish _ stack ((show TriggerWorkTail continuation continuation from Or.inl rfl).insert
        head q nonempty)

end Riftbound

end
