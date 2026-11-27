module

public import Riftbound.Invariant.BeginningWork

/-!
# From Beginning to the next decision (I12)
-/

@[expose] public section

namespace Riftbound

/-- Main sets the new phase, clears the Rune Pool and runs Cleanup. The engine then waits at
priority, a Showdown, an ordinary trigger choice or another decision, or finishes the game. -/
theorem advance_main_to_decision {s : GameState} {p : PlayerId} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = [.phase .main, .priority p]) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  let rest := [Frame.priority p]
  let raw := { s with phase := .main, pending := .cleanup :: rest, pools := {} }
  let emitted := [Event.phaseStarted (s.active.getD ⟨0⟩) .main]
  have step : microStep0 s = some (raw, emitted) := by
    simp only [microStep0, pending, raw, emitted, rest]
  obtain ⟨mid, used, events, positive, path, midWF, cards, route⟩ :=
    advance_rule_with_adds pending rfl step (microStep_wf0 wf step) rfl reads
  have head : ∀ f, rest.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
    intro f first
    have : f = .priority p := (Option.some.inj first).symm
    subst f
    exact ⟨rfl, by intro q h; cases h⟩
  have insertion (frames : List Frame) (track : TriggerWorkTail rest frames)
      (q : List PendTrigger) (ne : q ≠ []) : TriggerWorkTail rest (insertTriggers q frames) :=
    track.insert head q ne
  have finish (tail : List Frame) (stack : mid.pending = .cleanup :: tail) (track : TriggerWorkTail rest tail) :
      ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
        t.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨t, elapsed, later, _, cleanup, stop | ⟨waiting, afterWF, afterCards⟩⟩ :=
      advance_cleanup_with_adds midWF (cards ▸ reads) stack (TriggerWorkTail rest) track insertion
    · exact ⟨t, used + elapsed, events ++ later, by omega, path.append cleanup, stop⟩
    · obtain ⟨u, queued, triggers, decision | ⟨normal, _, _⟩⟩ :=
        advance_trigger_tail t rest afterWF (afterCards ▸ cards ▸ reads) waiting
      · exact ⟨u, used + elapsed + queued, _, by omega,
          by simpa only [List.append_nil] using (path.append cleanup).append triggers, decision⟩
      · exact ⟨u, used + elapsed + queued, _, by omega,
          by simpa only [List.append_nil] using (path.append cleanup).append triggers, by rw [normal]; rfl⟩
  change ObservedWorkStack (.cleanup :: rest) mid.pending at route
  generalize stack : mid.pending = frames at route
  cases route with
  | empty => exact ⟨mid, used, events, positive, path, by rw [stack]; rfl⟩
  | resume => exact finish rest stack (Or.inl rfl)
  | queue q nonempty => exact finish _ stack (insertion rest (Or.inl rfl) q nonempty)

private def advancesToStack (s : GameState) (rest : List Frame) : Prop :=
  ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
    (t.pending.head?.all (fun f => !f.isWork) = true ∨
      (t.pending = rest ∧ t.WF ∧ t.cards = s.cards))

/-- Execute the normal new turn from Beginning through Hold, Channel, Draw and Main.
The actual engine reaches a decision or the end of the game in finitely many steps. -/
theorem advance_beginning_to_decision {s : GameState} {p : PlayerId} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = (turnFrames p).drop 1) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      t.pending.head?.all (fun f => !f.isWork) = true := by
  have continueFrom {state : GameState} {rest : List Frame}
      (segment : advancesToStack state rest) (known : MightRead.database state.cards)
      (next : ∀ t : GameState, t.pending = rest → t.WF → MightRead.database t.cards →
        ∃ u used events, 0 < used ∧ AdvancePrefix t u used events ∧
          u.pending.head?.all (fun f => !f.isWork) = true) :
      ∃ u used events, 0 < used ∧ AdvancePrefix state u used events ∧
        u.pending.head?.all (fun f => !f.isWork) = true := by
    obtain ⟨t, used, events, positive, path, stop | ⟨atRest, tWF, cards⟩⟩ := segment
    · exact ⟨t, used, events, positive, path, stop⟩
    · obtain ⟨u, later, emitted, _, ran, done⟩ := next t atRest tWF (cards ▸ known)
      exact ⟨u, used + later, events ++ emitted, by omega, path.append ran, done⟩
  refine continueFrom (advance_beginning_to_holds wf reads pending) reads ?_
  intro atHolds ready holdsWF holdsReads
  refine continueFrom (advance_holds_to_channel holdsWF holdsReads ready) holdsReads ?_
  intro atChannel ready channelWF channelReads
  refine continueFrom (advance_channel_to_draw channelWF channelReads ready) channelReads ?_
  intro atDraw ready drawWF drawReads
  refine continueFrom (advance_draw_phase drawWF drawReads ready) drawReads ?_
  intro atMain ready mainWF mainReads
  exact advance_main_to_decision mainWF mainReads ready

end Riftbound

end
