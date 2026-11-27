module

public import Riftbound.Invariant.ObservedCleanupWork
public import Riftbound.Invariant.TurnDrawWork

/-!
# Beginning Phase and Hold work (I12)

Beginning triggers and Hold scoring can create cleanup, additional draws, and trigger queues.
The engine resolves these in their scheduled order before Channel.
-/

@[expose] public section

namespace Riftbound

private theorem scoreHolds_head (rest : List Frame) :
    ∀ f, (Frame.scoreHolds :: rest).head? = some f →
      f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
  intro f head
  cases Option.some.inj head
  exact ⟨rfl, by intro q h; cases h⟩

private theorem channel_head (rest : List Frame) :
    ∀ f, (Frame.phase .channel :: rest).head? = some f →
      f.isResolution = false ∧ ∀ q, f ≠ .triggers q := by
  intro f head
  cases Option.some.inj head
  exact ⟨rfl, by intro q h; cases h⟩

/-- Beginning queues the phase triggers, runs Cleanup, and draws the cards due at Beginning
before handing off to Hold scoring. -/
theorem advance_beginning_to_holds {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = .phase .beginning :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun f => !f.isWork) = true ∨
        (t.pending = .scoreHolds :: rest ∧ t.WF ∧ t.cards = s.cards)) := by
  let p := s.active.getD ⟨0⟩
  let draw := Frame.draw p (s.extraDraws p)
  let holds := Frame.scoreHolds :: rest
  let raw := { s with phase := .beginning, pending := .cleanup :: draw :: holds }
  have rule : microStep0 s = some (raw, [Event.phaseStarted p .beginning]) := by
    simp only [microStep0, pending, p, raw, draw, holds]
  obtain ⟨mid, used, events, positive, path, midWF, cards, route⟩ :=
    advance_rule_with_adds pending rfl rule (microStep_wf0 wf rule) rfl reads
  let keeps := fun frames => ∃ tail, frames = draw :: tail ∧ TriggerWorkTail holds tail
  have insertKeeps (frames : List Frame) (track : keeps frames) (q : List PendTrigger) (ne : q ≠ []) :
      keeps (insertTriggers q frames) := by
    obtain ⟨tail, rfl, seen⟩ := track
    exact ⟨_, rfl, seen.insert (scoreHolds_head rest) q ne⟩
  have base : keeps (draw :: holds) := ⟨holds, rfl, Or.inl rfl⟩
  have finish (tail : List Frame) (stack : mid.pending = .cleanup :: tail) (tracks : keeps tail) :
      ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
        (t.pending.head?.all (fun f => !f.isWork) = true ∨
          (t.pending = .scoreHolds :: rest ∧ t.WF ∧ t.cards = s.cards)) := by
    obtain ⟨after, elapsed, later, _, cleanup, stop | ⟨⟨waiting, draws, tracked⟩, afterWF, afterCards⟩⟩ :=
      advance_cleanup_with_adds midWF (cards ▸ reads) stack keeps tracks insertKeeps
    · exact ⟨after, used + elapsed, events ++ later, by omega, path.append cleanup, Or.inl stop⟩
    · obtain ⟨t, extra, emitted, _, batch, final⟩ :=
        advance_draw_with_adds afterWF (afterCards ▸ cards ▸ reads) draws tracked (scoreHolds_head rest)
      exact ⟨t, used + elapsed + extra, _, by omega, (path.append cleanup).append batch,
        final.imp_right (fun ⟨atHolds, finalWF, known⟩ => ⟨atHolds, finalWF, known.trans (afterCards.trans cards)⟩)⟩
  change ObservedWorkStack (.cleanup :: draw :: holds) mid.pending at route
  generalize stack : mid.pending = frames at route
  cases route with
  | empty => exact ⟨mid, used, events, positive, path, Or.inl (by rw [stack]; rfl)⟩
  | resume => exact finish _ stack base
  | queue q nonempty => exact finish _ stack (insertKeeps _ base q nonempty)

/-- Hold scoring may replace points with draws. Resolve the draws, Cleanup and any
leading ordinary triggers before handing off to Channel. -/
theorem advance_holds_to_channel {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = .scoreHolds :: .phase .channel :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun f => !f.isWork) = true ∨
        (t.pending = .phase .channel :: rest ∧ t.WF ∧ t.cards = s.cards)) := by
  let p := s.active.getD ⟨0⟩
  let result := hold s p
  let count := scoreDrawCount p result.2
  let next := Frame.phase .channel :: rest
  let raw := { result.1 with phase := .beginning, pending := .draw p count :: .cleanup :: next }
  have rule : microStep0 s = some (raw, result.2) := by
    simp only [microStep0, pending, raw, p, result, count, next]
  have known : raw.cards = s.cards := by
    change result.1.cards = s.cards
    obtain ⟨board, safe, changePoints⟩ := hold_safeP s p
    have cards := congrArg GameState.cards safe.same
    rcases changePoints with normal | ⟨who, points, withPoints⟩
    · rw [show result.1 = board from normal]
      exact cards
    · rw [show result.1 = board.gainPoints who points from withPoints]
      exact cards
  obtain ⟨mid, used, events, positive, path, midWF, cards, route⟩ :=
    advance_rule_with_adds pending rfl rule (microStep_wf0 wf rule) known reads
  let keeps := fun frames => ∃ tail, frames = .cleanup :: tail ∧ TriggerWorkTail next tail
  have insertKeeps (frames : List Frame) (track : keeps frames) (q : List PendTrigger) (ne : q ≠ []) :
      keeps (insertTriggers q frames) := by
    obtain ⟨tail, rfl, seen⟩ := track
    exact ⟨_, rfl, seen.insert (channel_head rest) q ne⟩
  have insertNext (frames : List Frame) (track : TriggerWorkTail next frames) (q : List PendTrigger) (ne : q ≠ []) :
      TriggerWorkTail next (insertTriggers q frames) := track.insert (channel_head rest) q ne
  have base : keeps (.cleanup :: next) := ⟨next, rfl, Or.inl rfl⟩
  have finish (tail : List Frame) (stack : mid.pending = .draw p count :: tail) (tracks : keeps tail) :
      ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
        (t.pending.head?.all (fun f => !f.isWork) = true ∨
          (t.pending = .phase .channel :: rest ∧ t.WF ∧ t.cards = s.cards)) := by
    obtain ⟨after, elapsed, later, _, draws, stop | ⟨⟨waiting, clear, tracked⟩, afterWF, afterCards⟩⟩ :=
      advance_draw_until midWF (cards ▸ reads) stack keeps tracks insertKeeps
    · exact ⟨after, used + elapsed, events ++ later, by omega, path.append draws, Or.inl stop⟩
    · obtain ⟨ready, extra, emitted, _, cleanup, outcome⟩ :=
        advance_cleanup_with_adds afterWF (afterCards ▸ cards ▸ reads) clear (TriggerWorkTail next) tracked insertNext
      have leading := (path.append draws).append cleanup
      rcases outcome with stop | ⟨cleanupTrack, readyWF, readyCards⟩
      · exact ⟨ready, used + elapsed + extra, _, by omega, leading, Or.inl stop⟩
      · obtain ⟨t, triggers, finalized, final⟩ :=
          advance_trigger_tail ready next readyWF (readyCards ▸ afterCards ▸ cards ▸ reads) cleanupTrack
        exact ⟨t, used + elapsed + extra + triggers, _, by omega,
          by simpa only [List.append_nil] using leading.append finalized,
          final.imp_right (fun ⟨atChannel, finalWF, known⟩ =>
            ⟨atChannel, finalWF, known.trans (readyCards.trans (afterCards.trans cards))⟩)⟩
  change ObservedWorkStack (.draw p count :: .cleanup :: next) mid.pending at route
  generalize stack : mid.pending = frames at route
  cases route with
  | empty => exact ⟨mid, used, events, positive, path, Or.inl (by rw [stack]; rfl)⟩
  | resume => exact finish _ stack base
  | queue q nonempty => exact finish _ stack (insertKeeps _ base q nonempty)

end Riftbound

end
