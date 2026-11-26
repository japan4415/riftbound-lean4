module

public import Riftbound.Engine.Step

/-!
# Termination of the opening draws (I12)

From `setupHands`, drawing the initial hands reaches a player mulligan or a Burn Out chance
decision after a bounded number of work steps. The argument follows the actual work dispatcher
and accounts for the final zero-count draw frame.
-/

@[expose] public section

namespace Riftbound

private theorem setup_noTriggers {s : GameState} (phase : s.phase = .setup) (events : List Event) :
    s.withTriggers events = s := by
  rcases withTriggers_cases s events with ⟨_, _, noSetup⟩ | unchanged | ⟨_, _, noSetup, _⟩
  · exact (noSetup phase).elim
  · rw [unchanged]
    cases s
    simp_all [GameState.recordTurnEvents]
  · exact (noSetup phase).elim

private theorem advance_onDecision (fuel : Nat) {s : GameState} {events : List Event}
    (decision : s.pending.head?.all (fun f => !f.isWork) = true) :
    advance fuel s events = .ok (s, events) := by
  cases next : s.pending with
  | nil => cases fuel <;> simp [advance, next]
  | cons frame rest =>
    have notWork : frame.isWork = false := by simpa [next] using decision
    cases fuel <;> simp [advance, next, notWork]

private theorem advance_setupDraw_then (count fuel : Nat) (s : GameState) (events : List Event)
    (p : PlayerId) (start : Option Nat) (rest : List Frame) {restOfBatch : List Frame}
    (phase : s.phase = .setup) (pending : s.pending = .draw p count start :: rest)
    (finish : ∀ t ev, t.phase = .setup → t.pending = rest →
      ∃ result, advance fuel t ev = .ok result ∧
        ((∃ q frames, result.1.pending = .chanceBurnOut q :: frames) ∨ result.1.pending = restOfBatch))
    : ∃ result, advance (count + 1 + fuel) s events = .ok result ∧
      ((∃ q frames, result.1.pending = .chanceBurnOut q :: frames) ∨ result.1.pending = restOfBatch) := by
  induction count generalizing s events start with
  | zero =>
    let next := { s with pending := rest }
    have work : workStep s = some (next, start.toList.map (.drewGroup p)) := by
      simp only [workStep, pending, microStep, microStep0, Option.map_some]
      rw [setup_noTriggers (s := next) phase]
    rw [show 0 + 1 + fuel = fuel + 1 by omega]
    simpa only [advance, pending, Frame.isWork, ite_true, work] using
      finish next (events ++ start.toList.map (.drewGroup p)) phase rfl
  | succ count ih =>
    rw [show count + 1 + 1 + fuel = (count + 1 + fuel) + 1 by omega]
    cases drawn : drawOne s p with
    | none =>
      let next := { s with pending := .chanceBurnOut p :: .draw p (count + 1) start :: rest }
      have work : workStep s = some (next, []) := by
        simp only [workStep, pending, microStep, microStep0, drawn, Option.map_some]
        rw [setup_noTriggers (s := next) phase]
      simpa only [advance, pending, Frame.isWork, ite_true, work, List.append_nil] using
        (show ∃ result, advance (count + 1 + fuel) next events = .ok result ∧
            ((∃ q frames, result.1.pending = .chanceBurnOut q :: frames) ∨
              result.1.pending = restOfBatch) from
          ⟨_, advance_onDecision _ rfl, Or.inl ⟨_, _, rfl⟩⟩)
    | some draw =>
      obtain ⟨board, en⟩ := draw
      let began := start <|> some ((s.zone (.player p .hand)).length)
      let next := { board.noteDraw p with pending := .draw p count began :: rest }
      have samePhase : next.phase = .setup := (drawOne_meta drawn).phase.trans phase
      have work : workStep s = some (next, en ++ [.drew p]) := by
        simp only [workStep, pending, microStep, microStep0, drawn, Option.map_some]
        rw [setup_noTriggers (s := next) samePhase]
      simpa only [advance, pending, Frame.isWork, ite_true, work] using
        ih next (events ++ (en ++ [.drew p])) began samePhase rfl

private theorem advance_openingDraws (players : List PlayerId) (s : GameState)
    (events : List Event) (rest : List Frame)
    (phase : s.phase = .setup) (pending : s.pending = players.map (fun p => Frame.draw p 4) ++ rest)
    (decision : rest.head?.all (fun f => !f.isWork) = true) :
    ∃ result, advance (5 * players.length) s events = .ok result ∧
      ((∃ q frames, result.1.pending = .chanceBurnOut q :: frames) ∨ result.1.pending = rest) := by
  induction players generalizing s events with
  | nil =>
    have stop : s.pending.head?.all (fun f => !f.isWork) = true := by simpa [pending] using decision
    exact ⟨_, advance_onDecision _ stop, Or.inr (by simpa using pending)⟩
  | cons p players ih =>
    have frames : s.pending = .draw p 4 :: (players.map (fun p => Frame.draw p 4) ++ rest) :=
      by simpa only [List.map_cons, List.cons_append] using pending
    simpa only [List.length_cons, Nat.mul_succ, Nat.add_comm (5 * players.length) 5] using
      advance_setupDraw_then 4 (5 * players.length) s events p none _ phase frames ih

/-- Opening hands reach a mulligan or a chance decision within one work step to enqueue the draws
and five work steps per seat. The bound counts drawing four cards and consuming the empty draw
frame. Exhausting a deck asks for a Burn Out decision within the same bound. -/
theorem advance_setupHands_bound {s : GameState} {events : List Event} {rest : List Frame}
    (phase : s.phase = .setup) (pending : s.pending = .setupHands :: rest)
    (seats : s.participatingOrder ≠ []) :
    ∃ result, advance (5 * s.participatingOrder.length + 1) s events = .ok result ∧
      (∃ p frames, result.1.pending = .mulligan p 0 :: frames ∨
        result.1.pending = .chanceBurnOut p :: frames) := by
  let afterDraws := s.participatingOrder.map (fun p => Frame.mulligan p 0) ++ .beginTurn :: rest
  let next := { s with pending := s.participatingOrder.map (fun p => Frame.draw p 4) ++ afterDraws }
  have work : workStep s = some (next, []) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some]
    simp only [List.append_assoc]
    change some (next.withTriggers _, []) = _
    rw [setup_noTriggers (s := next) phase]
  obtain ⟨first, tail, firstMulligan⟩ : ∃ first tail, afterDraws = .mulligan first 0 :: tail := by
    cases order : s.participatingOrder with
    | nil => exact (seats order).elim
    | cons p ps =>
      exact ⟨p, ps.map (fun q => Frame.mulligan q 0) ++ .beginTurn :: rest, by
        simp [afterDraws, order]⟩
  have decision : afterDraws.head?.all (fun f => !f.isWork) = true := by
    rw [firstMulligan]
    rfl
  obtain ⟨result, done, choice⟩ :=
    advance_openingDraws s.participatingOrder next events afterDraws phase rfl decision
  refine ⟨result, ?_, ?_⟩
  · simpa only [advance, pending, Frame.isWork, ite_true, work, List.append_nil] using done
  · rcases choice with ⟨p, frames, h⟩ | h
    · exact ⟨p, frames, Or.inr h⟩
    · exact ⟨first, tail, Or.inl (h.trans firstMulligan)⟩

end Riftbound

end
