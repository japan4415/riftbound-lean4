module

public import Riftbound.Invariant.Turn

/-!
# The clock (TR 408.2)

When time is called, the turn that is going on is played to its end, and 3 turns more. Then the game
is over: the player 2 points ahead wins, any other score is a draw. The clock is an actor of its
own; `timeCalled` is its only answer. It sets the turn after which the game ends
(`GameState.clock`); the beginning of the next turn is where the game ends.

These are the local facts of I14 (roadmap.md): what calling time does, what a turn does when the
clock has run out and when it has not, and how many turns remain. That the number of turns after the
call is finite in every run is the sum of these facts and of the fact that no other step changes
the turn or the clock, which is not proved here.
-/

@[expose] public section

namespace Riftbound

/-- Calling time sets the clock, whatever question is open. -/
theorem applyFrame0_timeCalled (s : GameState) (actor : Actor) :
    applyFrame0 s ⟨actor, .timeCalled⟩ = some ({ s with clock := some (s.turn + 3) }, []) := by
  unfold applyFrame0
  split <;> simp_all

/-- **Calling time sets the last turn** (TR 408.2): the game ends after 3 more turns than the one
that is going on. Nothing else changes: not the turn, not the result, not the stack. -/
theorem timeCalled_sets_clock {s s' : GameState} {es : List Event} {actor : Actor}
    (h : applyFrame0 s ⟨actor, .timeCalled⟩ = some (s', es)) :
    s'.clock = some (s.turn + 3) ∧ s'.turn = s.turn ∧ s'.result = s.result ∧
      s'.pending = s.pending := by
  rw [applyFrame0_timeCalled] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A legal call of time is the clock's, once, in a 1v1 game under the Tournament Rules, after the
first turn has begun (TR 408.2). -/
theorem legal_timeCalled {s : GameState} {a : Action} (hk : a.kind = .timeCalled)
    (h : LegalFrame s a) :
    a.actor = .clock ∧ s.config.ruleSet.isTournament = true ∧ s.playerCount = 2 ∧
      s.clock = none ∧ s.active.isSome = true := by
  unfold LegalFrame at h
  rw [hk] at h
  split at h <;> first | exact h | (simp_all; done)

/-- The clock has run out exactly when the turn that began last is the one the clock named or a
later one. -/
theorem clockDue_iff (s : GameState) :
    s.clockDue = true ↔ ∃ lim, s.clock = some lim ∧ lim ≤ s.turn := by
  unfold GameState.clockDue
  cases hc : s.clock with
  | none => simp
  | some lim => simp

/-- **Three more turns** (TR 408.2): when time is called in turn `t`, the clock has not run out at
the beginning of the turns `t + 1`, `t + 2` and `t + 3`, and has at the next one. -/
theorem three_more_turns {s : GameState} {t : Nat} (hc : s.clock = some (t + 3)) :
    (s.turn = t → s.clockDue = false) ∧ (s.turn = t + 1 → s.clockDue = false) ∧
      (s.turn = t + 2 → s.clockDue = false) ∧ (s.turn = t + 3 → s.clockDue = true) := by
  unfold GameState.clockDue
  rw [hc]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [h]

/-- **The game ends when the clock has run out** (TR 408.2): the next turn does not begin; the game
is over, and the result is decided by the points: the player 2 points ahead wins, any other score
is a draw. -/
theorem beginTurn_ends {s : GameState} {rest : List Frame} (hp : s.pending = .beginTurn :: rest)
    (hd : s.clockDue = true) :
    ∃ s', microStep0 s = some (s', []) ∧
      s'.result = some (gameOnTime (s.pointsOf ⟨0⟩) (s.pointsOf ⟨1⟩)) ∧
        s'.pending = [] ∧ s'.turn = s.turn := by
  refine ⟨beginTurnStep s rest, ?_, ?_⟩
  · unfold microStep0
    rw [hp]
  · simp [beginTurnStep, hd]

/-- **The turn that begins is not past the last turn** (TR 408.2): when the clock has not run out,
the next turn begins, and it is not later than the one the clock named. -/
theorem beginTurn_next {s : GameState} {rest : List Frame} (hp : s.pending = .beginTurn :: rest)
    (hd : s.clockDue = false) :
    ∃ s', microStep0 s = some (s', []) ∧ s'.turn = s.turn + 1 ∧ s'.clock = s.clock ∧
      ∀ lim, s.clock = some lim → s'.turn ≤ lim := by
  refine ⟨beginTurnStep s rest, ?_, ?_⟩
  · unfold microStep0
    rw [hp]
  · have hd' : s.clockDue ≠ true := by simp [hd]
    refine ⟨by simp [beginTurnStep, hd], by simp [beginTurnStep, hd, GameState.mapObjects],
      fun lim hl => ?_⟩
    simp only [GameState.clockDue, hl, decide_eq_false_iff_not, Nat.not_le] at hd
    simp [beginTurnStep, hd'] 
    omega

end Riftbound

end
