module

public import Riftbound.Invariant.Turn

/-!
# The clock (TR 408)

The clock is an actor of its own and `timeCalled` sets the last scheduled turn. After the
scheduled turns, the deadline decides the game or tied points send a tied single-elimination
match to sudden death. The run-level preservation and the finite bound for hard deadlines
are proved in `ClockRun.lean`.
-/

@[expose] public section

namespace Riftbound

/-- Calling time sets the clock, whatever question is open. -/
theorem applyFrame0_timeCalled (s : GameState) (actor : Actor) :
    applyFrame0 s ⟨actor, .timeCalled⟩ =
      some ({ s with clock := some (s.config.ruleSet.callClock s.turn) }, []) := by
  unfold applyFrame0
  cases s.pending with
  | nil => rfl
  | cons frame _ => cases frame <;> rfl

/-- **Calling time sets the last turn** (TR 408.2): the game ends after 3 more turns than the one
that is going on. Nothing else changes: not the turn, not the result, not the stack. -/
theorem timeCalled_sets_clock {s s' : GameState} {es : List Event} {actor : Actor}
    (h : applyFrame0 s ⟨actor, .timeCalled⟩ = some (s', es)) :
    s'.clock = some (s.config.ruleSet.callClock s.turn) ∧ s'.turn = s.turn ∧ s'.result = s.result ∧
      s'.pending = s.pending := by
  rw [applyFrame0_timeCalled] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A legal call of time is the clock's, once, in a two-sided Tournament game after the
first turn has begun (TR 408.2). -/
theorem legal_timeCalled {s : GameState} {a : Action} (hk : a.kind = .timeCalled)
    (h : LegalFrame s a) :
    a.actor = .clock ∧ s.config.ruleSet.isTournament = true ∧ s.config.mode.hasTwoSides = true ∧
      s.clock = none ∧ s.active.isSome = true := by
  rcases hp : s.pending with _ | ⟨frame, rest⟩
  · simpa only [LegalFrame, hp, hk] using h
  · cases frame <;> simpa only [LegalFrame, hp, hk] using h

/-- The clock has run out exactly when the turn that began last is the one the clock named or a
later one. -/
theorem clockDue_iff (s : GameState) :
    s.clockDue = true ↔ ∃ clock, s.clock = some clock ∧ clock.lastTurn ≤ s.turn := by
  unfold GameState.clockDue
  cases hc : s.clock with
  | none => simp
  | some lim => simp

/-- **Three more turns** (TR 408.2): when time is called in turn `t`, the clock has not run out at
the beginning of the turns `t + 1`, `t + 2` and `t + 3`, and has at the next one. -/
theorem three_more_turns {s : GameState} {t : Nat} {clock : RoundClock}
    (hc : s.clock = some clock) (limit : clock.lastTurn = t + 3) :
    (s.turn = t → s.clockDue = false) ∧ (s.turn = t + 1 → s.clockDue = false) ∧
      (s.turn = t + 2 → s.clockDue = false) ∧ (s.turn = t + 3 → s.clockDue = true) := by
  simp only [GameState.clockDue, hc, limit]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [h]

/-- A clock that requires a result prevents the next turn from beginning (TR 408.2, 408.4). -/
theorem beginTurn_ends {s : GameState} {rest : List Frame} {result : GameResult}
    (hp : s.pending = .beginTurn :: rest) (hd : s.clockConclusion = some result) :
    ∃ s', microStep0 s = some (s', []) ∧
      s'.result = some result ∧
        s'.pending = [] ∧ s'.turn = s.turn := by
  refine ⟨beginTurnStep s rest, ?_, ?_⟩
  · unfold microStep0
    rw [hp]
  · simp [beginTurnStep, hd]

/-- When sudden death is unavailable, play can continue only before the clock's deadline. -/
theorem clockConclusion_none_lt {s : GameState} {clock : RoundClock}
    (hc : s.clock = some clock) (hard : clock.allowsSuddenDeath = false)
    (noneDue : s.clockConclusion = none) : s.turn < clock.lastTurn := by
  by_cases due : s.turn < clock.lastTurn
  · exact due
  let second : PlayerId := ⟨if s.config.mode.isTeamDuel then 2 else 1⟩
  cases result : clock.resultOnTime (s.pointsOf ⟨0⟩) (s.pointsOf second) with
  | none => exact False.elim (clock.resultOnTime_ne_none _ _ hard result)
  | some r =>
    simp [GameState.clockConclusion, hc, due, show clock.resultOnTime (s.pointsOf ⟨0⟩)
      (s.pointsOf ⟨if s.config.mode.isTeamDuel then 2 else 1⟩) = some r from result] at noneDue

/-- A turn can begin before the clock's deadline or continue in sudden death. -/
theorem beginTurn_next {s : GameState} {rest : List Frame} (hp : s.pending = .beginTurn :: rest)
    (hd : s.clockConclusion = none) :
    ∃ s', microStep0 s = some (s', []) ∧ s'.turn = s.turn + 1 ∧ s'.clock = s.clock ∧
      ∀ clock, s.clock = some clock → clock.allowsSuddenDeath = false → s'.turn ≤ clock.lastTurn := by
  refine ⟨beginTurnStep s rest, ?_, ?_⟩
  · unfold microStep0
    rw [hp]
  · refine ⟨by simp [beginTurnStep, hd],
      by simp [beginTurnStep, hd, GameState.mapObjects, GameState.mapObjectsAt], ?_⟩
    intro clock hc hard
    simpa [beginTurnStep, hd] using Nat.succ_le_of_lt (clockConclusion_none_lt hc hard hd)

/-- The sudden-death point ends the game before any trigger or player decision can be queued. -/
theorem suddenDeath_ends {s : GameState} {es : List Event} {p : PlayerId}
    (scored : s.suddenDeathScorer es = some p) :
    (s.withTriggers es).result = some (.won (s.config.mode.sideSeats p)) ∧
      (s.withTriggers es).pending = [] := by
  simp [GameState.withTriggers, GameState.eventWinner, scored]

end Riftbound

end
