module

public import Riftbound.Invariant.Clock

/-!
# The judge's draw (TR 410.1, 505.6)

The players may agree to a draw (TR 410.1), and a loop that nobody can or will break is a draw
(TR 505.6). Both come from outside the game: the judge declares the draw (`declareDraw`), under
the Tournament Rules. The engine does not find loops (tournament-model.md §5). A draw ends the game
at once, with nothing left to answer.
-/

@[expose] public section

namespace Riftbound

/-- Declaring a draw ends the game at once, whatever question is open. -/
theorem applyFrame0_declareDraw (s : GameState) (actor : Actor) :
    applyFrame0 s ⟨actor, .declareDraw⟩ =
      some ({ s with result := some .draw, pending := [] }, []) := by
  unfold applyFrame0
  cases s.pending with
  | nil => rfl
  | cons frame _ => cases frame <;> rfl

/-- **A declared draw is a draw** (TR 410.1, 505.6): the result is a draw, and no frame is left. -/
theorem declareDraw_draws {s s' : GameState} {es : List Event} {actor : Actor}
    (h : applyFrame0 s ⟨actor, .declareDraw⟩ = some (s', es)) :
    s'.result = some .draw ∧ s'.pending = [] := by
  rw [applyFrame0_declareDraw] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨rfl, rfl⟩

/-- A legal declaration of a draw is the judge's, under the Tournament Rules. -/
theorem legal_declareDraw {s : GameState} {a : Action} (hk : a.kind = .declareDraw)
    (h : LegalFrame s a) : a.actor = .judge ∧ s.config.ruleSet.isTournament = true := by
  rcases hp : s.pending with _ | ⟨frame, rest⟩
  · simpa only [LegalFrame, hp, hk] using h
  · cases frame <;> simpa only [LegalFrame, hp, hk] using h

/-- A legal judge declaration returns the draw state immediately at any work limit. -/
theorem step_declareDraw_terminal (fuel : Nat) {s : GameState}
    (legal : Legal s ⟨.judge, .declareDraw⟩) :
    step fuel s ⟨.judge, .declareDraw⟩ =
      .ok ({ s with result := some .draw, pending := [] }, []) := by
  let action : Action := ⟨.judge, .declareDraw⟩
  let final := { s with result := some .draw, pending := [] }
  have noCost : s.actionDeathCostChoice action = none := by
    cases stack : s.pending with
    | nil => simp [GameState.actionDeathCostChoice, stack]
    | cons frame rest =>
      cases frame <;> simp [GameState.actionDeathCostChoice, GameState.actionKillCosts, stack, action,
        GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil]
  have applied : applyDeclaredAction s action = some (final, []) := by
    rw [applyDeclaredAction, noCost, applyAction_of_ne (by decide : action.kind ≠ .concede), applyFrame]
    simp [action, final, applyFrame0_declareDraw, GameState.paySurcharge, extraEvents,
      GameState.actionTransitionEvents, withTriggers_nil]
  change step fuel s action = .ok (final, [])
  rw [step, ite_eq_left legal, applied]
  cases fuel <;> rfl

/-- **When the game is over nothing is legal** (TR 410.1, 505.6): after a draw, or any result,
no answer is accepted. -/
theorem not_legal_of_result {s : GameState} {r : GameResult} (h : s.result = some r)
    (a : Action) : ¬ Legal s a := by
  intro hl
  have := hl.1
  rw [h] at this
  exact absurd this (by simp)

end Riftbound

end
