module

public import Riftbound.Invariant.MovementWork
public import Riftbound.Invariant.ExpirationWork

/-! # Concession and the automatic handoff in War (I12) -/

@[expose] public section

namespace Riftbound

private theorem applyFreeForAllConcession_cards {s board : GameState}
    {p : PlayerId} {blank : CardId} {events : List Event}
    (applied : applyFreeForAllConcession s p blank = some (board, events)) : board.cards = s.cards := by
  have withdrew : (s.withdrawSeat p).cards = s.cards := by
    unfold GameState.withdrawSeat
    split <;> rfl
  rcases applyFreeForAllConcession_cases applied with ⟨_, rfl⟩ | ⟨_, removed, rfl⟩
  · exact withdrew
  · have metadata := (removePlayerObjects_safe removed).same
    unfold SameMeta at metadata
    exact (congrArg GameState.cards metadata).trans withdrew

/-- A concession can be certified from the actual stack left by removing the player. -/
def concessionWorkSupported (s : GameState) (p : PlayerId) : Bool :=
  (applyFreeForAllConcession s p concessionBattlefieldToken.id).any (fun (board, _) =>
    board.pending.head?.all (fun frame => !frame.isWork) ||
      (decide (board.pending = [.cleanup, .expireTurn, .beginTurn]) ||
        match board.pending with
        | .cleanup :: rest => isOrdinaryDecisionTail rest
        | _ => false))

/-- A certified War concession reaches an input or ends the game after removal and observation. -/
theorem step_freeForAllConcede_checked_to_decision {s : GameState} {p : PlayerId}
    (wf : s.WF) (reads : MightRead.database s.cards.withConcessionBattlefield)
    (ordinaryMight : s.cards.withConcessionBattlefield.mightTriggersAreOrdinary)
    (ordinaryAwaken : s.cards.withConcessionBattlefield.awakenTriggersAreOrdinary)
    (ffa : s.config.mode.isFreeForAll = true) (legal : Legal s ⟨.player p, .concede⟩)
    (checked : concessionWorkSupported s p = true) :
    ∃ t used events, t.pending.head?.all (fun f => !f.isWork) = true ∧
      ∀ extra, step (used + extra) s ⟨.player p, .concede⟩ = .ok (t, events) := by
  let action : Action := ⟨.player p, .concede⟩
  have noCost : s.actionDeathCostChoice action = none := by
    cases pending : s.pending with
    | nil => simp [GameState.actionDeathCostChoice, pending]
    | cons frame rest =>
      cases frame <;> simp [GameState.actionDeathCostChoice, GameState.actionKillCosts, pending, action]
  unfold concessionWorkSupported at checked
  cases applied : applyFreeForAllConcession s p concessionBattlefieldToken.id with
  | none => simp [applied] at checked
  | some result =>
    obtain ⟨board, events⟩ := result
    let raw := { board with cards := board.cards.withConcessionBattlefield }
    let notices := if raw.result.isSome then [] else events ++ s.mightyEvents raw
    have safe : raw.WF := (applyFreeForAllConcession_preservesBoard wf applied).1.congr rfl rfl rfl rfl
    have cards : raw.cards = s.cards.withConcessionBattlefield :=
      congrArg CardDB.withConcessionBattlefield (applyFreeForAllConcession_cards applied)
    have declared : applyDeclaredAction s action = some (raw.withTriggers notices, notices) := by
      change applyDeclaredAction s action = _
      rw [show applyDeclaredAction s action = applyAction s action by simp [applyDeclaredAction, noCost]]
      rw [applyAction_concede_ffa (show action.kind = .concede from rfl)
        (show action.actor = .player p from rfl) ffa, applied]
      rfl
    simp only [applied, Option.any_some, Bool.or_eq_true_iff] at checked
    have path : ∃ t used events, AdvancePrefix (raw.withTriggers notices) t used events ∧
        t.pending.head?.all (fun f => !f.isWork) = true := by
      rcases checked with waiting | cleanup
      · obtain ⟨mid, used, events, firstPath, sound, known, route⟩ :=
          advance_observed_work raw notices safe (cards ▸ reads)
        obtain ⟨t, additional, resumed, stops⟩ :=
          advance_observed_decision mid raw.pending sound (known ▸ cards ▸ reads) route waiting
        exact ⟨t, used + additional, events, by simpa only [List.append_nil] using firstPath.append resumed, stops⟩
      · rcases cleanup with turnBoundary | cleanup
        · exact advance_observed_turn_boundary_to_decision raw notices safe (cards ▸ reads)
            (cards ▸ ordinaryMight) (cards ▸ ordinaryAwaken) (of_decide_eq_true turnBoundary)
        · split at cleanup
          · rename_i rest pending
            exact advance_observed_cleanup_to_decision raw notices safe (cards ▸ reads) pending cleanup
          · contradiction
    obtain ⟨t, used, work, firstPath, stops⟩ := path
    refine ⟨t, used, notices ++ work, stops, fun extra => step_mono ?_ (Nat.le_add_right _ extra)⟩
    change step used s action = _
    simp only [step, ite_eq_left (show Legal s action from legal), declared]
    exact firstPath.finish stops notices

end Riftbound

end
