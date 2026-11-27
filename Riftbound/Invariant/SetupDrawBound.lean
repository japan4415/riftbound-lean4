module

public import Riftbound.Engine.Step
public import Riftbound.Invariant.Setup

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
    (phase : s.phase = .setup) (decision : s.pending.head?.all (fun f => !f.isWork) = true) :
    advance fuel s events = .ok (s, events) := by
  cases next : s.pending with
  | nil => cases fuel <;> simp [advance, GameState.preparePriority_of_setup phase, next]
  | cons frame rest =>
    have notWork : frame.isWork = false := by simpa [next] using decision
    cases fuel <;> simp [advance, GameState.preparePriority_of_setup phase, next, notWork]

private theorem setupTail_waits {s : GameState} {frame : Frame} {rest : List Frame}
    (inv : SetupInv s) (pending : s.pending = frame :: rest) (setup : frame.isSetup = true) :
    rest.head?.all (fun f => !f.isWork) = true := by
  rcases inv.2 with ⟨ordered, _⟩ | noSetup
  · cases rest with
    | nil => rfl
    | cons next more =>
      have present : next ∈ s.pending := by rw [pending]; simp
      have nextSetup := startFrames_isSetup s.playerCount next (ordered.subset present)
      cases next <;> simp_all [Frame.isSetup, Frame.isWork]
  · have head := noSetup frame (pending ▸ List.mem_cons_self)
    simp [setup] at head

private theorem step_setup_chance {s t : GameState} {a : Action} {events : List Event}
    (fuel : Nat) (legal : Legal s a) (actor : a.actor = .chance) (ordinary : a.kind ≠ .concede)
    (noCost : s.actionDeathCostChoice a = none) (phase : t.phase = .setup)
    (applied : applyFrame0 s a = some (t, events)) :
    step fuel s a = advance fuel t (events ++ extraEvents a events) := by
  have declared : applyDeclaredAction s a = some (t, events ++ extraEvents a events) := by
    simp only [applyDeclaredAction, noCost, applyAction_of_ne ordinary, applyFrame, applied,
      Option.map_some, GameState.paySurcharge, actor]
    rw [setup_noTriggers phase]
  simp only [step, legal, ite_true, declared]

/-- An opening shuffle records the permutation and stops on the remaining setup decisions
without any automatic work. -/
theorem step_setupShuffle_waits {s : GameState} {z : Zone} {rest : List Frame} {order : List ObjId}
    (fuel : Nat) (phase : s.phase = .setup) (inv : SetupInv s)
    (pending : s.pending = .chanceShuffle z :: rest) (legal : Legal s ⟨.chance, .arrange order⟩) :
    step fuel s ⟨.chance, .arrange order⟩ = .ok ({ s.reorder z order with pending := rest }, []) := by
  let a : Action := ⟨.chance, .arrange order⟩
  let t := { s.reorder z order with pending := rest }
  have applied : applyFrame0 s a = some (t, []) := by simp [applyFrame0, pending, a, t]
  have noCost : s.actionDeathCostChoice a = none := by simp [GameState.actionDeathCostChoice, pending]
  have nextPhase : t.phase = .setup := phase
  rw [step_setup_chance fuel legal rfl (by intro eq; cases eq) noCost nextPhase applied]
  exact advance_onDecision fuel nextPhase (setupTail_waits inv pending rfl)

/-- A successful opening Battlefield pick stops on the remaining setup decisions, even with
zero work fuel. -/
theorem step_setupBattlefield_waits {s : GameState} {p : PlayerId} {rest : List Frame} {index : Nat}
    (fuel : Nat) (phase : s.phase = .setup) (inv : SetupInv s) (wf : s.WF) (owners : s.OwnerOk)
    (pending : s.pending = .chanceBattlefield p :: rest) (legal : Legal s ⟨.chance, .pick index⟩) :
    ∃ t events, step fuel s ⟨.chance, .pick index⟩ = .ok (t, events) ∧ t.pending = rest := by
  let a : Action := ⟨.chance, .pick index⟩
  have ordinary : a.kind ≠ .concede := by intro eq; cases eq
  obtain ⟨result, applied⟩ := applyFrame_isSome0 wf owners (Legal.frame (a := a) legal ordinary)
  have noCost : s.actionDeathCostChoice a = none := by simp [GameState.actionDeathCostChoice, pending]
  have pick := applied
  simp only [applyFrame0, pending, a] at pick
  split at pick
  · rename_i selected indexed
    simp only [Option.map_eq_some_iff] at pick
    obtain ⟨⟨board, id⟩, moved, rfl⟩ := pick
    obtain ⟨_, _, spec⟩ := moveObj_spec moved
    let t := { board with pending := rest }
    have nextPhase : t.phase = .setup := spec.other.phase.trans phase
    refine ⟨t, [.moved selected id .battlefieldZone], ?_, rfl⟩
    rw [step_setup_chance fuel legal rfl ordinary noCost nextPhase applied]
    exact advance_onDecision fuel nextPhase (setupTail_waits inv pending rfl)
  · contradiction

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
    simpa only [advance, GameState.preparePriority, pending, Frame.isWork, ite_true, work] using
      finish next (events ++ start.toList.map (.drewGroup p)) phase rfl
  | succ count ih =>
    rw [show count + 1 + 1 + fuel = (count + 1 + fuel) + 1 by omega]
    cases drawn : drawOne s p with
    | none =>
      let next := { s with pending := .chanceBurnOut p :: .draw p (count + 1) start :: rest }
      have work : workStep s = some (next, []) := by
        simp only [workStep, pending, microStep, microStep0, drawn, Option.map_some]
        rw [setup_noTriggers (s := next) phase]
      simpa only [advance, GameState.preparePriority, pending, Frame.isWork, ite_true, work, List.append_nil] using
        (show ∃ result, advance (count + 1 + fuel) next events = .ok result ∧
            ((∃ q frames, result.1.pending = .chanceBurnOut q :: frames) ∨
              result.1.pending = restOfBatch) from
          ⟨_, advance_onDecision _ phase rfl, Or.inl ⟨_, _, rfl⟩⟩)
    | some draw =>
      obtain ⟨board, en⟩ := draw
      let began := start <|> some ((s.zone (.player p .hand)).length)
      let next := { board.noteDraw p with pending := .draw p count began :: rest }
      have samePhase : next.phase = .setup := (drawOne_meta drawn).phase.trans phase
      have work : workStep s = some (next, en ++ [.drew p]) := by
        simp only [workStep, pending, microStep, microStep0, drawn, Option.map_some]
        rw [setup_noTriggers (s := next) samePhase]
      simpa only [advance, GameState.preparePriority, pending, Frame.isWork, ite_true, work] using
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
    exact ⟨_, advance_onDecision _ phase stop, Or.inr (by simpa using pending)⟩
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
  · simpa only [advance, GameState.preparePriority, pending, Frame.isWork, ite_true, work, List.append_nil] using done
  · rcases choice with ⟨p, frames, h⟩ | h
    · exact ⟨p, frames, Or.inr h⟩
    · exact ⟨first, tail, Or.inl (h.trans firstMulligan)⟩

/-- A legal opening turn order reaches the first Mulligan or Burn Out question within one
work step plus five per participating seat, including when a seat has already departed. -/
theorem step_setupTurnOrder_bound {s : GameState} {rest : List Frame} {order : List PlayerId}
    (phase : s.phase = .setup) (pending : s.pending = .chanceTurnOrder :: rest)
    (seats : s.participatingSeats ≠ []) (legal : Legal s ⟨.chance, .arrangePlayers order⟩) :
    ∃ result, step (5 * s.participatingSeats.length + 1) s ⟨.chance, .arrangePlayers order⟩ =
        .ok result ∧
      (∃ p frames, result.1.pending = .mulligan p 0 :: frames ∨
        result.1.pending = .chanceBurnOut p :: frames) := by
  let a : Action := ⟨.chance, .arrangePlayers order⟩
  let t := { s with turnOrder := s.completeOpeningOrder order, pending := .setupHands :: rest }
  have ordinary : a.kind ≠ .concede := by intro eq; cases eq
  have legalFrame := Legal.frame (a := a) legal ordinary
  simp only [LegalFrame, pending, a] at legalFrame
  have participants : t.participatingOrder.Perm s.participatingSeats :=
    legalFrame.2.1.filter s.participates
  have nonempty : t.participatingOrder ≠ [] := by
    intro empty
    exact seats (List.length_eq_zero_iff.mp (by simpa [empty] using participants.length_eq.symm))
  have applied : applyFrame0 s a = some (t, []) := by simp [applyFrame0, pending, a, t]
  have noCost : s.actionDeathCostChoice a = none := by simp [GameState.actionDeathCostChoice, pending]
  have nextPhase : t.phase = .setup := phase
  have done := advance_setupHands_bound (events := []) (s := t) nextPhase rfl nonempty
  rw [participants.length_eq] at done
  rw [step_setup_chance _ legal rfl ordinary noCost nextPhase applied]
  exact done

/-- After confirming at least one opening card, redraws reach the recycle order or Burn Out
within one work step per requested card and one to finish drawing. -/
theorem step_mulliganDone_redraw_bound {s : GameState} {p : PlayerId} {count : Nat}
    {rest : List Frame} (phase : s.phase = .setup)
    (pending : s.pending = .mulligan p (count + 1) :: rest)
    (legal : Legal s ⟨.player p, .mulliganDone⟩) :
    ∃ result, step (count + 2) s ⟨.player p, .mulliganDone⟩ = .ok result ∧
      (result.1.pending = .chanceRecycle p :: rest ∨
        ∃ seat frames, result.1.pending = .chanceBurnOut seat :: frames) := by
  let a : Action := ⟨.player p, .mulliganDone⟩
  let raw := { s with pending := .draw p (count + 1) :: .chanceRecycle p :: rest }
  let paid := s.paySurcharge a raw
  have phaseAfter : paid.phase = .setup := by
    rcases s.paySurcharge_cases a raw with equal | ⟨seat, pool, equal⟩ <;>
      rw [show paid = _ from equal] <;> exact phase
  have paidPending : paid.pending = .draw p (count + 1) :: .chanceRecycle p :: rest :=
    (s.paySurcharge_poolStep a raw).pending_eq
  have declared : applyDeclaredAction s a = some (paid, []) := by
    have noCost : s.actionDeathCostChoice a = none := by
      simp only [GameState.actionDeathCostChoice, pending]
    have applied : applyFrame0 s a = some (raw, []) := by
      simp only [applyFrame0, pending, a, raw]
    unfold applyDeclaredAction
    rw [noCost, applyAction_of_ne (by intro equal; cases equal)]
    simp only [applyFrame, applied, Option.map_some, extraEvents, a, List.nil_append]
    rw [setup_noTriggers (s := paid) phaseAfter]
  obtain ⟨result, drawn, stopped⟩ :=
    advance_setupDraw_then (count + 1) 0 paid [] p none _ phaseAfter paidPending
      (fun t ev setup atRecycle =>
        ⟨(t, ev), advance_onDecision 0 setup (by rw [atRecycle]; rfl), .inr atRecycle⟩)
  exact ⟨result, by simpa only [step, ite_eq_left legal, declared, Nat.add_zero, a] using drawn,
    stopped.symm⟩

end Riftbound

end
