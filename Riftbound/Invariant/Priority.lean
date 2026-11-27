module

public import Riftbound.Invariant.Choices
public import Riftbound.Invariant.Turn

/-!
# Passing and regaining priority (I16, I17)

The lemmas follow `step`, including the declaration and automatic work. Before the pass count
reaches the number of seats, play stops at the next seat's decision. The final pass schedules the
top item for resolution. The rotation lemmas identify the seats visited in a complete round.
The final lemmas cover Cleanup after an immediate Add during neutral priority.
-/

@[expose] public section

namespace Riftbound

/-- Only the player who currently has Chain priority can pass (CR 338.2). -/
theorem legal_chainPass_iff {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    (actor : Actor) (pending : s.pending = .chainPass p passes :: rest) :
    Legal s ⟨actor, .pass⟩ ↔ s.result = none ∧ actor = .player p := by
  simp [Legal, LegalFrame, LegalConcede, pending]

/-- Declaring a Chain pass changes which frame is pending and emits no event (CR 338.2, 339). -/
theorem applyDeclaredAction_chainPass {s : GameState} {p : PlayerId} {passes : Nat}
    {rest : List Frame} (pending : s.pending = .chainPass p passes :: rest) :
    let frame := if passes + 1 < s.participatingCount then .chainPass (s.nextParticipant p) (passes + 1)
      else .resolveChain
    applyDeclaredAction s ⟨.player p, .pass⟩ =
      some (({ s with pending := frame :: rest }).setPool p (s.poolOf p), []) := by
  unfold applyDeclaredAction
  simp only [GameState.actionDeathCostChoice, pending, GameState.actionKillCosts,
    GameState.deathGroupChoice, GameState.deathGroupChoiceWith_nil, ite_self]
  unfold applyAction applyFrame applyFrame0
  simp only [pending]
  by_cases h : passes + 1 < s.participatingCount <;>
    simp [h, extraEvents, GameState.actionTransitionEvents, pending, withTriggers_nil,
      GameState.paySurcharge, GameState.paidDeflectPool, GameState.deflectInPayment,
      Action.targetsOf, Action.spellSource,
      GameState.deflectCost, RunePool.takeN, GameState.poolOf]

/-- A non-final pass leaves the Chain intact and stops at the next player's priority without
using fuel (CR 338.2). -/
theorem step_chainPass_next {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    (fuel : Nat) (ongoing : s.result = none) (pending : s.pending = .chainPass p passes :: rest)
    (beforeLast : passes + 1 < s.participatingCount) :
    step fuel s ⟨.player p, .pass⟩ = .ok
      (({ s with pending := .chainPass (s.nextParticipant p) (passes + 1) :: rest }).setPool p (s.poolOf p),
        []) := by
  have legal := (legal_chainPass_iff (.player p) pending).mpr ⟨ongoing, rfl⟩
  have applied := applyDeclaredAction_chainPass pending
  simp only [beforeLast, ite_true] at applied
  simp only [step, legal, ite_true, applied]
  exact advance_waitsForDecision fuel rfl rfl rfl

/-- The last required pass hands control to resolution, leaving the Chain in place for that
work frame to read (CR 338.2, 339, 340). -/
theorem step_chainPass_last {s : GameState} {p : PlayerId} {passes : Nat} {rest : List Frame}
    (fuel : Nat) (ongoing : s.result = none) (pending : s.pending = .chainPass p passes :: rest)
    (last : s.participatingCount ≤ passes + 1) :
    step fuel s ⟨.player p, .pass⟩ =
      advance fuel (({ s with pending := .resolveChain :: rest }).setPool p (s.poolOf p)) [] := by
  have legal := (legal_chainPass_iff (.player p) pending).mpr ⟨ongoing, rfl⟩
  have applied := applyDeclaredAction_chainPass pending
  simp only [Nat.not_lt.mpr last, ite_false] at applied
  simp only [step, legal, ite_true, applied]

/-- Chain resolution adds Run frames followed by a finish frame for the top item (CR 340). -/
theorem resolveFrames_newest {s : GameState} {item : ObjId} {older : List ObjId}
    (chain : s.zone .chain = item :: older) (rest : List Frame) :
    ∃ body, resolveFrames s rest = body ++ (.finishSpell item :: rest) ∧
      ∀ frame ∈ body, ∃ p src env effects, frame = .run p src env effects := by
  cases object : s.obj? item with
  | none => exact ⟨[], by simp [resolveFrames, chain, object], by simp⟩
  | some o =>
    cases definition : s.cardDef? item with
    | none =>
      simp only [resolveFrames, chain, object, definition, itemFrames]
      split
      · refine ⟨[.run _ _ _ _], rfl, ?_⟩
        intro frame member
        obtain rfl := List.mem_singleton.mp member
        exact ⟨_, _, _, _, rfl⟩
      · exact ⟨[], rfl, by simp⟩
    | some d =>
      simp only [resolveFrames, chain, object, definition]
      split
      · refine ⟨_, rfl, ?_⟩
        intro frame member
        obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp member
        exact ⟨_, _, _, _, rfl⟩
      · refine ⟨[.run _ _ _ _], rfl, ?_⟩
        intro frame member
        obtain rfl := List.mem_singleton.mp member
        exact ⟨_, _, _, _, rfl⟩

/-- The first resolution work step after the last pass puts the top item's frames on the stack
before looking for abilities triggered by the transition (CR 340). -/
theorem microStep0_resolveNewest {s : GameState} {item : ObjId} {older : List ObjId}
    {rest : List Frame} (pending : s.pending = .resolveChain :: rest)
    (chain : s.zone .chain = item :: older) :
    ∃ body,
      microStep0 s = some ({ s with pending := body ++ (.finishSpell item :: rest) }, []) ∧
      ∀ frame ∈ body, ∃ p src env effects, frame = .run p src env effects := by
  obtain ⟨body, frames, onlyRuns⟩ := resolveFrames_newest chain rest
  exact ⟨body, by simp [microStep0, pending, frames], onlyRuns⟩

private theorem turnOrder_length {s : GameState}
    (order : s.turnOrder.Perm (allPlayers s.playerCount)) :
    s.turnOrder.length = s.playerCount := by
  simpa [allPlayers] using order.length_eq

/-- `nextPlayer` follows the declared turn order and wraps at the end (CR 338.2). -/
theorem nextPlayer_turnPlayerAt {s : GameState}
    (order : s.turnOrder.Perm (allPlayers s.playerCount)) (seats : 0 < s.playerCount) (i : Nat) :
    s.nextPlayer (s.turnPlayerAt i) = s.turnPlayerAt (i + 1) := by
  have length := turnOrder_length order
  have nodup := order.nodup_iff.mpr (allPlayers_nodup s.playerCount)
  have within : i % s.playerCount < s.turnOrder.length := by
    rw [length]
    exact Nat.mod_lt i seats
  have player : s.turnPlayerAt i = s.turnOrder[i % s.playerCount] := by
    simp [GameState.turnPlayerAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem within]
  have index : s.turnOrder.idxOf? (s.turnPlayerAt i) = some (i % s.playerCount) := by
    apply List.idxOf?_eq_some_iff.mpr
    refine ⟨within, player.symm, ?_⟩
    intro earlier hEarlier equal
    have before : earlier < s.turnOrder.length := Nat.lt_trans hEarlier within
    have same : s.turnOrder[earlier] = s.turnOrder[i % s.playerCount] := equal.trans player
    have := (nodup.getElem_inj (hi := before) (hj := within)).mp same
    omega
  unfold GameState.nextPlayer
  rw [index, length]
  change s.turnOrder.getD ((i % s.playerCount + 1) % s.playerCount) (s.turnPlayerAt i) = _
  rw [Nat.mod_add_mod]
  have next : (i + 1) % s.playerCount < s.turnOrder.length := by
    rw [length]
    exact Nat.mod_lt _ seats
  change s.turnOrder.getD ((i + 1) % s.playerCount) (s.turnPlayerAt i) =
    s.turnOrder.getD ((i + 1) % s.playerCount) ⟨0⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem next]

/-- Repeated handoffs agree with walking forward through the fixed seat order (CR 338.2). -/
theorem nextPlayer_repeat_turnPlayerAt {s : GameState}
    (order : s.turnOrder.Perm (allPlayers s.playerCount)) (seats : 0 < s.playerCount) (i n : Nat) :
    Nat.repeat s.nextPlayer n (s.turnPlayerAt i) = s.turnPlayerAt (i + n) := by
  induction n with
  | zero => simp [Nat.repeat]
  | succ n ih =>
    rw [Nat.repeat, ih, nextPlayer_turnPlayerAt order seats]
    rfl

/-- No two handoffs in one round reach the same seat, even across the end of the turn order. -/
theorem nextPlayer_round_inj {s : GameState}
    (order : s.turnOrder.Perm (allPlayers s.playerCount)) (i : Nat) {a b : Nat}
    (aBound : a < s.playerCount) (bBound : b < s.playerCount)
    (same : Nat.repeat s.nextPlayer a (s.turnPlayerAt i) =
      Nat.repeat s.nextPlayer b (s.turnPlayerAt i)) : a = b := by
  have seats := Nat.zero_lt_of_lt aBound
  have length := turnOrder_length order
  have nodup := order.nodup_iff.mpr (allPlayers_nodup s.playerCount)
  rw [nextPlayer_repeat_turnPlayerAt order seats, nextPlayer_repeat_turnPlayerAt order seats] at same
  have ha : (i + a) % s.playerCount < s.turnOrder.length := by
    rw [length]
    exact Nat.mod_lt _ seats
  have hb : (i + b) % s.playerCount < s.turnOrder.length := by
    rw [length]
    exact Nat.mod_lt _ seats
  have sameIndex : (i + a) % s.playerCount = (i + b) % s.playerCount := by
    apply (nodup.getElem_inj (hi := ha) (hj := hb)).mp
    simpa [GameState.turnPlayerAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha,
      List.getElem?_eq_getElem hb] using same
  rw [Nat.add_mod_eq_ite (m := i) (n := a), Nat.add_mod_eq_ite (m := i) (n := b),
    Nat.mod_eq_of_lt aBound, Nat.mod_eq_of_lt bBound] at sameIndex
  split at sameIndex <;> split at sameIndex <;> omega

/-- Every seat appears within a complete priority round, regardless of which seat started it. -/
theorem nextPlayer_round_covers {s : GameState} {p : PlayerId}
    (order : s.turnOrder.Perm (allPlayers s.playerCount)) (i : Nat) (seat : p.n < s.playerCount) :
    ∃ passed < s.playerCount, Nat.repeat s.nextPlayer passed (s.turnPlayerAt i) = p := by
  have seats := Nat.zero_lt_of_lt seat
  have length := turnOrder_length order
  have present := order.mem_iff.mpr ((mem_allPlayers s.playerCount p).mpr seat)
  obtain ⟨j, jWithin, named⟩ := List.mem_iff_getElem.mp present
  have jBound : j < s.playerCount := by simpa [length] using jWithin
  have startBound := Nat.mod_lt i seats
  let passed := if i % s.playerCount ≤ j then j - i % s.playerCount
    else j + s.playerCount - i % s.playerCount
  have within : passed < s.playerCount := by
    unfold passed
    split <;> omega
  have destination : (i + passed) % s.playerCount = j := by
    rw [← Nat.mod_add_mod i s.playerCount passed]
    unfold passed
    split
    · rw [show i % s.playerCount + (j - i % s.playerCount) = j by omega]
      exact Nat.mod_eq_of_lt jBound
    · rw [show i % s.playerCount + (j + s.playerCount - i % s.playerCount) =
          j + s.playerCount by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt jBound
  refine ⟨passed, within, ?_⟩
  rw [nextPlayer_repeat_turnPlayerAt order seats]
  simpa [GameState.turnPlayerAt, destination, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem jWithin] using named

/-- Work from an immediate Add is scheduled before the same neutral priority (CR 319, 430.2). -/
theorem applyFrame0_priority_mana_cleanup {s next : GameState} {p : PlayerId} {rest : List Frame}
    {source : ObjId} {index : Nat} {pay : RunePool.Payment} {chosen : Option ObjId}
    {events : List Event} (pending : s.pending = .priority p :: rest)
    (applied : applyFrame0 s ⟨.player p, .manaAbility source index pay chosen⟩ =
      some (next, events)) : next.pending = .cleanup :: .priority p :: rest := by
  simp only [applyFrame0, pending] at applied
  obtain ⟨⟨afterAdd, addEvents⟩, _, mapped⟩ := Option.map_eq_some_iff.mp applied
  exact (congrArg (fun result : GameState × List Event => result.1.pending) mapped).symm

/-- When the frame handler accepts a direct Unit or Gear play, it schedules Cleanup before
returning control (CR 319.6, 322). -/
theorem applyFrame0_permanentPlay_cleanup {s next : GameState} {actor : Actor}
    {card : ObjId} {pay : RunePool.Payment} {targets : List ObjId} {flow : Option Cost}
    {discard : Option ObjId} {pick : SpellPick} {events : List Event}
    {definition : CardDef} (known : s.cardDef? card = some definition)
    (permanent : definition.hasType .spell = false)
    (applied : applyFrame0 s ⟨actor, .playCard card pay targets flow discard pick⟩ =
      some (next, events)) : next.pending.head? = some .cleanup := by
  have notCastable (who : PlayerId) : castable s who card pay targets flow pick = false := by
    simp only [castable, known]
    cases s.obj? card <;> simp [permanent]
  cases pending : s.pending with
  | nil => simp [applyFrame0, pending] at applied
  | cons frame rest =>
    cases frame <;> simp only [applyFrame0, pending] at applied
    all_goals
      first
      | contradiction
      | simp only [applyPlayCard, reactStep, notCastable, Bool.false_eq_true, ite_false] at applied
        obtain ⟨_, _, eq⟩ := Option.map_eq_some_iff.mp applied
        exact (congrArg (fun result : GameState × List Event => result.1.pending.head?) eq).symm

/-- Cleanup must have run out of immediate work before it returns neutral priority (CR 322). -/
theorem cleanupFrame_priority_ready {s : GameState} {rest trailing : List Frame} {p : PlayerId}
    (pending : (cleanupFrame s rest).1.pending = .priority p :: trailing) :
    s.Settled ∧ s.stagedShowdowns rest = [] ∧ rest = .priority p :: trailing := by
  unfold cleanupFrame at pending
  split at pending
  · simp at pending
  next noWinner =>
    split at pending
    · cases pending
    · split at pending
      · cases pending
      · split at pending
        · cases pending
        next noWork =>
          split at pending
          · split at pending
            · cases pending
            · simp [continueAfterCleanup] at pending
          next staged =>
            exact ⟨⟨noWinner, noWork⟩, staged, by simpa only [continueAfterCleanup] using pending⟩

/-- **I17.** A successful step offers neutral priority during play only at a Cleanup fixed point. -/
theorem step_priority_settled {fuel : Nat} {s t : GameState} {events : List Event} {a : Action}
    (applied : step fuel s a = .ok (t, events)) {p : PlayerId} {tail : List Frame}
    (pending : t.pending = .priority p :: tail) (playing : t.phase ≠ .setup) : t.Settled := by
  unfold step at applied
  split at applied
  · split at applied
    · exact advance_priority_settled applied pending playing
    · contradiction
  · contradiction

end Riftbound

end
