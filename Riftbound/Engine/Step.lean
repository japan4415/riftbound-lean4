module

public import Riftbound.Spec.Legal

/-!
# The engine

`step` takes one answer, checks it with `Legal`, applies it, and works through the frames until
the next decision (design.md §6.1). `legalActions` lists the answers of the players, built
from the board, not by trying `step` (design.md §6.3).
-/

@[expose] public section

namespace Riftbound

/-- Why a step failed. -/
inductive RuleError where
  /-- The answer is not legal. -/
  | illegal
  /-- The automatic work did not reach the next decision within the fuel. -/
  | fuelExhausted
  /-- The engine's own bookkeeping failed. Under a well-formed state this does not happen
  (invariant I4, roadmap.md). -/
  | internal (msg : String)
deriving DecidableEq, Repr

/-- The declared board objects to be killed to pay for this play or ability (CR 357.2.a). -/
def GameState.actionKillCosts (s : GameState) (a : Action) : List ObjId :=
  match s.pending, a.kind with
  | .triggerOrder _ first more _ _ :: _, .putTrigger i _ (.pay ids ..) =>
    match (first :: more)[i]? with
    | some t => match trigCost s t with | .killFriendly .. | .killControlled .. => ids | _ => []
    | none => []
  | .priority _ :: _, .playCard card _ targets _ _ pick
  | .teamInvitation _ :: _, .playCard card _ targets _ _ pick
  | .chainPass .. :: _, .playCard card _ targets _ _ pick
  | .showdown .. :: _, .playCard card _ targets _ _ pick =>
    (s.playDeathCost card targets pick).toList
  | .priority _ :: _, .activate source index _ targets _ _ _ object
  | .teamInvitation _ :: _, .activate source index _ targets _ _ _ object
  | .chainPass .. :: _, .activate source index _ targets _ _ _ object
  | .showdown .. :: _, .activate source index _ targets _ _ _ object =>
    (activationKillVictim s source index targets object).toList
  | _, _ => []

/-- Check that the declaration came from a play decision before interrupting it for replacement
choices. No part of the declared payment has been committed yet. -/
def GameState.actionDeathCostChoice (s : GameState) (a : Action) :
    Option (ObjId × PlayerId × Effect × Effect) :=
  match s.pending with
  | .priority _ :: _ | .teamInvitation _ :: _ | .chainPass .. :: _ | .showdown .. :: _ | .triggerOrder .. :: _ =>
    if s.phase == .setup then none
    else s.deathGroupChoice (s.actionKillCosts a) false
  | _ => none

/-- Preserve every part of the declared answer while the affected controller decides whether
to replace the Kill. The confirmation is automatic and uses the original answer's events. -/
def applyDeclaredAction (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match s.actionDeathCostChoice a with
  | some (unit, p, first, other) =>
    some ({ s with pending := .eitherDo p unit {} first other .nil :: .resumeCost a :: s.pending }, [])
  | none => applyAction s a

/-- Advance a regular work frame or complete a locked declaration. The restored decision is
checked in the current state, and any further Kill replacement is handled before paying. -/
def workStep (s : GameState) : Option (GameState × List Event) :=
  match s.pending with
  | .resumeCost a :: rest =>
    let before := { s with pending := rest }
    if a.kind ≠ .timeCalled ∧ Legal before a then applyDeclaredAction before a
    else some (before, [])
  | _ => microStep s

/-- A payment is interrupted only in play and only from a non-setup decision. -/
theorem GameState.actionDeathCostChoice_context {s : GameState} {a : Action}
    {choice : ObjId × PlayerId × Effect × Effect} (h : s.actionDeathCostChoice a = some choice) :
    s.phase ≠ .setup ∧ ∃ frame rest, s.pending = frame :: rest ∧ frame.isSetup = false := by
  cases hp : s.pending with
  | nil => simp [GameState.actionDeathCostChoice, hp] at h
  | cons frame rest =>
    refine ⟨?_, frame, rest, rfl, ?_⟩
    · intro phase
      cases frame <;> simp [GameState.actionDeathCostChoice, hp, phase] at h
    · cases frame <;>
        first | rfl | (simp [GameState.actionDeathCostChoice, hp] at h)

/-- Applying a declaration either runs its ordinary transition or only inserts the two frames. -/
theorem applyDeclaredAction_cases {s s' : GameState} {a : Action} {es : List Event}
    (h : applyDeclaredAction s a = some (s', es)) :
    applyAction s a = some (s', es) ∨
    ∃ unit p first other,
      s.actionDeathCostChoice a = some (unit, p, first, other) ∧
      s' = { s with pending := .eitherDo p unit {} first other .nil :: .resumeCost a :: s.pending } ∧
      es = [] := by
  cases hh : s.actionDeathCostChoice a with
  | none => exact Or.inl (by simpa [applyDeclaredAction, hh] using h)
  | some choice =>
    obtain ⟨unit, p, first, other⟩ := choice
    simp only [applyDeclaredAction, hh, Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inr ⟨unit, p, first, other, rfl, h.1.symm, h.2.symm⟩

/-- A work step either operates on the top frame or removes the work marker and acts in the
restored decision. -/
theorem workStep_cases {s s' : GameState} {es : List Event} (h : workStep s = some (s', es)) :
    microStep s = some (s', es) ∨
      ∃ a rest, s.pending = .resumeCost a :: rest ∧
        ((a.kind ≠ .timeCalled ∧ Legal { s with pending := rest } a ∧
          applyDeclaredAction { s with pending := rest } a = some (s', es)) ∨
          (s' = { s with pending := rest } ∧ es = [])) := by
  unfold workStep at h
  split at h
  · rename_i a rest hp
    refine Or.inr ⟨a, rest, hp, ?_⟩
    dsimp only at h
    split at h
    · rename_i allowed
      exact Or.inl ⟨allowed.1, allowed.2, h⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨h.1.symm, h.2.symm⟩
  · exact Or.inl h

/-- Schedule Cleanup before a neutral priority decision if automatic board work remains
(CR 322-323). Other decisions keep their original timing. -/
def GameState.preparePriority (s : GameState) : GameState :=
  match s.pending with
  | .priority _ :: _ =>
    if s.phase == .setup || (s.winner.isNone && (cleanupStep s).isNone) then s
    else { s with pending := .cleanup :: s.pending }
  | _ => s

/-- Preparing a neutral decision changes at most the head of the stack. -/
theorem GameState.preparePriority_cases (s : GameState) :
    s.preparePriority = s ∨ ∃ p rest, s.pending = .priority p :: rest ∧ s.phase ≠ .setup ∧
      s.preparePriority = { s with pending := .cleanup :: s.pending } := by
  unfold GameState.preparePriority
  split
  · rename_i p rest pending
    split
    · exact Or.inl rfl
    · rename_i unsettled
      have play : s.phase ≠ .setup := by
        intro setup
        simp [setup] at unsettled
      exact Or.inr ⟨p, rest, pending, play, rfl⟩
  · exact Or.inl rfl

/-- Preparing the next decision leaves the phase unchanged. -/
theorem GameState.preparePriority_phase (s : GameState) : s.preparePriority.phase = s.phase := by
  rcases s.preparePriority_cases with unchanged | ⟨_, _, _, _, staged⟩
  · rw [unchanged]
  · rw [staged]

/-- During setup the engine follows the setup frames without inserting Cleanup. -/
theorem GameState.preparePriority_of_setup {s : GameState} (phase : s.phase = .setup) :
    s.preparePriority = s := by
  rcases s.preparePriority_cases with unchanged | ⟨_, _, _, playing, _⟩
  · exact unchanged
  · exact (playing phase).elim

/-- Existing work frames run directly, with no additional preparation. -/
theorem GameState.preparePriority_of_work {s : GameState} {f : Frame} {rest : List Frame}
    (pending : s.pending = f :: rest) (work : f.isWork = true) :
    s.preparePriority = s := by
  rcases s.preparePriority_cases with unchanged | ⟨p, tail, neutral, _, _⟩
  · exact unchanged
  · rw [neutral, List.cons.injEq] at pending
    obtain ⟨rfl, _⟩ := pending
    simp [Frame.isWork] at work

/-- A frame other than neutral priority does not require preparation. -/
theorem GameState.preparePriority_of_nonpriority {s : GameState} {frame : Frame} {rest : List Frame}
    (pending : s.pending = frame :: rest) (notNeutral : ∀ p, frame ≠ .priority p) :
    s.preparePriority = s := by
  rcases s.preparePriority_cases with unchanged | ⟨p, tail, neutral, _, _⟩
  · exact unchanged
  · rw [neutral, List.cons.injEq] at pending
    exact (notNeutral p pending.1.symm).elim

/-- A state can change during preparation only when a Cleanup frame becomes the next work. -/
theorem GameState.preparePriority_of_idle {s : GameState}
    (idle : s.preparePriority.pending.head?.all (fun f => !f.isWork) = true) :
    s.preparePriority = s := by
  rcases s.preparePriority_cases with unchanged | ⟨_, _, _, _, staged⟩
  · exact unchanged
  · simp [staged, Frame.isWork] at idle

/-- A prepared state exposes neutral priority only at a Cleanup fixed point. -/
theorem GameState.preparePriority_settled {s : GameState} {p : PlayerId} {rest : List Frame}
    (pending : s.preparePriority.pending = .priority p :: rest)
    (playing : s.preparePriority.phase ≠ .setup) : s.preparePriority.Settled := by
  rw [s.preparePriority_phase] at playing
  have phaseCheck : (s.phase == Phase.setup) = false := by simpa using playing
  by_cases neutral : ∃ owner tail, s.pending = .priority owner :: tail
  · obtain ⟨owner, tail, original⟩ := neutral
    by_cases ready : (s.winner.isNone && (cleanupStep s).isNone) = true
    · have unchanged : s.preparePriority = s := by
        simp only [GameState.preparePriority, original, phaseCheck, Bool.false_or, ready, ite_true]
      rw [unchanged]
      simpa [GameState.Settled, Bool.and_eq_true] using ready
    · simp only [GameState.preparePriority, original, phaseCheck, Bool.false_or, ite_eq_right ready] at pending
      cases pending
  · rcases s.preparePriority_cases with unchanged | ⟨owner, tail, original, _, _⟩
    · rw [unchanged] at pending
      exact (neutral ⟨_, _, pending⟩).elim
    · exact (neutral ⟨owner, tail, original⟩).elim

/-- Work through the work frames until the next decision or the end, one `workStep` at a time.
`fuel` is the number of steps allowed. -/
def advance : Nat → GameState → List Event → Except RuleError (GameState × List Event)
  | 0, s, es =>
    let prepared := s.preparePriority
    match prepared.pending with
    | f :: _ => if f.isWork then .error .fuelExhausted else .ok (prepared, es)
    | [] => .ok (prepared, es)
  | n + 1, s, es =>
    let prepared := s.preparePriority
    match prepared.pending with
    | f :: _ =>
      if f.isWork then
        match workStep prepared with
        | some (s', es') => advance n s' (es ++ es')
        | none => .error (.internal "microStep")
      else .ok (prepared, es)
    | [] => .ok (prepared, es)

/-- Automatic work preserves any predicate respected by preparation and each work step. -/
theorem advance_preserves (invariant : GameState → Prop)
    (prepare : ∀ s, invariant s → invariant s.preparePriority)
    (work : ∀ {s t : GameState} {events : List Event},
      invariant s → workStep s = some (t, events) → invariant t) :
    ∀ {fuel : Nat} {s t : GameState} {seen events : List Event},
      invariant s → advance fuel s seen = .ok (t, events) → invariant t := by
  intro fuel
  induction fuel with
  | zero =>
    intro s t seen events known done
    unfold advance at done
    dsimp only at done
    split at done
    · split at done
      · contradiction
      · obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj done)
        exact prepare s known
    · obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj done)
      exact prepare s known
  | succ fuel ih =>
    intro s t seen events known done
    unfold advance at done
    dsimp only at done
    split at done
    · split at done
      · split at done
        · exact ih (work (prepare s known) (by assumption)) done
        · contradiction
      · obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj done)
        exact prepare s known
    · obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj done)
      exact prepare s known

/-- Every successful advance that offers neutral priority has reached a Cleanup fixed point. -/
theorem advance_priority_settled {fuel : Nat} {s t : GameState} {seen events : List Event}
    (done : advance fuel s seen = .ok (t, events)) {p : PlayerId} {rest : List Frame}
    (pending : t.pending = .priority p :: rest) (playing : t.phase ≠ .setup) : t.Settled := by
  induction fuel generalizing s t seen events with
  | zero =>
    unfold advance at done
    dsimp only at done
    split at done
    · split at done
      · contradiction
      · obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj done)
        exact GameState.preparePriority_settled pending playing
    · rename_i empty
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj done)
      rw [empty] at pending
      contradiction
  | succ fuel ih =>
    unfold advance at done
    dsimp only at done
    split at done
    · split at done
      · split at done
        · exact ih done pending playing
        · contradiction
      · obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj done)
        exact GameState.preparePriority_settled pending playing
    · rename_i empty
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj done)
      rw [empty] at pending
      contradiction

/-- Take one answer. -/
def step (fuel : Nat) (s : GameState) (a : Action) :
    Except RuleError (GameState × List Event) :=
  if Legal s a then
    match applyDeclaredAction s a with
    | some (s1, es) => advance fuel s1 es
    | none => .error (.internal "applyAction")
  else .error .illegal

/-- The abilities of the player's Basic Runes that can be used (CR 164.2). -/
def legalRunes (s : GameState) (p : PlayerId) : List Action :=
  (s.zone (.player p .base)).flatMap (fun c =>
    ([RuneAbility.exhaust, .recycle].filter (fun ab => runeUsable s p c ab)).map
      (fun ab => ⟨.player p, .runeAbility c ab⟩))

/-- Every way the player can put one of the abilities of the group on the Chain: each ability with
each legal pick of targets and costs, or a decision to pass it over (CR 383.3, 355). -/
def legalPuts (s : GameState) (p : PlayerId) (grp : List PendTrigger) : List Action :=
  (List.range grp.length).flatMap (fun (i : Nat) =>
    match grp[i]? with
    | some g => (trigOptions s g).map (fun (ts, payment) => ⟨.player p, .putTrigger i ts payment⟩)
    | none => [])

/-- The puts listed are exactly the legal ones. -/
theorem mem_legalPuts (s : GameState) (p : PlayerId) (grp : List PendTrigger) (a : Action) :
    a ∈ legalPuts s p grp ↔ ∃ i ts payment, a = ⟨.player p, .putTrigger i ts payment⟩ ∧
      (grp[i]?.any (fun g => trigLegal s g ts payment)) = true := by
  unfold legalPuts
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, ha⟩
    rcases hg : grp[i]? with _ | g
    · rw [hg] at ha
      simp at ha
    · rw [hg] at ha
      simp only [List.mem_map] at ha
      obtain ⟨⟨ts, payment⟩, hts, rfl⟩ := ha
      exact ⟨i, ts, payment, rfl, by rw [hg]; simp [(mem_trigOptions s g ts payment).mp hts]⟩
  · rintro ⟨i, ts, payment, rfl, h⟩
    rcases hg : grp[i]? with _ | g
    · rw [hg] at h
      simp at h
    · rw [hg] at h
      refine ⟨i, (List.getElem?_eq_some_iff.mp hg).1, ?_⟩
      rw [hg]
      simp only [Option.any_some] at h
      simp only [List.mem_map]
      exact ⟨(ts, payment), (mem_trigOptions s g ts payment).mpr h, rfl⟩

/-- The target and cost selections for which the player can open a trigger's Add window. -/
def legalTriggerPreparations (s : GameState) (p : PlayerId) (group : List PendTrigger) : List Action :=
  (List.range group.length).flatMap (fun idx =>
    group[idx]?.elim [] (fun t =>
      ((acceptedTriggers s t false).filter (fun (ts, payment) =>
        !(triggerAdds s t ts payment).isEmpty)).map (fun (ts, payment) =>
          ⟨.player p, .prepareTrigger idx ts payment⟩)))

/-- The payment windows offered are exactly the preparations that can be chosen. -/
theorem mem_legalTriggerPreparations (s : GameState) (p : PlayerId) (group : List PendTrigger)
    (a : Action) : a ∈ legalTriggerPreparations s p group ↔
    ∃ i ts payment, a = ⟨.player p, .prepareTrigger i ts payment⟩ ∧
      (group[i]?.any (fun t => triggerPreparation s t ts payment)) = true := by
  unfold legalTriggerPreparations
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, ha⟩
    cases hg : group[i]? with
    | none => simp [hg] at ha
    | some t =>
      simp only [hg, Option.elim_some, List.mem_map, List.mem_filter] at ha
      obtain ⟨⟨ts, payment⟩, ⟨ht, hd⟩, rfl⟩ := ha
      exact ⟨i, ts, payment, rfl, by simp [hg, triggerPreparation, ht, hd]⟩
  · rintro ⟨i, ts, payment, rfl, h⟩
    cases hg : group[i]? with
    | none => simp [hg] at h
    | some t =>
      simp only [hg, Option.any_some, triggerPreparation, Bool.and_eq_true,
        List.contains_iff_mem] at h
      refine ⟨i, (List.getElem?_eq_some_iff.mp hg).1, ?_⟩
      simp only [hg, Option.elim_some, List.mem_map, List.mem_filter]
      exact ⟨(ts, payment), h, rfl⟩

/-- The next Add or finalization to choose while a trigger's other choices are locked. -/
def legalTriggerFunding (s : GameState) (p : PlayerId) (group : List PendTrigger)
    (plan : TriggerFunding) : List Action :=
  (if (commitTriggerFunding s group plan).isSome then
    [⟨.player p, .putTrigger plan.index plan.targets plan.payment⟩] else []) ++
    (triggerFundingAdds s group plan).map (fun a => ⟨.player p, .triggerAdd a⟩) ++
    [⟨.player p, .decide false⟩]

/-- Invitation grants spell timing without allowing a permanent to be played. -/
def legalInvitedSpells (s : GameState) (p : PlayerId) : List Action :=
  (legalPlays s p).filter (fun a =>
    match a.kind with
    | .playCard c pay targets flow _ pick => castable s p c pay targets flow pick
    | _ => false)

theorem mem_legalInvitedSpells (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalInvitedSpells s p ↔ ∃ c pay targets flow discard pick,
      a = ⟨.player p, .playCard c pay targets flow discard pick⟩ ∧
      c ∈ s.playSources p ∧ castable s p c pay targets flow pick = true ∧
      s.playDiscardOk p c discard = true := by
  simp only [legalInvitedSpells, List.mem_filter, mem_legalPlays]
  constructor
  · rintro ⟨⟨c, pay, ts, flow, discard, pick, rfl, hc, -, hd⟩, cast⟩
    exact ⟨c, pay, ts, flow, discard, pick, rfl, hc, cast, hd⟩
  · rintro ⟨c, pay, ts, flow, discard, pick, rfl, hc, cast, hd⟩
    exact ⟨⟨c, pay, ts, flow, discard, pick, rfl, hc, .inr (.inl cast), hd⟩, cast⟩

/-- The answers of the players to the open question. Chance answers are not listed. -/
def legalFrameActions (s : GameState) : List Action :=
  match s.pending with
  | .mulligan p n :: _ =>
    (if n < 2 then
      (s.zone (.player p .hand)).map (fun c => ⟨.player p, .mulliganPick c⟩)
    else []) ++ [⟨.player p, .mulliganDone⟩]
  | .discard p n :: _ =>
    if s.zone (.player p .hand) = [] ∨ n = 0 then [⟨.player p, .discardDone⟩]
    else (s.zone (.player p .hand)).map (fun c => ⟨.player p, .discardPick c⟩)
  | .mayDo p .. :: _ => [⟨.player p, .decide true⟩, ⟨.player p, .decide false⟩]
  | .eitherDo p src env x y _ :: _ =>
    ([⟨.player p, .decide true⟩, ⟨.player p, .decide false⟩] : List Action).filter (fun a =>
      match a.kind with
      | .decide yes => eitherOk s p src env x y yes
      | _ => true) ++
    (if x.isPayment then legalRunes s p ++ legalManas s p else [])
  | .pickDo p _ _ c more _ _ :: _ => (c :: more).map (fun o => ⟨.player p, .choose o⟩)
  | .guessCardType p .. :: _ =>
    CardTypeGuess.choices.map (fun guess => ⟨.player p, .guessCardType guess⟩)
  | .nameCard p _ _ c more _ :: _ => (c :: more).map (fun id => ⟨.player p, .nameCard id⟩)
  | .chooseBurnOut p :: _ =>
    ((allPlayers s.playerCount).filter (fun o => !s.config.mode.sameSide p o)).map
      (fun o => ⟨.player p, .burnOutTarget o⟩)
  | .chooseBurnOutAmong p first more :: _ =>
    (first :: more).map (fun o => ⟨.player p, .burnOutTarget o⟩)
  | .priority p :: _ =>
    ⟨.player p, .pass⟩ :: (legalRunes s p ++ legalManas s p ++ legalPlays s p ++
      legalMoves s p ++ legalActivates s p true ++ legalGroupMoveStarts s p ++
      ((s.teamInvitee p).toList.map (fun guest => ⟨.player p, .inviteTeammate guest⟩)))
  | .groupMove p dest pay units :: _ =>
    ⟨.player p, .decide false⟩ ::
    ((if s.groupMoveReady p dest pay units then [⟨.player p, .decide true⟩] else []) ++
      (s.groupMoveRemaining p dest pay units).map (fun u => ⟨.player p, .choose u⟩))
  | .teamInvitation guest :: _ =>
    ⟨.player guest, .pass⟩ :: (legalRunes s guest ++ legalManas s guest ++
      legalInvitedSpells s guest ++ legalActivates s guest true)
  | .chooseShowdown p first more :: _ =>
    (first :: more).map (fun (bf, _) => ⟨.player p, .choose bf⟩)
  | .chainPass p _ :: _ =>
    ⟨.player p, .pass⟩ :: (legalRunes s p ++ legalManas s p ++ legalReactions s p ++
      legalActivates s p false)
  | .triggerOrder p t more _ none :: _ =>
    legalPuts s p (t :: more) ++ legalTriggerPreparations s p (t :: more)
  | .triggerOrder p t more _ (some plan) :: _ => legalTriggerFunding s p (t :: more) plan
  | .showdown _ q _ :: _ =>
    ⟨.player q, .pass⟩ :: (legalRunes s q ++ legalManas s q ++ legalShowdownPlays s q ++
      legalShowdownActivates s q)
  | .assign bf _ side acc _ :: _ => legalAssigns s bf side acc
  | .predict p _ c cs _ _ :: _ =>
    (c :: cs).flatMap (fun id => [⟨.player p, .predictPick id false⟩, ⟨.player p, .predictPick id true⟩])
  | _ => []

/-- The eligible seats may concede regardless of the decision on top of the stack (CR 649-651). -/
def concedeActions (s : GameState) : List Action :=
  ((allPlayers s.playerCount).filter (fun p => decide (s.canConcede p))).map
    (fun p => ⟨.player p, .concede⟩)

/-- The answers of the players: to the open question, and the concessions. Nothing once the game
is over. -/
def legalActions (s : GameState) : List Action :=
  if s.result = none then legalFrameActions s ++ concedeActions s else []

end Riftbound

end
