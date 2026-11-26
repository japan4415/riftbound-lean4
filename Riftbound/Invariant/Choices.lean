module

public import Riftbound.Engine.Step

/-!
# Player decisions during resolution (I18)

The effect interpreter schedules questions without changing the game. A work step dispatches those
questions to the specified player, and the legal answers state who can accept, decline or pick an
object. Optional triggered abilities and explicitly declared Spell costs use the same principle at
finalization.
-/

@[expose] public section

namespace Riftbound

/-- A possible `may` instruction asks its controller before changing the game (CR 355.18). -/
theorem runEffect_may_choice (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (rest : EffectList) (funding : EffectAddPolicy)
    (possible : (requiredPlayCandidates s p src env e funding).any List.isEmpty = false) :
    runEffect s p src env (.may e) rest funding = (s, [.mayDo p src env e rest], []) := by
  simp [runEffect, Effect.pickSel?, runEffect1, possible]

/-- An explicit object choice asks its controller even when exactly one object remains eligible
(CR 355.18). -/
theorem runEffect_chooseObject_choice (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (side : Side) (place : Place) (filters : FilterList) (body : Effect) (rest : EffectList)
    (funding : EffectAddPolicy) (first : ObjId) (remaining : List ObjId)
    (candidates : (requiredPlayCandidates s p src env (.chooseObject side place filters body) funding <|>
      s.pickCandidates p src env side place filters true) = some (first :: remaining)) :
    runEffect s p src env (.chooseObject side place filters body) rest funding =
      (s, [.pickDo p src env first remaining (.seq (.cons body .nil)) rest], []) := by
  cases remaining <;> simp [runEffect, Effect.pickSel?, Effect.withPick, Effect.isLinkedCost, candidates]

/-- An effect with at least two alternatives asks about the first and preserves the other
alternatives until the controller responds (CR 355.18). -/
theorem runEffect_eitherOf_choice (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (first second : Effect) (remaining rest : EffectList) (funding : EffectAddPolicy) :
    let other := match remaining with
      | .nil => second
      | .cons _ _ => .eitherOf (.cons second remaining)
    runEffect s p src env (.eitherOf (.cons first (.cons second remaining))) rest funding =
      (s, [.eitherDo p src env first other rest], []) := by
  cases remaining <;> simp [runEffect, Effect.pickSel?, runEffect1]

/-- Automatic work stops at a decision frame even with fuel left. -/
theorem advance_waitsForDecision (fuel : Nat) {s : GameState} {events : List Event}
    {choice : Frame} {rest : List Frame} (pending : s.pending = choice :: rest)
    (decision : choice.isWork = false) : advance fuel s events = .ok (s, events) := by
  cases fuel <;> simp [advance, pending, decision]

private theorem insertTriggers_keepsDecision (triggers : List PendTrigger) {choice : Frame}
    (decision : choice.isWork = false) {stack : List Frame} (present : choice ∈ stack) :
    choice ∈ insertTriggers triggers stack := by
  induction stack with
  | nil => simp at present
  | cons frame rest ih =>
    unfold insertTriggers
    split
    · rcases List.mem_cons.mp present with rfl | inRest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih inRest)
    · split
      · rcases List.mem_cons.mp present with rfl | inRest
        · simp [Frame.isWork] at decision
        · exact List.mem_cons_of_mem _ inRest
      · exact List.mem_cons_of_mem _ present

private theorem withTriggers_keepsDecision {s : GameState} {events : List Event} {choice : Frame}
    (decision : choice.isWork = false) (present : choice ∈ s.pending)
    (ongoing : (s.withTriggers events).result = none) : choice ∈ (s.withTriggers events).pending := by
  rcases withTriggers_cases s events with ⟨_, ended, _⟩ | unchanged | ⟨_, queued, _, _⟩
  · simp [ended] at ongoing
  · simpa [unchanged, GameState.recordTurnEvents] using present
  · rw [queued]
    unfold insertDetectedTriggers
    apply List.mem_append_right
    split
    · exact present
    · exact insertTriggers_keepsDecision _ decision present

/-- A Run frame that schedules a decision leaves it on the stack after the actual work step, even
if triggered abilities are added, provided the game continues. -/
theorem workStep_keepsRunDecision {s after : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {effect : Effect} {body : EffectList} {rest : List Frame} {choice : Frame}
    {events : List Event} (pending : s.pending = .run p src env (.cons effect body) :: rest)
    (scheduled : runEffect s p src (env.withMight s.mightTable) effect body effectAddPolicy =
      (s, [choice], [])) (decision : choice.isWork = false)
    (worked : workStep s = some (after, events)) (ongoing : after.result = none) :
    choice ∈ after.pending ∧ events = [] := by
  have work : workStep s = some (({ s with pending := choice :: rest }).withTriggers
      (s.workTransitionEvents { s with pending := choice :: rest }), []) := by
    simp [workStep, pending, microStep, microStep0, scheduled]
  rw [work, Option.some.injEq, Prod.mk.injEq] at worked
  obtain ⟨rfl, rfl⟩ := worked
  exact ⟨withTriggers_keepsDecision decision List.mem_cons_self ongoing, rfl⟩

/-- A work step that schedules one decision and produces no events stops at that decision.
The transition check accounts for triggered abilities that may be queued by `workStep`. -/
theorem advance_runDecision {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {effect : Effect} {body : EffectList} {rest : List Frame} {choice : Frame}
    {events : List Event} (fuel : Nat) (pending : s.pending = .run p src env (.cons effect body) :: rest)
    (scheduled : runEffect s p src (env.withMight s.mightTable) effect body effectAddPolicy =
      (s, [choice], [])) (decision : choice.isWork = false)
    (quiet : s.workTransitionEvents { s with pending := choice :: rest } = []) :
    advance (fuel + 1) s events = .ok ({ s with pending := choice :: rest }, events) := by
  let waiting := { s with pending := choice :: rest }
  have work : workStep s = some (waiting, []) := by
    simp [workStep, pending, microStep, microStep0, scheduled, quiet, withTriggers_nil, waiting]
  simpa only [advance, pending, Frame.isWork, ite_true, work, List.append_nil] using
    (advance_waitsForDecision fuel (s := waiting) (events := events) rfl decision)

/-- While a `may` decision is open, either answer is legal exactly for the designated player. -/
theorem legal_mayDecision_iff {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {body : Effect} {rest : EffectList} {tail : List Frame} (actor : Actor) (accept : Bool)
    (pending : s.pending = .mayDo p src env body rest :: tail) :
    Legal s ⟨actor, .decide accept⟩ ↔ s.result = none ∧ actor = .player p := by
  simp [Legal, LegalFrame, LegalConcede, pending]

/-- The `may` answer schedules the body only when the player accepted it. -/
theorem applyFrame0_mayDecision {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {body : Effect} {rest : EffectList} {tail : List Frame} (accept : Bool)
    (pending : s.pending = .mayDo p src env body rest :: tail) :
    applyFrame0 s ⟨.player p, .decide accept⟩ =
      some ({ s with pending := .run p src env (if accept then .cons body rest else rest) :: tail }, []) := by
  simp [applyFrame0, pending]

/-- An object answer belongs to the designated player and to the candidates in the question. -/
theorem legal_objectDecision_iff {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {first : ObjId} {more : List ObjId} {body : Effect} {rest : EffectList} {tail : List Frame}
    (actor : Actor) (object : ObjId)
    (pending : s.pending = .pickDo p src env first more body rest :: tail) :
    Legal s ⟨actor, .choose object⟩ ↔
      s.result = none ∧ actor = .player p ∧ object ∈ first :: more := by
  simp [Legal, LegalFrame, LegalConcede, pending]

/-- The designated player can answer a choice between effects whenever the chosen branch is
legal in the current state. -/
theorem legal_eitherDecision_iff {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {first second : Effect} {rest : EffectList} {tail : List Frame} (actor : Actor) (accept : Bool)
    (pending : s.pending = .eitherDo p src env first second rest :: tail) :
    Legal s ⟨actor, .decide accept⟩ ↔
      s.result = none ∧ actor = .player p ∧ eitherOk s p src env first second accept = true := by
  simp [Legal, LegalFrame, LegalConcede, pending]

/-- An optional trigger cannot enter the automatic Add path (CR 383.3, 430.2). -/
theorem optionalTrigger_noImmediateAdd {s : GameState} {t : PendTrigger}
    (optional : trigOptional s t = true) : t.immediateAddFrame s = none := by
  cases ability : triggerAbility s t with
  | none => simp [PendTrigger.immediateAddFrame, ability]
  | some a =>
    cases a <;> simp_all [trigOptional, trigDeclaration, PendTrigger.immediateAddFrame]

/-- An optional trigger goes to the controller's trigger-order decision, even when it is the
only trigger and has no cost or targets (CR 383.3). -/
theorem triggersStep_optionalChoice {s : GameState} {t : PendTrigger}
    (more : List PendTrigger) (rest : List Frame) (optional : trigOptional s t = true) :
    ∃ group other, triggersStep s (t :: more) rest =
      (s, [.triggerOrder t.controller t group other]) := by
  simp [triggersStep, optional]

/-- When finalization is waiting for an initial decision, only the designated player can decline
an optional trigger in the group (CR 383.3). -/
theorem legal_declineTrigger_iff {s : GameState} {p : PlayerId} {first t : PendTrigger}
    {more other : List PendTrigger} {rest : List Frame} {index : Nat} (actor : Actor)
    (pending : s.pending = .triggerOrder p first more other none :: rest)
    (trigger : (first :: more)[index]? = some t) :
    Legal s ⟨actor, .putTrigger index [] .skip⟩ ↔
      s.result = none ∧ actor = .player p ∧ trigOptional s t = true := by
  simp [Legal, LegalFrame, LegalConcede, pending, triggerFinishOk, trigger, trigLegal]

/-- A printed optional Spell cost has both accept and decline candidates for every ordinary effect
choice and admissible Repeat count, before checking payment (CR 355.1, 356.4.f.1). -/
theorem castPicks_printedOptionalCost {s : GameState} {p : PlayerId} {card : ObjId} {d : CardDef}
    {pick : SpellPick} {repeats : Nat} (payCost : Bool) (spell : d.hasType .spell = true)
    (printed : d.additionalCost.isSome = true) (base : pick ∈ s.spellPicks p d)
    (bounded : repeats ≤ (s.extrasRaw p card d).countP Prod.snd) :
    .withCosts pick payCost repeats ∈ s.castPicks p card d := by
  have repeatsInRange : repeats ∈ List.range ((s.extrasRaw p card d).countP Prod.snd + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le bounded)
  simp only [GameState.castPicks, spell, printed, ite_true, Bool.true_or, List.mem_append]
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  simp only [List.mem_flatMap]
  refine ⟨pick, base, repeats, repeatsInRange, ?_⟩
  cases payCost <;> simp

/-- Legality requires an explicit accept-or-decline declaration for a printed optional Spell cost,
including when both choices can be made with the same payment (CR 355.1, 356.4.f.1). -/
theorem spellCostsOk_requiresPrintedCostChoice {s : GameState} {p : PlayerId} {card : ObjId}
    {d : CardDef} {cost : Cost} {targets : List ObjId} {pay : RunePool.Payment} {pick : SpellPick}
    (printed : d.additionalCost.isSome = true)
    (legal : s.spellCostsOk p card d cost targets pay pick = true) :
    pick.optionalCosts.isSome = true := by
  cases choice : pick.optionalCosts with
  | none =>
    simp [GameState.spellCostsOk, choice] at legal
    simp [legal.2.1] at printed
  | some choice => rfl

/-- A Spell's explicit additional-cost decisions are recorded verbatim, including when a chosen
cost is discounted to zero (CR 355.1, 356.4.f.1). -/
theorem playMark_declaredOptionalCosts (s : GameState) (p : PlayerId) (card : ObjId)
    (pay : RunePool.Payment) (targets : List ObjId) (directCast : Bool) (flow : Option Cost)
    (pick : SpellPick) (printed : Bool) (repeats : Nat)
    (declared : pick.optionalCosts = some (printed, repeats)) :
    let mark := s.playMark p card pay targets directCast flow pick
    mark.paid = printed ∧ mark.extraPaid = repeats := by
  simp [GameState.playMark, declared]

end Riftbound

end
