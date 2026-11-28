module

public import Riftbound.Invariant.ObservedWork

/-!
# Cleanup across immediate Adds (I12)

The rule's board measure decreases for each repeated Cleanup, even with immediate Adds
between iterations. A settled Cleanup leaves its continuation or stages a decision.
-/

@[expose] public section

namespace Riftbound

private theorem find?_agree {α : Type} (items : List α) (first second : α → Bool)
    (agree : ∀ x ∈ items, first x = second x) : items.find? first = items.find? second := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.find?_cons, agree x List.mem_cons_self,
      ih (fun y member => agree y (List.mem_cons_of_mem _ member))]

/-- Finishing linked damage updates the history without adding an ability to the stack. -/
theorem linkedCleanup_withTriggers_recorded (s : GameState) :
    s.withTriggers [.linkedDamageCleanupDone] = s.recordTurnEvents [.linkedDamageCleanupDone] := by
  have noScore : s.eventWinner [.linkedDamageCleanupDone] = none := by
    rw [eventWinner_of_noWin s _ rfl]
    cases hc : s.clock <;> simp [GameState.suddenDeathScorer, hc]
  have noDelay : s.delayedPlayTriggers [.linkedDamageCleanupDone] = [] := by
    unfold GameState.delayedPlayTriggers
    split
    · rfl
    · apply List.flatMap_eq_nil_iff.mpr
      intro note _
      split
      · simp [GameState.matchesDelayedPlay]
      · rfl
  let recorded := s.recordTurnEvents [.linkedDamageCleanupDone]
  have plays : recorded.playLog = s.playLog := by
    simp [recorded, GameState.recordTurnEvents, GameState.recordPlayEvent]
  have first : recorded.cardResolutionTriggers s = [] := by simp [GameState.cardResolutionTriggers, plays]
  have detect : recorded.detect [.linkedDamageCleanupDone] [] (some s.turnFx) = [] := by
    have empty (order : List PlayerId) : order.flatMap (fun _ => ([] : List PendTrigger)) = [] :=
      List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
    simp [GameState.detect, GameState.deathGroupWatchers, GameState.stunGroupWatchers, GameState.trimLimits,
      GameState.firstSpellFieldTriggers, detectOne, empty]
  unfold GameState.withTriggers
  rw [noScore]
  change (if _ then (match recorded.detect [.linkedDamageCleanupDone]
      (recorded.cardResolutionTriggers s ++ s.delayedPlayTriggers [.linkedDamageCleanupDone] ++
        s.delayedDamageTriggers [.linkedDamageCleanupDone])
      (some s.turnFx) with
      | [] => recorded | queue => { recorded with pending := insertDetectedTriggers recorded queue s.pending })
    else recorded) = recorded
  have noDamage : s.delayedDamageTriggers [.linkedDamageCleanupDone] = [] := rfl
  simp only [first, noDelay, noDamage, List.nil_append, detect, ite_self]

private def linkedDamageNote (note : TurnFx) : Bool :=
  match note.kind with
  | .linkedDamageDeath .. => true
  | _ => false

private def keepAfterLinkedDamage (note : TurnFx) : Bool :=
  match note.kind with
  | .linkedDamageDeath .. => false
  | _ => true

private theorem filter_withoutLinkedDamage (s : GameState) (test : TurnFx → Bool)
    (ignores : ∀ note, linkedDamageNote note = true → test note = false) :
    (s.turnFx.filter keepAfterLinkedDamage).filter test = s.turnFx.filter test := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro note _
  have complement : keepAfterLinkedDamage note = !linkedDamageNote note := by
    cases kind : note.kind <;> simp [keepAfterLinkedDamage, linkedDamageNote, kind]
  rw [complement]
  cases linked : linkedDamageNote note
  · simp
  · simp [ignores note linked]

private theorem withoutLinkedDamage_reads (s : GameState) :
    SameMightReads s { s with turnFx := s.turnFx.filter keepAfterLinkedDamage } := by
  let next := { s with turnFx := s.turnFx.filter keepAfterLinkedDamage }
  have buffs (p : PlayerId) :
      (next.fxOf p).filter (· == .buffsExtraMight) = (s.fxOf p).filter (· == .buffsExtraMight) := by
    rw [buffEffects, buffEffects]
    apply congrArg (List.map TurnFx.kind)
    apply filter_withoutLinkedDamage
    intro note linked
    cases kind : note.kind <;> simp_all [linkedDamageNote]
  have bonus : next.buffBonus = s.buffBonus := by
    funext id
    have lookup : next.obj? id = s.obj? id := rfl
    simp only [GameState.buffBonus, lookup, buffs]
  have facts : next.turnFx.filter (fun note => note.kind.isMightReadFact) =
      s.turnFx.filter (fun note => note.kind.isMightReadFact) := by
    apply filter_withoutLinkedDamage
    intro note linked
    cases kind : note.kind <;> simp_all [linkedDamageNote, TurnEffect.isMightReadFact]
  exact { SameMightReads.refl s with buffBonus := bonus, turnFacts := facts }

/-- Removing the active Cleanup frame does not make the board unsettled. In particular it
preserves the lethal test for each unit, including previously attributed damage. -/
private theorem GameState.Settled.pop_cleanup_core {s : GameState} {rest : List Frame}
    (settled : s.Settled) (wf : s.WF) (database : MightRead.database s.cards)
    (pending : s.pending = .cleanup :: rest) (notes : List TurnFx)
    (facts : SameMightReads s { s with turnFx := notes }) :
    ({ s with pending := rest, turnFx := notes } : GameState).Settled := by
  let next := { s with pending := rest, turnFx := notes }
  have combat : next.combatNow = s.combatNow := by
    unfold GameState.combatNow
    rw [pending]
    rfl
  have reads : SameMightReads s next := facts.replacePending rest combat
  have fights (field : ObjId) : next.fightingAt field = s.fightingAt field := by
    unfold GameState.fightingAt
    rw [pending]
    rfl
  have agrees (id : ObjId) (onBoard : id ∈ s.inPlay) : next.lethal id = s.lethal id := by
    have might := reads.mightNow_eq wf database (old_inPlay wf onBoard)
    have override (p : PlayerId) (target : Object) :
        next.makesDamageLethal p target = s.makesDamageLethal p target :=
      reads.makesDamageLethal_eq wf database p target
    have lookup : next.obj? id = s.obj? id := rfl
    have players : next.playerCount = s.playerCount := rfl
    have marks : next.damageMarks = s.damageMarks := rfl
    simp only [GameState.lethal, GameState.damageWillBeLethal, lookup, players, might, override, marks]
  have lethalFind : (next.inPlay.find? fun id => next.isUnit id && next.lethal id) =
      s.inPlay.find? (fun id => s.isUnit id && s.lethal id) := by
    change (s.inPlay.find? fun id => s.isUnit id && next.lethal id) = _
    exact find?_agree _ _ _ (fun id atBoard => by rw [agrees id atBoard])
  have lost : next.lostControl = s.lostControl := by
    funext field
    unfold GameState.lostControl
    rw [fights]
    rfl
  have stale : next.staleContest = s.staleContest := by
    funext field
    unfold GameState.staleContest
    rw [fights]
    rfl
  have fields : next.battlefields = s.battlefields := rfl
  have contests : next.newContest = s.newContest := rfl
  have step0 : cleanupStep0 next = none := by
    have h := cleanupStep0_of_none settled.2
    unfold cleanupStep0 at h ⊢
    rw [lethalFind, fields, lost, stale, contests]
    cases one : s.inPlay.find? (fun id => s.isUnit id && s.lethal id) <;> simp_all
    cases one : s.battlefields.find? s.lostControl <;> simp_all
    cases one : s.battlefields.find? s.staleContest <;> simp_all
    cases one : s.battlefields.findSome? (fun b => (s.newContest b).map (fun q => (b, q))) <;> simp_all
  have before := settled.2
  have oldToken : tokenStep s = none := by
    cases found : tokenStep s with
    | none => rfl
    | some result => simp [cleanupStep, found] at before
  have oldDetach : detachStep s = none := by
    cases found : detachStep s with
    | none => rfl
    | some result => simp [cleanupStep, oldToken, found] at before
  have oldLegend : returnReservedLegendStep s = none := by
    cases found : returnReservedLegendStep s with
    | none => rfl
    | some result => simp [cleanupStep, oldToken, oldDetach, found] at before
  have token : tokenStep next = none := by
    have offBoard : next.offBoardToken = s.offBoardToken := rfl
    simp only [tokenStep] at oldToken
    simp only [tokenStep, offBoard]
    cases h : s.offBoardToken with
    | none => rfl
    | some id =>
      have located : next.locate id = s.locate id := rfl
      simp only [removeObj, located] at oldToken ⊢
      cases found : s.locate id <;> simp_all
  have detached : detachStep next = none := by
    have gear : next.looseGear = s.looseGear := rfl
    simp only [detachStep] at oldDetach
    simp only [detachStep, gear]
    cases found : s.looseGear <;> simp_all
  have legend : returnReservedLegendStep next = none := by
    have expired : next.expiredReservedLegend = s.expiredReservedLegend := rfl
    simp only [returnReservedLegendStep] at oldLegend
    simp only [returnReservedLegendStep, expired]
    cases selected : s.expiredReservedLegend with
    | none => rfl
    | some card =>
      obtain ⟨p, id⟩ := card
      have located : next.locate id = s.locate id := rfl
      have lookup : next.obj? id = s.obj? id := rfl
      have players : next.playerCount = s.playerCount := rfl
      simp only [selected, Option.bind_eq_bind, Option.bind_some] at oldLegend
      simp only [Option.bind_eq_bind, Option.bind_some]
      have noMove : moveObj s id (.player p .reserveLegends) = none := by
        cases found : moveObj s id (.player p .reserveLegends) with
        | none => rfl
        | some result => simp [found] at oldLegend
      have noMoveNext : moveObj next id (.player p .reserveLegends) = none := by
        unfold moveObj at noMove ⊢
        rw [located, lookup, players]
        cases origin : s.locate id <;> cases object : s.obj? id <;> simp only [origin, object] at noMove ⊢ <;> try rfl
        split at noMove
        · rename_i blocked
          simp [blocked]
        · split at noMove <;> contradiction
      rw [noMoveNext]
      rfl
  have winner : next.winner = s.winner := by
    have score := reads.victoryScore_eq wf database
    unfold GameState.winner
    rw [score]
    rfl
  refine ⟨winner.trans settled.1, ?_⟩
  change cleanupStep next = none
  simp [cleanupStep, token, detached, legend, step0]

/-- Taking a Cleanup frame off a settled board preserves its fixed point. -/
theorem GameState.Settled.pop_cleanup {s : GameState} {rest : List Frame} (settled : s.Settled)
    (wf : s.WF) (database : MightRead.database s.cards) (pending : s.pending = .cleanup :: rest) :
    ({ s with pending := rest } : GameState).Settled :=
  settled.pop_cleanup_core wf database pending s.turnFx (SameMightReads.refl s)

/-- Frames at which Cleanup observes the combatants. -/
def Frame.observesCombat : Frame → Bool
  | .showdown .. | .endShowdown .. | .combatResolve .. | .combatResult ..
  | .combatControl .. | .combatFinish .. => true
  | _ => false

/-- A continuation without a combat observation frame leaves combat participation unchanged. -/
theorem GameState.observeCombat_idle (s : GameState) (stack : List Frame)
    (quiet : ∀ f ∈ stack, Frame.observesCombat f = false) :
    s.observeCombat stack = (s.combat, []) := by
  unfold GameState.observeCombat
  cases active : s.combat with
  | some c =>
    have none : stack.any (fun
        | .showdown bf .. | .endShowdown bf | .combatResolve bf _ | .combatResult bf |
          .combatControl bf | .combatFinish bf => bf == c.battlefield
        | _ => false) = false := by
      apply List.any_eq_false.mpr
      intro f member
      have silent := quiet f member
      cases f <;> simp [Frame.observesCombat] at silent ⊢
    dsimp only
    rw (config := { transparency := .all }) [none]
    simp only [Bool.false_eq_true, ↓reduceIte]
  | none =>
    have none : stack.findSome? (fun
      | .showdown bf p _ => some (bf, p)
      | _ => none) = none := by
      apply List.findSome?_eq_none_iff.mpr
      intro f member
      have silent := quiet f member
      cases f <;> simp [Frame.observesCombat] at silent ⊢
    dsimp only
    rw (config := { transparency := .all }) [none]

/-- Neutral priority followed only by frames that do not update combat participation. -/
def QuietPriorityStack (frames : List Frame) : Prop :=
  ∃ p tail, frames = .priority p :: tail ∧ ∀ f ∈ tail, f.observesCombat = false

private theorem settledCleanup_priority_step {s : GameState} {p : PlayerId} {tail : List Frame} (wf : s.WF)
    (database : MightRead.database s.cards) (pending : s.pending = .cleanup :: .priority p :: tail)
    (settled : s.Settled) (noShowdown : s.stagedShowdowns (.priority p :: tail) = [])
    (quiet : ∀ f ∈ tail, f.observesCombat = false) :
    let raw := { s with pending := (.priority p :: tail) }
    let next := raw.withTriggers (s.workTransitionEvents raw)
    workStep s = some (next, []) ∧ next.pending = (.priority p :: tail) ∧ next.Settled ∧
      (s.turnFx.any linkedDamageNote = false → next = raw) := by
  let next := { s with pending := .priority p :: tail }
  have deathGroup : cleanupDeathGroup s = [] := by
    unfold cleanupDeathGroup
    split
    · rfl
    · apply List.filter_eq_nil_iff.mpr
      intro unit onBoard
      cases isUnit : s.isUnit unit
      · simp
      · simpa using Settled.no_lethal settled unit onBoard isUnit
  have noChoice : cleanupDeathBanishChoice s = none := by
    simp [cleanupDeathBanishChoice, deathGroup, GameState.deathGroupChoiceWith_nil]
  have noGroup : cleanupResolveDeathGroup s = none := by
    simp [cleanupResolveDeathGroup, deathGroup]
  have observes := s.observeCombat_idle (.priority p :: tail) (by
    intro f member
    rcases List.mem_cons.mp member with rfl | inside
    · rfl
    · exact quiet f inside)
  have raw : cleanupFrame s (.priority p :: tail) = (next, []) := by
    simp [cleanupFrame, settled.1, settled.2, noChoice, noGroup, noShowdown, continueAfterCleanup,
      observes, GameState.showdownOpeningEvents, next]
  have combat : next.combatNow = s.combatNow := by
    unfold GameState.combatNow
    rw [pending]
    rfl
  have reads : SameMightReads s next := (SameMightReads.refl s).replacePending _ combat
  have mighty : s.mightyEvents next = [] :=
    mightyEvents_eq_nil_of_mightNow (fun id member =>
      (reads.mightNow_eq wf database (old_inPlay wf member)).symm)
  have noExhaust : s.exhaustionEvents next none = [] := by
    unfold GameState.exhaustionEvents
    have empty : ((s.inPlay ++ s.players.flatMap (fun q => s.zone (.player q .legendZone))).filter
        (fun id => (s.obj? id).any (fun o => !o.exhausted) && (next.obj? id).any (·.exhausted))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro id _
      have lookup : next.obj? id = s.obj? id := rfl
      rw [lookup]
      cases s.obj? id <;> simp
    dsimp only
    rw [empty]
    rfl
  have notices : s.workTransitionEvents next =
      (if s.turnFx.any linkedDamageNote then [.linkedDamageCleanupDone] else []) := by
    simp [GameState.workTransitionEvents, pending, next, noExhaust, mighty,
      GameState.mightReductionEvents, linkedDamageNote] <;> rfl
  refine ⟨?_, ?_⟩
  · simp only [workStep, pending, microStep, microStep0, raw, Option.map_some, List.nil_append]
    rfl
  · change (next.withTriggers (s.workTransitionEvents next)).pending = (.priority p :: tail) ∧
      (next.withTriggers (s.workTransitionEvents next)).Settled ∧
      (s.turnFx.any linkedDamageNote = false → next.withTriggers (s.workTransitionEvents next) = next)
    rw [notices]
    cases links : s.turnFx.any linkedDamageNote
    · simp only [Bool.false_eq_true, ↓reduceIte, withTriggers_nil]
      exact ⟨rfl, settled.pop_cleanup wf database pending, fun _ => trivial⟩
    · simp only [↓reduceIte, linkedCleanup_withTriggers_recorded]
      refine ⟨rfl, ?_, by simp⟩
      let inPlay := s.phase != .setup && (.priority p :: tail).all (fun f => !f.isSetup)
      have recorded : next.recordTurnEvents [.linkedDamageCleanupDone] =
          (if inPlay then { next with turnFx := s.turnFx.filter keepAfterLinkedDamage } else next) := by
        by_cases active : inPlay = true
        · rw [ite_eq_left active]
          simp only [GameState.recordTurnEvents,
            show (next.phase != .setup && next.pending.all (fun f => !f.isSetup)) = true from active,
            ↓reduceIte]
          rfl
        · rw [ite_eq_right active]
          simp only [GameState.recordTurnEvents,
            show ¬ (next.phase != .setup && next.pending.all (fun f => !f.isSetup)) = true from active]
          rfl
      rw [recorded]
      split
      · exact settled.pop_cleanup_core wf database pending _ (withoutLinkedDamage_reads s)
      · exact settled.pop_cleanup wf database pending

private theorem preparedPriority_of_settled {s : GameState} {p : PlayerId} {rest : List Frame}
    (stack : s.pending = .priority p :: rest) (settled : s.Settled) :
    s.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  simp [GameState.preparePriority, stack, settled.1, settled.2, Frame.isWork]

/-- When a settled Cleanup has no Showdown to open, it returns to prepared neutral priority
in one work step, including when it clears linked-damage notes. -/
theorem advance_settledCleanup_to_preparedPriority {s : GameState} {p : PlayerId} (wf : s.WF)
    (database : MightRead.database s.cards) (pending : s.pending = [.cleanup, .priority p])
    (settled : s.Settled) (noShowdown : s.stagedShowdowns [.priority p] = []) :
    ∃ t, AdvancePrefix s t 1 [] ∧ t.pending = [.priority p] ∧ t.Settled := by
  obtain ⟨work, stack, ready, _⟩ := settledCleanup_priority_step wf database pending settled noShowdown (by simp)
  refine ⟨_, ?_, stack, ready⟩
  exact (show AdvancePrefix _ _ 0 [] from fun fuel before => by simp).prepend pending rfl work

/-- Without a linked-damage notification the only change when returning to neutral priority
is the removal of the settled Cleanup frame. -/
theorem advance_settledCleanup_to_priority {s : GameState} {p : PlayerId} {seen : List Event} (wf : s.WF)
    (database : MightRead.database s.cards) (pending : s.pending = [.cleanup, .priority p])
    (settled : s.Settled) (noShowdown : s.stagedShowdowns [.priority p] = [])
    (noLinks : s.turnFx.any (fun f => match f.kind with
      | .linkedDamageDeath .. => true | _ => false) = false) :
    advance 1 s seen = .ok ({ s with pending := [.priority p] }, seen) := by
  obtain ⟨work, _, _, unchanged⟩ := settledCleanup_priority_step wf database pending settled noShowdown (by simp)
  rw [unchanged noLinks] at work
  let next := { s with pending := [.priority p] }
  have zero : AdvancePrefix next next 0 [] := by intro fuel before; simp
  have stop := preparedPriority_of_settled (s := next) (p := p) rfl
    (settled.pop_cleanup wf database pending)
  simpa only [List.append_nil] using (zero.prepend pending rfl work).finish stop seen

private theorem cleanupFrame_route (s : GameState) (rest : List Frame) (wf : s.WF)
    (pending : s.pending = .cleanup :: rest) :
    let raw := (cleanupFrame s rest).1
    (raw.pending.head?.all (fun f => !f.isWork) = true ∧
      (∀ p tail, raw.pending ≠ .priority p :: tail)) ∨
      (raw.pending = rest ∧ s.Settled ∧ s.stagedShowdowns rest = []) ∨
      (raw.pending = .cleanup :: rest ∧ MeasLt raw.cleanupMeasure s.cleanupMeasure) := by
  have reinstall (t : GameState) (safe : Safe s t) : { t with pending := .cleanup :: rest } = t := by
    rw [← safe.same.pending.trans pending]
  unfold cleanupFrame
  cases winner : s.winner with
  | some p => exact Or.inl ⟨rfl, by intro q tail equality; cases equality⟩
  | none =>
    cases choice : cleanupDeathBanishChoice s with
    | some r =>
      obtain ⟨src, player, first, other⟩ := r
      exact Or.inl ⟨rfl, by intro q tail equality; cases equality⟩
    | none =>
      cases group : cleanupResolveDeathGroup s with
      | some r =>
        refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        dsimp only
        rw [reinstall _ (cleanupResolveDeathGroup_safe group)]
        exact cleanupResolveDeathGroup_decreases wf group
      | none =>
        cases one : cleanupStep s with
        | some r =>
          obtain ⟨board, events⟩ := r
          refine Or.inr (Or.inr ⟨rfl, ?_⟩)
          dsimp only
          rw [reinstall _ (cleanupStep_safe (s' := board) (es := events) one)]
          exact cleanupStep_lt wf one
        | none =>
          cases staged : s.stagedShowdowns rest with
          | nil => exact Or.inr (Or.inl ⟨rfl, ⟨winner, one⟩, rfl⟩)
          | cons entry more =>
            obtain ⟨bf, player⟩ := entry
            dsimp only
            split <;> exact Or.inl ⟨rfl, by intro q tail equality; cases equality⟩

private theorem insertTriggers_ne_priorityHead (queue : List PendTrigger) (frames : List Frame)
    (p : PlayerId) (rest : List Frame) : insertTriggers queue frames ≠ .priority p :: rest := by
  cases frames with
  | nil => simp [insertTriggers]
  | cons frame tail =>
    unfold insertTriggers
    split
    · rename_i resolution
      intro h
      rw [List.cons.injEq] at h
      rw [h.1] at resolution
      cases resolution
    · split <;> simp

/-- Resolve Cleanup and its immediate Adds. A neutral priority continuation that
cannot update combat participation is a prepared decision. -/
theorem advance_cleanup_with_adds_prepared_quiet {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = .cleanup :: rest)
    (keeps : List Frame → Prop) (base : keeps rest)
    (insertion : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨
        (keeps t.pending ∧ t.WF ∧ t.cards = s.cards ∧ ¬ QuietPriorityStack t.pending)) := by
  revert wf reads rest
  apply (InvImage.wf GameState.cleanupMeasure MeasLt.wf).induction s
  intro state ih rest wellFormed reads pending base
  let raw := cleanupFrame state rest
  let notices := raw.2 ++ state.workTransitionEvents raw.1
  let observed := raw.1.withTriggers notices
  have work : workStep state = some (observed, raw.2) := by
    simp only [workStep, pending, microStep, microStep0, raw, Option.map_some, observed, notices]
  have known : raw.1.cards = state.cards := cleanupFrame_cards state rest
  have rawWF : raw.1.WF := (cleanupFrame_preservesBoard state rest wellFormed).1
  obtain ⟨mid, used, events, observedPath, midWF, observedCards, observedStack, measured⟩ :=
    advance_observed_work_measured raw.1 notices rawWF (known ▸ reads)
  have path := observedPath.prepend pending rfl work
  have cards : mid.cards = state.cards := observedCards.trans known
  have positive : 0 < used + 1 := by omega
  rcases cleanupFrame_route state rest wellFormed pending with
    ⟨decision, nonpriority⟩ | ⟨resume, settled, noShowdown⟩ | ⟨repeatStack, decreases⟩
  · obtain ⟨t, later, finished, stopped⟩ :=
      advance_observed_prepared_decision mid raw.1.pending midWF (cards ▸ reads) observedStack
        decision nonpriority
    exact ⟨t, used + 1 + later, raw.2 ++ events, by omega,
      by simpa only [List.append_nil] using path.append finished, Or.inl stopped⟩
  · by_cases neutral : QuietPriorityStack rest
    · obtain ⟨p, tail, rfl, quiet⟩ := neutral
      obtain ⟨step, stack, ready, _⟩ :=
        settledCleanup_priority_step wellFormed reads pending settled noShowdown quiet
      refine ⟨_, 1, [], by decide, ?_, Or.inl (preparedPriority_of_settled stack ready)⟩
      exact (show AdvancePrefix _ _ 0 [] from fun fuel before => by simp).prepend pending rfl step
    · change raw.1.pending = rest at resume
      rw [resume] at observedStack
      generalize stack : mid.pending = frames at observedStack
      cases observedStack with
      | empty =>
        have idle : mid.preparePriority.pending.head?.all (fun f => !f.isWork) = true :=
          GameState.prepared_idle_of_nonpriority (by rw [stack]; rfl) (by simp [stack])
        exact ⟨mid, _, _, positive, path, Or.inl idle⟩
      | resume =>
        exact ⟨mid, _, _, positive, path, Or.inr ⟨stack.symm ▸ base, midWF, cards,
          fun ⟨p, tail, h, quiet⟩ => neutral ⟨p, tail, stack.symm.trans h, quiet⟩⟩⟩
      | queue q nonempty =>
        exact ⟨mid, _, _, positive, path, Or.inr ⟨stack.symm ▸ insertion rest base q nonempty,
          midWF, cards, fun ⟨p, tail, h, _⟩ => insertTriggers_ne_priorityHead q rest p tail (stack.symm.trans h)⟩⟩
  · change raw.1.pending = .cleanup :: rest at repeatStack
    rw [repeatStack] at observedStack
    have again (tail : List Frame) (stack : mid.pending = .cleanup :: tail) (track : keeps tail) :
        ∃ t used events, 0 < used ∧ AdvancePrefix state t used events ∧
          (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨
            (keeps t.pending ∧ t.WF ∧ t.cards = state.cards ∧ ¬ QuietPriorityStack t.pending)) := by
      have same := measured (by rw [stack]; simp)
      have smaller : InvImage MeasLt GameState.cleanupMeasure mid state := by
        change MeasLt mid.cleanupMeasure state.cleanupMeasure
        rw [same]
        exact decreases
      obtain ⟨t, later, emitted, _, finished, stopped | ⟨lastStack, lastWF, lastCards, other⟩⟩ :=
        ih mid smaller midWF (cards ▸ reads) stack track
      · exact ⟨t, used + 1 + later, (raw.2 ++ events) ++ emitted, by omega, path.append finished,
          Or.inl stopped⟩
      · exact ⟨t, used + 1 + later, (raw.2 ++ events) ++ emitted, by omega, path.append finished,
          Or.inr ⟨lastStack, lastWF, lastCards.trans cards, other⟩⟩
    generalize stack : mid.pending = frames at observedStack
    cases observedStack with
    | empty =>
      have idle : mid.preparePriority.pending.head?.all (fun f => !f.isWork) = true :=
        GameState.prepared_idle_of_nonpriority (by rw [stack]; rfl) (by simp [stack])
      exact ⟨mid, _, _, positive, path, Or.inl idle⟩
    | resume => exact again rest stack base
    | queue q nonempty => exact again (insertTriggers q rest) stack (insertion rest base q nonempty)

/-- Resolve Cleanup and its immediate Adds, including preparation for a singleton neutral priority. -/
theorem advance_cleanup_with_adds_prepared {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = .cleanup :: rest)
    (keeps : List Frame → Prop) (base : keeps rest)
    (insertion : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.preparePriority.pending.head?.all (fun f => !f.isWork) = true ∨
        (keeps t.pending ∧ t.WF ∧ t.cards = s.cards ∧ ∀ p, t.pending ≠ [.priority p])) := by
  obtain ⟨t, used, events, positive, path, ready | ⟨track, safe, cards, notNeutral⟩⟩ :=
    advance_cleanup_with_adds_prepared_quiet wf reads pending keeps base insertion
  · exact ⟨t, used, events, positive, path, Or.inl ready⟩
  · exact ⟨t, used, events, positive, path, Or.inr ⟨track, safe, cards,
      fun p h => notNeutral ⟨p, [], h, by simp⟩⟩⟩

/-- Resolve Cleanup and every immediate Add it detects. Ordinary triggers waiting behind
Cleanup stay in the continuation tracked by `keeps`. -/
theorem advance_cleanup_with_adds {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = .cleanup :: rest)
    (keeps : List Frame → Prop) (base : keeps rest)
    (insertion : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun f => !f.isWork) = true ∨
        (keeps t.pending ∧ t.WF ∧ t.cards = s.cards)) := by
  obtain ⟨t, used, events, positive, path, prepared | ⟨track, sound, cards, _⟩⟩ :=
    advance_cleanup_with_adds_prepared wf reads pending keeps base insertion
  · exact ⟨t, used, events, positive, path,
      Or.inl (by simpa only [GameState.preparePriority_of_idle prepared] using prepared)⟩
  · exact ⟨t, used, events, positive, path, Or.inr ⟨track, sound, cards⟩⟩

/-- Resolve Cleanup and any queued ordinary triggers before returning to a waiting decision. -/
theorem advance_cleanup_at_preparedDecision {s : GameState} {rest original : List Frame}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .cleanup :: rest) (tracked : TriggerWorkTail original rest)
    (decision : original.head?.all (fun f => !f.isWork) = true)
    (front : ∀ f, original.head? = some f → f.isResolution = false ∧ ∀ q, f ≠ .triggers q)
    (quiet : ∀ p tail, original = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  obtain ⟨after, used, events, _, path, stop | ⟨track, safe, cards, notQuiet⟩⟩ :=
    advance_cleanup_with_adds_prepared_quiet wf reads pending (TriggerWorkTail original) tracked
      (fun _ keeps q ne => keeps.insert front q ne)
  · exact ⟨after, used, events, path, stop⟩
  · rcases track with resumed | ⟨queue, nonempty, queued⟩
    · have stop := GameState.prepared_idle_of_nonpriority (resumed.symm ▸ decision)
        (fun p tail equal => notQuiet ⟨p, tail, equal, quiet p tail (resumed.symm.trans equal)⟩)
      exact ⟨after, used, events, path, stop⟩
    · obtain ⟨t, more, _, _, _, later, _, _, stop⟩ :=
        advance_triggers_to_preparedDecision after safe queue original queued (cards ▸ reads) (Or.inl nonempty)
      exact ⟨t, used + more, events, by simpa only [List.append_nil] using path.append later, stop⟩

/-- Run any Cleanup that preparation schedules before returning a waiting decision. -/
theorem advance_waiting_to_preparedDecision {s : GameState} (wf : s.WF)
    (reads : MightRead.database s.cards) (waiting : s.pending.head?.all (fun f => !f.isWork) = true)
    (quiet : ∀ p tail, s.pending = .priority p :: tail → ∀ f ∈ tail, f.observesCombat = false) :
    ∃ t used events, AdvancePrefix s t used events ∧
      t.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
  rcases s.preparePriority_cases with unchanged | ⟨p, tail, stack, _, prepared⟩
  · exact ⟨s, 0, [], by intro fuel events; simp, by simpa only [unchanged] using waiting⟩
  · have staged : s.preparePriority.pending = .cleanup :: .priority p :: tail := by
      rw [prepared]
      exact congrArg (Frame.cleanup :: ·) stack
    have check : MightRead.database s.preparePriority.cards := by rw [prepared]; exact reads
    have agrees : s.preparePriority.preparePriority = s.preparePriority :=
      GameState.preparePriority_of_work staged rfl
    have same (fuel : Nat) (seen : List Event) : advance fuel s seen = advance fuel s.preparePriority seen := by
      cases fuel <;> simp only [advance, agrees]
    obtain ⟨t, used, events, path, ready⟩ :=
      advance_cleanup_at_preparedDecision wf.preparePriority check staged (Or.inl rfl) rfl
        (fun _ head => by cases head; exact ⟨rfl, by intro q eq; cases eq⟩)
        (fun q suffix equal => by cases equal; exact quiet p tail stack)
    exact ⟨t, used, events, fun fuel seen => (same (used + fuel) seen).trans (path fuel seen), ready⟩

end Riftbound

end
