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

/-- Removing the active Cleanup frame does not make the board unsettled. In particular it
preserves the lethal test for each unit, including previously attributed damage. -/
theorem GameState.Settled.pop_cleanup {s : GameState} {rest : List Frame} (settled : s.Settled)
    (wf : s.WF) (database : MightRead.database s.cards) (pending : s.pending = .cleanup :: rest) :
    ({ s with pending := rest } : GameState).Settled := by
  let next := { s with pending := rest }
  have combat : next.combatNow = s.combatNow := by
    unfold GameState.combatNow
    rw [pending]
    rfl
  have reads : SameMightReads s next := (SameMightReads.refl s).replacePending rest combat
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

/-- When a settled Cleanup has no Showdown or linked-damage notification to dispatch, it
returns to neutral priority in one work step without preparation scheduling another Cleanup. -/
theorem advance_settledCleanup_to_priority {s : GameState} {p : PlayerId} {seen : List Event} (wf : s.WF)
    (database : MightRead.database s.cards) (pending : s.pending = [.cleanup, .priority p])
    (settled : s.Settled) (noShowdown : s.stagedShowdowns [.priority p] = [])
    (noLinks : s.turnFx.any (fun f => match f.kind with
      | .linkedDamageDeath .. => true | _ => false) = false) :
    advance 1 s seen = .ok ({ s with pending := [.priority p] }, seen) := by
  let next := { s with pending := [.priority p] }
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
  have observes : s.observeCombat [.priority p] = (s.combat, []) := by
    unfold GameState.observeCombat
    cases current : s.combat <;> rfl
  have raw : cleanupFrame s [.priority p] = (next, []) := by
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
  have notices : s.workTransitionEvents next = [] := by
    simp [GameState.workTransitionEvents, pending, next, noExhaust, mighty, GameState.mightReductionEvents]
    intro note member
    have absent := (List.any_eq_false.mp noLinks) note member
    cases kind : note.kind <;> simp_all
  have work : workStep s = some (next, []) := by
    simp only [workStep, pending, microStep, microStep0, raw, Option.map_some,
      List.nil_append, notices, withTriggers_nil]
  have ready : next.Settled := settled.pop_cleanup wf database pending
  have prepared : next.preparePriority = next := by
    have nextStack : next.pending = [.priority p] := rfl
    simp [GameState.preparePriority, nextStack, ready.1, ready.2]
  have stop : next.preparePriority.pending.head?.all (fun f => !f.isWork) = true := by
    rw [prepared]
    rfl
  have zero : AdvancePrefix next next 0 [] := by intro fuel before; simp
  simpa only [List.append_nil] using (zero.prepend pending rfl work).finish stop seen

private theorem cleanupFrame_route (s : GameState) (rest : List Frame) (wf : s.WF)
    (pending : s.pending = .cleanup :: rest) :
    let raw := (cleanupFrame s rest).1
    raw.pending.head?.all (fun f => !f.isWork) = true ∨ raw.pending = rest ∨
      (raw.pending = .cleanup :: rest ∧ MeasLt raw.cleanupMeasure s.cleanupMeasure) := by
  have reinstall (t : GameState) (safe : Safe s t) : { t with pending := .cleanup :: rest } = t := by
    rw [← safe.same.pending.trans pending]
  unfold cleanupFrame
  cases winner : s.winner with
  | some p => exact Or.inl rfl
  | none =>
    cases choice : cleanupDeathBanishChoice s with
    | some r =>
      obtain ⟨src, player, first, other⟩ := r
      exact Or.inl rfl
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
          | nil => exact Or.inr (Or.inl rfl)
          | cons entry more =>
            obtain ⟨bf, player⟩ := entry
            dsimp only
            split <;> exact Or.inl rfl

/-- Resolve Cleanup and every immediate Add it detects, including when it opens a decision.
Ordinary triggers waiting behind Cleanup stay in the continuation tracked by `keeps`. -/
theorem advance_cleanup_with_adds {s : GameState} {rest : List Frame} (wf : s.WF)
    (reads : MightRead.database s.cards) (pending : s.pending = .cleanup :: rest)
    (keeps : List Frame → Prop) (base : keeps rest)
    (insertion : ∀ stack, keeps stack → ∀ q, q ≠ [] → keeps (insertTriggers q stack)) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      (t.pending.head?.all (fun f => !f.isWork) = true ∨
        (keeps t.pending ∧ t.WF ∧ t.cards = s.cards)) := by
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
  rcases cleanupFrame_route state rest wellFormed pending with decision | resume | ⟨repeatStack, decreases⟩
  · obtain ⟨t, later, finished, stopped⟩ :=
      advance_observed_decision mid raw.1.pending midWF (cards ▸ reads) observedStack decision
    exact ⟨t, used + 1 + later, raw.2 ++ events, by omega,
      by simpa only [List.append_nil] using path.append finished, Or.inl stopped⟩
  · change raw.1.pending = rest at resume
    rw [resume] at observedStack
    generalize stack : mid.pending = frames at observedStack
    cases observedStack with
    | empty => exact ⟨mid, _, _, positive, path, Or.inl (by rw [stack]; rfl)⟩
    | resume => exact ⟨mid, _, _, positive, path, Or.inr ⟨stack.symm ▸ base, midWF, cards⟩⟩
    | queue q nonempty =>
      exact ⟨mid, _, _, positive, path, Or.inr ⟨stack.symm ▸ insertion rest base q nonempty, midWF, cards⟩⟩
  · change raw.1.pending = .cleanup :: rest at repeatStack
    rw [repeatStack] at observedStack
    have again (tail : List Frame) (stack : mid.pending = .cleanup :: tail) (track : keeps tail) :
        ∃ t used events, 0 < used ∧ AdvancePrefix state t used events ∧
          (t.pending.head?.all (fun f => !f.isWork) = true ∨
            (keeps t.pending ∧ t.WF ∧ t.cards = state.cards)) := by
      have same := measured (by rw [stack]; simp)
      have smaller : InvImage MeasLt GameState.cleanupMeasure mid state := by
        change MeasLt mid.cleanupMeasure state.cleanupMeasure
        rw [same]
        exact decreases
      obtain ⟨t, later, emitted, _, finished, stopped | ⟨lastStack, lastWF, lastCards⟩⟩ :=
        ih mid smaller midWF (cards ▸ reads) stack track
      · exact ⟨t, used + 1 + later, (raw.2 ++ events) ++ emitted, by omega, path.append finished,
          Or.inl stopped⟩
      · exact ⟨t, used + 1 + later, (raw.2 ++ events) ++ emitted, by omega, path.append finished,
          Or.inr ⟨lastStack, lastWF, lastCards.trans cards⟩⟩
    generalize stack : mid.pending = frames at observedStack
    cases observedStack with
    | empty => exact ⟨mid, _, _, positive, path, Or.inl (by rw [stack]; rfl)⟩
    | resume => exact again rest stack base
    | queue q nonempty => exact again (insertTriggers q rest) stack (insertion rest base q nonempty)

end Riftbound

end
