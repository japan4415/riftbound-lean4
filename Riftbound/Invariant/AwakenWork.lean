module

public import Riftbound.Invariant.BeginTurnWork

/-!
# Automatic work during Awaken

Awaken readies objects before sending its timing, ready and Might notices to the ordinary
trigger queue. If that queue is nonempty, the engine asks for a decision before Beginning.
-/

@[expose] public section

namespace Riftbound

private theorem awaken_noExhaustion (s : GameState) (eligible : ObjId → Object → Bool)
    (after : GameState) (objects : ∀ id, after.obj? id = (s.obj? id).map (awakenReady eligible id)) :
    s.exhaustionEvents after none = [] := by
  have empty : ((s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))).filter
    (fun id => (s.obj? id).any (fun o => !o.exhausted) && (after.obj? id).any (·.exhausted))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro id _
    rw [objects]
    cases found : s.obj? id with
    | none => simp
    | some o =>
      simp only [Option.any_some, Option.map_some, awakenReady]
      split <;> cases o.exhausted <;> simp
  unfold GameState.exhaustionEvents
  dsimp only
  rw [empty]
  rfl

private theorem awaken_readied_notices (s : GameState) (eligible : ObjId → Object → Bool) :
    ∀ e ∈ s.objects.toList.filterMap
      (fun (k, o) => if o.exhausted && eligible ⟨k⟩ o then some (Event.readied ⟨k⟩) else none),
      AwakenNotice e := by
  intro e member
  obtain ⟨⟨id, object⟩, _, found⟩ := List.mem_filterMap.mp member
  dsimp only at found
  split at found
  · obtain rfl := Option.some.inj found
    exact .readied _
  · contradiction

/-- Awaken reaches the original Beginning stack or a player decision for the ordinary triggers
it observed. The Beginning continuation keeps the same card database and is well formed. -/
theorem advance_awaken {s : GameState} {rest : List Frame} (wf : s.WF)
    (mightReads : MightRead.database s.cards) (might : s.cards.mightTriggersAreOrdinary)
    (awaken : s.cards.awakenTriggersAreOrdinary)
    (pending : s.pending = .phase .awaken :: .phase .beginning :: rest) :
    ∃ t used events, 0 < used ∧ AdvancePrefix s t used events ∧
      ((t.pending = .phase .beginning :: rest ∧ t.WF ∧ t.cards = s.cards) ∨
        ∃ f tail, t.pending = f :: tail ∧ f.isWork = false) := by
  let p := s.active.getD ⟨0⟩
  let eligible := awakenCanReady s p (s.anyActive .skipUnitAwaken)
  let raw := { s.mapObjectsAt (awakenReady eligible) with
    phase := .awaken
    pending := .phase .beginning :: rest }
  let readied := s.objects.toList.filterMap
    (fun (k, o) => if o.exhausted && eligible ⟨k⟩ o then some (Event.readied ⟨k⟩) else none)
  let events := Event.phaseStarted p .awaken :: readied
  let notices := events ++ s.mightyEvents raw
  let detected := raw.detect notices
  let observes := raw.phase != .setup && raw.pending.all (fun f => !f.isSetup) && !detected.isEmpty
  have noExhaustion : s.exhaustionEvents raw none = [] :=
    awaken_noExhaustion s eligible raw (fun id => GameState.obj?_mapObjectsAt s _ id)
  have transition : s.workTransitionEvents raw = s.mightyEvents raw := by
    simp only [GameState.workTransitionEvents, pending, noExhaustion, GameState.mightReductionEvents,
      List.nil_append, List.append_nil]
  have known : ∀ e ∈ notices, AwakenNotice e := by
    intro e found
    rcases List.mem_append.mp found with emitted | observed
    · rcases List.mem_cons.mp emitted with rfl | ready
      · exact .phaseStarted p
      · exact awaken_readied_notices s eligible e ready
    · exact AwakenNotice.of_mightyEvents observed
  have work : workStep s = some (if observes then
      { raw with pending := insertTriggers detected raw.pending } else raw, events) := by
    simp only [workStep, pending, microStep, microStep0, Option.map_some]
    change some (raw.withTriggers (events ++ s.workTransitionEvents raw), events) = _
    rw [transition, withAwakenNotices_ordinary raw notices awaken might known]
  by_cases inserts : observes = true
  · rw [ite_eq_left inserts] at work
    let next := { raw with pending := insertTriggers detected raw.pending }
    have stack : next.pending = .triggers detected :: .phase .beginning :: rest := rfl
    have nonempty : detected ≠ [] := by
      intro empty
      simp [observes, empty] at inserts
    obtain ⟨t, used, f, tail, _, path, choice, decision⟩ :=
      advance_triggers_to_decision next (workStep_wf wf work) detected _ stack mightReads (Or.inl nonempty)
    exact ⟨t, used + 1, events, by omega, by simpa only [List.append_nil] using path.prepend pending rfl work,
      Or.inr ⟨f, tail, choice, decision⟩⟩
  · rw [ite_eq_right inserts] at work
    have zero : AdvancePrefix raw raw 0 [] := by intro fuel before; simp
    exact ⟨raw, 1, events, by decide, by simpa only [List.append_nil] using zero.prepend pending rfl work,
      Or.inl ⟨rfl, workStep_wf wf work, rfl⟩⟩

/-- The blank Battlefield added after a concession preserves the Awaken trigger check. -/
theorem CardDB.awakenTriggersAreOrdinary_withConcessionBattlefield {db : CardDB}
    (checked : db.awakenTriggersAreOrdinary) : db.withConcessionBattlefield.awakenTriggersAreOrdinary := by
  unfold CardDB.withConcessionBattlefield
  split
  · exact checked
  · change (db.cards ++ [concessionBattlefieldToken]).all CardDef.awakenTriggersAreOrdinary = true
    have blank : concessionBattlefieldToken.awakenTriggersAreOrdinary = true := rfl
    change db.cards.all CardDef.awakenTriggersAreOrdinary = true at checked
    simp only [List.all_append, List.all_cons, List.all_nil, blank, checked, Bool.and_self]

end Riftbound

end
