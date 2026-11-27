module

public import Riftbound.Rules.Trigger

/-!
# Board reads during automatic trigger finalization

Putting a trigger on the Chain without choosing anything changes its source's bookkeeping and
adds an ability object. The printed and copied text, Might thresholds, and non-passive Might
inputs can still be read from the old board.
-/

@[expose] public section

namespace Riftbound

private def recordAutomaticUse (s : GameState) (trigger : PendTrigger) (o : Object) : Object :=
  (o.noteAbilityUse trigger.idx trigger.copyStamp).noteChose s.turn []

private def eraseTriggerBookkeeping (o : Object) : Object :=
  { o with used := [], copiedUses := [], chose := [], choseTurn := none }

private theorem erase_recordAutomaticUse (s : GameState) (trigger : PendTrigger) (o : Object) :
    eraseTriggerBookkeeping (recordAutomaticUse s trigger o) = eraseTriggerBookkeeping o := rfl

private theorem automatic_addObject (s : GameState) (trigger : PendTrigger) :
    ∃ item, (addObject (s.modObj trigger.source (recordAutomaticUse s trigger)) item .chain).map Prod.fst =
      some (putTrigger s trigger []) ∧
      item.kind.cardId? = none ∧ item.attachmentCopies = [] ∧ item.attachmentTextCopies = [] ∧
      item.attached = none ∧ item.baseMightThisTurn = none ∧ item.buffed = false := by
  let used := s.modObj trigger.source (recordAutomaticUse s trigger)
  let item : Object :=
    { abilityItem trigger.card trigger.idx trigger.source trigger.controller
        trigger.subject.toList trigger.eventAmount with
      triggerSubject := trigger.subject
      triggerKeyword := trigger.triggerKeyword
      eventBattlefields := trigger.eventBattlefields
      eventObjects := trigger.eventObjects
      shownOff := trigger.shownOff
      abilityCopyStamp := trigger.copyStamp }
  have noMode : recordTriggerMode s trigger none = s := by
    unfold recordTriggerMode
    split <;> rfl
  unfold putTrigger
  rw [noMode]
  dsimp only
  change ∃ candidate, (addObject used candidate .chain).map Prod.fst =
    some (match addObject used item .chain with | some r => r.1 | none => used) ∧ _
  refine ⟨item, ?_, ?_⟩
  · simp only [addObject, Zone.valid_chain, Zone.fits, and_self, ↓reduceIte, Option.map_some]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem automatic_unchanged (s : GameState) (trigger : PendTrigger) :
    let t := putTrigger s trigger []
    t.config = s.config ∧ t.cards = s.cards ∧ t.turn = s.turn ∧ t.turnFx = s.turnFx ∧
      t.experience = s.experience ∧ ∀ z, z ≠ .chain → t.zone z = s.zone z := by
  obtain ⟨item, transition, _⟩ := automatic_addObject s trigger
  obtain ⟨⟨next, fresh⟩, added, eq⟩ := Option.map_eq_some_iff.mp transition
  dsimp only at eq
  rw [← eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun z ne => addObject_zone_other added ne⟩
  all_goals
    obtain ⟨_, _, rfl⟩ := addObject_spec added
    rfl

private theorem automatic_lookups (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    let next := putTrigger s trigger []
    (∀ query : ObjId, query.n ≠ s.nextId →
      (next.obj? query).map eraseTriggerBookkeeping = (s.obj? query).map eraseTriggerBookkeeping) ∧
    s.obj? ⟨s.nextId⟩ = none ∧
    ∃ item, next.obj? ⟨s.nextId⟩ = some item ∧
      item.kind.cardId? = none ∧ item.attachmentCopies = [] ∧ item.attachmentTextCopies = [] ∧
      item.attached = none ∧ item.baseMightThisTurn = none ∧ item.buffed = false := by
  obtain ⟨item, transition, card, copies, text, unattached, base, unbuffed⟩ := automatic_addObject s trigger
  obtain ⟨⟨next, fresh⟩, added, eq⟩ := Option.map_eq_some_iff.mp transition
  dsimp only at eq
  have absent : s.obj? ⟨s.nextId⟩ = none := by
    apply Std.ExtTreeMap.getElem?_eq_none
    intro member
    obtain ⟨id, inZones, idNum⟩ := wf.zone_of_table _ member
    exact (Nat.ne_of_lt (wf.lt_nextId id inZones)) idNum
  let used := s.modObj trigger.source (recordAutomaticUse s trigger)
  change addObject used item .chain = some (next, fresh) at added
  obtain ⟨_, _, shape⟩ := addObject_spec added
  dsimp only
  rw [← eq, shape]
  refine ⟨?_, absent, {item with timestamp := ⟨s.nextTimestamp⟩}, ?_, card, copies, text,
    unattached, base, unbuffed⟩
  · intro id notFresh
    have different : compare s.nextId id.n ≠ .eq :=
      fun h => notFresh (Nat.compare_eq_eq.mp h).symm
    change ((used.objects.insert s.nextId _)[id.n]?).map eraseTriggerBookkeeping = _
    simp only [Std.ExtTreeMap.getElem?_insert, different, ↓reduceIte]
    change (used.obj? id).map eraseTriggerBookkeeping = _
    unfold used
    rw [GameState.obj?_modObj]
    split
    · rename_i sameKey
      have sameId : trigger.source = id := congrArg ObjId.mk sameKey
      cases sameId
      simp only [Option.map_map, Function.comp_def, erase_recordAutomaticUse]
    · rfl
  · change (used.objects.insert s.nextId _)[s.nextId]? = _
    rw [Std.ExtTreeMap.getElem?_insert_self]
    rfl

private theorem removeBookkeeping_map {α : Type} {a b : Option Object}
    (same : a.map eraseTriggerBookkeeping = b.map eraseTriggerBookkeeping)
    (read : Object → α) (stable : ∀ o, read (eraseTriggerBookkeeping o) = read o) :
    a.map read = b.map read := by
  have projected := congrArg (Option.map read) same
  simpa only [Option.map_map, Function.comp_def, stable] using projected

private theorem removeBookkeeping_any {a b : Option Object}
    (same : a.map eraseTriggerBookkeeping = b.map eraseTriggerBookkeeping)
    (read : Object → Bool) (stable : ∀ o, read (eraseTriggerBookkeeping o) = read o) :
    a.any read = b.any read := by
  have projected := congrArg (fun o => o.any read) same
  simpa only [Option.any_map, Function.comp_def, stable] using projected

private theorem removeBookkeeping_read {α : Type} {a b : Option Object}
    (same : a.map eraseTriggerBookkeeping = b.map eraseTriggerBookkeeping)
    (read : Option Object → α) (stable : ∀ o, read (o.map eraseTriggerBookkeeping) = read o) :
    read a = read b := by
  rw [← stable a, ← stable b, same]

private theorem automatic_attachmentReads (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    let next := putTrigger s trigger []
    next.attachmentCopyActive = s.attachmentCopyActive ∧
      next.attachmentTextActive = s.attachmentTextActive := by
  obtain ⟨older, absent, fresh, found, _, _, _, unattached, _, _⟩ := automatic_lookups s wf trigger
  constructor <;> funext unit copy
  all_goals
    by_cases new : copy.gear.n = s.nextId
    · have key : copy.gear = ⟨s.nextId⟩ := congrArg ObjId.mk new
      simp [GameState.attachmentCopyActive, GameState.attachmentTextActive, key, found, absent, unattached]
    · first
      | exact removeBookkeeping_any (older _ new) (fun o =>
          o.attached == some unit && o.attachmentCopyStamp == some copy.stamp) (fun _ => rfl)
      | exact removeBookkeeping_any (older _ new) (fun o =>
          o.attached == some unit && o.attachmentTextStamp == some copy.stamp) (fun _ => rfl)

private theorem automatic_cardDef (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    (putTrigger s trigger []).cardDef? = s.cardDef? := by
  obtain ⟨copyActive, _⟩ := automatic_attachmentReads s wf trigger
  obtain ⟨_, cards, _, _, _, _⟩ := automatic_unchanged s trigger
  obtain ⟨older, absent, fresh, found, noCard, noCopies, _, _, _, _⟩ := automatic_lookups s wf trigger
  funext id
  unfold GameState.cardDef? GameState.attachmentCopyOf
  rw [copyActive, cards]
  by_cases new : id.n = s.nextId
  · have key : id = ⟨s.nextId⟩ := congrArg ObjId.mk new
    simp [key, found, absent, noCopies, noCard]
  · have inputs := older id new
    let read (o : Object) : Option CardDef := do
      let key ← ((o.attachmentCopies.find? (s.attachmentCopyActive id)).map (·.card)) <|> o.kind.cardId?
      let d ← s.cards.find? key
      return (o.unitGearEffects.head?.map Prod.snd).elim d d.withUnitGearMight
    change ((putTrigger s trigger []).obj? id).bind read = (s.obj? id).bind read
    have stable (o : Object) : read (eraseTriggerBookkeeping o) = read o := rfl
    simpa only [Option.bind_map, Function.comp_def, stable] using
      congrArg (fun value => value.bind read) inputs

private theorem automatic_inPlay (s : GameState) (trigger : PendTrigger) :
    (putTrigger s trigger []).inPlay = s.inPlay := by
  obtain ⟨cfg, _, _, _, _, zones⟩ := automatic_unchanged s trigger
  have players : (putTrigger s trigger []).players = s.players := by simp [GameState.players, GameState.playerCount, cfg]
  unfold GameState.inPlay
  rw [players, zones .battlefieldZone (by decide)]
  congr 1
  congr 1
  funext p
  exact zones _ (by intro eq; cases eq)

private theorem automatic_passiveSources (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    (putTrigger s trigger []).passiveSources = s.passiveSources := by
  let next := putTrigger s trigger []
  obtain ⟨cfg, _, _, _, _, zones⟩ := automatic_unchanged s trigger
  obtain ⟨older, _, _, _, _, _, _, _, _, _⟩ := automatic_lookups s wf trigger
  have players : next.players = s.players := by simp [next, GameState.players, GameState.playerCount, cfg]
  have legends (p : PlayerId) :
      (next.zone (.player p .legendZone)).filter
        (fun id => (next.obj? id).any (fun o => o.reservedBy.all (next.inPlay.contains))) =
      (s.zone (.player p .legendZone)).filter
        (fun id => (s.obj? id).any (fun o => o.reservedBy.all (s.inPlay.contains))) := by
    rw [zones _ (by intro eq; cases eq), automatic_inPlay s trigger]
    apply List.filter_congr
    intro id member
    have bound := wf.lt_nextId id
      (GameState.mem_zoneIds (GameState.zone_valid_of_mem wf member) member)
    exact removeBookkeeping_any (older id (Nat.ne_of_lt bound)) _ (fun _ => rfl)
  unfold GameState.passiveSources
  rw [automatic_inPlay s trigger, players]
  have same := congrArg (fun l => s.inPlay ++ s.players.flatMap l) (funext legends)
  simpa only [next, automatic_inPlay s trigger] using same

private theorem automatic_attachmentTextDefs (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    ∀ id, (putTrigger s trigger []).attachmentTextDefs id = s.attachmentTextDefs id := by
  obtain ⟨_, textActive⟩ := automatic_attachmentReads s wf trigger
  obtain ⟨_, cards, _, _, _, _⟩ := automatic_unchanged s trigger
  obtain ⟨older, absent, fresh, found, _, _, noText, _, _, _⟩ := automatic_lookups s wf trigger
  intro id
  unfold GameState.attachmentTextDefs GameState.activeAttachmentText
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, textActive, cards]
  by_cases new : id.n = s.nextId
  · have key : id = ⟨s.nextId⟩ := congrArg ObjId.mk new
    simp [key, found, absent, noText]
  · rw [removeBookkeeping_map (older _ new) Object.attachmentTextCopies (fun _ => rfl)]

private theorem automatic_mightOf (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    ∀ id, (putTrigger s trigger []).mightOf id = s.mightOf id := by
  intro id
  obtain ⟨older, absent, fresh, found, _, _, _, _, noBase, _⟩ := automatic_lookups s wf trigger
  unfold GameState.mightOf
  rw [automatic_cardDef s wf trigger]
  by_cases new : id.n = s.nextId
  · have key : id = ⟨s.nextId⟩ := congrArg ObjId.mk new
    have noDefinition : s.cardDef? ⟨s.nextId⟩ = none := by simp [GameState.cardDef?, absent]
    simp [key, found, absent, noDefinition, noBase]
  · have lookups := older _ new
    generalize (putTrigger s trigger []).obj? id = after at lookups ⊢
    generalize s.obj? id = before at lookups ⊢
    apply removeBookkeeping_read lookups
    intro o
    cases o <;> rfl

private theorem buffEffects (s : GameState) (p : PlayerId) :
    (s.fxOf p).filter (· == .buffsExtraMight) =
      (s.turnFx.filter (fun f => (f.kind == .buffsExtraMight) && (f.turn == s.turn && f.who == p))).map
        (·.kind) := by
  unfold GameState.fxOf
  rw [List.filter_map, List.filter_filter]
  apply congrArg (List.map TurnFx.kind)
  apply List.filter_congr
  intro f _
  by_cases extra : f.kind == .buffsExtraMight
  · have kind : f.kind = .buffsExtraMight := beq_iff_eq.mp extra
    simp [kind]
  · simp [extra]

private theorem automatic_buffBonus (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    ∀ id, (putTrigger s trigger []).buffBonus id = s.buffBonus id := by
  intro id
  obtain ⟨_, _, turn, facts, _, _⟩ := automatic_unchanged s trigger
  obtain ⟨older, absent, fresh, found, _, _, _, _, _, unbuffed⟩ := automatic_lookups s wf trigger
  unfold GameState.buffBonus
  simp only [buffEffects, facts, turn]
  by_cases new : id.n = s.nextId
  · have key : id = ⟨s.nextId⟩ := congrArg ObjId.mk new
    simp [key, found, absent, unbuffed]
  · have lookups := older _ new
    generalize (putTrigger s trigger []).obj? id = after at lookups ⊢
    generalize s.obj? id = before at lookups ⊢
    apply removeBookkeeping_read lookups
    intro o
    cases o <;> rfl

private theorem automatic_equipBonus (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    ∀ id, (putTrigger s trigger []).equipBonus id = s.equipBonus id := by
  intro id
  obtain ⟨_, _, turn, _, xp, _⟩ := automatic_unchanged s trigger
  obtain ⟨older, _, _, _, _, _, _, _, _, _⟩ := automatic_lookups s wf trigger
  have sameXP : (putTrigger s trigger []).xpOf = s.xpOf := by
    funext p
    simp only [GameState.xpOf, xp]
  unfold GameState.equipBonus
  simp only [automatic_cardDef s wf trigger, automatic_inPlay s trigger, turn, sameXP]
  apply congrArg List.sum
  apply filterMap_congr_mem
  intro gear member
  have inZone : gear ∈ s.zoneIds := by
    simp only [GameState.inPlay, List.mem_append, List.mem_flatMap] at member
    rcases member with ⟨_, _, inBase⟩ | onBattlefield
    · exact GameState.mem_zoneIds (GameState.zone_valid_of_mem wf inBase) inBase
    · exact GameState.mem_zoneIds (GameState.zone_valid_of_mem wf onBattlefield) onBattlefield
  have lookups := older gear (Nat.ne_of_lt (wf.lt_nextId _ inZone))
  generalize (putTrigger s trigger []).obj? gear = after at lookups ⊢
  generalize s.obj? gear = before at lookups ⊢
  apply removeBookkeeping_read lookups
  intro o
  cases o <;> cases s.cardDef? gear <;> rfl

/-- Automatically putting an ordinary ability on the Chain preserves the sources and text of
passive abilities, as well as printed and lasting Might, buffs, and equipment bonuses. -/
theorem putTrigger_automatic_mightInputs (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    let next := putTrigger s trigger []
    next.passiveSources = s.passiveSources ∧ next.cardDef? = s.cardDef? ∧
      (∀ id, next.attachmentTextDefs id = s.attachmentTextDefs id) ∧
      next.mightOf = s.mightOf ∧ next.buffBonus = s.buffBonus ∧ next.equipBonus = s.equipBonus :=
  ⟨automatic_passiveSources s wf trigger, automatic_cardDef s wf trigger,
    automatic_attachmentTextDefs s wf trigger, funext (automatic_mightOf s wf trigger),
    funext (automatic_buffBonus s wf trigger), funext (automatic_equipBonus s wf trigger)⟩

/-- Automatically finalizing a trigger preserves the list of Might thresholds being watched,
including thresholds from a Gear's copied traits and the turn's ability grants. -/
theorem putTrigger_automatic_mightWatches (s : GameState) (wf : s.WF) (trigger : PendTrigger) :
    (putTrigger s trigger []).mightWatches = s.mightWatches := by
  obtain ⟨_, cards, turn, facts, _, _⟩ := automatic_unchanged s trigger
  simp only [GameState.mightWatches, automatic_passiveSources s wf trigger,
    automatic_cardDef s wf trigger, cards, turn, facts]

/-- An ordinary trigger queue step preserves the thresholds being watched. -/
theorem triggersStep_mightWatches (s : GameState) (wf : s.WF) (queue : List PendTrigger)
    (rest : List Frame) : (triggersStep s queue rest).1.mightWatches = s.mightWatches := by
  cases queue with
  | nil => rfl
  | cons t ts =>
    simp only [triggersStep]
    split
    · exact putTrigger_automatic_mightWatches s wf t
    · rfl

end Riftbound

end
