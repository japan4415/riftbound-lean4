module

public import Riftbound.Invariant.TriggerObservation

/-!
# Which work a Might threshold can schedule

The engine queues an ability by card definition and index. Check both printed and animated
definitions at that index, because animation can change the list of implicit abilities.
-/

@[expose] public section

namespace Riftbound

private def TriggerEvent.isMightThreshold : TriggerEvent → Bool
  | .becomeMighty | .mightAtLeast _ => true
  | _ => false

/-- Whether the trigger dispatcher can run an ability as an immediate Add. -/
def Ability.isImmediateAdd : Ability → Bool
  | .triggered rule effect _ =>
    !rule.optional && rule.cost == .free && effect.choices.isEmpty && effect.modes.isEmpty &&
      effect.moveChoice.isNone && effect.playerTarget.isNone && effect.body.isTriggerAdd
  | _ => false

/-- Check every Might trigger index against the definition used during resolution. -/
def noImmediateAddAtMight (observed resolved : List Ability) : Bool :=
  (List.range observed.length).all fun i =>
    !((observed[i]?).any (·.mightWatch.isSome)) || !((resolved[i]?).any Ability.isImmediateAdd)

/-- At each index that can queue a Might trigger, looking the ability back up cannot resolve an
immediate Add. The second check covers the ability indices of animated Gear. -/
def CardDef.mightTriggersAreOrdinary (d : CardDef) : Bool :=
  noImmediateAddAtMight d.allAbilities d.allAbilities &&
    noImmediateAddAtMight (d.withUnitGearMight 0).allAbilities d.allAbilities

/-- The database has no Might observation that can enqueue an immediate Add. -/
def CardDB.mightTriggersAreOrdinary (db : CardDB) : Prop :=
  db.cards.all CardDef.mightTriggersAreOrdinary = true

instance (db : CardDB) : Decidable db.mightTriggersAreOrdinary := by
  unfold CardDB.mightTriggersAreOrdinary
  infer_instance

private theorem noImmediateAddAtMight_of_index {observed resolved : List Ability} {i : Nat}
    {a : Ability} (checked : noImmediateAddAtMight observed resolved = true)
    (lookup : observed[i]? = some a) (might : a.mightWatch.isSome = true) :
    (resolved[i]?).any Ability.isImmediateAdd = false := by
  have bound : i < observed.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have atIndex := List.all_eq_true.mp checked i (List.mem_range.mpr bound)
  simpa [lookup, might] using atIndex

private theorem animated_allAbilities (d : CardDef) (n : Nat) :
    (d.withUnitGearMight n).allAbilities = (d.withUnitGearMight 0).allAbilities := by
  rfl

private def DeclaredDefinition (db : CardDB) (seen : CardDef) : Prop :=
  ∃ d, db.find? seen.id = some d ∧
    (seen.allAbilities = d.allAbilities ∨ seen.allAbilities = (d.withUnitGearMight 0).allAbilities)

private theorem declared_of_find {db : CardDB} {id : CardId} {d : CardDef}
    (found : db.find? id = some d) : DeclaredDefinition db d := by
  exact ⟨d, (CardDB.find?_id found) ▸ found, Or.inl rfl⟩

private theorem declared_of_cardDef {s : GameState} {id : ObjId} {d : CardDef}
    (found : s.cardDef? id = some d) : DeclaredDefinition s.cards d := by
  unfold GameState.cardDef? at found
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found
  obtain ⟨obj, _, key, _, printed, lookup, equal⟩ := found
  simp only [pure, Option.some.injEq] at equal
  cases animation : obj.unitGearEffects.head?.map Prod.snd with
  | none =>
    simp only [animation, Option.elim_none] at equal
    exact equal ▸ declared_of_find lookup
  | some n =>
    simp only [animation, Option.elim_some] at equal
    subst d
    exact ⟨printed, (CardDB.find?_id lookup) ▸ lookup, Or.inr (animated_allAbilities printed n)⟩

private theorem declared_of_attachmentText {s : GameState} {id : ObjId} {last : Bool}
    {d : CardDef} {stamp : Timestamp} (member : (d, stamp) ∈ s.attachmentTextDefs id last) :
    DeclaredDefinition s.cards d := by
  unfold GameState.attachmentTextDefs at member
  obtain ⟨copy, _, found⟩ := List.mem_filterMap.mp member
  obtain ⟨c, lookup, eq⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨rfl, _⟩ := Prod.mk.inj eq
  exact declared_of_find lookup

private theorem declared_of_sourceLookup {s : GameState} {id : ObjId} {copy : Option AttachmentCopy}
    {d : CardDef} (lookup : (copy.bind (fun c => s.cards.find? c.card) <|> s.cardDef? id) = some d) :
    DeclaredDefinition s.cards d := by
  cases found : copy.bind (fun c => s.cards.find? c.card) with
  | none => exact declared_of_cardDef (by simpa [found] using lookup)
  | some printed =>
    obtain ⟨c, _, fromDB⟩ := Option.bind_eq_some_iff.mp found
    have eq : printed = d := by simpa [found] using lookup
    exact eq ▸ declared_of_find fromDB

private def QueuedMightAbility (db : CardDB) (trigger : PendTrigger) : Prop :=
  trigger.triggerKeyword = none ∧ ∃ d a, DeclaredDefinition db d ∧
    d.id = trigger.card ∧ d.allAbilities[trigger.idx]? = some a ∧ a.mightWatch.isSome = true

private theorem queuedMight_immediate_none {s : GameState} {t : PendTrigger}
    (database : s.cards.mightTriggersAreOrdinary) (queued : QueuedMightAbility s.cards t) :
    t.immediateAddFrame s = none := by
  obtain ⟨noKeyword, seen, a, ⟨d, found, printed | animated⟩, id, atIndex, might⟩ := queued
  all_goals
    have check : noImmediateAddAtMight d.allAbilities d.allAbilities = true ∧
        noImmediateAddAtMight (d.withUnitGearMight 0).allAbilities d.allAbilities = true := by
      simpa only [CardDef.mightTriggersAreOrdinary, Bool.and_eq_true] using
        List.all_eq_true.mp database d (CardDB.find?_mem found)
    rw [id] at found
    have noAdd : (d.allAbilities[t.idx]?).any Ability.isImmediateAdd = false := by
      first
      | rw [printed] at atIndex; exact noImmediateAddAtMight_of_index check.1 atIndex might
      | rw [animated] at atIndex; exact noImmediateAddAtMight_of_index check.2 atIndex might
    unfold PendTrigger.immediateAddFrame triggerAbility abilityAt
    simp only [noKeyword, found, Option.bind_none, Option.bind_some]
    cases ability : d.allAbilities[t.idx]? with
    | none => rfl
    | some resolved =>
      rw [ability] at noAdd
      cases resolved <;> simp only [Option.any_some, Ability.isImmediateAdd] at noAdd
      all_goals first | rfl | simp [noAdd]

private theorem mightWatch_of_threshold {rule : Trigger} {effect : EffectDef} {limit : Limit}
    (threshold : rule.event.isMightThreshold = true) :
    (Ability.triggered rule effect limit).mightWatch.isSome = true := by
  cases event : rule.event <;> simp [TriggerEvent.isMightThreshold, Ability.mightWatch, event] at *

private theorem triggersAmongMatching_queued {s : GameState} {src : ObjId} {p : PlayerId}
    {d : CardDef} {lo hi : Nat} {copy : Option Timestamp}
    {fields : Option (List ObjId)} {t : PendTrigger} {matchesEvent : TriggerEvent → Bool}
    (definition : DeclaredDefinition s.cards d)
    (matchesMight : ∀ e, matchesEvent e = true → e.isMightThreshold = true)
    (member : t ∈ triggersAmongMatching s src p matchesEvent d lo hi copy fields) :
    QueuedMightAbility s.cards t := by
  unfold triggersAmongMatching at member
  obtain ⟨j, _, queued⟩ := List.mem_filterMap.mp member
  split at queued
  · rename_i rule effect limit lookup
    split at queued
    · rename_i conditions
      have chosen := Option.some.inj queued
      subst t
      simp only [Bool.and_eq_true] at conditions
      exact ⟨rfl, d, .triggered rule effect limit, definition, rfl, lookup,
        mightWatch_of_threshold (matchesMight _ conditions.1.1)⟩
    · contradiction
  · contradiction

private theorem triggersOfMatching_queued {s : GameState} {src : ObjId} {p : PlayerId}
    {copy : Option AttachmentCopy} {fields : Option (List ObjId)} {t : PendTrigger}
    {matchesEvent : TriggerEvent → Bool}
    (matchesMight : ∀ e, matchesEvent e = true → e.isMightThreshold = true)
    (member : t ∈ triggersOfMatching s src p matchesEvent copy fields) :
    QueuedMightAbility s.cards t := by
  unfold triggersOfMatching at member
  dsimp only at member
  simp only [List.mem_append] at member
  rcases member with (((printed | equipment) | copied) | granted)
  · split at printed
    · rename_i d found
      exact triggersAmongMatching_queued (declared_of_sourceLookup found) matchesMight printed
    · simp at printed
  · obtain ⟨id, _, fromEquipment⟩ := List.mem_flatMap.mp equipment
    split at fromEquipment
    · rename_i o d lookedObject lookedCard
      split at fromEquipment
      · exact triggersAmongMatching_queued (declared_of_cardDef lookedCard) matchesMight fromEquipment
      · simp at fromEquipment
    · simp at fromEquipment
  · obtain ⟨⟨d, stamp⟩, text, fromCopy⟩ := List.mem_flatMap.mp copied
    exact triggersAmongMatching_queued (declared_of_attachmentText text) matchesMight fromCopy
  · obtain ⟨fact, _, fromGrant⟩ := List.mem_flatMap.mp granted
    split at fromGrant
    · split at fromGrant
      · split at fromGrant
        · rename_i d found
          exact triggersAmongMatching_queued (declared_of_find found) matchesMight fromGrant
        · simp at fromGrant
      · simp at fromGrant
    · simp at fromGrant

private theorem watchersAt_queued {s : GameState} {src subj : ObjId} {who : PlayerId}
    {event : TriggerEvent} {t : PendTrigger} {occurrence : Occurrence} {dead : Option PlayerId}
    (threshold : event.isMightThreshold = true)
    (member : t ∈ watchersAt s subj who event occurrence src dead) :
    QueuedMightAbility s.cards t := by
  have notPlay : event ≠ .play := by rintro rfl; contradiction
  have notToken : event ≠ .playToken := by rintro rfl; contradiction
  have notDeath : (event == .die || event == .firstUnitDeathHere) = false := by
    cases event <;> simp_all [TriggerEvent.isMightThreshold]
  unfold watchersAt at member
  split at member
  · rename_i obj foundObject
    dsimp only at member
    split at member
    · rename_i definition foundDefinition
      obtain ⟨⟨d, limit, copy⟩, source, selected⟩ := List.mem_flatMap.mp member
      have declared : DeclaredDefinition s.cards d := by
        rcases List.mem_cons.mp source with equal | copied
        · have cardEq : d = definition := congrArg Prod.fst equal
          rw [cardEq]
          exact declared_of_sourceLookup foundDefinition
        · obtain ⟨⟨text, stamp⟩, original, eq⟩ := List.mem_map.mp copied
          have cardEq : text = d := congrArg Prod.fst eq
          rw [← cardEq]
          exact declared_of_attachmentText original
      obtain ⟨i, _, recorded⟩ := List.mem_filterMap.mp selected
      split at recorded
      · rename_i rule body perTurn lookup
        dsimp only at recorded
        simp only [notDeath, Bool.false_eq_true, ↓reduceIte] at recorded
        generalize (if definition.hasType .battlefield then who else dead.getD obj.controller) =
          controller at recorded
        split at recorded
        · rename_i satisfied
          obtain rfl := Option.some.inj recorded
          have matchEvent : rule.event = event := by
            simp only [Bool.and_eq_true, Bool.or_eq_true] at satisfied
            rcases satisfied.1.1.1.1.1 with direct | includes
            · exact beq_iff_eq.mp direct
            · rcases includes.2 with played | playedToken
              · exact False.elim (notPlay (beq_iff_eq.mp played))
              · exact False.elim (notToken (beq_iff_eq.mp playedToken))
          exact ⟨rfl, d, .triggered rule body perTurn, declared, rfl, lookup,
            mightWatch_of_threshold (matchEvent ▸ threshold)⟩
        · contradiction
      · contradiction
    · simp at member
  · simp at member

private theorem mem_foldl_retainOrAppend {α : Type} (f : List α → α → List α)
    (keeps : ∀ kept x a, a ∈ f kept x → a ∈ kept ∨ a = x) (a : α)
    (todo kept : List α) (member : a ∈ todo.foldl f kept) : a ∈ kept ∨ a ∈ todo := by
  induction todo generalizing kept with
  | nil => exact Or.inl member
  | cons x more ih =>
    rcases ih (f kept x) member with prior | later
    · rcases keeps kept x a prior with old | rfl
      · exact Or.inl old
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ later)

private theorem trimLimits_mem {s : GameState} {queue : List PendTrigger} {t : PendTrigger}
    (member : t ∈ s.trimLimits queue) : t ∈ queue := by
  unfold GameState.trimLimits at member
  have kept := mem_foldl_retainOrAppend _ (by
    intro kept x a keptMember
    dsimp only at keptMember
    split at keptMember
    · split at keptMember
      · simpa only [List.mem_append, List.mem_singleton] using keptMember
      · exact Or.inl keptMember
    · simpa only [List.mem_append, List.mem_singleton] using keptMember) t queue [] member
  exact kept.resolve_left List.not_mem_nil

private theorem detect_mem {s : GameState} {events : List Event} {t : PendTrigger}
    (member : t ∈ s.detect events) : t ∈ events.flatMap (detectOne s) ++ s.deathGroupWatchers events := by
  let candidates : List PendTrigger := (events.flatMap (detectOne s) ++ s.deathGroupWatchers events ++ []).filter
    (fun t => !s.departures.seats.contains t.controller)
  let active := s.active.getD ⟨0⟩
  let seatOrder (group : List PendTrigger) :=
    if s.config.mode.isTeamDuel then
      (s.triggerSeatOrder events).flatMap (fun p => group.filter (fun t => t.controller == p))
    else group.filter (fun t => t.controller == active) ++ group.filter (fun t => t.controller != active)
  have seatMem (group : List PendTrigger) (seated : t ∈ seatOrder group) : t ∈ group := by
    unfold seatOrder at seated
    split at seated
    · obtain ⟨_, _, selected⟩ := List.mem_flatMap.mp seated
      exact (List.mem_filter.mp selected).1
    · rcases List.mem_append.mp seated with first | later
      · exact (List.mem_filter.mp first).1
      · exact (List.mem_filter.mp later).1
  let parts := (s.trimLimits candidates).partition (·.beforeStandardMove)
  change t ∈ seatOrder parts.1 ++ seatOrder parts.2 at member
  have trimmed : t ∈ s.trimLimits candidates := by
    rcases List.mem_append.mp member with first | later
    · exact List.mem_partition.mpr (Or.inl (seatMem _ first))
    · exact List.mem_partition.mpr (Or.inr (seatMem _ later))
  simpa only [List.append_nil] using (List.mem_filter.mp (trimLimits_mem trimmed)).1

private theorem mightyEvents_deathGroupWatchers (before after : GameState) :
    after.deathGroupWatchers (before.mightyEvents after) = [] := by
  have empty : (before.mightyEvents after).filterMap (fun
      | .died object controller => some (object, controller)
      | _ => none) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e member
    rcases mightyEvents_cases member with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
  unfold GameState.deathGroupWatchers
  dsimp only
  rw (config := { transparency := .all }) [empty]
  rfl

private theorem mightTriggers_queued {s : GameState} {id : ObjId} {event : TriggerEvent}
    {t : PendTrigger} (threshold : event.isMightThreshold = true)
    (member : t ∈ s.mightTriggers id event) : QueuedMightAbility s.cards t := by
  unfold GameState.mightTriggers at member
  split at member
  · split at member
    · rcases List.mem_append.mp member with own | watched
      · exact triggersOfMatching_queued (matchesEvent := (· == event))
          (fun _ h => (beq_iff_eq.mp h) ▸ threshold) own
      · obtain ⟨_, _, watcher⟩ := List.mem_flatMap.mp watched
        exact watchersAt_queued threshold watcher
    · simp at member
  · simp at member

/-- The real detector cannot schedule an immediate Add from a Might crossing in a checked database. -/
theorem detect_mightyEvents_noImmediateAdd {before after : GameState} {t : PendTrigger}
    (database : after.cards.mightTriggersAreOrdinary)
    (member : t ∈ after.detect (before.mightyEvents after)) : t.immediateAddFrame after = none := by
  have candidate := detect_mem member
  rw [mightyEvents_deathGroupWatchers before after, List.append_nil] at candidate
  obtain ⟨event, found, queued⟩ := List.mem_flatMap.mp candidate
  apply queuedMight_immediate_none database
  rcases mightyEvents_cases found with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> exact mightTriggers_queued rfl queued

private theorem insertDetectedTriggers_ordinary (s : GameState) (queue : List PendTrigger)
    (rest : List Frame) (ordinary : ∀ t ∈ queue, t.immediateAddFrame s = none) :
    insertDetectedTriggers s queue rest = if queue.isEmpty then rest else insertTriggers queue rest := by
  have arrivals : queue.map (fun t => (t, t.immediateAddFrame s)) =
      queue.map (fun t => (t, (none : Option Frame))) := by
    apply List.map_congr_left
    intro t member
    rw [ordinary t member]
  unfold insertDetectedTriggers
  rw [arrivals]
  simp [List.filterMap_map, Function.comp_def]

/-- In a checked database, observing Might crossings uses the ordinary trigger stack insertion.
Existing work stays on the stack and no immediate Add frames are created by the observation. -/
theorem withMightyEvents_ordinary (before after : GameState)
    (database : after.cards.mightTriggersAreOrdinary) :
    let detected := after.detect (before.mightyEvents after)
    after.withTriggers (before.mightyEvents after) =
      if after.phase != .setup && after.pending.all (fun f => !f.isSetup) && !detected.isEmpty
      then { after with pending := insertTriggers detected after.pending } else after := by
  rw [withMightyEvents]
  dsimp only
  rw [insertDetectedTriggers_ordinary after _ after.pending
    (fun _ member => detect_mightyEvents_noImmediateAdd database member)]
  split <;> rename_i observe
  · simp only [Bool.and_eq_true] at observe
    have nonempty : (after.detect (before.mightyEvents after)).isEmpty = false := by
      cases empty : (after.detect (before.mightyEvents after)).isEmpty
      · rfl
      · rw [empty] at observe
        exact False.elim (Bool.noConfusion observe.2)
    simp only [nonempty, Bool.false_eq_true, ↓reduceIte]
  · rfl

/-- Any new work observed while finalizing an ordinary trigger uses the ordinary trigger queue. -/
theorem workStep_triggers_mightOrdinary (s : GameState) (wf : s.WF) (queue : List PendTrigger)
    (rest : List Frame) (pending : s.pending = .triggers queue :: rest)
    (database : s.cards.mightTriggersAreOrdinary) :
    let outcome := triggersStep s queue rest
    let next := { outcome.1 with pending := outcome.2 ++ rest }
    let detected := next.detect (s.mightyEvents next)
    workStep s = some (if next.phase != .setup && next.pending.all (fun f => !f.isSetup) &&
      !detected.isEmpty then { next with pending := insertTriggers detected next.pending }
      else next, ([] : List Event)) := by
  let outcome := triggersStep s queue rest
  let next := { outcome.1 with pending := outcome.2 ++ rest }
  have same : next.cards = s.cards := by
    have metadata := (triggersStep_spec s queue rest).1.same
    unfold SameMeta at metadata
    have projected := congrArg GameState.cards metadata
    exact projected
  have nextDatabase : next.cards.mightTriggersAreOrdinary := same ▸ database
  rw [workStep_triggers_observed s wf queue rest pending]
  have before := withMightyEvents s next
  have after := withMightyEvents_ordinary s next nextDatabase
  exact congrArg (fun state => some (state, [])) (before.symm.trans after)

private theorem expiration_noExhaustion (s : GameState) (rest : List Frame) :
    let next := { s.mapObjects endTurnObj with pending := rest, pools := {}, turnFx := [] }
    s.exhaustionEvents next none = [] := by
  intro next
  have empty : ((s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))).filter
      (fun id => (s.obj? id).any (fun o => !o.exhausted) && (next.obj? id).any (·.exhausted))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro id _
    have lookup : next.obj? id = (s.obj? id).map endTurnObj := GameState.obj?_mapObjects ..
    rw [lookup]
    cases obj : s.obj? id with
    | none => decide
    | some o => simp [endTurnObj, healObj]
  unfold GameState.exhaustionEvents
  dsimp only
  rw [empty]
  rfl

/-- Expiration can add ordinary Might triggers, while the reset and its observation add no
immediate Add work. The theorem follows the actual work step and its scheduled continuation. -/
theorem workStep_expireTurn_mightOrdinary (s : GameState) (rest : List Frame)
    (pending : s.pending = .expireTurn :: rest) (database : s.cards.mightTriggersAreOrdinary) :
    let next := { s.mapObjects endTurnObj with
      pending := expirationFrames s ++ rest, pools := {}, turnFx := [] }
    let detected := next.detect (s.mightyEvents next)
    workStep s = some (if next.phase != .setup && next.pending.all (fun f => !f.isSetup) &&
      !detected.isEmpty then { next with pending := insertTriggers detected next.pending }
      else next, ([] : List Event)) := by
  let next := { s.mapObjects endTurnObj with
    pending := expirationFrames s ++ rest, pools := {}, turnFx := [] }
  have raw : microStep0 s = some (next, []) := by simp only [microStep0, pending, next]
  have transitions : s.workTransitionEvents next = s.mightyEvents next := by
    unfold GameState.workTransitionEvents
    rw [pending]
    change s.exhaustionEvents next none ++ s.mightyEvents next ++ [] ++ [] = _
    rw [expiration_noExhaustion s (expirationFrames s ++ rest), List.nil_append, List.append_nil,
      List.append_nil]
  simp only [workStep, pending, microStep, raw, Option.map_some, transitions, List.nil_append]
  rw [withMightyEvents_ordinary s next database]

end Riftbound

end
