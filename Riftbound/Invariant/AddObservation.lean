module

public import Riftbound.Invariant.MightValue

/-!
# Observer stability for immediate Adds

A resource-only Add preserves the inputs to Might, and recording its ability use leaves
gameplay reads intact. Neither change exhausts objects. Skipped instructions emit a diagnostic
event that does not schedule any more work.
-/

@[expose] public section

namespace Riftbound

private theorem noteUse_objects (s : GameState) (id : ObjId) (i : Nat) (copy : Option Timestamp) :
    ∀ query, ((s.modObj id (fun o => o.noteAbilityUse i copy)).obj? query).map eraseTriggerBookkeeping =
      (s.obj? query).map eraseTriggerBookkeeping := by
  intro query
  rw [GameState.obj?_modObj]
  split
  · rename_i eq
    have sameId : id = query := congrArg ObjId.mk eq
    subst query
    cases s.obj? id <;> rfl
  · rfl

private theorem sameBookkeeping_cardDef {s t : GameState} (cards : t.cards = s.cards)
    (same : ∀ id, (t.obj? id).map eraseTriggerBookkeeping = (s.obj? id).map eraseTriggerBookkeeping) :
    t.cardDef? = s.cardDef? := by
  have active : t.attachmentCopyActive = s.attachmentCopyActive := by
    funext unit copy
    exact eraseTriggerBookkeeping_read (same copy.gear)
      (fun opt => opt.any (fun o => o.attached == some unit && o.attachmentCopyStamp == some copy.stamp))
      (by intro o; cases o <;> rfl)
  funext unit
  unfold GameState.cardDef? GameState.attachmentCopyOf
  rw [cards, active]
  let read (o : Object) : Option CardDef := do
    let key ← ((o.attachmentCopies.find? (s.attachmentCopyActive unit)).map (·.card)) <|> o.kind.cardId?
    let defn ← s.cards.find? key
    return (o.unitGearEffects.head?.map Prod.snd).elim defn defn.withUnitGearMight
  change (t.obj? unit).bind read = (s.obj? unit).bind read
  exact eraseTriggerBookkeeping_read (same unit) (·.bind read) (by intro o; cases o <;> rfl)

private theorem sameBookkeeping_attachmentText {s t : GameState} (cards : t.cards = s.cards)
    (same : ∀ id, (t.obj? id).map eraseTriggerBookkeeping = (s.obj? id).map eraseTriggerBookkeeping) :
    ∀ id, t.attachmentTextDefs id = s.attachmentTextDefs id := by
  have active : t.attachmentTextActive = s.attachmentTextActive := by
    funext unit copy
    exact eraseTriggerBookkeeping_read (same copy.gear)
      (fun opt => opt.any (fun o => o.attached == some unit && o.attachmentTextStamp == some copy.stamp))
      (by intro o; cases o <;> rfl)
  intro id
  unfold GameState.attachmentTextDefs GameState.activeAttachmentText
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, active, cards]
  have copies := eraseTriggerBookkeeping_read (same id) (·.map Object.attachmentTextCopies)
    (by intro o; cases o <;> rfl)
  rw [copies]

/-- Recording a triggered ability use preserves the reads that contribute to Might. -/
theorem noteAbilityUse_sameMightReads (s : GameState) (source : ObjId) (idx : Nat)
    (copy : Option Timestamp) : SameMightReads s (s.modObj source (fun o => o.noteAbilityUse idx copy)) := by
  let t := s.modObj source (fun o => o.noteAbilityUse idx copy)
  have same := noteUse_objects s source idx copy
  have defs : t.cardDef? = s.cardDef? := sameBookkeeping_cardDef rfl same
  have text : ∀ id, t.attachmentTextDefs id = s.attachmentTextDefs id :=
    sameBookkeeping_attachmentText rfl same
  have reading {α : Type} (id : ObjId) (read : Option Object → α)
      (kept : ∀ o, read (o.map eraseTriggerBookkeeping) = read o) :
      read (t.obj? id) = read (s.obj? id) := eraseTriggerBookkeeping_read (same id) read kept
  have units : t.unitsAtOf = s.unitsAtOf := by
    funext field player
    unfold GameState.unitsAtOf
    have zones : t.zone .battlefieldZone = s.zone .battlefieldZone := rfl
    rw [zones, defs]
    apply List.filter_congr
    intro id _
    exact reading id _ (by intro o; cases o <;> rfl)
  have combatNow : t.combatNow = s.combatNow := by
    unfold GameState.combatNow
    have recorded : t.combat = s.combat := rfl
    have pending : t.pending = s.pending := rfl
    rw [recorded, pending]
    congr 1
    funext _
    apply congrArg (List.findSome? · s.pending)
    funext frame
    cases frame <;> try rfl
    all_goals
      have players : t.players = s.players := rfl
      have seat : t.active = s.active := rfl
      have cfg : t.config = s.config := rfl
      have contested (field : ObjId) := reading field (·.bind (·.contested)) (by intro o; cases o <;> rfl)
      simp only [units, players, seat, cfg, contested]
  have base : t.mightOf = s.mightOf := by
    funext id
    unfold GameState.mightOf
    rw [defs]
    have objects := same id
    generalize t.obj? id = after at objects ⊢
    generalize s.obj? id = before at objects ⊢
    apply eraseTriggerBookkeeping_read objects
    intro o
    cases o <;> rfl
  have gear : t.equipBonus = s.equipBonus := by
    funext id
    unfold GameState.equipBonus
    have board : t.inPlay = s.inPlay := rfl
    have turn : t.turn = s.turn := rfl
    have xp : t.xpOf = s.xpOf := rfl
    simp only [defs, board, turn, xp]
    apply congrArg List.sum
    apply filterMap_congr_mem
    intro g _
    have objects := same g
    generalize t.obj? g = after at objects ⊢
    generalize s.obj? g = before at objects ⊢
    apply eraseTriggerBookkeeping_read objects
    intro o
    cases o <;> cases s.cardDef? g <;> rfl
  have buff : t.buffBonus = s.buffBonus := by
    funext id
    unfold GameState.buffBonus
    have eqEffects (p : PlayerId) :
        ((t.fxOf p).filter (· == .buffsExtraMight)) = ((s.fxOf p).filter (· == .buffsExtraMight)) := by
      rw [buffEffects, buffEffects]
      rfl
    simp only [eqEffects]
    have objects := same id
    generalize t.obj? id = after at objects ⊢
    generalize s.obj? id = before at objects ⊢
    apply eraseTriggerBookkeeping_read objects
    intro o
    cases o <;> rfl
  exact ⟨rfl, fun _ _ => rfl, fun id _ => same id, defs, text, base, gear, buff, rfl,
    combatNow, units, rfl, rfl, (fun _ => rfl), rfl, rfl, rfl, (fun _ _ _ _ => rfl)⟩


/-- Running an instruction that preserves Might reads and readiness contributes no transition
events. This includes downward Might notices made on behalf of the effect's controller. -/
theorem workTransitionEvents_run_quiet {s t : GameState} {p : PlayerId}
    {src : ObjId} {env : Env} {program : EffectList} {rest : List Frame}
    (wf : s.WF) (cards : MightRead.database s.cards) (reads : SameMightReads s t)
    (pending : s.pending = .run p src env program :: rest) :
    s.workTransitionEvents t = [] := by
  have mighty : s.mightyEvents t = [] :=
    mightyEvents_eq_nil_of_mightNow (fun _ member => (reads.mightNow_eq wf cards (old_inPlay wf member)).symm)
  have reduction : s.mightReductionEvents t (some p) = [] := by
    simp only [GameState.mightReductionEvents]
    split
    · apply List.filterMap_eq_nil_iff.mpr
      intro id member
      have old := old_inPlay wf (reads.inPlay ▸ member)
      split
      · rfl
      · rw [reads.mightNow_eq wf cards old]
        cases s.mightNow id <;> simp
    · rfl
  have exhaustion : s.exhaustionEvents t (some p) = [] := by
    have empty : ((s.inPlay ++ s.players.flatMap (fun q => s.zone (.player q .legendZone))).filter
        (fun id => (s.obj? id).any (fun o => !o.exhausted) && (t.obj? id).any (·.exhausted))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro id member
      have old : id.n < s.nextId := by
        rcases List.mem_append.mp member with board | legend
        · exact old_inPlay wf board
        · obtain ⟨q, _, inLegend⟩ := List.mem_flatMap.mp legend
          exact old_of_zone wf inLegend
      rw [reads.readObj old (fun o => o.any (·.exhausted)) (by intro o; cases o <;> rfl)]
      cases s.obj? id <;> simp
    unfold GameState.exhaustionEvents
    dsimp only
    rw [empty]
    rfl
  simp only [GameState.workTransitionEvents, pending, mighty, reduction, exhaustion, List.nil_append]

private theorem dropPowerFx_filter_of_disjoint {predicate : TurnFx → Bool} {turn : Nat}
    {p : PlayerId} {restriction : TurnEffect}
    (disjoint : ∀ f, f.kind == restriction → predicate f = false) (n : Nat) (notes : List TurnFx) :
    (dropPowerFx turn p restriction n notes).filter predicate = notes.filter predicate := by
  induction notes generalizing n with
  | nil => cases n <;> rfl
  | cons first rest ih =>
    cases n with
    | zero => rfl
    | succ n =>
      unfold dropPowerFx
      split
      · rename_i removed
        have no := disjoint first ((Bool.and_eq_true _ _).mp removed).2
        simp only [List.filter_cons, no, Bool.false_eq_true, ↓reduceIte, ih]
      · simp only [List.filter_cons, ih]

private theorem trimGear_read {s : GameState} {p : PlayerId} {predicate : TurnFx → Bool}
    (ignoresGear : ∀ f, f.kind == .gearMana → predicate f = false) :
    (s.trimGear p).turnFx.filter predicate = s.turnFx.filter predicate := by
  unfold GameState.trimGear dropGearFx
  exact dropPowerFx_filter_of_disjoint ignoresGear _ _

private theorem setPool_spent {s : GameState} {p : PlayerId} {pool : RunePool}
    (unchanged : pool.powerSpent = (s.poolOf p).powerSpent) :
    ∀ q, ((s.setPool p pool).poolOf q).powerSpent = (s.poolOf q).powerSpent := by
  intro q
  by_cases eq : q = p
  · subst q
    rwa [GameState.poolOf_setPool_self]
  · rw [GameState.poolOf_setPool_ne _ eq]

private theorem poolsMap_spent {f : RunePool → RunePool}
    (unchanged : ∀ pool, (f pool).powerSpent = pool.powerSpent) (s : GameState) (players : List PlayerId) :
    ∀ p, ((poolsMap f s players).poolOf p).powerSpent = (s.poolOf p).powerSpent := by
  induction players generalizing s with
  | nil => intro p; rfl
  | cons p rest ih =>
    intro q
    rw [poolsMap, ih, setPool_spent (unchanged (s.poolOf p))]

private theorem poolsAddAny_spent (n : Nat) (s : GameState) (players : List PlayerId) :
    ∀ p, ((poolsAddAny n s players).poolOf p).powerSpent = (s.poolOf p).powerSpent := by
  induction players generalizing s with
  | nil => intro p; rfl
  | cons p rest ih =>
    intro q
    rw [poolsAddAny, ih, setPool_spent (pool := ((s.trimGear p).poolOf p).addAny n) rfl]
    rfl

private theorem poolsAddAny_read (n : Nat) (s : GameState) (players : List PlayerId)
    {predicate : TurnFx → Bool} (ignoresGear : ∀ f, f.kind == .gearMana → predicate f = false) :
    (poolsAddAny n s players).turnFx.filter predicate = s.turnFx.filter predicate := by
  induction players generalizing s with
  | nil => rfl
  | cons p rest ih =>
    rw [poolsAddAny, ih]
    exact trimGear_read ignoresGear

private theorem poolsMap_onlyPools (f : RunePool → RunePool) (s : GameState) (players : List PlayerId) :
    poolsMap f s players = { s with pools := (poolsMap f s players).pools } := by
  induction players generalizing s with
  | nil => rfl
  | cons p rest ih =>
    rw [poolsMap]
    exact ih (s.setPool p (f (s.poolOf p)))

private theorem poolsAddAny_onlyPoolsAndFx (k : Nat) (s : GameState) (players : List PlayerId) :
    poolsAddAny k s players =
      { s with pools := (poolsAddAny k s players).pools, turnFx := (poolsAddAny k s players).turnFx } := by
  induction players generalizing s with
  | nil => rfl
  | cons p rest ih =>
    rw [poolsAddAny]
    exact ih ((s.trimGear p).setPool p (((s.trimGear p).poolOf p).addAny k))

private theorem poolAndFactsReads (s : GameState) (pools : Std.ExtTreeMap Nat RunePool)
    (notes : List TurnFx)
    (turnFacts : notes.filter (fun note => note.kind != .gearMana) =
      s.turnFx.filter (fun note => note.kind != .gearMana))
    (powerSpent : ∀ p, (pools.getD p.n RunePool.empty).powerSpent = (s.poolOf p).powerSpent)
    (buffFacts : ∀ p, notes.filter (fun f => (f.kind == .buffsExtraMight) && (f.turn == s.turn && f.who == p)) =
      s.turnFx.filter (fun f => (f.kind == .buffsExtraMight) && (f.turn == s.turn && f.who == p))) :
    SameMightReads s { s with pools, turnFx := notes } := by
  let t := { s with pools, turnFx := notes }
  have buffs (p : PlayerId) :
      (t.fxOf p).filter (· == .buffsExtraMight) = (s.fxOf p).filter (· == .buffsExtraMight) := by
    rw [buffEffects, buffEffects]
    exact congrArg (List.map TurnFx.kind) (buffFacts p)
  have base : t.buffBonus = s.buffBonus := by
    funext id
    unfold GameState.buffBonus
    have objects : t.obj? id = s.obj? id := rfl
    rw [objects]
    cases s.obj? id <;> simp only [buffs]
  exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ => rfl,
    rfl, rfl, base, rfl, rfl, rfl, rfl, turnFacts, powerSpent, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

private theorem poolsMap_reads {f : RunePool → RunePool} (s : GameState) (players : List PlayerId)
    (unchanged : ∀ pool, (f pool).powerSpent = pool.powerSpent) :
    SameMightReads s (poolsMap f s players) ∧ (poolsMap f s players).cards = s.cards ∧
      (poolsMap f s players).objects = s.objects ∧ (poolsMap f s players).zones = s.zones := by
  have shape := poolsMap_onlyPools f s players
  have spent := poolsMap_spent unchanged s players
  have projected : ∀ p, ((poolsMap f s players).pools.getD p.n RunePool.empty).powerSpent =
      (s.poolOf p).powerSpent := spent
  have reads := poolAndFactsReads s (poolsMap f s players).pools s.turnFx rfl projected (fun _ => rfl)
  have cards := congrArg GameState.cards shape
  have objects := congrArg GameState.objects shape
  have zones := congrArg GameState.zones shape
  exact ⟨shape.symm ▸ reads, cards, objects, zones⟩

private theorem poolsAddAny_reads (k : Nat) (s : GameState) (players : List PlayerId) :
    SameMightReads s (poolsAddAny k s players) ∧ (poolsAddAny k s players).cards = s.cards ∧
      (poolsAddAny k s players).objects = s.objects ∧ (poolsAddAny k s players).zones = s.zones := by
  let t := poolsAddAny k s players
  have shape := poolsAddAny_onlyPoolsAndFx k s players
  have facts : t.turnFx.filter (fun f => f.kind != .gearMana) = s.turnFx.filter (fun f => f.kind != .gearMana) :=
    poolsAddAny_read k s players (fun f gear => by simp [beq_iff_eq.mp gear])
  have buffs (p : PlayerId) :
      t.turnFx.filter (fun f => (f.kind == .buffsExtraMight) && (f.turn == s.turn && f.who == p)) =
      s.turnFx.filter (fun f => (f.kind == .buffsExtraMight) && (f.turn == s.turn && f.who == p)) :=
    poolsAddAny_read k s players (fun f gear => by simp [beq_iff_eq.mp gear])
  have reads := poolAndFactsReads s t.pools t.turnFx facts (poolsAddAny_spent k s players) buffs
  have cards := congrArg GameState.cards shape
  have objects := congrArg GameState.objects shape
  have zones := congrArg GameState.zones shape
  exact ⟨shape.symm ▸ reads, cards, objects, zones⟩

private theorem addOutcome_reads {s t : GameState} {events : List Event} {players : Option (List PlayerId)}
    {amount : Option Nat} (gain : Nat → List PlayerId → GameState)
    (preserved : ∀ count who, SameMightReads s (gain count who) ∧ (gain count who).cards = s.cards ∧
      (gain count who).objects = s.objects ∧ (gain count who).zones = s.zones)
    (run : players.bind (fun who => amount.map (fun count => (gain count who, ([] : List Event)))) =
      some (t, events)) : SameMightReads s t ∧ t.cards = s.cards ∧ t.objects = s.objects ∧ t.zones = s.zones ∧ events = [] := by
  obtain ⟨who, _, selected⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨count, _, equal⟩ := Option.map_eq_some_iff.mp selected
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  obtain ⟨reads, cards, objects, zones⟩ := preserved count who
  exact ⟨reads, cards, objects, zones, rfl⟩

/-- Successful resource-only Add primitives emit no rule events and keep the inputs to Might. -/
theorem applyPrim_add_geometry {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {pr : Prim}
    (accepts : (Effect.prim pr).isTriggerAdd = true) {t : GameState} {events : List Event}
    (applied : applyPrim s p src env pr = some (t, events)) :
    SameMightReads s t ∧ t.cards = s.cards ∧ t.objects = s.objects ∧ t.zones = s.zones ∧ events = [] := by
  cases pr <;> try (simp [Effect.isTriggerAdd] at accepts; done)
  case addEnergy who n only =>
    cases who <;> cases only <;> simp [Effect.isTriggerAdd] at accepts
    exact addOutcome_reads (fun k ps => poolsMap (·.addEnergy k) s ps)
      (fun _ ps => poolsMap_reads s ps (fun _ => rfl)) applied
  case addUnitEnergy who n =>
    cases who <;> simp [Effect.isTriggerAdd] at accepts
    exact addOutcome_reads (fun k ps => poolsMap (·.addUnitEnergy k) s ps)
      (fun _ ps => poolsMap_reads s ps (fun _ => rfl)) applied
  case addSpellEnergy who n =>
    cases who <;> simp [Effect.isTriggerAdd] at accepts
    exact addOutcome_reads (fun k ps => poolsMap (·.addSpellEnergy k) s ps)
      (fun _ ps => poolsMap_reads s ps (fun _ => rfl)) applied
  case addPower who n domain only =>
    cases who <;> cases only <;> simp [Effect.isTriggerAdd] at accepts
    cases domain with
    | none => exact addOutcome_reads (fun k ps => poolsAddAny k s ps) (fun k ps => poolsAddAny_reads k s ps) applied
    | some d =>
      exact addOutcome_reads (fun k ps => poolsMap (·.addPower d k) s ps)
        (fun _ ps => poolsMap_reads s ps (fun pool => by cases d <;> rfl)) applied


/-- Successful Add primitives preserve Might reads and card definitions and emit no rule events. -/
theorem applyPrim_add_reads {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {pr : Prim}
    (accepts : (Effect.prim pr).isTriggerAdd = true) {t : GameState} {events : List Event}
    (applied : applyPrim s p src env pr = some (t, events)) :
    SameMightReads s t ∧ t.cards = s.cards ∧ events = [] := by
  obtain ⟨reads, cards, _, _, noEvents⟩ := applyPrim_add_geometry accepts applied
  exact ⟨reads, cards, noEvents⟩

/-- An instruction's skipped notice has no effects on the observer. -/
theorem withTriggers_skipped (s : GameState) (source : ObjId) :
    s.withTriggers [.skipped source] = s := by
  have empty (order : List PlayerId) : order.flatMap (fun _ => ([] : List PendTrigger)) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  have noScore : s.eventWinner [.skipped source] = none := by
    rw [eventWinner_of_noWin s _ rfl]
    cases hc : s.clock <;> simp [GameState.suddenDeathScorer, hc]
  have noDelay : s.delayedPlayTriggers [.skipped source] = [] := by
    unfold GameState.delayedPlayTriggers
    split
    · rfl
    · apply List.flatMap_eq_nil_iff.mpr
      intro note _
      split
      · simp [GameState.matchesDelayedPlay]
      · rfl
  have noFacts : s.recordTurnEvents [.skipped source] = s := by
    simp [GameState.recordTurnEvents, GameState.recordPlayEvent, GameState.recordTurnEvent]
  unfold GameState.withTriggers
  rw [noFacts, noScore]
  dsimp only
  split
  · simp [GameState.detect, GameState.deathGroupWatchers, GameState.stunGroupWatchers, GameState.trimLimits,
      GameState.firstCardTriggers, GameState.firstSpellFieldTriggers, detectOne, empty, noDelay,
      GameState.delayedDamageTriggers, GameState.damageTriggerSubject]
  · rfl

end Riftbound

end
