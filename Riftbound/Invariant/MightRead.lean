module

public import Riftbound.Invariant.MightObservation
public import Riftbound.Invariant.MightReadSyntax
import all Init.Data.List.Control

/-!
# Invariance of the reads used by Might-related passives
-/

@[expose] public section

namespace Riftbound

/-- An identifier in an occupied zone is older than the next identifier. -/
theorem old_of_zone {s : GameState} (wf : s.WF) {z : Zone} {id : ObjId}
    (member : id ∈ s.zone z) : id.n < s.nextId :=
  wf.lt_nextId id (GameState.mem_zoneIds (GameState.zone_valid_of_mem wf member) member)

/-- Bookkeeping for Gear-only funding and linked deaths does not affect earlier Power spending. -/
private theorem spendingBeforeMain_filter (notes : List TurnFx) (p : PlayerId) (turn : Nat) :
    ((notes.filter (fun note => note.kind.isMightReadFact)).filterMap (·.spendingBeforeMain p turn)) =
      notes.filterMap (·.spendingBeforeMain p turn) := by
  rw [List.filterMap_filter]
  apply congrArg (List.filterMap · notes)
  funext note
  cases kind : note.kind <;> simp [TurnEffect.isMightReadFact, TurnFx.spendingBeforeMain, kind]

/-- Every object on the Board has an existing identifier. -/
theorem old_inPlay {s : GameState} (wf : s.WF) {id : ObjId}
    (member : id ∈ s.inPlay) : id.n < s.nextId := by
  simp only [GameState.inPlay, List.mem_append, List.mem_flatMap] at member
  rcases member with ⟨_, _, base⟩ | field
  · exact old_of_zone wf base
  · exact old_of_zone wf field

private theorem find_congr_mem {α : Type} (items : List α) (f g : α → Bool)
    (same : ∀ i ∈ items, f i = g i) : items.find? f = items.find? g := by
  induction items with
  | nil => rfl
  | cons first later ih =>
    simp only [List.find?_cons, same _ List.mem_cons_self, ih (fun _ h => same _ (List.mem_cons_of_mem _ h))]

private theorem eraseReadPair {α : Type} {a b c d : Option Object}
    (first : a.map eraseTriggerBookkeeping = b.map eraseTriggerBookkeeping)
    (second : c.map eraseTriggerBookkeeping = d.map eraseTriggerBookkeeping)
    (read : Option Object → Option Object → α)
    (stable : ∀ x y, read (x.map eraseTriggerBookkeeping) (y.map eraseTriggerBookkeeping) = read x y) :
    read a c = read b d := by
  rw [← stable a c, ← stable b d, first, second]

/-- A declared definition inherits the ability check from the database. -/
theorem declared_mightReads {db : CardDB} {d : CardDef}
    (accepted : MightRead.database db) (declared : DeclaredDefinition db d) :
    d.allAbilities.all MightRead.ability = true := by
  obtain ⟨printed, found, shape, _⟩ := declared
  have check := List.all_eq_true.mp accepted printed (CardDB.find?_mem found)
  simp only [MightRead.card, Bool.and_eq_true] at check
  rcases shape with definition | definition
  · exact definition ▸ check.1.1
  · exact definition ▸ check.1.2

/-- The abilities of a live definition and its attached Effect Text inherit the Might read check. -/
theorem accepted_appendedAbilities {s : GameState} (accepted : MightRead.database s.cards)
    {source : ObjId} {d : CardDef} (found : s.cardDef? source = some d) :
    ∀ a ∈ s.appendedAbilities source d, MightRead.ability a = true := by
  intro a member
  rcases List.mem_append.mp member with own | attached
  · exact List.all_eq_true.mp (declared_mightReads accepted (declared_of_cardDef found)) a
      (List.mem_append_left _ own)
  · obtain ⟨⟨copy, stamp⟩, comesFrom, text⟩ := List.mem_flatMap.mp attached
    have available : a ∈ copy.allAbilities := by
      simp only [CardDef.textAbilities, List.mem_append] at text
      simp only [CardDef.allAbilities, CardDef.fullAbilities, CardDef.keywordAbilities, List.mem_append]
      rcases text with print | keyword
      · exact Or.inl (Or.inl print)
      · exact Or.inl (Or.inr (Or.inl (Or.inl keyword)))
    exact List.all_eq_true.mp (declared_mightReads accepted (declared_of_attachmentText comesFrom)) a available

namespace SameMightReads

variable {s t : GameState} (same : SameMightReads s t)
include same

/-- The contents of a player's zone are shared. -/
theorem playerZone (p : PlayerId) (kind : ZoneKind) :
    t.zone (.player p kind) = s.zone (.player p kind) :=
  same.zone _ (by intro eq; cases eq)

/-- The contents of the Battlefield Zone are shared. -/
theorem fieldZone : t.zone .battlefieldZone = s.zone .battlefieldZone :=
  same.zone _ (by decide)

/-- The games have the same players. -/
theorem players : t.players = s.players := by
  simp only [GameState.players, GameState.playerCount, same.config]

/-- The games have the same Board object identifiers. -/
theorem inPlay : t.inPlay = s.inPlay := by
  simp only [GameState.inPlay, same.players, same.playerZone, same.fieldZone]

private theorem hereOf (wf : s.WF) {self : ObjId} (old : self.n < s.nextId) :
    t.hereOf self = s.hereOf self := by
  have scored (p : PlayerId) :
      (s.zone .battlefieldZone).find? (fun b => (t.obj? b).any (·.scored.contains p)) =
      (s.zone .battlefieldZone).find? (fun b => (s.obj? b).any (·.scored.contains p)) := by
    apply find_congr_mem
    intro bf member
    exact same.readObj (old_of_zone wf member) (fun o => o.any (·.scored.contains p))
      (by intro o; cases o <;> rfl)
  unfold GameState.hereOf
  simp only [same.cardDef, same.fieldZone, scored]
  have lookup := same.objects self old
  generalize t.obj? self = after at lookup ⊢
  generalize s.obj? self = before at lookup ⊢
  apply eraseTriggerBookkeeping_read lookup
  intro o
  cases o <;> rfl

private theorem baseHere {self : ObjId} (old : self.n < s.nextId) :
    t.baseHere self = s.baseHere self := by
  unfold GameState.baseHere
  simp only [same.cardDef, same.playerZone]
  have lookup := same.objects self old
  generalize t.obj? self = after at lookup ⊢
  generalize s.obj? self = before at lookup ⊢
  apply eraseTriggerBookkeeping_read lookup
  intro o
  cases o <;> rfl

private theorem fieldOccupants (wf : s.WF) (bf : ObjId) :
    (s.zone .battlefieldZone).filter (fun id => id == bf || (t.obj? id).any (·.loc == some bf)) =
    (s.zone .battlefieldZone).filter (fun id => id == bf || (s.obj? id).any (·.loc == some bf)) := by
  apply List.filter_congr
  intro id member
  rw [same.readObj (old_of_zone wf member) (fun o => o.any (·.loc == some bf))
    (by intro o; cases o <;> rfl)]

private theorem baseOccupants (wf : s.WF) (p : PlayerId) :
    (s.players.flatMap (fun q => s.zone (.player q .base))).filter
        (fun id => (t.obj? id).any (·.controller == p)) =
    (s.players.flatMap (fun q => s.zone (.player q .base))).filter
        (fun id => (s.obj? id).any (·.controller == p)) := by
  apply List.filter_congr
  intro id member
  obtain ⟨_, _, inBase⟩ := List.mem_flatMap.mp member
  exact same.readObj (old_of_zone wf inBase) (fun o => o.any (·.controller == p))
    (by intro o; cases o <;> rfl)

private theorem placeObjs (wf : s.WF) {self : ObjId} (old : self.n < s.nextId)
    {place : Place} (supported : MightRead.place place = true) :
    t.placeObjs self place = s.placeObjs self place := by
  cases place <;> simp only [MightRead.place, Bool.false_eq_true] at supported
  case anywhere => exact congrArg some same.inPlay
  case inTrash => rfl
  case here =>
    simp only [GameState.placeObjs, same.hereOf wf old, same.baseHere old, same.fieldZone,
      same.players, same.playerZone, same.fieldOccupants wf, same.baseOccupants wf]
    split
    · rfl
    · split
      · have lookup := same.objects self old
        generalize t.obj? self = after at lookup ⊢
        generalize s.obj? self = before at lookup ⊢
        apply eraseTriggerBookkeeping_read lookup
        intro o
        cases o <;> rfl
      · rfl

private theorem gainedTags (wf : s.WF) {id : ObjId} (old : id.n < s.nextId) :
    t.gainedTags id = s.gainedTags id := by
  unfold GameState.gainedTags
  simp only [same.cardDef, same.inPlay]
  congr 1
  · exact same.readObj old (fun o => (o.map (fun x => x.tagsGained.map (fun n => (⟨n⟩ : Tag)))).getD [])
      (by intro o; cases o <;> rfl)
  · apply flatMap_congr_mem
    intro gear member
    have lookup := same.objects gear (old_inPlay wf member)
    generalize t.obj? gear = after at lookup ⊢
    generalize s.obj? gear = before at lookup ⊢
    apply eraseTriggerBookkeeping_read lookup
    intro o
    cases o <;> cases s.cardDef? gear <;> rfl

omit same in
private theorem placeObjects_old (wf : s.WF) {self : ObjId} {place : Place}
    (supported : MightRead.place place = true) {ids : List ObjId}
    (found : s.placeObjs self place = some ids) {id : ObjId} (member : id ∈ ids) : id.n < s.nextId := by
  cases place <;> simp only [MightRead.place, Bool.false_eq_true] at supported
  case anywhere =>
    change some s.inPlay = some ids at found
    obtain rfl := Option.some.inj found
    exact old_inPlay wf member
  case inTrash => contradiction
  case here =>
    simp only [GameState.placeObjs] at found
    split at found
    · obtain rfl := Option.some.inj found
      exact old_of_zone wf (List.mem_filter.mp member).1
    · split at found
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨_, _, inBase⟩ := List.mem_flatMap.mp (List.mem_filter.mp member).1
        exact old_of_zone wf inBase
      · contradiction

private theorem filter_eq (wf : s.WF) (env : Env) {self id : ObjId}
    (oldSelf : self.n < s.nextId) (old : id.n < s.nextId) (f : Filter) (supported : MightRead.filter f = true) :
    f.holds t self env id = f.holds s self env id := by
  cases f <;> try simp only [MightRead.filter, Bool.false_eq_true] at supported
  case either a b =>
    simp only [Bool.and_eq_true] at supported
    simp only [Filter.holds, filter_eq wf env oldSelf old a supported.1,
      filter_eq wf env oldSelf old b supported.2]
  case at_ sel =>
    cases sel <;> simp only [MightRead.filter, Bool.false_eq_true] at supported
    simp only [Filter.holds, same.cardDef, Option.bind_eq_bind, Option.bind_some]
    have lookup := same.objects id old
    have source := same.objects self oldSelf
    generalize t.obj? id = a at lookup ⊢
    generalize s.obj? id = b at lookup ⊢
    generalize t.obj? self = c at source ⊢
    generalize s.obj? self = d at source ⊢
    apply eraseReadPair lookup source
    intro x y
    cases x <;> cases y <;> rfl
  case tag key => simp only [Filter.holds, same.cardDef, same.gainedTags wf old]
  all_goals
    simp only [Filter.holds, same.cardDef, same.attachmentText, same.mightOf, same.equipBonus,
      same.buffBonus, same.combatNow, same.unitsAtOf, same.players, same.config, same.fieldZone]
  all_goals
    have lookup := same.objects id old
    generalize t.obj? id = after at lookup ⊢
    generalize s.obj? id = before at lookup ⊢
    apply eraseTriggerBookkeeping_read lookup
    intro o
    cases o <;> first | rfl | (cases s.combatNow <;> rfl)
termination_by structural f

private theorem filters_eq (wf : s.WF) (env : Env) {self id : ObjId}
    (oldSelf : self.n < s.nextId) (old : id.n < s.nextId) (fs : FilterList)
    (supported : MightRead.filters fs = true) : fs.holds t self env id = fs.holds s self env id := by
  cases fs with
  | nil => rfl
  | cons f rest =>
    simp only [MightRead.filters, Bool.and_eq_true] at supported
    simp only [FilterList.holds, same.filter_eq wf env oldSelf old f supported.1,
      filters_eq wf env oldSelf old rest supported.2]
termination_by structural fs

private theorem matchesOne_eq (wf : s.WF) (p : PlayerId) (env : Env) (side : Side)
    {self id : ObjId} (oldSelf : self.n < s.nextId) (old : id.n < s.nextId) (fs : FilterList)
    (supported : MightRead.filters fs = true) :
    t.matchesOne p self env side fs id = s.matchesOne p self env side fs id := by
  simp only [GameState.matchesOne, same.config, same.filters_eq wf env oldSelf old fs supported]
  have lookup := same.objects id old
  generalize t.obj? id = after at lookup ⊢
  generalize s.obj? id = before at lookup ⊢
  apply eraseTriggerBookkeeping_read lookup
  intro o
  cases o <;> cases side <;> rfl

private theorem keepMatching_eq (wf : s.WF) (p : PlayerId) (env : Env) (side : Side)
    {self : ObjId} (oldSelf : self.n < s.nextId) (fs : FilterList) (supported : MightRead.filters fs = true)
    (ids : List ObjId) (old : ∀ id ∈ ids, id.n < s.nextId) :
    t.keepMatching p self env side fs ids = s.keepMatching p self env side fs ids := by
  induction ids with
  | nil => rfl
  | cons id rest ih =>
    simp only [GameState.keepMatching, same.matchesOne_eq wf p env side oldSelf
      (old id List.mem_cons_self) fs supported, ih (fun i h => old i (List.mem_cons_of_mem _ h))]

/-- For selectors used in Might-related expressions, both states return the same objects. -/
theorem selector_eq (wf : s.WF) (p : PlayerId) (env : Env) {self : ObjId} (oldSelf : self.n < s.nextId)
    (sel : Selector) (supported : MightRead.selector sel = true) :
    sel.eval t p self env = sel.eval s p self env := by
  cases sel <;> try simp only [MightRead.selector, Bool.false_eq_true] at supported
  case self => rfl
  case pick quantity side place fs =>
    cases quantity <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at supported
    case all =>
      simp only [Selector.eval, GameState.candidates, same.placeObjs wf oldSelf supported.1]
      cases positions : s.placeObjs self place with
      | none => rfl
      | some ids =>
        exact same.keepMatching_eq wf p env side oldSelf fs supported.2 ids
          (fun _ member => placeObjects_old wf supported.1 positions member)

omit same in
private theorem selector_old (wf : s.WF) (p : PlayerId) (env : Env) {self : ObjId}
    (oldSelf : self.n < s.nextId) (sel : Selector) (supported : MightRead.selector sel = true)
    {ids : List ObjId} (found : sel.eval s p self env = some ids) {id : ObjId} (member : id ∈ ids) :
    id.n < s.nextId := by
  cases sel <;> try simp only [MightRead.selector, Bool.false_eq_true] at supported
  case self =>
    change some [self] = some ids at found
    obtain rfl := Option.some.inj found
    obtain rfl := List.mem_singleton.mp member
    exact oldSelf
  case pick quantity side place fs =>
    cases quantity <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at supported
    case all =>
      simp only [Selector.eval, GameState.candidates, Option.bind_eq_bind] at found
      obtain ⟨positions, available, chosen⟩ := Option.bind_eq_some_iff.mp found
      exact placeObjects_old wf supported.1 available (s.mem_keepMatching chosen _ member)

omit same in
private theorem filterM_eq_on {α : Type} (items : List α) (a b : α → Option Bool)
    (agree : ∀ x ∈ items, a x = b x) : items.filterM a = items.filterM b := by
  have aux (acc) : List.filterAuxM a items acc = List.filterAuxM b items acc := by
    induction items generalizing acc with
    | nil => rfl
    | cons i rest ih =>
      have later := ih (fun j h => agree j (List.mem_cons_of_mem _ h))
      simp only [List.filterAuxM, agree i List.mem_cons_self, later]
  simp only [List.filterM, aux]

omit same in
private theorem mapM_eq_on {α β : Type} (items : List α) (a b : α → Option β)
    (agree : ∀ x ∈ items, a x = b x) : items.mapM a = items.mapM b := by
  induction items with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.mapM_cons, agree i List.mem_cons_self, ih (fun j h => agree j (List.mem_cons_of_mem _ h))]

omit same in
private theorem all_eq_on {α : Type} (items : List α) (a b : α → Bool)
    (agree : ∀ x ∈ items, a x = b x) : items.all a = items.all b := by
  induction items with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.all_cons, agree i List.mem_cons_self, ih (fun j h => agree j (List.mem_cons_of_mem _ h))]

private theorem count_eq (wf : s.WF) (p : PlayerId) (env : Env) {self : ObjId} (oldSelf : self.n < s.nextId)
    (sel : Selector) (supported : MightRead.selector sel = true) :
    (Amount.count sel).evalS0 t p self env = (Amount.count sel).evalS0 s p self env := by
  have selection := same.selector_eq wf p env oldSelf sel supported
  cases sel <;> try simp only [MightRead.selector, Bool.false_eq_true] at supported
  case self => rfl
  case pick quantity side place fs =>
    cases quantity <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at supported
    case all =>
      simp only [Amount.evalS0, same.players, same.config]
      cases place.zoneKind? with
      | none => exact congrArg (Option.map List.length) selection
      | some kind =>
        have everySeat (q : PlayerId) :
            (t.zone (.player q kind)).filterM (fun id => fs.holds t self env id) =
            (s.zone (.player q kind)).filterM (fun id => fs.holds s self env id) := by
          rw [same.playerZone]
          apply filterM_eq_on
          intro id member
          exact same.filters_eq wf env oldSelf (old_of_zone wf member) fs supported.2
        simp only [everySeat]

/-- Supported Might amounts have the same value, including counts in the Trash. -/
theorem amount_eq (wf : s.WF) (p : PlayerId) (env : Env) {self : ObjId} (oldSelf : self.n < s.nextId)
    (amount : Amount) (supported : MightRead.amount amount = true) :
    amount.evalS0 t p self env = amount.evalS0 s p self env := by
  cases amount <;> try simp only [MightRead.amount, Bool.false_eq_true] at supported
  case const => rfl
  case count sel => exact same.count_eq wf p env oldSelf sel supported
  case mul a b =>
    simp only [Bool.and_eq_true] at supported
    simp only [Amount.evalS0, amount_eq wf p env oldSelf a supported.1, amount_eq wf p env oldSelf b supported.2]
  case empowerCount =>
    simp only [Amount.evalS0]
    exact same.readObj oldSelf (fun o => some ((o.map (·.empowerCount)).getD 0))
      (by intro o; cases o <;> rfl)
  case points target =>
    cases target <;> simp only [MightRead.amount, Bool.false_eq_true] at supported
    simp only [Amount.evalS0, PlayerSel.resolve, same.departures, same.pointsOf]
  case powerSpent =>
    have prior : t.powerSpentBeforeMain p = s.powerSpentBeforeMain p := by
      unfold GameState.powerSpentBeforeMain
      rw [same.turn, ← spendingBeforeMain_filter t.turnFx p s.turn,
        ← spendingBeforeMain_filter s.turnFx p s.turn, same.turnFacts]
    simp only [Amount.evalS0, same.powerSpent, prior]
  case xp => simp only [Amount.evalS0, same.xpOf]
termination_by structural amount

omit same in
private theorem any_readFacts (notes : List TurnFx) (test : TurnFx → Bool)
    (disjoint : ∀ note, note.kind.isMightReadFact = false → test note = false) :
    (notes.filter (fun note => note.kind.isMightReadFact)).any test = notes.any test := by
  rw [List.any_filter]
  apply congrArg (List.any notes)
  funext note
  cases readable : note.kind.isMightReadFact
  · simp [disjoint note readable]
  · simp

private theorem turnFact_eq (p : PlayerId) (kind : TurnEffect) (readable : kind.isMightReadFact = true) :
    t.turnFx.any (fun note => note.turn == t.turn && note.who == p && note.kind == kind) =
      s.turnFx.any (fun note => note.turn == s.turn && note.who == p && note.kind == kind) := by
  rw [same.turn]
  let test := fun note : TurnFx => note.turn == s.turn && note.who == p && note.kind == kind
  have disjoint (note : TurnFx) (ignored : note.kind.isMightReadFact = false) : test note = false := by
    have different : note.kind ≠ kind := by
      intro eq
      rw [eq, readable] at ignored
      contradiction
    simp [test, different]
  rw [← any_readFacts t.turnFx test disjoint, ← any_readFacts s.turnFx test disjoint, same.turnFacts]

/-- A passive condition supported by the Might check reads the same result in both states. -/
theorem condition_eq (wf : s.WF) (p : PlayerId) (env : Env) {self : ObjId} (oldSelf : self.n < s.nextId)
    (condition : Condition) (supported : MightRead.condition condition = true) :
    condition.eval t p self env = condition.eval s p self env := by
  cases condition <;> simp only [MightRead.condition, Bool.false_eq_true, Bool.and_eq_true] at supported
  case always => rfl
  case discardedThisTurn =>
    simpa only [Condition.eval, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc] using
      congrArg some (same.turnFact_eq p .cardDiscarded rfl)
  case noted kind =>
    exact congrArg some (same.turnFact_eq p kind supported)
  case spentOnSpell cost => exact same.spentOnSpell p self env cost
  case and a b =>
    simp only [Condition.eval, condition_eq wf p env oldSelf a supported.1,
      condition_eq wf p env oldSelf b supported.2]
  case cmp _ a b =>
    simp only [Condition.eval, same.amount_eq wf p env oldSelf a supported.1,
      same.amount_eq wf p env oldSelf b supported.2]
  case «exists» sel => simp only [Condition.eval, same.selector_eq wf p env oldSelf sel supported]
  case empowered sel =>
    simp only [Condition.eval, same.selector_eq wf p env oldSelf sel supported]
    cases found : sel.eval s p self env with
    | none => rfl
    | some ids =>
      have who : ids.all (fun id => (t.obj? id).any (fun o => 0 < o.empowerCount)) =
          ids.all (fun id => (s.obj? id).any (fun o => 0 < o.empowerCount)) := by
        apply all_eq_on
        intro id member
        have old := selector_old wf p env oldSelf sel supported found member
        exact same.readObj old (fun o => o.any (fun x => 0 < x.empowerCount))
          (by intro o; cases o <;> rfl)
      simp only [Option.map_some, who]
  case «matches» sel f =>
    simp only [Condition.eval, same.selector_eq wf p env oldSelf sel supported.1]
    cases found : sel.eval s p self env with
    | none => rfl
    | some ids =>
      have matching : ids.mapM (fun id => f.holds t self env id) =
          ids.mapM (fun id => f.holds s self env id) := by
        apply mapM_eq_on
        intro id member
        exact same.filter_eq wf env oldSelf (selector_old wf p env oldSelf sel supported.1 found member)
          f supported.2
      simp only [Option.bind_eq_bind, Option.bind_some, matching]
termination_by structural condition

/-- All active modifiers that can contribute to Might agree across states with the same reads,
when their source's printed or copied text passes the database check. -/
theorem activeMods_eq (wf : s.WF) (database : MightRead.database s.cards) {source : ObjId}
    (old : source.n < s.nextId) : (t.activeMods source).filter MightRead.relevant =
      (s.activeMods source).filter MightRead.relevant := by
  have controllers := same.readObj old (Option.map Object.controller) (by intro o; cases o <;> rfl)
  simp only [GameState.activeMods, same.cardDef, GameState.appendedAbilities, same.attachmentText]
  cases definition : s.cardDef? source with
  | none => cases t.obj? source <;> cases s.obj? source <;> rfl
  | some d =>
    cases before : s.obj? source <;> cases after : t.obj? source <;>
      simp only [before, after, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at controllers
    case none.none => rfl
    case some.some earlier later =>
      simp only [controllers, List.filter_flatMap]
      apply flatMap_congr_mem
      intro ability member
      cases ability with
      | passive c mods =>
        dsimp only
        have checked := accepted_appendedAbilities database definition (.passive c mods) member
        simp only [MightRead.ability, Bool.and_eq_true] at checked
        by_cases affects : mods.any MightRead.relevant = true
        · have condition : MightRead.condition c = true := by simpa [affects] using checked.2
          rw [same.condition_eq wf earlier.controller {} old c condition]
        · have noRelevant : mods.filter MightRead.relevant = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro m member relevant
            exact affects (List.any_eq_true.mpr ⟨m, member, relevant⟩)
          split <;> split <;> simp only [noRelevant, List.filter_nil]
      | _ => rfl

end SameMightReads

/-- The real ordinary trigger dispatcher preserves every active Might-related passive modifier
on existing objects in a checked database, even if the game is in Combat. -/
theorem triggersStep_activeMightMods (s : GameState) (wf : s.WF) (queue : List PendTrigger)
    (rest : List Frame) (pending : s.pending = .triggers queue :: rest)
    (database : MightRead.database s.cards) {source : ObjId} (old : source.n < s.nextId) :
    let outcome := triggersStep s queue rest
    let next := { outcome.1 with pending := outcome.2 ++ rest }
    (next.activeMods source).filter MightRead.relevant = (s.activeMods source).filter MightRead.relevant :=
  (triggersStep_sameMightReads s wf queue rest pending).activeMods_eq wf database old

end Riftbound

end
