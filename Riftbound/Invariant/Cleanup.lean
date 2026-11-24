module

public import Riftbound.Invariant.Sound

/-!
# The Cleanup stops (I12a)

The Cleanup (CR 323) does one step at a time until none applies: it removes a token that is off the
Board (CR 183), detaches an Equipment whose Unit is gone (CR 137), kills a Unit with lethal damage
(CR 323.4), and settles the Control and the Contested state of the Battlefields (CR 323.5, 323.10).
A step of the Cleanup goes down a measure, a tuple of six numbers compared one after the other:
the objects in play, the tokens off the Board, the loose Equipment, the Battlefields that lost
their Control, the stale Contests and the new Contests. So the steps cannot go on for ever
(`cleanup_terminates`).

The proof needs the owner of a Unit with lethal damage to be a player of the game. Killing a Unit
sends it to its owner's Trash; if that were not a zone of the game, the move would fail, leave the
state as it is, and make the Cleanup repeat for ever. A game that can be played has no such object;
`GameState.lethal` says so (its owner is a player), which lets the Cleanup stop in every well-formed
state (`cleanup_terminates`), without a further assumption.
-/

@[expose] public section

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Riftbound

theorem countP_lt_of_imp {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, q x = true → p x = true) →
      (∃ x ∈ l, p x = true ∧ q x = false) → l.countP q < l.countP p
  | [], _, ⟨x, hx, _⟩ => absurd hx (by simp)
  | a :: l, himp, ⟨x, hx, hp, hq⟩ => by
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hle : l.countP q ≤ l.countP p :=
        List.countP_mono_left (fun y hy hqy => himp y (List.mem_cons_of_mem _ hy) hqy)
      simp [hp, hq]; omega
    · have ih := countP_lt_of_imp p q l (fun y hy => himp y (List.mem_cons_of_mem _ hy))
        ⟨x, hx', hp, hq⟩
      by_cases ha : q a = true
      · have := himp a List.mem_cons_self ha
        simp [ha, this]; omega
      · by_cases hpa : p a = true <;> simp [ha, hpa] <;> omega

/-- An object that is a token (CR 183). -/
def GameState.isTok (s : GameState) (id : ObjId) : Bool :=
  (s.obj? id).any (fun o => match o.kind with | .token _ => true | _ => false)

/-- The zones that are not on the Board. -/
def GameState.nbZones (s : GameState) : List Zone :=
  (allZones s.playerCount).filter (fun z => !z.isBoard)

/-- The tokens in the zones that are not on the Board. -/
def GameState.tokC (s : GameState) : Nat :=
  (s.nbZones.flatMap (fun z => (s.zone z).filter (fun id => s.isTok id))).length

/-- An Equipment that is attached to something that is not a Unit in play. -/
def GameState.looseP (s : GameState) (g : ObjId) : Bool :=
  (s.obj? g).any (fun o => match o.attached with
    | some u => !(s.inPlay.contains u && s.isUnit u)
    | none => false)

/-- How many Equipment in play are loose. -/
def GameState.cLoose (s : GameState) : Nat := s.inPlay.countP s.looseP
/-- How many Battlefields are controlled by a player with no Unit there. -/
def GameState.cLost (s : GameState) : Nat := s.battlefields.countP (fun b => s.lostControl b)
/-- How many Battlefields are Contested by a player with no Unit there. -/
def GameState.cStale (s : GameState) : Nat := s.battlefields.countP (fun b => s.staleContest b)
/-- How many Battlefields a Unit makes Contested next. -/
def GameState.cNew (s : GameState) : Nat :=
  s.battlefields.countP (fun b => (s.newContest b).isSome)

section modObj
variable (s : GameState) (b : ObjId) (f : Object → Object)

/-- After changing one object, an object is as it was, or it is the changed one. -/
theorem obj?_modObj_cases (x : ObjId) :
    (s.modObj b f).obj? x = s.obj? x ∨
      ∃ o, s.obj? x = some o ∧ (s.modObj b f).obj? x = some (f o) := by
  rw [GameState.obj?_modObj]
  by_cases h : b.n = x.n
  · have hx : s.obj? b = s.obj? x := by
      unfold GameState.obj?
      rw [h]
    rw [if_pos h, hx]
    cases hh : s.obj? x with
    | none => exact Or.inl rfl
    | some o => exact Or.inr ⟨o, rfl, rfl⟩
  · rw [if_neg h]
    exact Or.inl rfl

theorem cardDef?_modObj (hf : ∀ o, (f o).kind = o.kind) (x : ObjId) :
    (s.modObj b f).cardDef? x = s.cardDef? x := by
  rcases obj?_modObj_cases s b f x with h | ⟨o, h1, h2⟩
  · unfold GameState.cardDef?
    rw [h]
    rfl
  · unfold GameState.cardDef?
    rw [h1, h2]
    simp only [hf]
    rfl

theorem isUnit_modObj (hf : ∀ o, (f o).kind = o.kind) (x : ObjId) :
    (s.modObj b f).isUnit x = s.isUnit x := by
  unfold GameState.isUnit GameState.hasType
  rw [cardDef?_modObj s b f hf]

theorem isBattlefield_modObj (hf : ∀ o, (f o).kind = o.kind) (x : ObjId) :
    (s.modObj b f).isBattlefield x = s.isBattlefield x := by
  unfold GameState.isBattlefield GameState.hasType
  rw [cardDef?_modObj s b f hf]

theorem battlefields_modObj (hf : ∀ o, (f o).kind = o.kind) :
    (s.modObj b f).battlefields = s.battlefields := by
  unfold GameState.battlefields
  simp only [GameState.zone_modObj, isBattlefield_modObj s b f hf]

theorem inPlay_modObj : (s.modObj b f).inPlay = s.inPlay := by
  unfold GameState.inPlay
  simp only [GameState.zone_modObj]
  rfl

/-- What goes down when a unit dies or is recalled from a Battlefield: the objects in play, and the
objects on the Battlefield Zone (counted twice, as a unit on it is also in play). -/
def GameState.pot (s : GameState) : Nat :=
  s.inPlay.length + (s.zone Zone.battlefieldZone).length

theorem pot_modObj : (s.modObj b f).pot = s.pot := by
  unfold GameState.pot
  rw [inPlay_modObj]
  simp only [GameState.zone_modObj]

theorem unitsAt_modObj (hf : ∀ o, (f o).kind = o.kind) (hl : ∀ o, (f o).loc = o.loc)
    (bf : ObjId) : (s.modObj b f).unitsAt bf = s.unitsAt bf := by
  unfold GameState.unitsAt
  simp only [GameState.zone_modObj]
  apply List.filter_congr
  intro u _
  unfold GameState.isAt
  rw [isUnit_modObj s b f hf]
  rcases obj?_modObj_cases s b f u with h | ⟨o, h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    simp only [Option.bind_some, hl]

theorem unitsOf_modObj (hf : ∀ o, (f o).kind = o.kind) (hl : ∀ o, (f o).loc = o.loc)
    (hc : ∀ o, (f o).controller = o.controller) (p : PlayerId) (bf : ObjId) :
    (s.modObj b f).unitsOf p bf = s.unitsOf p bf := by
  unfold GameState.unitsOf
  rw [unitsAt_modObj s b f hf hl]
  apply List.filter_congr
  intro u _
  unfold GameState.isControlledBy
  rcases obj?_modObj_cases s b f u with h | ⟨o, h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    simp only [Option.map_some, hc]

theorem isTok_modObj (hf : ∀ o, (f o).kind = o.kind) (x : ObjId) :
    (s.modObj b f).isTok x = s.isTok x := by
  unfold GameState.isTok
  rcases obj?_modObj_cases s b f x with h | ⟨o, h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    simp only [Option.any_some, hf]

theorem tokC_modObj (hf : ∀ o, (f o).kind = o.kind) : (s.modObj b f).tokC = s.tokC := by
  unfold GameState.tokC GameState.nbZones
  have h1 : (s.modObj b f).playerCount = s.playerCount := rfl
  simp only [h1, GameState.zone_modObj, isTok_modObj s b f hf]

end modObj

/-- The measure of a state, for the Cleanup: it goes down at every step (I12a). -/
def GameState.cleanupMeasure (s : GameState) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (s.pot, s.tokC, s.cLoose, s.cLost, s.cStale, s.cNew)

/-- Lexicographic order on the measure. -/
def MeasLt : Nat × Nat × Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat × Nat × Nat →
    Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·)
    (Prod.Lex (· < ·) (· < ·)))))

theorem MeasLt.wf : WellFounded MeasLt :=
  (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩
    (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩
      (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ ⟨_, Nat.lt_wfRel.wf⟩))))).wf

theorem MeasLt.at1 {a' a : Nat} {r' r : Nat × Nat × Nat × Nat × Nat} (h : a' < a) :
    MeasLt (a', r') (a, r) := Prod.Lex.left _ _ h

theorem MeasLt.at2 {a a' b' b : Nat} {r' r : Nat × Nat × Nat × Nat} (h1 : a' = a) (h : b' < b) :
    MeasLt (a', b', r') (a, b, r) := by
  subst h1
  exact Prod.Lex.right _ (Prod.Lex.left _ _ h)

theorem MeasLt.at3 {a a' b b' c' c : Nat} {r' r : Nat × Nat × Nat} (h1 : a' = a) (h2 : b' = b)
    (h : c' < c) : MeasLt (a', b', c', r') (a, b, c, r) := by
  subst h1 h2
  exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ h))

theorem MeasLt.at4 {a a' b b' c c' d' d : Nat} {r' r : Nat × Nat} (h1 : a' = a) (h2 : b' = b)
    (h3 : c' = c) (h : d' < d) : MeasLt (a', b', c', d', r') (a, b, c, d, r) := by
  subst h1 h2 h3
  exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ h)))

theorem MeasLt.at5 {a a' b b' c c' d d' e' e f' f : Nat} (h1 : a' = a) (h2 : b' = b)
    (h3 : c' = c) (h4 : d' = d) (h : e' < e) :
    MeasLt (a', b', c', d', e', f') (a, b, c, d, e, f) := by
  subst h1 h2 h3 h4
  exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _
    (Prod.Lex.left _ _ h))))

theorem MeasLt.at6 {a a' b b' c c' d d' e e' f' f : Nat} (h1 : a' = a) (h2 : b' = b)
    (h3 : c' = c) (h4 : d' = d) (h5 : e' = e) (h : f' < f) :
    MeasLt (a', b', c', d', e', f') (a, b, c, d, e, f) := by
  subst h1 h2 h3 h4 h5
  exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _
    (Prod.Lex.right _ h))))

/-- Detaching one loose Equipment (any change of one object that keeps its kind and clears what it
is attached to) leaves fewer loose Equipment. -/
theorem cLoose_detach (s : GameState) (g : ObjId) (f : Object → Object)
    (hf : ∀ o, (f o).kind = o.kind) (hn : ∀ o, (f o).attached = none)
    (hgm : s.looseP g = true) (hgmem : g ∈ s.inPlay) : (s.modObj g f).cLoose < s.cLoose := by
  have hin := inPlay_modObj s g f
  unfold GameState.cLoose
  rw [hin]
  apply countP_lt_of_imp
  · intro x hx hq
    by_cases hn' : g.n = x.n
    · exfalso
      have hxg : x = g := by cases x; cases g; simp_all
      subst hxg
      unfold GameState.looseP at hq
      rw [GameState.obj?_modObj, if_pos rfl] at hq
      cases ho : s.obj? x with
      | none => simp [ho] at hq
      | some o => simp [ho, hn] at hq
    · unfold GameState.looseP at hq ⊢
      simp only [GameState.obj?_modObj, hn', ↓reduceIte, hin, isUnit_modObj s g f hf] at hq
      exact hq
  · refine ⟨g, hgmem, hgm, ?_⟩
    unfold GameState.looseP
    rw [GameState.obj?_modObj, if_pos rfl]
    cases ho : s.obj? g with
    | none => simp
    | some o => simp [hn]

/-- Detaching a loose Equipment makes the measure go down. -/
theorem detachStep_lt {s s' : GameState} {es : List Event} (h : detachStep s = some (s', es)) :
    MeasLt s'.cleanupMeasure s.cleanupMeasure := by
  unfold detachStep at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨g, hg, hr⟩ := h
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, -⟩ := hr
  have hf : ∀ o : Object, ({ o with attached := none } : Object).kind = o.kind := fun _ => rfl
  have hn : ∀ o : Object, ({ o with attached := none } : Object).attached = none := fun _ => rfl
  unfold GameState.looseGear at hg
  have hgm : s.looseP g = true := List.find?_some hg
  have hgmem : g ∈ s.inPlay := List.mem_of_find?_eq_some hg
  exact MeasLt.at3 (by rw [pot_modObj]) (tokC_modObj s g _ hf)
    (cLoose_detach s g _ hf hn hgm hgmem)

section bfStep
variable (s : GameState) (b : ObjId) (f : Object → Object)

theorem looseP_modObj (hf : ∀ o, (f o).kind = o.kind) (ha : ∀ o, (f o).attached = o.attached)
    (x : ObjId) : (s.modObj b f).looseP x = s.looseP x := by
  unfold GameState.looseP
  simp only [inPlay_modObj, isUnit_modObj s b f hf]
  rcases obj?_modObj_cases s b f x with h | ⟨o, h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    simp only [Option.any_some, ha]

theorem cLoose_modObj (hf : ∀ o, (f o).kind = o.kind) (ha : ∀ o, (f o).attached = o.attached) :
    (s.modObj b f).cLoose = s.cLoose := by
  unfold GameState.cLoose
  rw [inPlay_modObj]
  exact List.countP_congr (fun x _ => by rw [looseP_modObj s b f hf ha x])

/-- Control of the other Battlefields is as it was. -/
theorem controlOf_modObj_ne {x : ObjId} (hx : b.n ≠ x.n) :
    (s.modObj b f).controlOf x = s.controlOf x := by
  unfold GameState.controlOf
  rw [GameState.obj?_modObj, if_neg hx]

theorem contested_modObj_ne {x : ObjId} (hx : b.n ≠ x.n) :
    ((s.modObj b f).obj? x).bind (·.contested) = (s.obj? x).bind (·.contested) := by
  rw [GameState.obj?_modObj, if_neg hx]

end bfStep

/-- Whether two Battlefield objects are the same one. -/
theorem objId_eq_of_n {x y : ObjId} (h : x.n = y.n) : x = y := by
  cases x; cases y; simp_all

/-- A Battlefield loses its Control with nobody there: the measure goes down. -/
theorem lostControl_lt {s : GameState} {b : ObjId} (hb : b ∈ s.battlefields)
    (hl : s.lostControl b = true) :
    MeasLt (s.modObj b (fun o => { o with control := none })).cleanupMeasure s.cleanupMeasure := by
  have hk : ∀ o : Object, ({ o with control := none } : Object).kind = o.kind := fun _ => rfl
  have hloc : ∀ o : Object, ({ o with control := none } : Object).loc = o.loc := fun _ => rfl
  have hc : ∀ o : Object, ({ o with control := none } : Object).controller = o.controller :=
    fun _ => rfl
  have ha : ∀ o : Object, ({ o with control := none } : Object).attached = o.attached :=
    fun _ => rfl
  have hbf := battlefields_modObj s b _ hk
  have hlt : (s.modObj b (fun o => { o with control := none })).cLost < s.cLost := by
    unfold GameState.cLost
    rw [hbf]
    apply countP_lt_of_imp
    · intro x hx hq
      by_cases hn : b.n = x.n
      · exfalso
        have hxb : x = b := (objId_eq_of_n hn).symm
        subst hxb
        unfold GameState.lostControl GameState.controlOf at hq
        rw [GameState.obj?_modObj, if_pos rfl] at hq
        cases ho : s.obj? x with
        | none => simp [ho] at hq
        | some o => simp [ho] at hq
      · unfold GameState.lostControl at hq ⊢
        simp only [controlOf_modObj_ne s b _ hn, unitsOf_modObj s b _ hk hloc hc] at hq
        exact hq
    · refine ⟨b, hb, hl, ?_⟩
      unfold GameState.lostControl GameState.controlOf
      rw [GameState.obj?_modObj, if_pos rfl]
      cases ho : s.obj? b with
      | none => simp
      | some o => simp
  exact MeasLt.at4 (by rw [pot_modObj]) (tokC_modObj s b _ hk) (cLoose_modObj s b _ hk ha) hlt

section bfStep2
variable (s : GameState) (b : ObjId) (f : Object → Object)

theorem controlOf_modObj_keep (hc : ∀ o, (f o).control = o.control) (x : ObjId) :
    (s.modObj b f).controlOf x = s.controlOf x := by
  unfold GameState.controlOf
  rcases obj?_modObj_cases s b f x with h | ⟨o, h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    simp only [Option.bind_some, hc]

theorem ctrl_modObj (hc : ∀ o, (f o).controller = o.controller) (u : ObjId) :
    ((s.modObj b f).obj? u).map (·.controller) = (s.obj? u).map (·.controller) := by
  rcases obj?_modObj_cases s b f u with h | ⟨o, h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    simp only [Option.map_some, hc]

theorem staleContest_modObj_ne (hk : ∀ o, (f o).kind = o.kind) (hl : ∀ o, (f o).loc = o.loc)
    (hc : ∀ o, (f o).controller = o.controller) {x : ObjId} (hx : b.n ≠ x.n) :
    (s.modObj b f).staleContest x = s.staleContest x := by
  unfold GameState.staleContest
  rw [contested_modObj_ne s b f hx]
  simp only [unitsOf_modObj s b f hk hl hc]

theorem newContest_modObj_ne (hk : ∀ o, (f o).kind = o.kind) (hl : ∀ o, (f o).loc = o.loc)
    (hc : ∀ o, (f o).controller = o.controller) (hctl : ∀ o, (f o).control = o.control)
    {x : ObjId} (hx : b.n ≠ x.n) : (s.modObj b f).newContest x = s.newContest x := by
  unfold GameState.newContest
  rw [controlOf_modObj_keep s b f hctl, contested_modObj_ne s b f hx,
    unitsAt_modObj s b f hk hl]
  simp only [ctrl_modObj s b f hc]

end bfStep2

/-- What it means that a Battlefield is newly Contested. -/
theorem newContest_spec {s : GameState} {b : ObjId} {q : PlayerId} (h : s.newContest b = some q) :
    s.controlOf b = none ∧ (s.obj? b).bind (·.contested) = none ∧
      ∃ u, u ∈ s.unitsAt b ∧ (s.obj? u).map (·.controller) = some q := by
  unfold GameState.newContest at h
  cases hc : s.controlOf b <;> cases hd : (s.obj? b).bind (·.contested) <;>
    simp only [hc, hd] at h
  · refine ⟨rfl, rfl, ?_⟩
    cases hu : (s.unitsAt b).head? with
    | none => simp [hu] at h
    | some u =>
      simp only [hu, Option.bind_some] at h
      exact ⟨u, List.mem_of_mem_head? hu, h⟩
  all_goals simp at h

/-- A Battlefield stops being Contested by a player with no Unit there: the measure goes down. -/
theorem staleContest_lt {s : GameState} {b : ObjId} (hb : b ∈ s.battlefields)
    (hl : s.staleContest b = true) :
    MeasLt (s.modObj b (fun o => { o with contested := none })).cleanupMeasure
      s.cleanupMeasure := by
  have hk : ∀ o : Object, ({ o with contested := none } : Object).kind = o.kind := fun _ => rfl
  have hloc : ∀ o : Object, ({ o with contested := none } : Object).loc = o.loc := fun _ => rfl
  have hc : ∀ o : Object, ({ o with contested := none } : Object).controller = o.controller :=
    fun _ => rfl
  have ha : ∀ o : Object, ({ o with contested := none } : Object).attached = o.attached :=
    fun _ => rfl
  have hctl : ∀ o : Object, ({ o with contested := none } : Object).control = o.control :=
    fun _ => rfl
  have hbf := battlefields_modObj s b _ hk
  have hlost : (s.modObj b (fun o => { o with contested := none })).cLost = s.cLost := by
    unfold GameState.cLost
    rw [hbf]
    refine List.countP_congr (fun x _ => ?_)
    unfold GameState.lostControl
    rw [controlOf_modObj_keep s b _ hctl x]
    simp only [unitsOf_modObj s b _ hk hloc hc]
  have hlt : (s.modObj b (fun o => { o with contested := none })).cStale < s.cStale := by
    unfold GameState.cStale
    rw [hbf]
    apply countP_lt_of_imp
    · intro x hx hq
      by_cases hn : b.n = x.n
      · exfalso
        have hxb : x = b := (objId_eq_of_n hn).symm
        subst hxb
        unfold GameState.staleContest at hq
        rw [GameState.obj?_modObj, if_pos rfl] at hq
        cases ho : s.obj? x with
        | none => simp [ho] at hq
        | some o => simp [ho] at hq
      · rw [staleContest_modObj_ne s b _ hk hloc hc hn] at hq
        exact hq
    · refine ⟨b, hb, hl, ?_⟩
      unfold GameState.staleContest
      rw [GameState.obj?_modObj, if_pos rfl]
      cases ho : s.obj? b with
      | none => simp
      | some o => simp
  exact MeasLt.at5 (by rw [pot_modObj]) (tokC_modObj s b _ hk) (cLoose_modObj s b _ hk ha)
    hlost hlt

/-- A Battlefield of the game is an object of the table. -/
theorem obj?_of_mem_battlefields {s : GameState} {b : ObjId} (hb : b ∈ s.battlefields) :
    ∃ o, s.obj? b = some o := by
  unfold GameState.battlefields at hb
  have h := (List.mem_filter.mp hb).2
  unfold GameState.isBattlefield GameState.hasType GameState.cardDef? at h
  cases ho : s.obj? b with
  | none => simp [ho] at h
  | some o => exact ⟨o, rfl⟩

/-- A Unit at an uncontrolled Battlefield makes it Contested: the measure goes down. -/
theorem newContest_lt {s : GameState} {b : ObjId} {q : PlayerId} (hb : b ∈ s.battlefields)
    (hn : s.newContest b = some q) :
    MeasLt (s.modObj b (fun o => { o with contested := some q })).cleanupMeasure
      s.cleanupMeasure := by
  have hk : ∀ o : Object, ({ o with contested := some q } : Object).kind = o.kind := fun _ => rfl
  have hloc : ∀ o : Object, ({ o with contested := some q } : Object).loc = o.loc :=
    fun _ => rfl
  have hc : ∀ o : Object, ({ o with contested := some q } : Object).controller = o.controller :=
    fun _ => rfl
  have ha : ∀ o : Object, ({ o with contested := some q } : Object).attached = o.attached :=
    fun _ => rfl
  have hctl : ∀ o : Object, ({ o with contested := some q } : Object).control = o.control :=
    fun _ => rfl
  have hbf := battlefields_modObj s b _ hk
  obtain ⟨hcn, hdn, u, hu, huq⟩ := newContest_spec hn
  obtain ⟨ob, hob⟩ := obj?_of_mem_battlefields hb
  have hlost : (s.modObj b (fun o => { o with contested := some q })).cLost = s.cLost := by
    unfold GameState.cLost
    rw [hbf]
    refine List.countP_congr (fun x _ => ?_)
    unfold GameState.lostControl
    rw [controlOf_modObj_keep s b _ hctl x]
    simp only [unitsOf_modObj s b _ hk hloc hc]
  have hstale : (s.modObj b (fun o => { o with contested := some q })).cStale = s.cStale := by
    unfold GameState.cStale
    rw [hbf]
    refine List.countP_congr (fun x _ => ?_)
    by_cases hnx : b.n = x.n
    · have hxb : x = b := (objId_eq_of_n hnx).symm
      subst hxb
      have h1 : s.staleContest x = false := by
        unfold GameState.staleContest
        rw [hdn]
      have h2 : (s.modObj x (fun o => { o with contested := some q })).staleContest x = false := by
        unfold GameState.staleContest
        rw [GameState.obj?_modObj, if_pos rfl]
        cases ho : s.obj? x with
        | none => simp [ho]
        | some o =>
          simp only [Option.map_some, Option.bind_some]
          have hmem : u ∈ (s.modObj x (fun o => { o with contested := some q })).unitsOf q x := by
            rw [unitsOf_modObj s x _ hk hloc hc]
            unfold GameState.unitsOf
            refine List.mem_filter.mpr ⟨hu, ?_⟩
            unfold GameState.isControlledBy
            simp [huq]
          cases hl : (s.modObj x (fun o => { o with contested := some q })).unitsOf q x with
          | nil => rw [hl] at hmem; simp at hmem
          | cons _ _ => simp
      rw [h1, h2]
    · rw [staleContest_modObj_ne s b _ hk hloc hc hnx]
  have hlt : (s.modObj b (fun o => { o with contested := some q })).cNew < s.cNew := by
    unfold GameState.cNew
    rw [hbf]
    apply countP_lt_of_imp
    · intro x hx hq
      by_cases hnx : b.n = x.n
      · exfalso
        have hxb : x = b := (objId_eq_of_n hnx).symm
        subst hxb
        unfold GameState.newContest at hq
        rw [controlOf_modObj_keep s x _ hctl, GameState.obj?_modObj, if_pos rfl] at hq
        cases ho : s.obj? x with
        | none => rw [hob] at ho; cases ho
        | some o =>
          cases hcx : s.controlOf x <;> simp [ho, hcx] at hq
      · rw [newContest_modObj_ne s b _ hk hloc hc hctl hnx] at hq
        exact hq
    · refine ⟨b, hb, by simp [hn], ?_⟩
      unfold GameState.newContest
      rw [controlOf_modObj_keep s b _ hctl, GameState.obj?_modObj, if_pos rfl]
      cases ho : s.obj? b with
      | none => rw [hob] at ho; cases ho
      | some o => cases hcx : s.controlOf b <;> simp
  exact MeasLt.at6 (by rw [pot_modObj]) (tokC_modObj s b _ hk) (cLoose_modObj s b _ hk ha)
    hlost hstale hlt

/-- Taking one object out of one list of a `flatMap` takes one object out of the whole. -/
theorem length_flatMap_erase_one {L : List Zone} (hnd : L.Nodup) (f g : Zone → List ObjId)
    (z : Zone) (hz : z ∈ L) (u : ObjId) (hu : u ∈ f z) (hg : g z = (f z).erase u)
    (hrest : ∀ x ∈ L, x ≠ z → g x = f x) :
    (L.flatMap g).length + 1 = (L.flatMap f).length := by
  have h1 := (flatMap_split L g z hz).length_eq
  have h2 := (flatMap_split L f z hz).length_eq
  rw [flatMap_one_congr L hnd f g z hrest] at h1
  simp only [List.length_append] at h1 h2
  rw [hg, List.length_erase_of_mem hu] at h1
  have : 0 < (f z).length := List.length_pos_of_mem hu
  omega

/-- Moving one object from one list of a `flatMap` to another leaves the length of the whole as it
was. -/
theorem length_flatMap_move {L : List Zone} (hnd : L.Nodup) (f g : Zone → List ObjId)
    (a b : Zone) (ha : a ∈ L) (hb : b ∈ L) (u : ObjId) (hu : u ∈ f a)
    (hga : g a = (f a).erase u) (hgb : (g b).length = (f b).length + 1) (hab : a ≠ b)
    (hrest : ∀ x ∈ L, x ≠ a → x ≠ b → g x = f x) :
    (L.flatMap g).length = (L.flatMap f).length := by
  let h : Zone → List ObjId := fun x => if x = a then g a else f x
  have h1 := length_flatMap_erase_one hnd f h a ha u hu (by simp [h, hga])
    (fun x hx hne => by simp [h, hne])
  have e1 := (flatMap_split L g b hb).length_eq
  have e2 := (flatMap_split L h b hb).length_eq
  rw [flatMap_one_congr L hnd h g b (fun x hx hne => by
    by_cases hxa : x = a
    · subst hxa; simp [h]
    · simp [h, hxa, hrest x hx hxa hne])] at e1
  simp only [List.length_append] at e1 e2
  have hb' : h b = f b := by simp [h, hab.symm]
  rw [hb'] at e2
  omega

/-- The zones of the objects in play: the Bases of the players, then the Battlefield Zone. -/
def GameState.inPlayZones (s : GameState) : List Zone :=
  s.players.map (fun p => Zone.player p .base) ++ [Zone.battlefieldZone]

theorem GameState.inPlay_eq_flatMap (s : GameState) :
    s.inPlay = s.inPlayZones.flatMap s.zone := by
  unfold GameState.inPlay GameState.inPlayZones
  simp [List.flatMap_append, List.flatMap_map]

theorem GameState.inPlayZones_nodup (s : GameState) : s.inPlayZones.Nodup := by
  unfold GameState.inPlayZones GameState.players
  rw [List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · refine List.Pairwise.map (S := fun a b : Zone => a ≠ b)
      (fun p : PlayerId => Zone.player p .base) ?_
      (List.Pairwise.map (S := fun a b : PlayerId => a ≠ b)
        (fun i : Nat => (⟨i⟩ : PlayerId)) ?_ List.nodup_range)
    · intro a b hab h
      simp only [Zone.player.injEq, and_true] at h
      exact hab h
    · intro a b hab h
      simp only [PlayerId.mk.injEq] at h
      exact hab h
  · intro x hx y hy
    simp only [List.mem_map, List.mem_singleton] at hx hy
    obtain ⟨p, -, rfl⟩ := hx
    subst hy
    intro h
    cases h

/-- A Unit with lethal damage has an owner who is a player. -/
theorem lethal_owner {s : GameState} {u : ObjId} (h : s.lethal u = true) :
    ∀ o, s.obj? u = some o → o.owner.n < s.playerCount := by
  intro o ho
  unfold GameState.lethal at h
  rw [ho] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- Noting that a unit died alone leaves the objects in play as they are. -/
theorem noteAlone_inPlay (s : GameState) (o : Object) (moved : Option ObjId) (alone : Bool) :
    (noteAlone s o moved alone).inPlay = s.inPlay := by
  unfold noteAlone
  cases moved with
  | none => rfl
  | some n =>
    unfold noteIf
    by_cases h : alone = true
    · simp only [h, ite_true]; rfl
    · simp [h]

/-- Noting a death leaves the objects in play as they are. -/
theorem noteDeath_inPlay (s : GameState) (o : Object) (isUnit marked mighty : Bool)
    (moved : Option ObjId) (banisher : Option ObjId) :
    (noteDeath s o isUnit marked mighty moved banisher).inPlay = s.inPlay := by
  have key : ∀ (b : Bool) (f : GameState → GameState), (∀ t, (f t).inPlay = t.inPlay) →
      ∀ t, (noteIf b f t).inPlay = t.inPlay := by
    intro b f hf t
    unfold noteIf
    split
    · exact hf t
    · rfl
  unfold noteDeath
  cases moved with
  | none =>
    dsimp only
    exact key _ (fun t => t.addTurnFx o.controller .unitDied) (fun t => rfl) s
  | some n =>
    dsimp only
    rw [key _ (fun t => t.modObj n (fun x => { x with banishedWith := banisher }))
        (fun t => inPlay_modObj t n _),
      key _ (fun t => t.addTurnFxOn o.controller n .recallDied) (fun t => rfl),
      key _ (fun t => t.addTurnFxOn o.controller n .mightyUnitDied) (fun t => rfl),
      key _ (fun t => t.addTurnFxOn o.controller n .stunnedUnitDied) (fun t => rfl),
      key _ (fun t => t.addTurnFxOn o.controller n .buffedUnitDied) (fun t => rfl),
      key _ (fun t => t.addTurnFx o.controller .unitDied) (fun t => rfl)]

/-- Noting that a unit died alone leaves the zones as they are. -/
theorem noteAlone_zone (s : GameState) (o : Object) (moved : Option ObjId) (alone : Bool)
    (z : Zone) : (noteAlone s o moved alone).zone z = s.zone z := by
  unfold noteAlone
  cases moved with
  | none => rfl
  | some n =>
    unfold noteIf
    by_cases h : alone = true
    · simp only [h, ite_true]; rfl
    · simp [h]

/-- Noting a death leaves the zones as they are. -/
theorem noteDeath_zone (s : GameState) (o : Object) (isUnit marked mighty : Bool)
    (moved : Option ObjId) (banisher : Option ObjId) (z : Zone) :
    (noteDeath s o isUnit marked mighty moved banisher).zone z = s.zone z := by
  have key : ∀ (b : Bool) (f : GameState → GameState), (∀ t, (f t).zone z = t.zone z) →
      ∀ t, (noteIf b f t).zone z = t.zone z := by
    intro b f hf t
    unfold noteIf
    split
    · exact hf t
    · rfl
  unfold noteDeath
  cases moved with
  | none =>
    dsimp only
    exact key _ (fun t => t.addTurnFx o.controller .unitDied) (fun t => rfl) s
  | some n =>
    dsimp only
    rw [key _ (fun t => t.modObj n (fun x => { x with banishedWith := banisher }))
        (fun t => by simp only [GameState.zone_modObj]),
      key _ (fun t => t.addTurnFxOn o.controller n .recallDied) (fun t => rfl),
      key _ (fun t => t.addTurnFxOn o.controller n .mightyUnitDied) (fun t => rfl),
      key _ (fun t => t.addTurnFxOn o.controller n .stunnedUnitDied) (fun t => rfl),
      key _ (fun t => t.addTurnFxOn o.controller n .buffedUnitDied) (fun t => rfl),
      key _ (fun t => t.addTurnFx o.controller .unitDied) (fun t => rfl)]

/-- **Killing an object in play takes it out of play** (I12a). In a well-formed game, when the
owner is a player, the Trash of the owner is a zone of the game and the object is on the Board, so
the move happens, and one object fewer is in play. -/
theorem killObj_pot_lt {s : GameState} (hwf : s.WF) {u : ObjId}
    (hov : ∀ o, s.obj? u = some o → o.owner.n < s.playerCount)
    (hu : u ∈ s.inPlay) : (killObj s u).1.pot < s.pot := by
  rw [GameState.inPlay_eq_flatMap] at hu
  obtain ⟨z0, hz0, huz⟩ := List.mem_flatMap.mp hu
  obtain ⟨o, ho⟩ := GameState.obj_of_mem hwf huz
  -- where it goes: the Trash of the owner, or (if an Equipment says so) the Banishment
  obtain ⟨dk, hdk⟩ : ∃ dk, dk = (if s.banishedOnDeath u = true then ZoneKind.banishment
      else ZoneKind.trash) := ⟨_, rfl⟩
  have hk : dk = ZoneKind.trash ∨ dk = ZoneKind.banishment := by
    rw [hdk]; split <;> simp
  -- the destination: a zone of the owner that is not a zone in play
  have hdst : ∀ o', s.obj? u = some o' →
      (Zone.normalize o'.owner (.player o'.owner dk)).Valid s.playerCount ∧
        z0 ≠ Zone.normalize o'.owner (.player o'.owner dk) := by
    intro o' ho'
    have hlt := hov o' ho'
    rcases hk with rfl | rfl <;>
    · simp only [Zone.normalize, Zone.isBoard]
      refine ⟨Zone.valid_player hlt _, ?_⟩
      have hz0' := hz0
      unfold GameState.inPlayZones at hz0'
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hz0'
      rcases hz0' with ⟨p, -, rfl⟩ | rfl <;> intro h <;> cases h
  obtain ⟨r, hr⟩ := moveObj_isSome hwf huz (.player o.owner dk) .top (by
    intro o' ho'
    rw [ho] at ho'
    cases ho'
    exact hdst o ho)
  obtain ⟨s', id'⟩ := r
  obtain ⟨src, d, hs, o2, ho2, hd⟩ := moveObj_spec_dst hr
  have hloc : s.locate u = some z0 :=
    GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf huz) huz
  have hsrc : src = z0 := Option.some.inj (hs.locate.symm.trans hloc)
  subst hsrc
  have hkill : (killObj s u).1.inPlay = s'.inPlay := by
    unfold killObj sendObj
    rw [← hdk, ho]
    simp only [hr]
    exact (noteAlone_inPlay _ _ _ _).trans (noteDeath_inPlay _ _ _ _ _ _ _)
  have hkillz : ∀ z, (killObj s u).1.zone z = s'.zone z := by
    intro z
    unfold killObj sendObj
    rw [← hdk, ho]
    simp only [hr]
    exact (noteAlone_zone _ _ _ _ _).trans (noteDeath_zone _ _ _ _ _ _ _ _)
  unfold GameState.pot
  rw [hkillz, hkill, GameState.inPlay_eq_flatMap, GameState.inPlay_eq_flatMap]
  have hdnot : d ∉ s.inPlayZones := by
    have : o2 = o := Option.some.inj (ho2.symm.trans ho)
    subst this
    rw [hd]
    rcases hk with rfl | rfl <;>
    · simp only [Zone.normalize, Zone.isBoard]
      unfold GameState.inPlayZones
      simp only [List.mem_append, List.mem_map, List.mem_singleton, not_or, not_exists, not_and]
      refine ⟨fun p _ h => ?_, fun h => ?_⟩ <;> cases h
  have hpc : s'.playerCount = s.playerCount := by
    unfold GameState.playerCount
    rw [hs.config]
  have hsame : s'.inPlayZones = s.inPlayZones := by
    unfold GameState.inPlayZones GameState.players
    rw [hpc]
  have key := length_flatMap_erase_one s.inPlayZones_nodup s.zone s'.zone src hz0 u huz
    (hs.zone_src) (fun x hx hne => hs.zone_other hne (fun h => hdnot (h ▸ hx)))
  have hbf : (s'.zone Zone.battlefieldZone).length ≤ (s.zone Zone.battlefieldZone).length := by
    by_cases hb : Zone.battlefieldZone = src
    · rw [hb, hs.zone_src]
      exact List.length_erase_le
    · have hbd : Zone.battlefieldZone ≠ d := by
        intro e
        apply hdnot
        rw [← e]
        simp [GameState.inPlayZones]
      rw [hs.zone_other hb hbd]
      exact Nat.le_refl _
  rw [hsame]
  omega

theorem killObj_mem_inPlay_ne {s : GameState} (hwf : s.WF) {u x : ObjId} (hne : x ≠ u)
    (hx : x ∈ s.inPlay)
    (hov : ∀ o, s.obj? u = some o → o.owner.n < s.playerCount)
    (hu : u ∈ s.inPlay) : x ∈ (killObj s u).1.inPlay := by
  rw [GameState.inPlay_eq_flatMap] at hu
  obtain ⟨z0, hz0, huz⟩ := List.mem_flatMap.mp hu
  obtain ⟨o, ho⟩ := GameState.obj_of_mem hwf huz
  -- where it goes: the Trash of the owner, or (if an Equipment says so) the Banishment
  obtain ⟨dk, hdk⟩ : ∃ dk, dk = (if s.banishedOnDeath u = true then ZoneKind.banishment
      else ZoneKind.trash) := ⟨_, rfl⟩
  have hk : dk = ZoneKind.trash ∨ dk = ZoneKind.banishment := by
    rw [hdk]; split <;> simp
  -- the destination: a zone of the owner that is not a zone in play
  have hdst : ∀ o', s.obj? u = some o' →
      (Zone.normalize o'.owner (.player o'.owner dk)).Valid s.playerCount ∧
        z0 ≠ Zone.normalize o'.owner (.player o'.owner dk) := by
    intro o' ho'
    have hlt := hov o' ho'
    rcases hk with rfl | rfl <;>
    · simp only [Zone.normalize, Zone.isBoard]
      refine ⟨Zone.valid_player hlt _, ?_⟩
      have hz0' := hz0
      unfold GameState.inPlayZones at hz0'
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hz0'
      rcases hz0' with ⟨p, -, rfl⟩ | rfl <;> intro h <;> cases h
  obtain ⟨r, hr⟩ := moveObj_isSome hwf huz (.player o.owner dk) .top (by
    intro o' ho'
    rw [ho] at ho'
    cases ho'
    exact hdst o ho)
  obtain ⟨s', id'⟩ := r
  obtain ⟨src, d, hs, o2, ho2, hd⟩ := moveObj_spec_dst hr
  have hloc : s.locate u = some z0 :=
    GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf huz) huz
  have hsrc : src = z0 := Option.some.inj (hs.locate.symm.trans hloc)
  subst hsrc
  have hkill : (killObj s u).1.inPlay = s'.inPlay := by
    unfold killObj sendObj
    rw [← hdk, ho]
    simp only [hr]
    exact (noteAlone_inPlay _ _ _ _).trans (noteDeath_inPlay _ _ _ _ _ _ _)
  rw [hkill, GameState.inPlay_eq_flatMap]
  have hdnot : d ∉ s.inPlayZones := by
    have : o2 = o := Option.some.inj (ho2.symm.trans ho)
    subst this
    rw [hd]
    rcases hk with rfl | rfl <;>
    · simp only [Zone.normalize, Zone.isBoard]
      unfold GameState.inPlayZones
      simp only [List.mem_append, List.mem_map, List.mem_singleton, not_or, not_exists, not_and]
      refine ⟨fun p _ h => ?_, fun h => ?_⟩ <;> cases h
  have hpc : s'.playerCount = s.playerCount := by
    unfold GameState.playerCount
    rw [hs.config]
  have hsame : s'.inPlayZones = s.inPlayZones := by
    unfold GameState.inPlayZones GameState.players
    rw [hpc]
  rw [hsame]
  obtain ⟨zx, hzx, hxz⟩ := List.mem_flatMap.mp (GameState.inPlay_eq_flatMap s ▸ hx)
  refine List.mem_flatMap.mpr ⟨zx, hzx, ?_⟩
  by_cases hzs : zx = src
  · subst hzs
    rw [hs.zone_src]
    exact List.mem_erase_of_ne hne |>.mpr hxz
  · rw [hs.zone_other hzs (fun h => hdnot (h ▸ hzx))]
    exact hxz

/-- The Equipment that dies instead of a unit is in play. -/
theorem deathSaver_mem {s : GameState} {u g : ObjId} (h : s.deathSaver u = some (some g)) :
    g ∈ s.inPlay := by
  unfold GameState.deathSaver at h
  split at h
  · rename_i g' hg'
    simp only [Option.some.injEq] at h
    obtain rfl := h
    exact List.mem_of_find?_eq_some hg'
  · split at h
    · split at h
      · simp at h
      · simp at h
    · simp at h

theorem filter_erase_of_true {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (l : List α)
    (a : α)
    (ha : p a = true) : (l.erase a).filter p = (l.filter p).erase a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x = a
    · subst hx
      simp [List.erase_cons_head, ha]
    · have hxa : (x == a) = false := by simpa using hx
      cases hp : p x <;> simp [List.erase_cons_tail, hxa, List.filter_cons, hp, ih, hxa]

/-- What the zone of an object in a well-formed game says: no other zone holds it. -/
theorem ne_of_mem_other_zone {s : GameState} (hwf : s.WF) {z x : Zone} {id y : ObjId}
    (hid : id ∈ s.zone z) (hy : y ∈ s.zone x) (hxz : x ≠ z) : y ≠ id := by
  intro h
  subst h
  have h1 := GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hid) hid
  have h2 := GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hy) hy
  exact hxz (Option.some.inj (h2.symm.trans h1))

/-- Readying or exhausting an object leaves what goes down as it is. -/
theorem setExhausted_pot (b : Bool) (s : GameState) (id : ObjId) :
    (setExhausted b s id).1.pot = s.pot := by
  unfold setExhausted
  split
  · exact pot_modObj _ _ _
  · rfl

/-- What a move of a unit in play to its controller's Base does to what goes down: nothing, but
one less on the Battlefield Zone if it was there. -/
theorem sendHome_core {s : GameState} (hwf : s.WF) {u : ObjId} (hu : u ∈ s.inPlay) {o : Object}
    (ho : s.obj? u = some o) {s' : GameState} {id' : ObjId}
    (hm : moveObj s u (.player o.controller .base) = some (s', id')) :
    s'.pot + (if u ∈ s.zone Zone.battlefieldZone then 1 else 0) = s.pot := by
  obtain ⟨src, d, hs, o2, ho2, hd⟩ := moveObj_spec_dst hm
  rw [GameState.inPlay_eq_flatMap] at hu
  obtain ⟨z0, hz0, huz⟩ := List.mem_flatMap.mp hu
  have hloc : s.locate u = some z0 :=
    GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf huz) huz
  have hsrc : src = z0 := Option.some.inj (hs.locate.symm.trans hloc)
  subst hsrc
  have hdn : d = .player o.controller .base := by
    have : o2 = o := Option.some.inj (ho2.symm.trans ho)
    subst this
    rw [hd]
    simp [Zone.normalize, Zone.isBoard]
  have hdv : d ∈ s.inPlayZones := by
    have hmem := hs.dst_mem
    rw [hdn] at hmem ⊢
    unfold GameState.inPlayZones GameState.players
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
    left
    refine ⟨o.controller, ⟨o.controller.n, ?_, rfl⟩, rfl⟩
    exact Zone.lt_of_valid_player hmem
  have hpc : s'.playerCount = s.playerCount := by
    unfold GameState.playerCount
    rw [hs.config]
  have hsame : s'.inPlayZones = s.inPlayZones := by
    unfold GameState.inPlayZones GameState.players
    rw [hpc]
  have hin : s'.inPlay.length = s.inPlay.length := by
    rw [GameState.inPlay_eq_flatMap, GameState.inPlay_eq_flatMap, hsame]
    exact length_flatMap_move s.inPlayZones_nodup s.zone s'.zone src d hz0 hdv u huz
      hs.zone_src (by rw [hs.zone_dst, (Pos.insert_perm _ _ _).length_eq]; simp) hs.ne
      (fun x hx h1 h2 => hs.zone_other h1 h2)
  have hbd : Zone.battlefieldZone ≠ d := by
    rw [hdn]
    intro e
    cases e
  unfold GameState.pot
  by_cases hb : Zone.battlefieldZone = src
  · have hub : u ∈ s.zone Zone.battlefieldZone := by rw [hb]; exact huz
    rw [if_pos hub, hb, hs.zone_src, List.length_erase_of_mem huz]
    have := List.length_pos_of_mem huz
    omega
  · have hnu : u ∉ s.zone Zone.battlefieldZone := fun hmem =>
      ne_of_mem_other_zone hwf huz hmem hb rfl
    rw [if_neg hnu, hs.zone_other hb hbd]
    omega

/-- Recalling a unit in play never raises what goes down. -/
theorem sendHome_pot_le {s : GameState} (hwf : s.WF) {u : ObjId} (hu : u ∈ s.inPlay) :
    (sendHome s u).1.pot ≤ s.pot := by
  unfold sendHome
  cases ho : s.obj? u with
  | none => exact Nat.le_refl _
  | some o =>
    simp only
    cases hm : moveObj s u (.player o.controller .base) with
    | none => exact Nat.le_refl _
    | some r =>
      obtain ⟨s', id'⟩ := r
      simp only
      rw [pot_modObj]
      have := sendHome_core hwf hu ho hm
      omega

/-- Recalling a unit from the Battlefield Zone lowers what goes down. -/
theorem sendHome_pot_lt {s : GameState} (hwf : s.WF) {u : ObjId}
    (hb : u ∈ s.zone Zone.battlefieldZone)
    (hc : ∀ o, s.obj? u = some o → o.controller.n < s.playerCount) :
    (sendHome s u).1.pot < s.pot := by
  have hu : u ∈ s.inPlay := by
    rw [GameState.inPlay_eq_flatMap]
    exact List.mem_flatMap.mpr ⟨Zone.battlefieldZone, by simp [GameState.inPlayZones], hb⟩
  obtain ⟨o, ho⟩ := GameState.obj_of_mem hwf hb
  obtain ⟨r, hr⟩ := moveObj_isSome hwf hb (.player o.controller .base) .top (by
    intro o' ho'
    rw [ho] at ho'
    cases ho'
    refine ⟨?_, ?_⟩
    · simp only [Zone.normalize, Zone.isBoard]
      exact Zone.valid_player (hc o ho) _
    · simp only [Zone.normalize, Zone.isBoard]
      intro h
      cases h)
  obtain ⟨s', id'⟩ := r
  unfold sendHome
  rw [ho]
  simp only [hr]
  rw [pot_modObj]
  have := sendHome_core hwf hu ho hr
  rw [if_pos hb] at this
  omega

/-- Killing the Equipment of a unit that is saved, and healing, exhausting and recalling the unit,
takes something out of play. -/
theorem saveUnit_pot_lt {s : GameState} (hwf : s.WF) {u g : ObjId} (hug : u ≠ g)
    (hu : u ∈ s.inPlay) (hg : g ∈ s.inPlay)
    (hov : ∀ o, s.obj? g = some o → o.owner.n < s.playerCount) :
    (saveUnit s u (some g)).1.pot < s.pot := by
  have h1 := killObj_pot_lt hwf hov hg
  have hwf1 : (killObj s g).1.WF := (killObj_safe s g).wf hwf
  have hu1 : u ∈ (killObj s g).1.inPlay := killObj_mem_inPlay_ne hwf hug hu hov hg
  have h2 : ((killObj s g).1.modObj u (fun o => { o with damage := 0 })).pot =
      (killObj s g).1.pot := pot_modObj _ _ _
  have hu2 : u ∈ ((killObj s g).1.modObj u (fun o => { o with damage := 0 })).inPlay := by
    rw [inPlay_modObj]; exact hu1
  have hwf2 : ((killObj s g).1.modObj u (fun o => { o with damage := 0 })).WF :=
    GameState.wf_modObj hwf1 _ _
  have h3 := sendHome_pot_le hwf2 hu2
  unfold saveUnit recallFx
  dsimp only
  simp only [if_true, setExhausted_pot]
  omega

/-- Saving a unit with no Equipment to die instead (Soraka), healing, exhausting and recalling it
from the Battlefield Zone, lowers what goes down. -/
theorem saveUnit_none_pot_lt {s : GameState} (hwf : s.WF) {u : ObjId}
    (hb : u ∈ s.zone Zone.battlefieldZone)
    (hc : ∀ o, s.obj? u = some o → o.controller.n < s.playerCount) :
    (saveUnit s u none).1.pot < s.pot := by
  have hwf2 : (s.modObj u (fun o => { o with damage := 0 })).WF := GameState.wf_modObj hwf _ _
  have hb2 : u ∈ (s.modObj u (fun o => { o with damage := 0 })).zone Zone.battlefieldZone := by
    rw [GameState.zone_modObj]; exact hb
  have hc2 : ∀ o, (s.modObj u (fun o => { o with damage := 0 })).obj? u = some o →
      o.controller.n < s.playerCount := by
    intro o ho
    rcases obj?_modObj_cases s u (fun o => { o with damage := 0 }) u with h | ⟨o', h1, h2⟩
    · rw [h] at ho; exact hc o ho
    · rw [h2] at ho
      cases ho
      exact hc o' h1
  have h3 := sendHome_pot_lt hwf2 hb2 hc2
  unfold saveUnit recallFx
  dsimp only
  simp only [if_true, setExhausted_pot]
  rw [pot_modObj] at h3
  exact h3

/-- A zone of a well-formed game holds each object once. -/
theorem zone_nodup {s : GameState} (hwf : s.WF) {z : Zone} (hz : z ∈ allZones s.playerCount) :
    (s.zone z).Nodup := by
  have h := (flatMap_split (allZones s.playerCount) s.zone z hz).nodup_iff.mp hwf.nodup
  exact (List.nodup_append.mp h).1

/-- The token that is off the Board is in a zone of the game that is not on the Board. -/
theorem offBoardToken_zone {s : GameState} {id : ObjId} (h : s.offBoardToken = some id) :
    ∃ z, z ∈ allZones s.playerCount ∧ z.isBoard = false ∧ id ∈ s.zone z ∧
      s.isTok id = true := by
  unfold GameState.offBoardToken at h
  obtain ⟨l1, z, l2, hl, hf, -⟩ := List.findSome?_eq_some_iff.mp h
  have hz : z ∈ allZones s.playerCount := by rw [hl]; simp
  by_cases hb : z.isBoard = true
  · simp [hb] at hf
  · have hb' : z.isBoard = false := by simpa using hb
    simp only [hb, ite_false] at hf
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    refine ⟨z, hz, hb', hm, ?_⟩
    unfold GameState.isTok
    exact hp

/-- Removing an object does not change what the others are. -/
theorem obj?_removed {s : GameState} {id y : ObjId} (h : y.n ≠ id.n) (z : Zone) (l : List ObjId) :
    ({ s.setZone z l with objects := s.objects.erase id.n } : GameState).obj? y = s.obj? y := by
  unfold GameState.obj?
  have : ¬ compare id.n y.n = .eq := fun e => h (Nat.compare_eq_eq.mp e).symm
  simp [Std.ExtTreeMap.getElem?_erase, this]

/-- Removing a token that is off the Board leaves fewer tokens off the Board and the same objects
in play (I12a). -/
theorem tokenStep_lt {s s' : GameState} {es : List Event} (hwf : s.WF)
    (h : tokenStep s = some (s', es)) :
    MeasLt s'.cleanupMeasure s.cleanupMeasure := by
  unfold tokenStep at h
  cases hoff : s.offBoardToken with
  | none => simp [hoff] at h
  | some id =>
    simp only [hoff, Option.map_eq_some_iff] at h
    obtain ⟨s1, hrm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨z, hz, hnb, hidz, hid⟩ := offBoardToken_zone hoff
    obtain ⟨z', hz', hidz', rfl⟩ := removeObj_spec hrm
    have hzz : z' = z := by
      have h1 := GameState.locate_eq hwf hz hidz
      have h2 := GameState.locate_eq hwf hz' hidz'
      exact Option.some.inj (h2.symm.trans h1)
    subst hzz
    -- the Board is untouched
    have hin : ({ s.setZone z' ((s.zone z').erase id) with objects := s.objects.erase id.n } :
        GameState).inPlay = s.inPlay := by
      rw [GameState.inPlay_eq_flatMap, GameState.inPlay_eq_flatMap]
      have hpc : ({ s.setZone z' ((s.zone z').erase id) with objects := s.objects.erase id.n } :
          GameState).inPlayZones = s.inPlayZones := rfl
      rw [hpc]
      apply flatMap_congr_mem
      intro x hx
      have hxz : x ≠ z' := by
        intro e
        subst e
        unfold GameState.inPlayZones at hx
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
        rcases hx with ⟨p, -, rfl⟩ | rfl <;> simp [Zone.isBoard, ZoneKind.isBoard] at hnb
      exact GameState.zone_setZone_ne s hxz _
    have hlt : ({ s.setZone z' ((s.zone z').erase id) with objects := s.objects.erase id.n } :
        GameState).tokC < s.tokC := by
      obtain ⟨s1, hs1⟩ : ∃ s1 : GameState, s1 =
          { s.setZone z' ((s.zone z').erase id) with
            objects := s.objects.erase id.n } := ⟨_, rfl⟩
      rw [← hs1]
      have hisTok : ∀ y : ObjId, y ≠ id → s1.isTok y = s.isTok y := by
        intro y hy
        have hn : y.n ≠ id.n := fun e => hy (objId_eq_of_n e)
        unfold GameState.isTok
        rw [hs1]
        exact congrArg _ (obj?_removed hn _ _)
      unfold GameState.tokC
      have hnbz : s1.nbZones = s.nbZones := by rw [hs1]; rfl
      rw [hnbz]
      have hnd : s.nbZones.Nodup := by
        unfold GameState.nbZones
        exact List.Pairwise.sublist (List.filter_sublist) (allZones_nodup _)
      have hmem : z' ∈ s.nbZones := by
        unfold GameState.nbZones
        simp [List.mem_filter, hz', hnb]
      have hu : id ∈ (s.zone z').filter (fun x => s.isTok x) :=
        List.mem_filter.mpr ⟨hidz', hid⟩
      have hg : (s1.zone z').filter (fun x => s1.isTok x) =
          ((s.zone z').filter (fun x => s.isTok x)).erase id := by
        have hz1 : s1.zone z' = (s.zone z').erase id := by
          rw [hs1]; exact GameState.zone_setZone_self s z' _
        rw [hz1, ← filter_erase_of_true _ _ _ hid]
        apply List.filter_congr
        intro x hx
        have hxid : x ≠ id := ((List.Nodup.mem_erase_iff (zone_nodup hwf hz')).mp hx).1
        rw [hisTok x hxid]
      have hrest : ∀ x ∈ s.nbZones, x ≠ z' →
          (s1.zone x).filter (fun y => s1.isTok y) = (s.zone x).filter (fun y => s.isTok y) := by
        intro x _ hxz
        have hx1 : s1.zone x = s.zone x := by
          rw [hs1]; exact GameState.zone_setZone_ne s hxz _
        rw [hx1]
        apply List.filter_congr
        intro y hy
        rw [hisTok y (ne_of_mem_other_zone hwf hidz' hy hxz)]
      have key := length_flatMap_erase_one hnd (fun z => (s.zone z).filter (fun x => s.isTok x))
        (fun z => (s1.zone z).filter (fun x => s1.isTok x)) z' hmem id hu hg hrest
      omega
    have hbz : Zone.battlefieldZone ≠ z' := by
      intro e
      rw [← e] at hnb
      simp [Zone.isBoard] at hnb
    have hbf : ({ s.setZone z' ((s.zone z').erase id) with objects := s.objects.erase id.n } :
        GameState).zone Zone.battlefieldZone = s.zone Zone.battlefieldZone :=
      GameState.zone_setZone_ne s hbz _
    exact MeasLt.at2 (by unfold GameState.pot; rw [hin, hbf]) hlt

/-- The Battlefield the Cleanup makes Contested is one of the game's, newly Contested. -/
theorem findSome_newContest {s : GameState} {b : ObjId} {q : PlayerId}
    (h : s.battlefields.findSome? (fun b => (s.newContest b).map (fun q => (b, q))) = some (b, q)) :
    b ∈ s.battlefields ∧ s.newContest b = some q := by
  obtain ⟨l1, a, l2, hl, hf, -⟩ := List.findSome?_eq_some_iff.mp h
  have ha : a ∈ s.battlefields := by rw [hl]; simp
  cases hn : s.newContest a with
  | none => simp [hn] at hf
  | some q' =>
    simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨ha, hn⟩

/-- Every step of the Cleanup makes the measure go down (I12a). -/
theorem cleanupStep0_lt {s s' : GameState} {es : List Event} (hwf : s.WF)
    (h : cleanupStep0 s = some (s', es)) : MeasLt s'.cleanupMeasure s.cleanupMeasure := by
  unfold cleanupStep0 at h
  split at h
  · rename_i u hu
    obtain rfl : s' = (cleanupKill s u).1 := (congrArg Prod.fst (Option.some.inj h)).symm
    have hl := List.find?_some hu
    simp only [Bool.and_eq_true] at hl
    have hmem := List.mem_of_find?_eq_some hu
    unfold cleanupKill
    split
    · rename_i g hg
      split
      · rename_i hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Option.any_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hne, o, ho, hlt⟩ := hc
        exact MeasLt.at1 (saveUnit_pot_lt hwf (Ne.symm hne) hmem (deathSaver_mem hg)
          (fun o' ho' => by rw [ho] at ho'; cases ho'; exact hlt))
      · exact MeasLt.at1 (killObj_pot_lt hwf (lethal_owner hl.2) hmem)
    · split
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at hc
        obtain ⟨hb, o, ho, hlt⟩ := hc
        exact MeasLt.at1 (saveUnit_none_pot_lt hwf hb
          (fun o' ho' => by rw [ho] at ho'; cases ho'; exact hlt))
      · exact MeasLt.at1 (killObj_pot_lt hwf (lethal_owner hl.2) hmem)
    · exact MeasLt.at1 (killObj_pot_lt hwf (lethal_owner hl.2) hmem)
  · split at h
    · rename_i b hb
      obtain rfl : s' = s.modObj b (fun o => { o with control := none }) :=
        (congrArg Prod.fst (Option.some.inj h)).symm
      exact lostControl_lt (List.mem_of_find?_eq_some hb) (List.find?_some hb)
    · split at h
      · rename_i b hb
        obtain rfl : s' = s.modObj b (fun o => { o with contested := none }) :=
          (congrArg Prod.fst (Option.some.inj h)).symm
        exact staleContest_lt (List.mem_of_find?_eq_some hb) (List.find?_some hb)
      · split at h
        · rename_i b q hbq
          obtain rfl : s' = s.modObj b (fun o => { o with contested := some q }) :=
            (congrArg Prod.fst (Option.some.inj h)).symm
          obtain ⟨hmem, hq⟩ := findSome_newContest hbq
          exact newContest_lt hmem hq
        · exact absurd h (by simp)

/-- Every step of the Cleanup makes the measure go down (I12a). -/
theorem cleanupStep_lt {s s' : GameState} {es : List Event} (hwf : s.WF)
    (h : cleanupStep s = some (s', es)) : MeasLt s'.cleanupMeasure s.cleanupMeasure := by
  unfold cleanupStep at h
  split at h
  · rename_i r hr
    obtain rfl : s' = r.1 := (congrArg Prod.fst (Option.some.inj h)).symm
    exact tokenStep_lt hwf hr
  · split at h
    · rename_i r hr
      obtain rfl : s' = r.1 := (congrArg Prod.fst (Option.some.inj h)).symm
      exact detachStep_lt hr
    · exact cleanupStep0_lt hwf h

/-- The Cleanup moves from a state to the next one. -/
def CleanupRel (s' s : GameState) : Prop := ∃ es, cleanupStep s = some (s', es)

theorem cleanup_acc_aux : ∀ (m : Nat × Nat × Nat × Nat × Nat × Nat) (s : GameState),
    s.cleanupMeasure = m → s.WF → Acc CleanupRel s := by
  intro m
  refine MeasLt.wf.induction (C := fun m => ∀ s : GameState, s.cleanupMeasure = m → s.WF →
    Acc CleanupRel s) m ?_
  intro m ih s hm hwf
  refine Acc.intro s (fun s' hs' => ?_)
  obtain ⟨es, h⟩ := hs'
  exact ih s'.cleanupMeasure (hm ▸ cleanupStep_lt hwf h) s' rfl ((cleanupStep_safe h).wf hwf)

/-- **I12a: the Cleanup stops.** In a well-formed game where every owner is a player, the steps of
the Cleanup (CR 323) cannot go on for ever: after a finite number of them none applies. -/
theorem cleanup_terminates {s : GameState} (hwf : s.WF) : Acc CleanupRel s :=
  cleanup_acc_aux _ s rfl hwf

/-- No infinite run of Cleanup steps starts in such a game. -/
theorem cleanup_no_infinite_run {f : Nat → GameState} (hwf : (f 0).WF)
    (hstep : ∀ n, CleanupRel (f (n + 1)) (f n)) : False := by
  have key : ∀ s : GameState, Acc CleanupRel s → ∀ n, f n = s → False := by
    intro s hs
    induction hs with
    | intro s _ ih => exact fun n hn => ih (f (n + 1)) (hn ▸ hstep n) (n + 1) rfl
  exact key (f 0) (cleanup_terminates hwf) 0 rfl

end Riftbound

end
