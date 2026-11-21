module

public import Riftbound.Rules.Objects

/-!
# Choosing objects

What a Spell can choose when it is played, and which objects a selector of an effect stands for
when it resolves (CR 355, 340) (design.md §7.2). A target is chosen among the objects in play that
match the declaration of the choice. The selector of an effect names objects by the slot of a
choice, by a variable, or as all that match.

Only what can be read from the printed card and the attributes of the object is understood:
the type, supertype, tag, name, keyword, domain and printed Might of the card, and whether the
object is exhausted, ready, damaged, or another one. A filter or a place that is not understood
yet makes the question unanswerable (`none`), never a guess.

Also here: the changes of the board that effects make from the objects they select (`Safe`):
each keeps the game well formed, the physical cards and `OwnerOk`.
-/

@[expose] public section

namespace Riftbound

namespace GameState

/-- The definition of the card an object is. -/
def cardDef? (s : GameState) (c : ObjId) : Option CardDef :=
  match s.obj? c with
  | some o =>
    match o.kind with
    | .card _ id => s.cards.find? id
    | .token id => s.cards.find? id
    | .chainAbility .. => none
  | none => none

/-- The players of the game, in seat order. -/
def players (s : GameState) : List PlayerId := (List.range s.playerCount).map (fun i => ⟨i⟩)

/-- The objects in play: the Bases of the players, then the Battlefield Zone. -/
def inPlay (s : GameState) : List ObjId :=
  s.players.flatMap (fun p => s.zone (.player p .base)) ++ s.zone .battlefieldZone

/-- The XP of a player (CR 728): kept with their Legend. -/
def xpOf (s : GameState) (p : PlayerId) : Nat :=
  ((s.zone (.player p .legendZone)).map (fun l => ((s.obj? l).map (·.xp)).getD 0)).sum

/-- The Might an object has: the printed Might and the lasting changes effects made to it
(CR 475-478). The abilities that change Might as long as a condition holds come with the full
Layers (roadmap.md, M6). -/
def mightOf (s : GameState) (id : ObjId) : Option Int :=
  ((s.cardDef? id).bind (·.might)).map (fun m =>
    m + match s.obj? id with
      | some o => (o.mightMods.map (·.amount)).sum
      | none => 0)

end GameState

/-- The comparison of two numbers. -/
def Cmp.holds : Cmp → Int → Int → Bool
  | .eq, a, b => a == b
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)

/-- The players a selector of players names, seen by `self`. `none` if it cannot be known yet. -/
def PlayerSel.resolve (s : GameState) (self : PlayerId) : PlayerSel → Option (List PlayerId)
  | .you => some [self]
  | .opponent => (s.players.filter (· ≠ self)).head?.map (fun o => [o])
  | .eachPlayer => some s.players
  | .eachOpponent => some (s.players.filter (· ≠ self))
  | .chosen _ => none
  | .eventPlayer => none

/-- The number an amount stands for, if it can be computed from the variables alone. -/
def Amount.eval (env : Env) : Amount → Option Nat
  | .const n => some n
  | .var v =>
    match env.lookup v with
    | some (.int i) => some i.toNat
    | _ => none
  | .add a b => do pure ((← Amount.eval env a) + (← Amount.eval env b))
  | .sub a b => do pure ((← Amount.eval env a) - (← Amount.eval env b))
  | .mul a b => do pure ((← Amount.eval env a) * (← Amount.eval env b))
  | .min a b => do pure (Nat.min (← Amount.eval env a) (← Amount.eval env b))
  | .max a b => do pure (Nat.max (← Amount.eval env a) (← Amount.eval env b))
  | _ => none

/-- Whether the object has the property, for the properties that are understood. `self` is the
object the effect belongs to. -/
def Filter.holds (s : GameState) (self : ObjId) (env : Env) (id : ObjId) : Filter → Option Bool
  | .ofType t => (s.cardDef? id).map (·.hasType t)
  | .ofSupertype sp => (s.cardDef? id).map (·.hasSupertype sp)
  | .tag t => (s.cardDef? id).map (·.tags.contains t)
  | .named n => (s.cardDef? id).map (fun d => d.name == n)
  | .hasKeyword k => (s.cardDef? id).map (·.hasKeyword k)
  | .domain d => (s.cardDef? id).map (·.domains.contains d)
  | .might op a => do
    let m ← s.mightOf id
    let n ← a.eval env
    pure (op.holds m n)
  | .exhausted => (s.obj? id).map (·.exhausted)
  | .ready => (s.obj? id).map (fun o => !o.exhausted)
  | .damaged => (s.obj? id).map (fun o => decide (0 < o.damage))
  | .notSelf => some (id != self)
  | .stunned => (s.obj? id).map (·.stunned)
  | .buffed => (s.obj? id).map (·.buffed)
  | _ => none

/-- Whether the object has every property of the list. -/
def FilterList.holds (s : GameState) (self : ObjId) (env : Env) (id : ObjId) :
    FilterList → Option Bool
  | .nil => some true
  | .cons f rest => do
    let a ← f.holds s self env id
    let b ← FilterList.holds s self env id rest
    pure (a && b)

/-- The side of an object, seen from player `p`: the controller (CR 740.1). -/
def Side.admits (p : PlayerId) (side : Side) (o : Object) : Bool :=
  match side with
  | .friendly => o.controller == p
  | .enemy => o.controller != p
  | .any => true

/-- The Battlefield an object is "here" at: its own, for a Battlefield, and the one a Unit is at
(CR 106). -/
def GameState.hereOf (s : GameState) (self : ObjId) : Option ObjId :=
  match s.obj? self with
  | some o => if (s.cardDef? self).any (·.hasType .battlefield) then some self else o.loc
  | none => none

/-- The objects a place can hold, if the place is understood. `self` is the object the effect
belongs to: "here" is the Battlefield it is at. -/
def GameState.placeObjs (s : GameState) (self : ObjId) : Place → Option (List ObjId)
  | .anywhere => some s.inPlay
  | .here =>
    (s.hereOf self).map (fun bf =>
      (s.zone .battlefieldZone).filter (fun u => u == bf || (s.obj? u).any (·.loc == some bf)))
  | .atBase => some (s.players.flatMap (fun p => s.zone (.player p .base)))
  | .atBattlefield => some (s.zone .battlefieldZone)
  | _ => none

/-- Whether an object is on the side and has the properties. -/
def GameState.matchesOne (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) (side : Side)
    (fs : FilterList) (id : ObjId) : Option Bool :=
  match s.obj? id with
  | some o => if side.admits p o then fs.holds s self env id else some false
  | none => some false

/-- Keep the objects of the list that are on the side and have the properties. -/
def GameState.keepMatching (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) (side : Side)
    (fs : FilterList) : List ObjId → Option (List ObjId)
  | [] => some []
  | id :: rest => do
    let ok ← s.matchesOne p self env side fs id
    let tl ← s.keepMatching p self env side fs rest
    pure (if ok then id :: tl else tl)

/-- The objects of a side at a place that have the properties, seen from player `p`. -/
def GameState.candidates (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) (side : Side)
    (place : Place) (fs : FilterList) : Option (List ObjId) := do
  let objs ← s.placeObjs self place
  s.keepMatching p self env side fs objs

/-- A member of the answer is a member of the list that was filtered. -/
theorem GameState.mem_keepMatching {s : GameState} {p : PlayerId} {self : ObjId} {env : Env}
    {side : Side} {fs : FilterList} {l r : List ObjId}
    (h : s.keepMatching p self env side fs l = some r) : ∀ x ∈ r, x ∈ l := by
  induction l generalizing r with
  | nil =>
    simp only [keepMatching, Option.some.injEq] at h
    subst h; simp
  | cons id rest ih =>
    intro x hx
    simp only [keepMatching] at h
    cases hok : s.matchesOne p self env side fs id with
    | none => simp [hok] at h
    | some ok =>
      cases htl : s.keepMatching p self env side fs rest with
      | none => simp [hok, htl] at h
      | some tl =>
        simp only [hok, htl] at h
        have h' : (some (if ok = true then id :: tl else tl) : Option (List ObjId)) = some r := h
        have hr := Option.some.inj h'
        subst hr
        cases ok
        · exact List.mem_cons_of_mem _ (ih htl x hx)
        · simp only [ite_true] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih htl x hx)

/-- A candidate is in play when the place is a place of the board. -/
theorem GameState.mem_placeObjs {s : GameState} {self : ObjId} {pl : Place} {l : List ObjId}
    (h : s.placeObjs self pl = some l) : ∀ x ∈ l, x ∈ s.inPlay := by
  intro x hx
  cases pl with
  | anywhere =>
    simp only [placeObjs, Option.some.injEq] at h
    subst h; exact hx
  | here =>
    simp only [placeObjs] at h
    obtain ⟨bf, -, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold inPlay
    exact List.mem_append_right _ (List.mem_filter.mp hx).1
  | atBattlefield =>
    simp only [placeObjs, Option.some.injEq] at h
    subst h
    unfold inPlay
    exact List.mem_append_right _ hx
  | atBase =>
    simp only [placeObjs, Option.some.injEq] at h
    subst h
    unfold inPlay
    exact List.mem_append_left _ hx
  | inHand => simp [placeObjs] at h
  | inTrash => simp [placeObjs] at h
  | inMainDeck => simp [placeObjs] at h
  | inRuneDeck => simp [placeObjs] at h
  | inCombat => simp [placeObjs] at h

/-- The objects a candidate list can hold are objects in play. -/
theorem GameState.mem_candidates {s : GameState} {p : PlayerId} {self : ObjId} {env : Env}
    {side : Side} {place : Place} {fs : FilterList} {r : List ObjId}
    (h : s.candidates p self env side place fs = some r) : ∀ x ∈ r, x ∈ s.inPlay := by
  unfold candidates at h
  cases hp : s.placeObjs self place with
  | none => simp [hp] at h
  | some objs =>
    simp only [hp] at h
    exact fun x hx => GameState.mem_placeObjs hp x (GameState.mem_keepMatching h x hx)

/-- The objects a selector stands for when an effect resolves, seen by `p`, for the object `self`.
A chosen object that has left play is nothing (CR 340): the selector stands for no object.
`none` if the selector cannot be answered yet. -/
def Selector.eval (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) :
    Selector → Option (List ObjId)
  | .self => some [self]
  | .slot i =>
    match env.slots[i]? with
    | some (.obj o) => some (if o ∈ s.inPlay then [o] else [])
    | _ => none
  | .var v =>
    match env.lookup v with
    | some (.obj o) => some (if o ∈ s.inPlay then [o] else [])
    | _ => none
  | .it =>
    match env.it with
    | some o => some (if o ∈ s.inPlay then [o] else [])
    | none => none
  | .pick .all side place fs => s.candidates p self env side place fs
  | _ => none

/-- The number an amount stands for, reading the game: the count of the objects a selector stands
for, the size of a hand, and the arithmetic of these. `none` if it cannot be known yet. -/
def Amount.evalS (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) : Amount → Option Nat
  | .count sel => (sel.eval s p self env).map List.length
  | .xp => some (s.xpOf p)
  | .handSize ps => do
    let l ← ps.resolve s p
    pure ((l.map (fun q => (s.zone (.player q .hand)).length)).foldl (· + ·) 0)
  | .add a b => do pure ((← Amount.evalS s p self env a) + (← Amount.evalS s p self env b))
  | .sub a b => do pure ((← Amount.evalS s p self env a) - (← Amount.evalS s p self env b))
  | .mul a b => do pure ((← Amount.evalS s p self env a) * (← Amount.evalS s p self env b))
  | .min a b =>
    do pure (Nat.min (← Amount.evalS s p self env a) (← Amount.evalS s p self env b))
  | .max a b =>
    do pure (Nat.max (← Amount.evalS s p self env a) (← Amount.evalS s p self env b))
  | a => a.eval env

/-- Whether a question about the game is true, for the questions that are understood. `none` if it
cannot be answered yet. -/
def Condition.eval (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) :
    Condition → Option Bool
  | .always => some true
  | .not c => (Condition.eval s p self env c).map (fun b => !b)
  | .and a b => do pure ((← Condition.eval s p self env a) && (← Condition.eval s p self env b))
  | .or a b => do pure ((← Condition.eval s p self env a) || (← Condition.eval s p self env b))
  | .cmp op a b => do
    let x ← a.evalS s p self env
    let y ← b.evalS s p self env
    pure (op.holds x y)
  | .exists sel => (sel.eval s p self env).map (fun l => !l.isEmpty)
  | .matches sel f => do
    let ids ← sel.eval s p self env
    let bs ← ids.mapM (fun id => f.holds s self env id)
    pure (!ids.isEmpty && bs.all id)
  | .yourTurn => some (decide (s.active = some p))
  | _ => none

/-- The objects a choice of a Spell can pick: for a target of exactly one object, the matching
objects in play. Nothing for a choice that is not understood yet. -/
def Choice.candidates (s : GameState) (p : PlayerId) (self : ObjId) : Choice → List ObjId
  | .target .one side place fs => (s.candidates p self {} side place fs).getD []
  | _ => []

/-- Whether a choice is one that a Spell can make for now: one target. -/
def Choice.simple : Choice → Bool
  | .target .one _ _ _ => true
  | _ => false

/-- The objects chosen are a legal pick for the choices, one for each. -/
def targetsOk (s : GameState) (p : PlayerId) (self : ObjId) : List Choice → List ObjId → Bool
  | [], [] => true
  | c :: cs, t :: ts => c.simple && decide (t ∈ c.candidates s p self) && targetsOk s p self cs ts
  | _, _ => false

/-- Every legal pick for the choices. -/
def targetTuples (s : GameState) (p : PlayerId) (self : ObjId) : List Choice → List (List ObjId)
  | [] => [[]]
  | c :: cs =>
    if c.simple then
      (c.candidates s p self).flatMap (fun t => (targetTuples s p self cs).map (t :: ·))
    else []

/-- The picks listed are exactly the legal ones. -/
theorem mem_targetTuples (s : GameState) (p : PlayerId) (self : ObjId) :
    ∀ (cs : List Choice) (ts : List ObjId),
      ts ∈ targetTuples s p self cs ↔ targetsOk s p self cs ts = true
  | [], ts => by
    cases ts <;> simp [targetTuples, targetsOk]
  | c :: cs, [] => by
    simp only [targetTuples, targetsOk]
    split <;> simp
  | c :: cs, t :: ts => by
    simp only [targetTuples, targetsOk, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hs : c.simple = true
    · simp only [hs, ite_true, List.mem_flatMap, List.mem_map, List.cons.injEq, true_and]
      constructor
      · rintro ⟨t', ht', ts', hts', rfl, rfl⟩
        exact ⟨ht', (mem_targetTuples s p self cs ts').mp hts'⟩
      · rintro ⟨ht, hts⟩
        exact ⟨t, ht, ts, (mem_targetTuples s p self cs ts).mpr hts, rfl, rfl⟩
    · simp [hs]

/-- Every object chosen is in play. -/
theorem targetsOk_mem_inPlay {s : GameState} {p : PlayerId} {self : ObjId} :
    ∀ {cs : List Choice} {ts : List ObjId}, targetsOk s p self cs ts = true →
      ∀ t ∈ ts, t ∈ s.inPlay
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [targetsOk] at h
  | _ :: _, [], h => by simp [targetsOk] at h
  | c :: cs, t :: ts, h => by
    simp only [targetsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hs, ht⟩, hrest⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · cases c with
      | target q side place fs =>
        cases q <;> simp [Choice.simple] at hs
        simp only [Choice.candidates] at ht
        cases hc : s.candidates p self {} side place fs with
        | none => simp [hc] at ht
        | some r =>
          simp only [hc, Option.getD_some] at ht
          exact GameState.mem_candidates hc x ht
      | mode _ => simp [Choice.simple] at hs
      | xValue => simp [Choice.simple] at hs
      | extraCost _ _ => simp [Choice.simple] at hs
    · exact targetsOk_mem_inPlay hrest x hx

/-- A change of the board that the invariants survive: it keeps the game well formed, the physical
cards, and `OwnerOk`, and changes only objects, zones and counters. -/
structure Safe (s s' : GameState) : Prop where
  /-- Well formed. -/
  wf : s.WF → s'.WF
  /-- The physical cards. -/
  phys : s.WF → s'.physIds.Perm s.physIds
  /-- `OwnerOk`. -/
  own : s.WF → s.OwnerOk → s'.OwnerOk
  /-- Only objects, zones and counters change. -/
  same : SameMeta s s'

namespace Safe

/-- No change. -/
theorem refl (s : GameState) : Safe s s :=
  ⟨id, fun _ => List.Perm.refl _, fun _ h => h, SameMeta.refl s⟩

/-- One change after another. -/
theorem trans {s s' s'' : GameState} (h1 : Safe s s') (h2 : Safe s' s'') : Safe s s'' :=
  ⟨fun h => h2.wf (h1.wf h), fun h => (h2.phys (h1.wf h)).trans (h1.phys h),
    fun h ho => h2.own (h1.wf h) (h1.own h ho), h1.same.trans h2.same⟩

/-- A change of one object that keeps its kind and its owner. -/
theorem modObj (s : GameState) (id : ObjId) {f : Object → Object}
    (hk : ∀ o, (f o).kind = o.kind) (ho : ∀ o, (f o).owner = o.owner) :
    Safe s (s.modObj id f) :=
  ⟨fun h => GameState.wf_modObj h id f, fun _ => by rw [GameState.physIds_modObj s id hk],
    fun _ h => GameState.ownerOk_modObj h id ho, GameState.sameMeta_modObj s id f⟩

/-- Moving an object. -/
theorem moveObj {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    (h : Riftbound.moveObj s id dst pos = some (s', id')) : Safe s s' :=
  ⟨fun hwf => moveObj_wf hwf h, fun hwf => moveObj_physIds hwf h,
    fun hwf hown => moveObj_ownerOk hwf hown h,
    (moveObj_spec h).choose_spec.choose_spec.other⟩

end Safe

end Riftbound

end
