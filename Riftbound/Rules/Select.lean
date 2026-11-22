module

public import Riftbound.Rules.Objects
public import Riftbound.Rules.Pay

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

/-- What the Equipment attached to an object adds to its Might: the Might bonus of each (CR 137). -/
def GameState.equipBonus (s : GameState) (id : ObjId) : Int :=
  (s.inPlay.filterMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d => if o.attached == some id then d.mightBonus else none
    | _, _ => none)).sum

/-- The Units of the player that are at the Battlefield. -/
def GameState.unitsAtOf (s : GameState) (bf : ObjId) (p : PlayerId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun u => (s.obj? u).any (fun o => o.loc == some bf &&
    o.controller == p) && (s.cardDef? u).any (·.hasType .unit))

/-- The Combat that is going on: its Battlefield and its Attacker. It goes on from the moment it
starts (CR 466) to its end (CR 468): the frames of the Combat are on the stack. -/
def GameState.combatNow (s : GameState) : Option (ObjId × PlayerId) :=
  s.pending.findSome? (fun f =>
    match f with
    | .showdown bf _ _ =>
      -- the Showdown of a Combat: Units of at least two players are at the Battlefield (CR 464);
      -- the Attacker is the player who made it Contested (CR 466)
      if 2 ≤ (s.players.filter (fun p => !(s.unitsAtOf bf p).isEmpty)).length then
        some (bf, ((s.obj? bf).bind (·.contested)).getD (s.active.getD ⟨0⟩))
      else none
    | .combatDamage bf att => some (bf, att)
    | .assign bf att _ _ _ => some (bf, att)
    | .combatResolve bf att => some (bf, att)
    | _ => none)

/-- The player has played a card of the kind since the timestamp counter was `stamp`. -/
def GameState.playedSince (s : GameState) (p : PlayerId) (t : CardType) (stamp : Nat) : Bool :=
  s.objects.toList.any (fun (k, o) =>
    o.owner == p && (o.playedStamp.any (fun x => decide (stamp ≤ x))) &&
      (s.cardDef? ⟨k⟩).any (·.hasType t))

/-- The player has played a card this turn other than the object `self`. -/
def GameState.playedOther (s : GameState) (p : PlayerId) (self : ObjId) : Bool :=
  s.objects.toList.any (fun (k, o) => o.owner == p && o.playedTurn == some s.turn && k != self.n)

/-- The lasting effects of the turn that are the player's and still wait: for "the next" card of
a kind, no card of the kind has been played since. -/
def GameState.fxOf (s : GameState) (p : PlayerId) : List TurnEffect :=
  (s.turnFx.filter (fun f =>
    f.turn == s.turn && f.who == p &&
      (match f.kind with
        | .nextSpellCostMinus _ | .nextUnitReady => !s.playedSince p f.kind.playType f.stamp
        | _ => true))).map (·.kind)

/-- Units the player plays now enter ready, by an effect of the turn. -/
def GameState.readyByFx (s : GameState) (p : PlayerId) : Bool :=
  (s.fxOf p).any (fun k => k == .nextUnitReady || k == .unitsReady)

/-- The Energy less the next spell of the player costs, by the effects of the turn. -/
def GameState.spellCutFx (s : GameState) (p : PlayerId) : List Nat :=
  (s.fxOf p).filterMap (fun k => match k with | .nextSpellCostMinus n => some n | _ => none)

/-- A unit that takes damage is killed, by an effect of this turn that is about every unit or about
this one. -/
def GameState.killOnHit (s : GameState) (id : ObjId) : Bool :=
  s.turnFx.any (fun f => f.turn == s.turn && f.kind == .killOnDamage &&
    (f.target.isNone || f.target == some id))

/-- The Bonus Damage a turn effect gives to the next spell. -/
def TurnEffect.spellBonusOf : TurnEffect → Nat
  | .nextSpellBonus n => n
  | _ => 0

/-- The Bonus Damage the spell `src` of the player deals with each instance of damage: that of an
effect of the turn for the next spell the player plays (the first spell they played since it was
made). -/
def GameState.spellBonus (s : GameState) (p : PlayerId) (src : ObjId) : Nat :=
  match s.obj? src, (s.cardDef? src).any (·.hasType .spell) with
  | some o, true =>
    (match o.playedStamp with
      | some st =>
        (s.turnFx.filter (fun f => f.turn == s.turn && f.who == p && f.stamp ≤ st &&
          -- no spell of the player was played between the effect and this one
          !(s.objects.toList.any (fun (k, x) =>
            x.owner == p && (s.cardDef? ⟨k⟩).any (·.hasType .spell) &&
              x.playedStamp.any (fun y => f.stamp ≤ y && y < st))))).foldl
          (fun acc f => acc + f.kind.spellBonusOf) 0
      | none => 0)
  | _, _ => 0

/-- The player cannot play cards now, by an effect of this turn that is an opponent's. -/
def GameState.cantPlay (s : GameState) (p : PlayerId) : Bool :=
  s.turnFx.any (fun f => f.turn == s.turn && f.kind == .opponentsCantPlay && f.who != p)

/-- Spells and abilities deal no damage, by an effect of this turn. -/
def GameState.damageOff (s : GameState) : Bool :=
  s.turnFx.any (fun f => f.turn == s.turn && f.kind == .preventEffectDamage)

/-- What the buff of a unit adds to its Might: +1, and +1 more for each effect of the turn that
makes buffs give more (CR 701). Nothing for a unit that is not buffed. -/
def GameState.buffBonus (s : GameState) (id : ObjId) : Int :=
  match s.obj? id with
  | some o =>
    if o.buffed then
      1 + (((s.fxOf o.controller).filter (fun k => k == .buffsExtraMight)).length : Int)
    else 0
  | none => 0

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
    let n ← a.eval env
    -- an object without Might (a Battlefield, a Spell) does not have the Might asked for
    -- the buff and the Equipment count (CR 701, 137); a passive ability is not read here, as
    -- the Layers are (`mightNow`) defined after the filters
    match s.mightOf id with
    | some m =>
      let buff : Int := s.buffBonus id
      pure (op.holds (m + s.equipBonus id + buff) n)
    | none => pure false
  | .cost op a => do
    let n ← a.eval env
    let d ← s.cardDef? id
    pure (match d.cost with | some k => op.holds (Int.ofNat k.energy) n | none => false)
  | .powerCost op a => do
    let n ← a.eval env
    let d ← s.cardDef? id
    pure (match d.cost with | some k => op.holds (Int.ofNat k.power.length) n | none => false)
  | .exhausted => (s.obj? id).map (·.exhausted)
  | .hideRoom =>
    some (decide ((s.players.flatMap (fun q => s.zone (.player q .hidden))).countP
      (fun h => (s.obj? h).any (·.hiddenAt == some id)) <
        if ((s.cardDef? id).map (·.fullAbilities)).getD [] |>.any (fun ab =>
            match ab with | .passive _ mods => mods.contains .extraHide | _ => false)
        then 2 else 1))
  | .onBattlefield =>
    (s.obj? id).map (fun o => o.loc.isSome && (s.zone .battlefieldZone).contains id)
  | .ready => (s.obj? id).map (fun o => !o.exhausted)
  | .damaged => (s.obj? id).map (fun o => decide (0 < o.damage))
  | .at_ sel => do
    -- the place the object named by the selector is at: a Battlefield, the Battlefield a Unit is
    -- at, or a Base (the selector is `self`, a chosen object or a variable)
    let d? : Option ObjId := match sel with
      | .self => some self
      | .slot i => match env.slots[i]? with | some (.obj o) => some o | _ => none
      | .var v => match env.lookup v with | some (.obj o) => some o | _ => none
      | _ => none
    let d ← d?
    pure (match s.obj? id with
      | some o =>
        if (s.cardDef? d).any (·.hasType .battlefield) then o.loc == some d
        else
          match s.obj? d with
          | some od => o.loc == od.loc && (od.loc.isSome || o.controller == od.controller)
          | none => false
      | none => false)
  | .lethal =>
    pure (match s.mightOf id, s.obj? id with
      | some m, some o =>
        let buff : Int := s.buffBonus id
        decide (0 < o.damage ∧ m + s.equipBonus id + buff ≤ (o.damage : Int))
      | _, _ => false)
  | .notSelf => some (id != self)
  | .not f => (f.holds s self env id).map (fun b => !b)
  | .top n =>
    some (match s.obj? id with
      | some o =>
        -- one of the first `n` cards of the Main Deck or of the Rune Deck of its owner
        (decide ((s.zone (.player o.owner .mainDeck)).idxOf id < n) &&
          (s.zone (.player o.owner .mainDeck)).contains id) ||
        (decide ((s.zone (.player o.owner .runeDeck)).idxOf id < n) &&
          (s.zone (.player o.owner .runeDeck)).contains id)
      | none => false)
  | .openBf => some (match s.obj? id with | some b => b.control.isNone | none => false)
  | .enemyOccupied =>
    some (match s.obj? self with
      | some me =>
        (s.zone .battlefieldZone).any (fun u => (s.obj? u).any (fun o => o.loc == some id &&
          o.controller != me.controller))
      | none => false)
  | .hidden =>
    some (match s.obj? id with
      | some o => (s.zone (.player o.owner .hidden)).contains id
      | none => false)
  | .movedFromHere =>
    some (match s.obj? id with
      | some o =>
        -- from the Battlefield, or from where the Unit is (its Battlefield, or its Base)
        o.movesTurn == some s.turn &&
          (match s.obj? self with
            | some me =>
              o.prevLoc ==
                (if (s.cardDef? self).any (·.hasType .battlefield) then some self else me.loc)
            | none => false)
      | none => false)
  | .controlledByOpponent =>
    some (match s.obj? id, s.obj? self with
      | some b, some o => b.control.any (fun q => q != o.controller)
      | _, _ => false)
  | .controlled =>
    -- a Battlefield the controller of the object the effect belongs to controls
    some (match s.obj? id, s.obj? self with
      | some b, some o => b.control == some o.controller
      | _, _ => false)
  | .sameAs sel =>
    match sel with
    | .self => some (id == self)
    | .slot i => match env.slots[i]? with | some (.obj o) => some (id == o) | _ => none
    | .var v => match env.lookup v with | some (.obj o) => some (id == o) | _ => none
    | _ => none
  | .stunned => (s.obj? id).map (·.stunned)
  | .buffed => (s.obj? id).map (·.buffed)
  | .mighty =>
    -- Might 5 or more, counting the printed Might, the lasting changes, the buff and the Equipment;
    -- the passive abilities are not read here (they read filters themselves), as for `Filter.might`
    pure (match s.mightOf id with
      | some m =>
        let buff : Int := s.buffBonus id
        decide (5 ≤ m + s.equipBonus id + buff)
      | none => false)
  | .attacker =>
    pure (match s.combatNow, s.obj? id with
      | some (bf, att), some o => o.loc == some bf && o.controller == att
      | _, _ => false)
  | .defender =>
    pure (match s.combatNow, s.obj? id with
      | some (bf, att), some o => o.loc == some bf && o.controller != att
      | _, _ => false)
  | .alone =>
    pure (match s.combatNow, s.obj? id with
      | some (bf, _), some o => o.loc == some bf && (s.unitsAtOf bf o.controller).length == 1
      | _, _ => false)
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
  | .onChain =>
    -- the spells on the Chain, not the effect's own spell (an ability on the Chain is no spell)
    some ((s.zone .chain).filter (fun u =>
      u != self &&
        (s.obj? u).any (fun o => match o.kind with | .chainAbility .. => false | _ => true)))
  | .inCombat =>
    s.combatNow.map (fun (bf, _) =>
      (s.zone .battlefieldZone).filter (fun u => (s.obj? u).any (·.loc == some bf)))
  | _ => none

/-- The zone of a player's cards that a place off the board stands for. -/
def Place.zoneKind? : Place → Option ZoneKind
  | .inHand => some .hand
  | .inTrash => some .trash
  | .inMainDeck => some .mainDeck
  | .inRuneDeck => some .runeDeck
  | .inHidden => some .hidden
  | _ => none

/-- Whether a player is on the side, seen from player `p`. -/
def Side.admitsPlayer (p : PlayerId) (side : Side) (q : PlayerId) : Bool :=
  match side with
  | .friendly => q == p
  | .enemy => q != p
  | .any => true

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

/-- The objects of a side at a place that have the properties, for a choice made while an effect
resolves: also the cards of a player's zone off the board (the hand, the Trash, a deck), which a
target cannot be. -/
def GameState.pickCandidates (s : GameState) (p : PlayerId) (self : ObjId) (env : Env)
    (side : Side) (place : Place) (fs : FilterList) : Option (List ObjId) :=
  match place.zoneKind? with
  | some z =>
    (s.players.filter (fun q => side.admitsPlayer p q)).foldl (fun acc q =>
      acc.bind (fun l => ((s.zone (.player q z)).filterM (fun u =>
        FilterList.holds s self env u fs)).map (fun m => l ++ m))) (some [])
  | none => s.candidates p self env side place fs

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

/-- A candidate is in play when the place is a place of the board, or a spell on the Chain. -/
theorem GameState.mem_placeObjs {s : GameState} {self : ObjId} {pl : Place} {l : List ObjId}
    (h : s.placeObjs self pl = some l) : ∀ x ∈ l, x ∈ s.inPlay ∨ x ∈ s.zone .chain := by
  intro x hx
  cases pl with
  | anywhere =>
    simp only [placeObjs, Option.some.injEq] at h
    subst h; exact Or.inl hx
  | here =>
    simp only [placeObjs] at h
    obtain ⟨bf, -, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold inPlay
    exact Or.inl (List.mem_append_right _ (List.mem_filter.mp hx).1)
  | atBattlefield =>
    simp only [placeObjs, Option.some.injEq] at h
    subst h
    unfold inPlay
    exact Or.inl (List.mem_append_right _ hx)
  | atBase =>
    simp only [placeObjs, Option.some.injEq] at h
    subst h
    unfold inPlay
    exact Or.inl (List.mem_append_left _ hx)
  | onChain =>
    simp only [placeObjs, Option.some.injEq] at h
    subst h
    exact Or.inr (List.mem_filter.mp hx).1
  | inHand => simp [placeObjs] at h
  | inTrash => simp [placeObjs] at h
  | inMainDeck => simp [placeObjs] at h
  | inRuneDeck => simp [placeObjs] at h
  | inHidden => simp [placeObjs] at h
  | inCombat =>
    simp only [placeObjs] at h
    obtain ⟨bf, -, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold inPlay
    exact Or.inl (List.mem_append_right _ (List.mem_filter.mp hx).1)

/-- The objects a candidate list can hold are objects in play, or spells on the Chain. -/
theorem GameState.mem_candidates {s : GameState} {p : PlayerId} {self : ObjId} {env : Env}
    {side : Side} {place : Place} {fs : FilterList} {r : List ObjId}
    (h : s.candidates p self env side place fs = some r) :
    ∀ x ∈ r, x ∈ s.inPlay ∨ x ∈ s.zone .chain := by
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
    | some (.obj o) => some (if o ∈ s.inPlay ∨ o ∈ s.zone .chain then [o] else [])
    | _ => none
  | .var v =>
    match env.lookup v with
    | some (.obj o) => some (if (s.obj? o).isSome then [o] else [])
    | _ => none
  | .it =>
    match env.it with
    | some o => some (if o ∈ s.inPlay then [o] else [])
    | none => none
  | .pick .all side place fs => s.candidates p self env side place fs
  | .locationOf sel =>
    (sel.eval s p self env).map (fun ids =>
      ids.filterMap (fun u => (s.obj? u).bind (·.loc)))
  | _ => none

/-- The Rune Pool of the player after paying the cost `c` for the object `src` (its domains are the
Power the cost may name), if it can: the first payment that the Pool has. -/
def GameState.payNow (s : GameState) (p : PlayerId) (src : ObjId) (c : Cost) : Option RunePool :=
  let own := ((s.cardDef? src).map (·.domains)).getD []
  (c.payments own).findSome? (fun pay => (s.poolOf p).spend pay)

/-- The Victory Score as the passive abilities with no condition leave it (CR 194): the mode's, and
the changes by an amount that is a number. The abilities with a condition are read in
`GameState.victoryScore`, defined later. -/
def GameState.victoryBase (s : GameState) : Nat :=
  let objs := s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))
  let delta : Int := (objs.flatMap (fun src => match s.cardDef? src with
    | some d => d.fullAbilities.flatMap (fun ab =>
      match ab with
      | Ability.passive .always mods => mods.map (fun m =>
        match m with
        | .victoryScorePlus (.const k) => (k : Int)
        | .victoryScoreMinus (.const k) => -(k : Int)
        | _ => 0)
      | _ => [])
    | none => [])).sum
  (s.config.mode.victoryScore + delta).toNat

/-- The number an amount stands for, reading the game: the count of the objects a selector stands
for, the size of a hand, and the arithmetic of these. `none` if it cannot be known yet. -/
def Amount.evalS0 (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) : Amount → Option Nat
  | .count (.pick .all side place fs) =>
    -- the cards of a player's zone off the board are counted from the zone
    match place.zoneKind? with
    | some z =>
      (s.players.filter (fun q => side.admitsPlayer p q)).foldl (fun acc q =>
        acc.bind (fun n => ((s.zone (.player q z)).filterM (fun u =>
          (FilterList.holds s self env u fs))).map (fun l => n + l.length))) (some 0)
    | none => ((Selector.pick .all side place fs).eval s p self env).map List.length
  | .count sel => (sel.eval s p self env).map List.length
  | .xp => some (s.xpOf p)
  | .victoryScore => some s.victoryBase
  | .energyPaid => some (((s.obj? self).map (·.energyPaid)).getD 0)
  | .movesThisTurn =>
    some (match s.obj? self with
      | some o => if o.movesTurn == some s.turn then o.moves else 0
      | none => 0)
  | .cardsPlayed =>
    some (s.objects.toList.filter (fun (_, o) =>
      o.owner == p && o.playedTurn == some s.turn)).length
  | .costOf sel =>
    -- the Energy cost of the cards a selector names: a chosen object or a variable
    let ids : Option (List ObjId) := match sel with
      | .self => some [self]
      | .slot i => match env.slots[i]? with | some (.obj o) => some [o] | _ => none
      | .var v => match env.lookup v with | some (.obj o) => some [o] | _ => none
      | _ => none
    let energy (id : ObjId) : Nat := (((s.cardDef? id).bind (·.cost)).map (·.energy)).getD 0
    ids.map (fun l => (l.map energy).sum)
  | .points ps => do
    let l ← ps.resolve s p
    pure (l.foldl (fun acc q => acc + s.pointsOf q) 0)
  | .turnsTaken ps => do
    -- the turns the players have taken, this one included (CR 301)
    let l ← ps.resolve s p
    pure (l.foldl (fun acc q =>
      acc + ((List.range s.turn).filter
        (fun k => s.turnOrder.getD (k % s.playerCount) ⟨0⟩ == q)).length) 0)
  | .handSize ps => do
    let l ← ps.resolve s p
    pure ((l.map (fun q => (s.zone (.player q .hand)).length)).foldl (· + ·) 0)
  | .add a b => do pure ((← Amount.evalS0 s p self env a) + (← Amount.evalS0 s p self env b))
  | .sub a b => do pure ((← Amount.evalS0 s p self env a) - (← Amount.evalS0 s p self env b))
  | .mul a b => do pure ((← Amount.evalS0 s p self env a) * (← Amount.evalS0 s p self env b))
  | .min a b =>
    do pure (Nat.min (← Amount.evalS0 s p self env a) (← Amount.evalS0 s p self env b))
  | .max a b =>
    do pure (Nat.max (← Amount.evalS0 s p self env a) (← Amount.evalS0 s p self env b))
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
    let x ← a.evalS0 s p self env
    let y ← b.evalS0 s p self env
    pure (op.holds x y)
  | .exists sel => (sel.eval s p self env).map (fun l => !l.isEmpty)
  | .matches sel f => do
    let ids ← sel.eval s p self env
    let bs ← ids.mapM (fun id => f.holds s self env id)
    pure (!ids.isEmpty && bs.all id)
  | .yourTurn => some (decide (s.active = some p))
  | .legion => some ((s.obj? self).any (·.legion))
  | .paid => some ((s.obj? self).any (·.paid))
  | .playedAnother => some (s.playedOther p self)
  | .canPay c => some (s.payNow p self c).isSome
  | .diedWith e =>
    some (match env.slots.head? with
      | some (Value.obj o) =>
        s.turnFx.any (fun f => f.turn == s.turn && f.kind == e && f.target == some o)
      | _ => false)
  | .marked e =>
    some (s.turnFx.any (fun f => f.turn == s.turn && f.kind == e && f.who == p &&
      f.target == some self))
  | .enemyUnitDied =>
    some (s.turnFx.any (fun f => f.turn == s.turn && f.kind == .unitDied && f.who != p))
  | .discardedThisTurn =>
    some (s.turnFx.any (fun f => f.turn == s.turn && f.kind == .cardDiscarded && f.who == p))
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

/-- Every object chosen is in play, or a spell on the Chain. -/
theorem targetsOk_mem_inPlay {s : GameState} {p : PlayerId} {self : ObjId} :
    ∀ {cs : List Choice} {ts : List ObjId}, targetsOk s p self cs ts = true →
      ∀ t ∈ ts, t ∈ s.inPlay ∨ t ∈ s.zone .chain
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
