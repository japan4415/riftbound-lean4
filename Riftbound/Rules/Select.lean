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
  -- Gearhead: each Equipment gives double its Might bonus
  let doubled := (s.cardDef? id).any (fun du => du.fullAbilities.any (fun ab =>
    match ab with | Ability.passive .always mods => mods.contains .doubleEquip | _ => false))
  (s.inPlay.filterMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      if o.attached == some id then
        -- Brutalizer: more Might if the Equipment was attached this turn
        let fresh : Int := d.grants.foldl (fun acc ab =>
          match ab with
          | Ability.passive .always mods =>
            mods.foldl (fun a2 m => match m with
              | .mightIfFresh n => if o.attachedTurn == some s.turn then a2 + (n : Int) else a2
              | _ => a2) acc
          | _ => acc) 0
        let b : Int := d.mightBonus.getD 0
        some ((if doubled then 2 * b else b) + fresh)
      else none
    | _, _ => none)).sum

/-- The tags an Equipment gives to the Unit it is attached to. -/
def GameState.gainedTags (s : GameState) (id : ObjId) : List Tag :=
  s.inPlay.flatMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      if o.attached == some id then
        d.grants.flatMap (fun ab =>
          match ab with
          | Ability.passive .always mods =>
            mods.filterMap (fun m => match m with | .gainsTag t => some t | _ => none)
          | _ => [])
      else []
    | _, _ => [])

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
        | .nextSpellCostMinus _ | .nextUnitReady | .nextSpellRepeat =>
          !s.playedSince p f.kind.playType f.stamp
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
      (1 + (o.extraBuffs : Int)) *
        (1 + (((s.fxOf o.controller).filter (fun k => k == .buffsExtraMight)).length : Int))
    else 0
  | none => 0

/-- Whether the object has the property, for the properties that are understood. `self` is the
object the effect belongs to. -/
def Filter.holds (s : GameState) (self : ObjId) (env : Env) (id : ObjId) : Filter → Option Bool
  | .ofType t => (s.cardDef? id).map (·.hasType t)
  | .ofSupertype sp => (s.cardDef? id).map (·.hasSupertype sp)
  | .tag t => (s.cardDef? id).map (fun d => d.tags.contains t || (s.gainedTags id).contains t)
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
      pure (op.holds (m + s.equipBonus id + buff + env.passOf id) n)
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
  -- the passive is read from the card as it is printed: its condition is not asked (only
  -- `always` conditions are written)
  | .permitsOpenPlay =>
    some (((s.cardDef? id).map (·.fullAbilities)).getD [] |>.any (fun ab =>
      match ab with | .passive _ mods => mods.contains .playToOpenBf | _ => false))
  | .hideRoom =>
    some (decide ((s.players.flatMap (fun q => s.zone (.player q .hidden))).countP
      (fun h => (s.obj? h).any (·.hiddenAt == some id)) <
        if ((s.cardDef? id).map (·.fullAbilities)).getD [] |>.any (fun ab =>
            match ab with | .passive _ mods => mods.contains .extraHide | _ => false)
        then 2 else 1))
  | .costBelowPoints => do
    let o ← s.obj? self
    let d ← s.cardDef? id
    pure (match d.cost with | some k => decide (k.energy < s.pointsOf o.controller) | none => false)
  | .noChoices =>
    some (((s.cardDef? id).bind (·.spellEffect)).any (fun e => e.choices.isEmpty))
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
        decide (0 < o.damage ∧ m + s.equipBonus id + buff + env.passOf id ≤ (o.damage : Int))
      | _, _ => false)
  | .notSelf => some (id != self)
  | .not f => (f.holds s self env id).map (fun b => !b)
  | .either a b => do
    let x ← a.holds s self env id
    let y ← b.holds s self env id
    pure (x || y)
  | .both a b => do
    let x ← a.holds s self env id
    let y ← b.holds s self env id
    pure (x && y)
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
  | .unitsPlayable =>
    some (!((s.cardDef? id).any (fun d => d.fullAbilities.any (fun ab =>
      match ab with
      | Ability.passive .always mods =>
        mods.any (fun m => match m with | .cantPlayer _ .play .here _ => true | _ => false)
      | _ => false))))
  | .inHandZone => some ((s.obj? id).any (fun o => decide (id ∈ s.zone (.player o.owner .hand))))
  | .playedThisTurn => some ((s.obj? id).any (·.playedTurn == some s.turn))
  | .playedFromElsewhere =>
    some ((s.obj? id).any (fun o => o.playedTurn == some s.turn && !o.playedFromHand))
  | .wasTakenByMyCard =>
    some ((s.obj? id).any (fun o => o.takenBy.isSome && o.takenBy == (s.cardDef? self).map (·.id)))
  | .takenByMyCard =>
    some ((s.obj? id).any (fun o => o.takenBy.isSome &&
      o.takenBy == (s.cardDef? self).map (·.id) &&
      some o.controller == (s.obj? self).map (·.owner)))
  | .givesLegendsAttach =>
    some (((s.cardDef? id).map (·.abilities)).getD [] |>.any (fun ab =>
      match ab with | .passive _ mods => mods.contains .legendsAttach | _ => false))
  | .copiesText =>
    some (((s.cardDef? id).map (·.abilities)).getD [] |>.any (fun ab =>
      match ab with | .passive _ mods => mods.contains .copiesUnitText | _ => false))
  | .sameController sel =>
    let other : Option ObjId :=
      match sel with
      | .self => some self
      | .slot i => match env.slots[i]? with | some (.obj o) => some o | _ => none
      | .var v => match env.lookup v with | some (.obj o) => some o | _ => none
      | _ => none
    other.map (fun o => decide ((s.obj? o).map (·.controller) = (s.obj? id).map (·.controller)))
  | .scoredByMine =>
    let me := ((s.obj? self).map (·.controller)).getD ⟨0⟩
    some (((s.obj? id).map (·.scored.contains me)).getD false)
  | .attackedByMine =>
    some (((s.obj? id).bind (·.contested)) == (s.obj? self).map (·.controller))
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
    -- the passive abilities come in `env.passMight` (the passives read filters themselves, with
    -- no table: they read the Might without the passives)
    pure (match s.mightOf id with
      | some m =>
        let buff : Int := s.buffBonus id
        decide (5 ≤ m + s.equipBonus id + buff + env.passOf id)
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
  | .isAttached => pure ((s.obj? id).any (·.attached.isSome))
  | .attached => pure (s.inPlay.any (fun g => (s.obj? g).any (·.attached == some id)))
  | .token =>
    pure ((s.obj? id).any (fun o => match o.kind with | .token _ => true | _ => false))
  | .fromBattlefield => pure ((s.obj? id).any (·.prevLoc.isSome))
  | .choosesMine => do
    let me ← s.obj? self
    let o ← s.obj? id
    pure (o.targets.any (fun t => (s.obj? t).any (fun u => u.controller == me.controller &&
      (s.cardDef? t).any (fun d => d.hasType .unit || d.hasType .gear))))
  | .attachedTo sel => do
    -- the object the selector names: `self`, a chosen object or a variable
    let d? : Option ObjId := match sel with
      | .self => some self
      | .slot i => match env.slots[i]? with | some (.obj o) => some o | _ => none
      | .var v => match env.lookup v with | some (.obj o) => some o | _ => none
      | _ => none
    let d ← d?
    pure ((s.obj? id).any (·.attached == some d))

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
  | .inChampionZone => some .championZone
  | .inLegendZone => some .legendZone
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

/-- The player `p` cannot choose the object: it is of another player, and it has the passive ability
that says it can't be chosen by enemy spells and abilities (Ruin Runner). -/
def GameState.blocksChoice (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  (s.obj? id).any (·.controller != p) &&
    (s.cardDef? id).any (fun d => d.fullAbilities.any (fun ab =>
      match ab with
      | Ability.passive .always mods => mods.contains (.cant .self .beChosen)
      | _ => false))

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
  | none => (s.candidates p self env side place fs).map (·.filter (fun id => !s.blocksChoice p id))

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
  | inChampionZone => simp [placeObjs] at h
  | inLegendZone => simp [placeObjs] at h
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
    | some (.int _) => some []  -- a target of up to one, that was left out (`slotValues`)
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
  | .slotsFrom i =>
    some ((env.slots.drop i).filterMap (fun v =>
      match v with
      | .obj o => if o ∈ s.inPlay ∨ o ∈ s.zone .chain then some o else none
      | _ => none))
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
  | .notes e =>
    some (s.turnFx.filter (fun f => f.turn == s.turn && f.who == p && f.kind == e &&
      f.target == some self)).length
  | .movesThisTurn =>
    some (match s.obj? self with
      | some o => if o.movesTurn == some s.turn then o.moves else 0
      | none => 0)
  | .excess =>
    some ((s.turnFx.filterMap (fun f =>
      match f.kind with
      | .excessDamage k => if f.turn == s.turn && f.who == p then some k else none
      | _ => none)).foldl Nat.max 0)
  | .heldPoints =>
    some ((s.zone .battlefieldZone).countP (fun b => (s.obj? b).any (·.held.contains p)))
  | .spellsChoseEnemy =>
    -- an enemy object is a Unit or Gear of another player (or one that is gone)
    let enemy (t : ObjId) : Bool :=
      (s.obj? t).all (fun x => x.controller != p &&
        ((s.cardDef? t).any (fun d => d.hasType .unit || d.hasType .gear) || (s.cardDef? t).isNone))
    -- the Spells of the player that chose one, and each one the abilities of their Units chose
    let spells := (s.objects.toList.filter (fun (k, o) =>
      o.owner == p && o.playedTurn == some s.turn &&
        ((s.cardDef? ⟨k⟩).any (·.hasType .spell)) &&
        o.targets.any enemy)).length
    let abilities := (s.objects.toList.filter (fun (k, o) =>
      o.controller == p && o.choseTurn == some s.turn &&
        (s.cardDef? ⟨k⟩).any (·.hasType .unit))).foldl
      (fun acc (_, o) => acc + (o.chose.filter enemy).length) 0
    some (spells + abilities)
  | .powerSpent => some (s.poolOf p).spent
  | .gearsPlayed =>
    some (s.objects.toList.filter (fun (k, o) =>
      o.owner == p && o.playedTurn == some s.turn &&
        ((s.cardDef? ⟨k⟩).any (·.hasType .gear)))).length
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
    -- the turns the players have taken, this one included (CR 301), not counting the extra turns
    let l ← ps.resolve s p
    pure (l.foldl (fun acc q =>
      acc + ((List.range (s.turn - s.turnShift)).filter
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
  | .and a b =>
    -- a false side makes it false, even if the other cannot be answered yet
    match Condition.eval s p self env a, Condition.eval s p self env b with
    | some x, some y => some (x && y)
    | some false, none => some false
    | none, some false => some false
    | _, _ => none
  | .or a b =>
    match Condition.eval s p self env a, Condition.eval s p self env b with
    | some x, some y => some (x || y)
    | some true, none => some true
    | none, some true => some true
    | _, _ => none
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
  | .inCombat => some s.combatNow.isSome
  | .legendReady =>
    some ((s.zone (.player p .legendZone)).any (fun l => (s.obj? l).any (fun o => !o.exhausted)))
  | .openConquered =>
    some (s.turnFx.any (fun f => f.turn == s.turn && f.kind == .openConquest && f.who == p &&
      f.target == s.hereOf self))
  | .legion => some ((s.obj? self).any (·.legion))
  | .paid => some ((s.obj? self).any (·.paid))
  | .playedAnother => some (s.playedOther p self)
  | .canPay c => some (s.payNow p self c).isSome
  | .diedWith e =>
    -- the object a watching ability is about, or (an ability of the dead card itself) the card
    some (match env.slots.head? with
      | some (Value.obj o) =>
        s.turnFx.any (fun f => f.turn == s.turn && f.kind == e && f.target == some o)
      | _ => s.turnFx.any (fun f => f.turn == s.turn && f.kind == e && f.target == some self))
  | .fromHidden => some ((s.obj? self).any (·.fromHidden))
  -- the passives are read from the cards as printed (their conditions are not asked)
  | .hasFriendlyCard cid =>
    some ((s.players.flatMap (fun q => s.zone (.player q .legendZone)) ++ s.inPlay).any (fun g =>
      (s.obj? g).any (·.controller == p) && (s.cardDef? g).any (·.id == cid)))
  | .hidesWithEnergy =>
    some ((s.players.flatMap (fun q => s.zone (.player q .legendZone)) ++ s.inPlay).any (fun g =>
      (s.obj? g).any (·.controller == p) &&
        (((s.cardDef? g).map (·.fullAbilities)).getD []).any (fun ab =>
          match ab with | .passive _ mods => mods.contains .hideWithEnergy | _ => false)))
  | .noted e => some (s.turnFx.any (fun f => f.turn == s.turn && f.who == p && f.kind == e))
  | .excessAtLeast n =>
    some (s.turnFx.any (fun f => f.turn == s.turn && f.who == p &&
      (match f.kind with | .excessDamage k => decide (n ≤ k) | _ => false)))
  | .marked e =>
    some (s.turnFx.any (fun f => f.turn == s.turn && f.kind == e && f.who == p &&
      f.target == some self))
  | .enemyUnitDied =>
    some (s.turnFx.any (fun f => f.turn == s.turn && f.kind == .unitDied && f.who != p))
  | .discardedThisTurn =>
    some (s.turnFx.any (fun f => f.turn == s.turn && f.kind == .cardDiscarded && f.who == p))
  | _ => none

/-- A target of this quantity is one a Spell can make for now: one, or up to some number. -/
def Quantity.pickable : Quantity → Bool
  | .one => true
  | .upTo n => decide (1 ≤ n)
  | _ => false

/-- The objects a choice of a Spell can pick, when the choices before it picked `acc` (a later
choice may name an earlier pick as `slot i`): for a target of one object, up to one, or any number up
to a bound, the matching objects in play. Nothing for a choice that is not understood yet. -/
def Choice.candidatesAfter (s : GameState) (p : PlayerId) (self : ObjId)
    (pm : List (ObjId × Int)) (acc : List ObjId) :
    Choice → List ObjId
  | .target q side place fs =>
    if q.pickable then
      ((s.candidates p self { slots := acc.map Value.obj, passMight := pm } side place
        fs).getD []).filter (fun id => !s.blocksChoice p id)
    else []
  | _ => []

/-- The objects a choice can pick when nothing was picked before. -/
def Choice.candidates (s : GameState) (p : PlayerId) (self : ObjId) (c : Choice) : List ObjId :=
  c.candidatesAfter s p self [] []

/-- Whether a choice is one that a Spell can make for now: one target, or up to some number (which
may be left out when nothing after it is required). -/
def Choice.simple : Choice → Bool
  | .target .one _ _ _ => true
  | .target (.upTo n) _ _ _ => decide (1 ≤ n)
  | _ => false

/-- Whether a choice may be left out: a target of up to some number. -/
def Choice.optional : Choice → Bool
  | .target (.upTo n) _ _ _ => decide (1 ≤ n)
  | _ => false

/-- An optional choice is one that can be made. -/
theorem Choice.simple_of_optional {c : Choice} (h : c.optional = true) : c.simple = true := by
  unfold Choice.optional at h
  split at h
  · simpa [Choice.simple] using h
  · simp at h

/-- Whether a choice is of several objects: up to two or more. It is the last choice of its Spell,
and the objects are chosen in the order of the objects, so that a set is chosen once. -/
def Choice.multi : Choice → Bool
  | .target (.upTo n) _ _ _ => decide (2 ≤ n)
  | _ => false

/-- The most objects a choice picks. -/
def Choice.maxPicks : Choice → Nat
  | .target (.upTo n) _ _ _ => n
  | _ => 1

/-- Every way to leave some of the objects out, the others in their order. -/
def subseqs {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (subseqs xs).flatMap (fun t => [t, x :: t])

/-- The ways listed are exactly the sublists. -/
theorem mem_subseqs {α : Type} : ∀ (l t : List α), t ∈ subseqs l ↔ t.Sublist l
  | [], t => by simp [subseqs, List.sublist_nil]
  | x :: xs, t => by
    rw [List.sublist_cons_iff]
    simp only [subseqs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
      mem_subseqs xs]
    constructor
    · rintro ⟨u, hu, rfl | rfl⟩
      · exact Or.inl hu
      · exact Or.inr ⟨u, rfl, hu⟩
    · rintro (h | ⟨r, rfl, hr⟩)
      · exact ⟨t, h, Or.inl rfl⟩
      · exact ⟨r, hr, Or.inr rfl⟩

/-- The objects a choice of several can pick, in the order of the objects. -/
def Choice.sortedCands (s : GameState) (p : PlayerId) (self : ObjId)
    (pm : List (ObjId × Int)) (acc : List ObjId) (c : Choice) : List ObjId :=
  (c.candidatesAfter s p self pm acc).mergeSort (fun a b => decide (a.n ≤ b.n))

/-- The choices after one can all be left out. A choice of several is the last one. -/
def skipOk : List Choice → Bool
  | [] => true
  | c :: cs => c.optional && (!c.multi || cs.isEmpty) && skipOk cs

/-- The objects chosen are a legal pick for the choices, one for each, each seeing the picks before
it; the last choice may be of several. -/
def targetsOkAfter (s : GameState) (p : PlayerId) (self : ObjId) (pm : List (ObjId × Int))
    (acc : List ObjId) :
    List Choice → List ObjId → Bool
  | [], [] => true
  | [], _ :: _ => false
  | c :: cs, ts =>
    if c.multi then
      cs.isEmpty && decide (ts.length ≤ c.maxPicks) &&
        decide (ts.Sublist (c.sortedCands s p self pm acc))
    else
      match ts with
      | [] => c.optional && skipOk cs
      | t :: ts =>
        c.simple && decide (t ∈ c.candidatesAfter s p self pm acc) &&
          targetsOkAfter s p self pm (acc ++ [t]) cs ts

/-- What the check of the picks says for a choice and the ones after it. -/
theorem targetsOkAfter_cons (s : GameState) (p : PlayerId) (self : ObjId)
    (pm : List (ObjId × Int)) (acc : List ObjId) (c : Choice) (cs : List Choice)
    (ts : List ObjId) :
    targetsOkAfter s p self pm acc (c :: cs) ts =
      (if c.multi then
        cs.isEmpty && decide (ts.length ≤ c.maxPicks) &&
          decide (ts.Sublist (c.sortedCands s p self pm acc))
      else
        match ts with
        | [] => c.optional && skipOk cs
        | t :: ts =>
          c.simple && decide (t ∈ c.candidatesAfter s p self pm acc) &&
            targetsOkAfter s p self pm (acc ++ [t]) cs ts) := by
  rw [targetsOkAfter.eq_def]

/-- The objects chosen are a legal pick for the choices. -/
def targetsOk (s : GameState) (p : PlayerId) (self : ObjId) (pm : List (ObjId × Int))
    (cs : List Choice) (ts : List ObjId) : Bool :=
  targetsOkAfter s p self pm [] cs ts

/-- The pick of nothing, when this choice and the ones after it may all be left out. -/
def skipTuple (c : Choice) (cs : List Choice) : List (List ObjId) :=
  if c.optional && skipOk cs then [[]] else []

/-- A pick that starts with an object is not the pick of nothing. -/
theorem cons_not_mem_skipTuple {c : Choice} {cs : List Choice} {t : ObjId} {ts : List ObjId} :
    (t :: ts) ∉ skipTuple c cs := by
  unfold skipTuple
  split <;> simp

/-- Every legal pick for the choices, after the picks `acc`. -/
def targetTuplesAfter (s : GameState) (p : PlayerId) (self : ObjId) (pm : List (ObjId × Int))
    (acc : List ObjId) :
    List Choice → List (List ObjId)
  | [] => [[]]
  | c :: cs =>
    if c.multi then
      (if cs.isEmpty then
        (subseqs (c.sortedCands s p self pm acc)).filter (fun t => decide (t.length ≤ c.maxPicks))
      else [])
    else if c.simple then
      (c.candidatesAfter s p self pm acc).flatMap (fun t =>
        (targetTuplesAfter s p self pm (acc ++ [t]) cs).map (t :: ·)) ++
        skipTuple c cs
    else []

/-- Every legal pick for the choices. -/
def targetTuples (s : GameState) (p : PlayerId) (self : ObjId) (pm : List (ObjId × Int))
    (cs : List Choice) : List (List ObjId) :=
  targetTuplesAfter s p self pm [] cs

/-- The picks listed are exactly the legal ones. -/
theorem mem_targetTuplesAfter (s : GameState) (p : PlayerId) (self : ObjId)
    (pm : List (ObjId × Int)) :
    ∀ (cs : List Choice) (acc ts : List ObjId),
      ts ∈ targetTuplesAfter s p self pm acc cs ↔ targetsOkAfter s p self pm acc cs ts = true
  | [], acc, ts => by
    cases ts <;> simp [targetTuplesAfter, targetsOkAfter]
  | c :: cs, acc, ts => by
    by_cases hm : c.multi = true
    · simp only [targetTuplesAfter, targetsOkAfter_cons, hm, ite_true, Bool.and_eq_true,
        decide_eq_true_eq]
      by_cases hc : cs.isEmpty = true
      · simp [hc, List.mem_filter, mem_subseqs, and_comm]
      · simp [hc]
    · have hm' : c.multi = false := by simpa using hm
      cases ts with
      | nil =>
        by_cases hs : c.simple = true
        · simp [targetTuplesAfter, targetsOkAfter_cons, hm', hs, skipTuple]
        · have : c.optional = false := by
            cases h : c.optional
            · rfl
            · exact absurd (Choice.simple_of_optional h) hs
          simp [targetTuplesAfter, targetsOkAfter_cons, hm', hs, this, skipTuple]
      | cons t ts =>
        simp only [targetTuplesAfter, targetsOkAfter_cons, hm', Bool.false_eq_true, ite_false,
          Bool.and_eq_true, decide_eq_true_eq]
        by_cases hs : c.simple = true
        · simp only [hs, ite_true, List.mem_append, List.mem_flatMap, List.mem_map,
            List.cons.injEq, true_and, cons_not_mem_skipTuple, or_false]
          constructor
          · rintro ⟨t', ht', ts', hts', rfl, rfl⟩
            exact ⟨ht', (mem_targetTuplesAfter s p self pm cs (acc ++ [t']) ts').mp hts'⟩
          · rintro ⟨ht, hts⟩
            exact ⟨t, ht, ts, (mem_targetTuplesAfter s p self pm cs (acc ++ [t]) ts).mpr hts,
              rfl, rfl⟩
        · simp [hs]

/-- The picks listed are exactly the legal ones. -/
theorem mem_targetTuples (s : GameState) (p : PlayerId) (self : ObjId) (pm : List (ObjId × Int))
    (cs : List Choice) (ts : List ObjId) :
    ts ∈ targetTuples s p self pm cs ↔ targetsOk s p self pm cs ts = true :=
  mem_targetTuplesAfter s p self pm cs [] ts

/-- What a choice can pick is in play, or a spell on the Chain. -/
theorem Choice.candidatesAfter_mem {s : GameState} {p : PlayerId} {self : ObjId}
    {pm : List (ObjId × Int)} {acc : List ObjId} {c : Choice} {x : ObjId}
    (h : x ∈ c.candidatesAfter s p self pm acc) : x ∈ s.inPlay ∨ x ∈ s.zone .chain := by
  cases c with
  | target q side place fs =>
    simp only [Choice.candidatesAfter] at h
    split at h
    · cases hc : s.candidates p self { slots := acc.map Value.obj, passMight := pm } side place
        fs with
      | none => simp [hc] at h
      | some r =>
        simp only [hc, Option.getD_some] at h
        exact GameState.mem_candidates hc x (List.mem_filter.mp h).1
    · simp at h
  | mode _ => simp [Choice.candidatesAfter] at h
  | xValue => simp [Choice.candidatesAfter] at h
  | extraCost _ _ => simp [Choice.candidatesAfter] at h

/-- Every object chosen is in play, or a spell on the Chain. -/
theorem targetsOkAfter_mem_inPlay {s : GameState} {p : PlayerId} {self : ObjId}
    {pm : List (ObjId × Int)} :
    ∀ {cs : List Choice} {acc ts : List ObjId}, targetsOkAfter s p self pm acc cs ts = true →
      ∀ t ∈ ts, t ∈ s.inPlay ∨ t ∈ s.zone .chain
  | [], _, [], _ => by simp
  | [], _, _ :: _, h => by simp [targetsOkAfter] at h
  | c :: cs, acc, ts, h => by
    intro x hx
    by_cases hm : c.multi = true
    · simp only [targetsOkAfter_cons, hm, ite_true, Bool.and_eq_true, decide_eq_true_eq] at h
      have hsub := h.2
      have hx' : x ∈ c.sortedCands s p self pm acc := hsub.subset hx
      exact Choice.candidatesAfter_mem
        ((List.mem_mergeSort).mp hx')
    · have hm' : c.multi = false := by simpa using hm
      cases ts with
      | nil => cases hx
      | cons t ts =>
        simp only [targetsOkAfter_cons, hm', Bool.false_eq_true, ite_false, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨hs, ht⟩, hrest⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Choice.candidatesAfter_mem ht
        · exact targetsOkAfter_mem_inPlay hrest x hx

/-- Every object chosen is in play, or a spell on the Chain. -/
theorem targetsOk_mem_inPlay {s : GameState} {p : PlayerId} {self : ObjId}
    {pm : List (ObjId × Int)} {cs : List Choice}
    {ts : List ObjId} (h : targetsOk s p self pm cs ts = true) :
    ∀ t ∈ ts, t ∈ s.inPlay ∨ t ∈ s.zone .chain :=
  targetsOkAfter_mem_inPlay h

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
