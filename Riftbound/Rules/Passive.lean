module

public import Riftbound.Rules.Select

/-!
# Passive abilities

A passive ability changes the game as long as the object that has it is in play and its condition
holds (CR 363-366). The changes are read where the rules ask: whether a Unit enters ready, the
Might of a Unit.

The Might the rules read (`mightNow`) is the Might of the Layers' last step: the printed Might and
the lasting changes (`mightOf`) with the passive changes added (CR 479.4). What the passive
abilities select and test reads the Might without them, so the passives do not depend on one
another. The dependencies between abilities (CR 480-481) wait for a card that needs them.
-/

@[expose] public section

namespace Riftbound

/-- The card enters ready: it has the passive ability that says so, with no condition. -/
def CardDef.entersReady (d : CardDef) : Bool :=
  d.abilities.any (fun ab =>
    match ab with
    | Ability.passive .always mods => mods.contains (.entersReady .self)
    | _ => false)

namespace GameState

/-- The objects whose passive abilities apply: those in play, and the Legends (CR 363). -/
def passiveSources (s : GameState) : List ObjId :=
  s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))

/-- The changes the passive abilities of `src` make now: those of the abilities whose condition
holds. -/
def activeMods (s : GameState) (src : ObjId) : List StaticMod :=
  match s.obj? src, s.cardDef? src with
  | some o, some d =>
    d.fullAbilities.flatMap (fun ab =>
      match ab with
      | Ability.passive cond mods =>
        if cond.eval s o.controller src {} == some true then mods else []
      | _ => [])
  | _, _ => []

/-- A passive ability of an object that the opponents of the player control, with the change. -/
def oppHas (s : GameState) (p : PlayerId) (m : StaticMod) : Bool :=
  s.passiveSources.any (fun g => (s.obj? g).any (fun o => o.controller != p) &&
    (s.activeMods g).contains m)

/-- How much the passive change `m` of `src` changes the Might of `id`: more, less, or nothing. -/
def modMight (s : GameState) (src id : ObjId) : StaticMod → Int
  | .mightPlus sel a =>
    match s.obj? src, sel.eval s ((s.obj? src).map (·.controller) |>.getD ⟨0⟩) src {} with
    | some o, some ids =>
      if ids.contains id then ((a.evalS0 s o.controller src {}).map (fun k => (k : Int))).getD 0
      else 0
    | _, _ => 0
  | .mightMinus sel a =>
    match s.obj? src, sel.eval s ((s.obj? src).map (·.controller) |>.getD ⟨0⟩) src {} with
    | some o, some ids =>
      if ids.contains id then -((a.evalS0 s o.controller src {}).map (fun k => (k : Int))).getD 0
      else 0
    | _, _ => 0
  -- `mightMinusMin` has a floor: it is read after the others (`modFloor`)
  | _ => 0

/-- The passive change `m` of `src` that takes Might away down to a floor, for the Might of `id`:
how much it takes away at most, and the floor ("to a minimum of 1"). -/
def modFloor (s : GameState) (src id : ObjId) : StaticMod → Option (Nat × Nat)
  | .mightMinusMin sel a fl =>
    match s.obj? src, sel.eval s ((s.obj? src).map (·.controller) |>.getD ⟨0⟩) src {} with
    | some o, some ids =>
      if ids.contains id then (a.evalS0 s o.controller src {}).map (fun k => (k, fl)) else none
    | _, _ => none
  | _ => none

/-- The player `p` cannot score the Battlefield `bf` now, by a passive ability that says so ("players
can't score here until their third turn", "while I'm at a battlefield, opponents can't score"). -/
def cantActHere (s : GameState) (p : PlayerId) (a : Act) (bf : ObjId) : Bool :=
  s.passiveSources.any (fun g =>
    let c := ((s.obj? g).map (·.controller)).getD ⟨0⟩
    (s.activeMods g).any (fun m =>
      match m with
      | .cantPlayer who act place untilTurn =>
        act == a && ((who.resolve s c).map (·.contains p)).getD false &&
          (match place with
            | .here => s.hereOf g == some bf
            | .anywhere => true
            | _ => false) &&
          (untilTurn == 0 ||
            decide (((List.range (s.turn - s.turnShift)).filter
              (fun k => s.turnOrder.getD (k % s.playerCount) ⟨0⟩ == p)).length < untilTurn))
      | _ => false))

/-- The player `p` cannot score the Battlefield `bf` now. -/
def cantScoreHere (s : GameState) (p : PlayerId) (bf : ObjId) : Bool := s.cantActHere p .score bf

/-- Some passive ability in play has the change `m`, whoever controls it. -/
def anyActive (s : GameState) (m : StaticMod) : Bool :=
  s.passiveSources.any (fun g => (s.activeMods g).contains m)

/-- A Unit at the Battlefield `bf` cannot move to the Base: by the Battlefield, or by a Unit
(Minotaur Reckoner). -/
def homeForbidden (s : GameState) (bf : ObjId) : Bool :=
  (s.activeMods bf).contains .noMoveToBase || s.anyActive .noMoveToBaseAny

/-- The controller of an object (the first player if it is gone). -/
def controllerOf (s : GameState) (src : ObjId) : PlayerId :=
  ((s.obj? src).map (·.controller)).getD ⟨0⟩

/-- The points needed to win the game: those of the mode, and the changes the passive abilities
make (CR 194). -/
def victoryScore (s : GameState) : Nat :=
  let delta : Int := (s.passiveSources.flatMap (fun src =>
    (s.activeMods src).map (fun m =>
      match m with
      | .victoryScorePlus a => ((a.evalS0 s (s.controllerOf src) src {}).getD 0 : Int)
      | .victoryScoreMinus a => -((a.evalS0 s (s.controllerOf src) src {}).getD 0 : Int)
      | _ => 0))).sum
  (s.config.mode.victoryScore + delta).toNat

/-- The Bonus Damage the passive abilities of the player give to each instance of damage of their
spells and abilities: those of the objects they control, and those an Equipment gives the Unit it
is attached to (Rabadon's Deathcrown). -/
def passiveBonus (s : GameState) (p : PlayerId) : Nat :=
  let amount (src : ObjId) (m : StaticMod) : Option Nat :=
    match m with
    | .bonusDamage a => a.evalS0 s p src {}
    | _ => none
  (s.passiveSources.flatMap (fun g =>
    if (s.obj? g).any (·.controller == p) then (s.activeMods g).filterMap (amount g)
    else [])).sum +
  (s.inPlay.flatMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      match o.attached with
      | some u =>
        if (s.obj? u).any (·.controller == p) then
          d.grants.flatMap (fun ab =>
            match ab with
            | Ability.passive .always mods => mods.filterMap (amount g)
            | _ => [])
        else []
      | none => []
    | _, _ => [])).sum

/-- The Bonus Damage with each instance of damage that the spell or ability `src` of the player
deals to the object `id`: that of the effect of the turn for the next spell, and that of the
Battlefield the object is at (CR 142). -/
def bonusOn (s : GameState) (p : PlayerId) (src id : ObjId) : Nat :=
  s.spellBonus p src + s.passiveBonus p +
    (match (s.obj? id).bind (·.loc) with
      | some bf =>
        (s.activeMods bf).foldl
          (fun acc m => match m with | .bonusDamageHere n => acc + n | _ => acc) 0
      | none => 0)

/-- What the passive abilities add to the Might of an object. -/
def passiveMight (s : GameState) (id : ObjId) : Int :=
  (s.passiveSources.flatMap (fun src => (s.activeMods src).map (s.modMight src id))).sum

/-- The keywords the Equipment attached to an object gives it (CR 137): the passive abilities with
no condition that give the object the keyword. -/
def equipKws (s : GameState) (id : ObjId) : List KeywordInst :=
  s.inPlay.flatMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      -- the keywords it gives the Unit it is attached to
      (if o.attached == some id then
        d.grants.flatMap (fun ab =>
          match ab with
          | Ability.passive .always mods =>
            mods.filterMap (fun m => match m with | .keyword .self k => some k | _ => none)
          | _ => [])
      else []) ++
      -- Shurelya's Requiem: the units of the player at the place of the unit it is attached to
      (match o.attached.bind (fun u => s.obj? u), s.obj? id with
        | some host, some me =>
          if host.controller == me.controller && host.loc == me.loc && id ∈ s.inPlay &&
              (s.cardDef? id).any (·.hasType .unit) then
            d.grants.flatMap (fun ab =>
              match ab with
              | Ability.passive .always mods =>
                mods.filterMap (fun m => match m with | .keywordHere k => some k | _ => none)
              | _ => [])
          else []
        | _, _ => [])
    | _, _ => [])

/-- The keywords the passive abilities give an object now: those of the abilities whose condition
holds and whose selector stands for the object (CR 479.3). The selectors and the conditions read
only what the card prints (`Filter.hasKeyword`), never `grantedKws`, which would not end; so a
filter for the units that have a keyword does not see the keywords that are given. -/
def passiveKws (s : GameState) (id : ObjId) : List KeywordInst :=
  s.passiveSources.flatMap (fun src =>
    match s.obj? src with
    | some o =>
      (s.activeMods src).filterMap (fun m =>
        match m with
        | .keyword sel k =>
          match sel.eval s o.controller src {} with
          | some ids => if ids.contains id then some k else none
          | none => none
        | _ => none)
    | none => [])

/-- The keywords an object has besides those printed on its card: those the Equipment attached to
it gives it, those the passive abilities of other objects give it now, and those an effect gave it
for a while (CR 479.3). -/
def grantedKws (s : GameState) (id : ObjId) : List KeywordInst :=
  s.equipKws id ++ s.passiveKws id ++ (((s.obj? id).map (·.tempKws)).getD []).map (·.1)

/-- The number a printed keyword carries on the card of an object (0 if it does not print it). -/
def kwAmount (s : GameState) (u : ObjId) (k : Keyword) : Nat :=
  let amount (i : KeywordInst) : Option Nat :=
    -- "[Assault]" and "[Shield]" with no number are Assault 1 and Shield 1
    if i.keyword == k then
      (match i.arg with
        | .amount n => some n
        | .none => if k == .assault || k == .shield then some 1 else none
        | _ => none)
    else none
  -- Assault that equals a number of objects (Ancient Warmonger: the enemy units here)
  let counted : Nat :=
    if k == .assault then
      (s.activeMods u).foldl (fun acc m =>
        match m with
        | .assaultCount sel =>
          acc + (((sel.eval s ((s.obj? u).map (·.controller) |>.getD ⟨0⟩) u {}).map
            (·.length)).getD 0)
        | _ => acc) 0
    else 0
  (match s.cardDef? u with
    | some d => (d.keywords.filterMap amount).sum
    | none => 0) + ((s.grantedKws u).filterMap amount).sum + counted

/-- The Might an object has now: the printed Might, the lasting changes and the passive changes
(CR 475-479). The rules that read a Might read this one. -/
def mightNow (s : GameState) (id : ObjId) : Option Int :=
  (s.mightOf id).map (fun m =>
    let total := m + s.equipBonus id + s.passiveMight id +
      s.buffBonus id
    -- the changes with a floor come last: they take away down to the floor, never below it
    (s.passiveSources.flatMap (fun src =>
      (s.activeMods src).filterMap (s.modFloor src id))).foldl
      (fun (t : Int) (c : Nat × Nat) =>
        if t ≤ (c.2 : Int) then t else max (c.2 : Int) (t - (c.1 : Int))) total)

end GameState

/-- The value of an amount in an effect. `Amount.evalS0` reads everything but the Might of objects,
which the Layers decide (`mightNow`): "equal to my Might" is the Might the rules read (CR 479.4),
the sum over the objects the selector gives. -/
def Amount.evalS (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) : Amount → Option Nat
  | .mightOf sel =>
    (sel.eval s p self env).map (fun ids =>
      (ids.map (fun id => ((s.mightNow id).getD 0).toNat)).sum)
  | .highestMight sel =>
    (sel.eval s p self env).map (fun ids =>
      (ids.map (fun id => ((s.mightNow id).getD 0).toNat)).foldl Nat.max 0)
  | .kwAmount sel k =>
    (sel.eval s p self env).map (fun ids => (ids.map (fun id => s.kwAmount id k)).sum)
  | .add a b => do pure ((← Amount.evalS s p self env a) + (← Amount.evalS s p self env b))
  | .sub a b => do pure ((← Amount.evalS s p self env a) - (← Amount.evalS s p self env b))
  | .mul a b => do pure ((← Amount.evalS s p self env a) * (← Amount.evalS s p self env b))
  | .min a b =>
    do pure (Nat.min (← Amount.evalS s p self env a) (← Amount.evalS s p self env b))
  | .max a b =>
    do pure (Nat.max (← Amount.evalS s p self env a) (← Amount.evalS s p self env b))
  | a => a.evalS0 s p self env

end Riftbound

end
