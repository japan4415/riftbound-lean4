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
  -- `mightMinusMin` is a change an effect makes for a while (`applyGrant`); a passive ability with
  -- a floor is not read here yet
  | _ => 0

/-- What the passive abilities add to the Might of an object. -/
def passiveMight (s : GameState) (id : ObjId) : Int :=
  (s.passiveSources.flatMap (fun src => (s.activeMods src).map (s.modMight src id))).sum

/-- The keywords the Equipment attached to an object gives it (CR 137): the passive abilities with
no condition that give the object the keyword. -/
def equipKws (s : GameState) (id : ObjId) : List KeywordInst :=
  s.inPlay.flatMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      if o.attached == some id then
        d.grants.flatMap (fun ab =>
          match ab with
          | Ability.passive .always mods =>
            mods.filterMap (fun m => match m with | .keyword .self k => some k | _ => none)
          | _ => [])
      else []
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

/-- The Might an object has now: the printed Might, the lasting changes and the passive changes
(CR 475-479). The rules that read a Might read this one. -/
def mightNow (s : GameState) (id : ObjId) : Option Int :=
  (s.mightOf id).map (fun m => m + s.equipBonus id + s.passiveMight id +
    (if ((s.obj? id).map (·.buffed)).getD false then 1 else 0))

end GameState

/-- The value of an amount in an effect. `Amount.evalS0` reads everything but the Might of objects,
which the Layers decide (`mightNow`): "equal to my Might" is the Might the rules read (CR 479.4),
the sum over the objects the selector gives. -/
def Amount.evalS (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) : Amount → Option Nat
  | .mightOf sel =>
    (sel.eval s p self env).map (fun ids =>
      (ids.map (fun id => ((s.mightNow id).getD 0).toNat)).sum)
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
