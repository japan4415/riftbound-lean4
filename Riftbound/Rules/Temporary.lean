module

public import Riftbound.Rules.Effects
public import Riftbound.Rules.Battlefield

/-!
# Temporary

A permanent with active Temporary supplies a triggered ability at the start of its controller's
Beginning Phase, before Scoring (CR 816, 315.2.a).
-/

@[expose] public section

namespace Riftbound

/-- A unit of the player at the Battlefield has the passive ability that their Temporary effects at
its Battlefield don't happen (LeBlanc, Everywhere at Once). -/
def GameState.ignoresTemporary (s : GameState) (u : ObjId) : Bool :=
  match s.obj? u with
  | some o =>
    o.loc.isSome && s.inPlay.any (fun g =>
      (s.obj? g).any (fun og => og.controller == o.controller && og.loc == o.loc) &&
        (s.cardDef? g).any (fun d => d.fullAbilities.any (fun ab =>
          match ab with
          | Ability.passive .always mods => mods.contains (.ignoreKeyword .temporary .here)
          | _ => false)))
  | none => false

/-- The permanents the player controls with active Temporary at their Base or a Battlefield. -/
def tempUnits (s : GameState) (tp : PlayerId) : List ObjId :=
  (s.zone (.player tp .base) ++ s.zone .battlefieldZone).filter
    (fun u => (s.obj? u).any (·.controller == tp) &&
      (s.activeKeywords u).any (·.keyword == .temporary) &&
      !s.ignoresTemporary u)

end Riftbound

end
