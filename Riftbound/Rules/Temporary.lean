module

public import Riftbound.Rules.Effects
public import Riftbound.Rules.Battlefield

/-!
# Temporary

A unit with Temporary is killed at the start of its controller's Beginning Phase, before Scoring
(CR 816, 315.2.a). Here that is a step of the Beginning Phase that runs before the Hold points are
scored: `beginStep`.
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

/-- The units of the player that have Temporary, on their Base and at the Battlefields. -/
def tempUnits (s : GameState) (tp : PlayerId) : List ObjId :=
  (s.zone (.player tp .base) ++ s.zone .battlefieldZone).filter
    (fun u => (s.obj? u).any (·.controller == tp) && s.hasKw u .temporary &&
      !s.ignoresTemporary u)

/-- Kill the objects, one after the other. -/
def killAll : List ObjId → GameState → List Event → GameState × List Event
  | [], s, es => (s, es)
  | u :: us, s, es =>
    let r := killOrSave s u
    killAll us r.1 (es ++ r.2)

/-- Killing objects one after the other is a safe change. -/
theorem killAll_safe : ∀ (us : List ObjId) (s : GameState) (es : List Event),
    Safe s (killAll us s es).1
  | [], s, _ => Safe.refl s
  | u :: us, s, _ => (killOrSave_safe s u).trans (killAll_safe us _ _)

/-- The start of the Beginning Phase: the Temporary units of the turn player are killed, and then
the turn player scores their Holds (CR 816, 315.2). -/
def beginStep (s : GameState) (tp : PlayerId) : GameState × List Event :=
  let k := killAll (tempUnits s tp) s []
  let h := hold k.1 tp
  (h.1, k.2 ++ h.2)

/-- The start of the Beginning Phase is a safe change, then points. -/
theorem beginStep_safeP (s : GameState) (tp : PlayerId) : SafeP s (beginStep s tp).1 :=
  SafeP.trans_safe (killAll_safe _ s []) (hold_safeP _ tp)

end Riftbound

end
