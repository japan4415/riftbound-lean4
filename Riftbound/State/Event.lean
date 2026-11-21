module

public import Riftbound.State.Zone

/-!
# Events

What happened, as data: the record `step` returns next to the new state (design.md §6.6). The
stage where replacement effects rewrite an event before it is applied arrives with the engine
(milestone M2b) and the ability system (M6).
-/

@[expose] public section

namespace Riftbound

/-- Something that happened in the game. -/
inductive Event where
  /-- An object moved to a zone. It has the new identifier `new`. -/
  | moved (old new : ObjId) (dst : Zone)
  /-- A player gained points (CR 194). -/
  | pointsGained (p : PlayerId) (n : Nat)
  /-- A player burned out (CR 432). -/
  | burnedOut (p : PlayerId)
  /-- An instruction of an effect could not be done and was skipped (design.md §7.1). The object
  is the card whose effect it was. -/
  | skipped (source : ObjId)
  /-- An object was dealt damage (CR 142). -/
  | damaged (target : ObjId) (amount : Nat)
  /-- Damage was healed from an object (CR 419). -/
  | healed (target : ObjId) (amount : Nat)
  /-- An object became ready (CR 416). -/
  | readied (target : ObjId)
  /-- An object became exhausted (CR 415). -/
  | exhausted (target : ObjId)
deriving DecidableEq, Repr

end Riftbound

end
