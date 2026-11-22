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
  /-- A Unit made a Standard Move (CR 144) to a Battlefield (`some`) or to its Base (`none`). -/
  | standardMoved (unit : ObjId) (dest : Option ObjId)
  /-- A player took control of a Battlefield (`some`), or the Battlefield lost its controller
  (`none`) (CR 190.6). -/
  | controlChanged (battlefield : ObjId) (controller : Option PlayerId)
  /-- A player scored a Battlefield (CR 471): by Conquer (`true`) or by Hold (`false`). -/
  | scored (p : PlayerId) (battlefield : ObjId) (conquer : Bool)
  /-- A Unit was Recalled to its controller's Base (CR 456). -/
  | recalled (unit : ObjId)
  /-- A player won the game (CR 323.1). -/
  | won (p : PlayerId)
  /-- A player used an ability (CR 361): the ability at place `idx` of the card of `source`. -/
  | activated (p : PlayerId) (source : ObjId) (idx : Nat)
  /-- A player played a card: the object it has become on the Base or on the Chain (CR 349-359). -/
  | played (p : PlayerId) (obj : ObjId)
  /-- An object was killed (CR 323.4, 419): the object it has become in the Trash, and the player
  who controlled it. -/
  | died (obj : ObjId) (controller : PlayerId)
  /-- An object was stunned (CR 424). -/
  | stunned (target : ObjId)
  /-- A player discarded a card: the object it has become in the Trash (CR 423). -/
  | discarded (p : PlayerId) (obj : ObjId)
  /-- A Combat began at a Battlefield, with the Attacker (CR 466). -/
  | combatStarted (bf : ObjId) (attacker : PlayerId)
deriving DecidableEq, Repr

end Riftbound

end
