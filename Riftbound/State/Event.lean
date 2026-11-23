module

public import Riftbound.State.Zone
public import Riftbound.State.Phase

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
  /-- A phase of the turn of a player began (CR 315-317). -/
  | phaseStarted (p : PlayerId) (ph : Phase)
  /-- An object was stunned (CR 424). -/
  | stunned (target : ObjId)
  /-- An object got a buff (CR 701). -/
  | buffed (target : ObjId)
  /-- The player looked at a card of their Main Deck (and did not draw it). -/
  | lookedAt (p : PlayerId) (card : ObjId)
  /-- The player chose the object with a spell they played. -/
  | chosenBySpell (p : PlayerId) (target : ObjId)
  /-- The player killed a unit with a spell. -/
  | killedBySpell (p : PlayerId)
  /-- The player recycled one or more cards. -/
  | recycled (p : PlayerId)
  /-- The conquer effects of a unit are activated by an effect. -/
  | conquerActivated (u : ObjId)
  /-- The player played a card from Hidden (CR 811). -/
  | hiddenPlayed (p : PlayerId)
  /-- A player discarded a card: the object it has become in the Trash (CR 423). `last` is
  whether it ends the discarding of the effect: the abilities that wait for "one or more" cards
  to be discarded fire only then. -/
  | discarded (p : PlayerId) (obj : ObjId) (last : Bool)
  /-- An Equipment was attached to a unit. -/
  | attached (gear unit : ObjId)
  /-- A player spent a buff of a unit of theirs (CR 704). -/
  | buffSpent (p : PlayerId)
  /-- A Combat began at a Battlefield, with the Attacker (CR 466). -/
  | combatStarted (bf : ObjId) (attacker : PlayerId)
  /-- A Combat at a Battlefield ended and only the units of the player were left there: they won
  it (CR 468). -/
  | combatWon (bf : ObjId) (winner : PlayerId)
deriving DecidableEq, Repr

end Riftbound

end
