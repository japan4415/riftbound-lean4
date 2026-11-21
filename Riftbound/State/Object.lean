module

public import Riftbound.Core.Ids
public import Riftbound.Core.Domain

/-!
# Game objects

The attributes of a game object (CR 119-124), kept in a table keyed by `ObjId`
(design.md §5.2). More attributes (Attach target, counters, status effects) arrive with the
rules that use them.
-/

@[expose] public section

namespace Riftbound

/-- What an object is. -/
inductive ObjKind where
  /-- A card: a physical card of a deck, and its logical card. -/
  | card (phys : PhysId) (card : CardId)
  /-- A token (CR 179-187): it has a definition but no physical card. -/
  | token (card : CardId)
  /-- An ability on the Chain (CR 337, 361): the card it comes from (kept, so that it resolves
  even when the source has left play), the place of the ability among the card's abilities, and
  the object it was used from. -/
  | chainAbility (card : CardId) (idx : Nat) (source : ObjId)
deriving DecidableEq, Repr

/-- The physical card behind an object, if it is a card. -/
def ObjKind.phys? : ObjKind → Option PhysId
  | .card p _ => some p
  | _ => none

/-- When a lasting change of Might ends (CR 475-478). -/
inductive EndPoint where
  /-- At the end of the turn. -/
  | turn
  /-- Never: for the rest of the game. -/
  | never
deriving DecidableEq, Repr

/-- A lasting change of an object's Might: how much, and when it ends. -/
structure MightMod where
  /-- The change: positive or negative. -/
  amount : Int
  /-- When it ends. -/
  ends : EndPoint
deriving DecidableEq, Repr

/-- The attributes of a game object. -/
structure Object where
  /-- What the object is. -/
  kind : ObjKind
  /-- The player who owns it (CR 127). -/
  owner : PlayerId
  /-- The player who controls it: the base value, before continuous effects (CR 188-192). -/
  controller : PlayerId
  /-- Whether it is exhausted (CR 415). -/
  exhausted : Bool := false
  /-- The damage it has taken (CR 142). -/
  damage : Nat := 0
  /-- When it became an object (CR 482). -/
  timestamp : Timestamp
  /-- For a Rune: its domain, the domain of the Power it adds (CR 164.2). `none` for what is not
  a Rune. A copy of the printed domain made when the object is made; the derived value comes with
  the Layers (milestone M6). -/
  runeDomain : Option Domain := none
  /-- For a Spell on the Chain: the objects chosen when it was played, in the order of its
  choices (CR 355). Slot `i` of the effect is `targets[i]`. It means nothing off the Chain. -/
  targets : List ObjId := []
  /-- For a Unit at a Battlefield: that Battlefield (CR 106, 144). `none` for a Unit on a Base and
  for what is not a Unit. Leaving the Board clears it. -/
  loc : Option ObjId := none
  /-- For a Battlefield: the player who controls it, if any (CR 190.6). -/
  control : Option PlayerId := none
  /-- For a Battlefield: the player whose Unit made it Contested (CR 190.3). -/
  contested : Option PlayerId := none
  /-- For a Battlefield: the players who have scored it this turn (CR 472). -/
  scored : List PlayerId := []
  /-- The abilities of this object that have been used this turn, by their place among the card's
  abilities: once for each use (CR 371, 386). Cleared when a turn begins. -/
  used : List Nat := []
  /-- The lasting changes of Might that effects have made to this object (CR 475-478). Leaving the
  Board clears them. -/
  mightMods : List MightMod := []
deriving DecidableEq, Repr

end Riftbound

end
