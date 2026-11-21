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
  /-- An ability on the Chain, with the object it comes from. -/
  | chainAbility (source : ObjId)
deriving DecidableEq, Repr

/-- The physical card behind an object, if it is a card. -/
def ObjKind.phys? : ObjKind → Option PhysId
  | .card p _ => some p
  | _ => none

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
deriving DecidableEq, Repr

end Riftbound

end
