module

/-!
# Identifiers

Identifiers of the static data (design.md §5.1). Identifiers of players,
physical cards and game objects are values of the running game (design.md §5.1).
-/

@[expose] public section

namespace Riftbound

/-- Identifier of a logical card (a card definition). Reprints, showcase and alt-art printings
share one `CardId`. The value is the first printing's public code without the set size,
for example `"OGN-029"` (card-data.md §3). -/
structure CardId where
  /-- The textual identifier. -/
  code : String
deriving DecidableEq, Repr, Hashable

/-- Identifier of a set (expansion), for example `"OGN"` for Origins. -/
structure SetCode where
  /-- The textual set code. -/
  code : String
deriving DecidableEq, Repr, Hashable

/-- A seat (CR 115). Seats are numbered from 0 in turn order. -/
structure PlayerId where
  /-- The seat number. -/
  n : Nat
deriving DecidableEq, Repr, Hashable

/-- A physical card: one card of a deck list. Conservation laws are stated per `PhysId`
(design.md §5.1). Tokens have no `PhysId` (CR 185). -/
structure PhysId where
  /-- The number. -/
  n : Nat
deriving DecidableEq, Repr, Hashable

/-- A game object. Moving into or out of a Non-Board zone makes a new object with a new
`ObjId` (CR 124). -/
structure ObjId where
  /-- The number. -/
  n : Nat
deriving DecidableEq, Repr, Hashable

/-- The point in time an effect started to apply (CR 482). -/
structure Timestamp where
  /-- The number. -/
  n : Nat
deriving DecidableEq, Repr, Hashable

end Riftbound

end
