module

/-!
# Identifiers

Identifiers of the static data (design.md §5.1). Identifiers of game objects
(`PlayerId`, `PhysId`, `ObjId`, `Timestamp`) are added with the state (milestone M2).
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

end Riftbound

end
