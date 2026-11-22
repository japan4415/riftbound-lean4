module

/-!
# Formats

The formats of the Tournament Rules (TR 402, 601, 602). Changes a format makes to the course of
a game (the extra draw of a Limited deck without a Legend) (TR 602.4.a.5.b) arrive in
milestone M5b.
-/

@[expose] public section

namespace Riftbound

/-- A tournament format (TR 402, 601, 602). -/
inductive Format where
  /-- Constructed (TR 601). -/
  | constructed
  /-- Sealed (TR 602.4.a). -/
  | sealed
  /-- Draft (TR 602.4.b). -/
  | draft
deriving DecidableEq, Repr, Hashable

/-- The format is Limited: Sealed or Draft (TR 602). -/
def Format.isLimited : Format → Bool
  | .constructed => false
  | .sealed => true
  | .draft => true

/-- The smallest Main Deck of a Limited format: 25 for Sealed (TR 602.4.a.2), 20 for Draft
(TR 602.4.b.3). Constructed has an exact size instead. -/
def Format.limitedMinMain : Format → Option Nat
  | .constructed => none
  | .sealed => some 25
  | .draft => some 20

end Riftbound

end
