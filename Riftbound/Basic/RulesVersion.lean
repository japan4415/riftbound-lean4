module

/-!
# Rules version

The versions of the Riftbound Core Rules (CR) and Tournament Rules (TR) that every
`(CR ...)` / `(TR ...)` citation in this repository refers to (design.md §9).
-/

@[expose] public section

namespace Riftbound

/-- A calendar date, used to identify a version of an official rules document. -/
structure RulesDate where
  /-- Year. -/
  year : Nat
  /-- Month, 1 to 12. -/
  month : Nat
  /-- Day of month, 1 to 31. -/
  day : Nat
deriving DecidableEq, Repr

/-- The version of the Riftbound Core Rules that citations `(CR n)` refer to.
The official documents have no version number; the "Last Updated" date identifies them. -/
def coreRulesVersion : RulesDate := ⟨2026, 10, 9⟩

/-- The version of the Riftbound Tournament Rules that citations `(TR n)` refer to. -/
def tournamentRulesVersion : RulesDate := ⟨2026, 10, 9⟩

/-- A date is well formed when its month and day are in range. -/
def RulesDate.WellFormed (d : RulesDate) : Prop :=
  1 ≤ d.month ∧ d.month ≤ 12 ∧ 1 ≤ d.day ∧ d.day ≤ 31

instance (d : RulesDate) : Decidable d.WellFormed := by
  unfold RulesDate.WellFormed; infer_instance

/-- The Core Rules version is a well formed date. -/
theorem coreRulesVersion_wellFormed : coreRulesVersion.WellFormed := by decide

/-- The Tournament Rules version is a well formed date. -/
theorem tournamentRulesVersion_wellFormed : tournamentRulesVersion.WellFormed := by decide

end Riftbound

end
