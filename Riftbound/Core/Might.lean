module

/-!
# Might

Might (CR 143) and being Mighty (CR 706-711).
-/

@[expose] public section

namespace Riftbound

/-- Might is an integer: it can be negative (CR 143.2.c). -/
abbrev Might := Int

namespace Might

/-- The value used when Might is referenced or summed for combat damage: a negative Might
counts as 0. The real value stays negative (CR 143.2.c). -/
def eff (m : Int) : Nat := m.toNat

/-- Mighty: Might of 5 or more (CR 708). -/
def Mighty (m : Int) : Prop := 5 ≤ m

instance (m : Int) : Decidable (Mighty m) := by unfold Mighty; infer_instance

/-- A negative Might counts as 0 (CR 143.2.c). -/
theorem eff_of_neg {m : Int} (h : m < 0) : eff m = 0 := by
  simp only [eff]
  omega

/-- A non-negative Might counts as itself. -/
theorem eff_of_nonneg {m : Int} (h : 0 ≤ m) : (eff m : Int) = m := by
  simp only [eff]
  omega

/-- Mighty is decided by the counted value: a negative Might is never Mighty (CR 708). -/
theorem mighty_iff_eff (m : Int) : Mighty m ↔ 5 ≤ eff m := by
  simp only [Mighty, eff]
  omega

end Might

end Riftbound

end
