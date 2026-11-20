module

public import Riftbound.Core.Domain

/-!
# Costs

Energy and Power costs (CR 131, 135.2.e) and the arithmetic of cost modification (CR 356).
-/

@[expose] public section

namespace Riftbound

/-- One Power symbol of a cost (CR 135.2.e). -/
inductive PowerSym where
  /-- Power of a specific domain. -/
  | domain (d : Domain)
  /-- `[A]`: Power of any domain. -/
  | any
  /-- `[C]`: Power of the domain of the card itself. -/
  | own
deriving DecidableEq, Repr, Hashable

/-- A cost: a number of Energy and a list of Power symbols (CR 131, 135.2.e). -/
structure Cost where
  /-- Energy. Never negative (CR 356.6). -/
  energy : Nat
  /-- Power symbols. -/
  power : List PowerSym
deriving DecidableEq, Repr, Hashable

namespace Cost

/-- The cost that is free. -/
def zero : Cost := ⟨0, []⟩

/-- The sum of Energy and Power to pay (CR 357.1). -/
def total (c : Cost) : Nat := c.energy + c.power.length

/-- Change Energy by `d`. A negative `d` is a reduction, and Energy never goes below 0
(CR 356.6). -/
def addEnergy (c : Cost) (d : Int) : Cost := { c with energy := ((c.energy : Int) + d).toNat }

/-- Remove up to `n` Power symbols, from the front (a discount on the Power part, CR 356.4).
Removing more than there are leaves none (CR 356.6). -/
def dropPower (c : Cost) (n : Nat) : Cost := { c with power := c.power.drop n }

/-- Energy after `addEnergy` is the clamped sum (CR 356.6). -/
theorem energy_addEnergy (c : Cost) (d : Int) :
    ((c.addEnergy d).energy : Int) = max ((c.energy : Int) + d) 0 := by
  simp only [addEnergy]
  omega

/-- A change of 0 changes nothing. -/
theorem addEnergy_zero (c : Cost) : c.addEnergy 0 = c := by
  simp [addEnergy]

/-- A reduction never raises Energy. -/
theorem energy_addEnergy_le (c : Cost) {d : Int} (h : d ≤ 0) :
    (c.addEnergy d).energy ≤ c.energy := by
  simp only [addEnergy]
  omega

/-- An increase never lowers Energy. -/
theorem le_energy_addEnergy (c : Cost) {d : Int} (h : 0 ≤ d) :
    c.energy ≤ (c.addEnergy d).energy := by
  simp only [addEnergy]
  omega

/-- A reduction larger than the Energy leaves 0 (CR 356.6). -/
theorem energy_addEnergy_eq_zero (c : Cost) {d : Int} (h : (c.energy : Int) + d ≤ 0) :
    (c.addEnergy d).energy = 0 := by
  simp only [addEnergy]
  omega

/-- The Power part after a discount of `n` symbols. -/
theorem length_power_dropPower (c : Cost) (n : Nat) :
    (c.dropPower n).power.length = c.power.length - n := by
  simp [dropPower]

/-- Discounting Power never adds symbols. -/
theorem length_power_dropPower_le (c : Cost) (n : Nat) :
    (c.dropPower n).power.length ≤ c.power.length := by
  simp [dropPower]

/-- Discounting 0 Power changes nothing. -/
theorem dropPower_zero (c : Cost) : c.dropPower 0 = c := by
  simp [dropPower]

/-- Discounts never raise the total to pay. -/
theorem total_le_of_discount (c : Cost) {d : Int} (h : d ≤ 0) (n : Nat) :
    ((c.addEnergy d).dropPower n).total ≤ c.total := by
  have h1 := energy_addEnergy_le c h
  have h2 := length_power_dropPower_le (c.addEnergy d) n
  simp only [total, dropPower, addEnergy] at h1 h2 ⊢
  omega

end Cost

end Riftbound

end
