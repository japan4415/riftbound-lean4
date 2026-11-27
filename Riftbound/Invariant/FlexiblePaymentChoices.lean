module

public import Riftbound.Rules.Pay

/-!
# Canonical flexible payments (CR 356-357)

The engine enumerates domain bags in its fixed domain order. This specification describes a bag by
choosing a number for each domain without referring to the enumeration or to its search bounds.
-/

@[expose] public section

namespace Riftbound

/-- The bag uses each domain consecutively in the given order and within its stated limit. -/
inductive PowerBagWithin {Source : Type} : List (Source × Nat) → List Source → Prop where
  /-- With no more domain limits there are no further choices. -/
  | empty : PowerBagWithin [] []
  /-- Choose the number used from the first domain before assigning the rest. -/
  | extend {source : Source} {limit used : Nat} {caps : List (Source × Nat)} {rest : List Source}
      (within : used ≤ limit) (remaining : PowerBagWithin caps rest) :
      PowerBagWithin ((source, limit) :: caps) (List.replicate used source ++ rest)

/-- Enumeration offers all and only the canonical bags of the required size. -/
theorem mem_powerBagsOf_iff {Source : Type} {amount : Nat}
    {caps : List (Source × Nat)} {bag : List Source} :
    bag ∈ powerBagsOf amount caps ↔ bag.length = amount ∧ PowerBagWithin caps bag := by
  induction caps generalizing amount bag with
  | nil =>
    constructor
    · intro membership
      by_cases zero : amount = 0
      · subst amount
        have empty : bag = [] := by simpa [powerBagsOf] using membership
        subst bag
        exact ⟨rfl, .empty⟩
      · simp [powerBagsOf, zero] at membership
    · rintro ⟨length, within⟩
      cases within
      simp_all [powerBagsOf]
  | cons limit caps ih =>
    obtain ⟨domain, cap⟩ := limit
    simp only [powerBagsOf, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨used, hused, rest, placed, rfl⟩
      obtain ⟨size, follows⟩ := ih.mp placed
      have within : used ≤ min cap amount := by omega
      exact ⟨by simp only [List.length_append, List.length_replicate]; omega,
        .extend (Nat.le_trans within (Nat.min_le_left _ _)) follows⟩
    · rintro ⟨size, follows⟩
      cases follows
      rename_i used rest within remaining
      simp only [List.length_append, List.length_replicate] at size
      have withinBound : used ≤ min cap amount := Nat.le_min.mpr ⟨within, by omega⟩
      exact ⟨used, by omega, rest, ih.mpr ⟨by omega, remaining⟩, rfl⟩

namespace RunePool

/-- An explicit allocation is offered exactly when its canonical order, size, and source
balances are valid. -/
theorem mem_allocatedPowerPayments_iff {pool : RunePool} {amount : Nat} {sources : List PowerBucket} :
    sources ∈ pool.allocatedPowerPayments amount ↔ sources.length = amount ∧
      PowerBagWithin (PowerBucket.all.map (fun source => (source, pool.powerIn source))) sources ∧
      ∀ source, sources.count source ≤ pool.powerIn source := by
  simp only [allocatedPowerPayments, List.mem_filter, mem_powerBagsOf_iff, takeBuckets_isSome_iff,
    and_assoc]


private theorem totalPower_takePower {pool remaining : RunePool} {domain : Domain}
    (paid : pool.takePower domain = some remaining) : remaining.totalPower + 1 = pool.totalPower := by
  have total := total_takePower paid
  have energy : pool.energy = remaining.energy := by
    unfold takePower at paid
    split at paid
    · cases domain <;> injection paid with h <;> subst remaining <;> rfl
    · split at paid
      · injection paid with h
        subst remaining
        rfl
      · cases paid
  have unitEnergy := unitEnergy_takePower paid
  have spellEnergy : pool.spellEnergy = remaining.spellEnergy := by
    exact (spellEnergy_takePowers [domain] (by simp [takePowers, paid])).symm
  simp only [RunePool.total] at total
  omega

/-- A payable list of domain payments uses exactly that much Power. -/
theorem totalPower_takePowers {pool remaining : RunePool} {domains : List Domain}
    (paid : pool.takePowers domains = some remaining) :
    remaining.totalPower + domains.length = pool.totalPower := by
  induction domains generalizing pool with
  | nil =>
    simp only [takePowers, Option.some.injEq] at paid
    subst pool
    simp
  | cons domain rest ih =>
    cases h : pool.takePower domain with
    | none => simp [takePowers, h] at paid
    | some next =>
      have takeOne := totalPower_takePower h
      have takeRest := ih (by simpa [takePowers, h] using paid)
      simp only [List.length_cons]
      omega

end RunePool

/-- A flexible payment is offered exactly when its canonical domain bag is payable. The
aggregate budget check in the enumeration rules out no payable answer. -/
theorem Cost.mem_flexiblePayments_iff {cost : Cost} {pool : RunePool} {payment : RunePool.Payment} :
    payment ∈ cost.flexiblePayments pool ↔
      cost.paidBy [] payment = true ∧ (pool.takePowers payment.power).isSome = true ∧
        PowerBagWithin (Domain.all.map (fun domain => (domain, pool.get domain + pool.any))) payment.power := by
  constructor
  · intro member
    unfold flexiblePayments at member
    split at member
    · simp at member
    · obtain ⟨combined, accepted⟩ := List.mem_filter.mp member
      obtain ⟨bag, within, rfl⟩ := List.mem_map.mp combined
      simp only [Bool.and_eq_true] at accepted
      exact ⟨accepted.1, accepted.2, (mem_powerBagsOf_iff.mp within).2⟩
  · rintro ⟨pays, available, within⟩
    have energy : cost.energy = payment.energy := by
      simp only [Cost.paidBy, Bool.and_eq_true, beq_iff_eq] at pays
      exact pays.1
    have total := Cost.total_of_paidBy pays
    have count : payment.power.length = cost.power.length := by
      simp only [Cost.total, energy] at total
      omega
    have budget : cost.power.length ≤ pool.totalPower := by
      obtain ⟨remaining, paid⟩ := Option.isSome_iff_exists.mp available
      have := RunePool.totalPower_takePowers paid
      omega
    unfold flexiblePayments
    split
    · omega
    · exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨payment.power,
        mem_powerBagsOf_iff.mpr ⟨count, within⟩, by cases payment; simp_all⟩,
        by simp [pays, available]⟩

end Riftbound

end
