module

public import Riftbound.State.Pool
public import Riftbound.Core.Cost

/-!
# Paying a cost

How a `Payment` (Energy, and the domain of each Power) pays a `Cost` (CR 356, 357, 445): the
Energy is the cost's Energy, and each Power symbol of the cost is paid by one Power of a domain it
admits. `Cost.payments` lists every such payment, so that the legal answers can be enumerated, and
`mem_payments` says the list is exactly the payments that pay.
-/

@[expose] public section

namespace Riftbound

/-- A Power of the domain pays the symbol. `own` is the domains of the card the cost belongs to,
which the symbol `[C]` stands for (CR 135.2.e). -/
def PowerSym.paidBy (own : List Domain) : PowerSym → Domain → Bool
  | .domain d, e => d == e
  | .any, _ => true
  | .own, e => own.contains e

/-- The domains that can pay the symbol. -/
def PowerSym.choices (own : List Domain) : PowerSym → List Domain
  | .domain d => [d]
  | .any => Domain.all
  | .own => own

/-- The Power of the domains pays the symbols, one for one. -/
def powerPaid (own : List Domain) : List PowerSym → List Domain → Bool
  | [], [] => true
  | s :: ss, d :: ds => s.paidBy own d && powerPaid own ss ds
  | _, _ => false

/-- Every way of choosing a domain for each symbol. -/
def powerChoices (own : List Domain) : List PowerSym → List (List Domain)
  | [] => [[]]
  | s :: ss => (s.choices own).flatMap (fun d => (powerChoices own ss).map (d :: ·))

/-- A domain can pay a symbol exactly when it is among its choices. -/
theorem PowerSym.mem_choices (own : List Domain) (s : PowerSym) (d : Domain) :
    d ∈ s.choices own ↔ s.paidBy own d = true := by
  cases s with
  | domain e =>
    simp only [choices, paidBy, List.mem_singleton, beq_iff_eq]
    exact eq_comm
  | any => simp [choices, paidBy, Domain.mem_all]
  | own => simp [choices, paidBy]

/-- The listed choices are exactly the domain lists that pay the symbols. -/
theorem mem_powerChoices (own : List Domain) :
    ∀ (ss : List PowerSym) (ds : List Domain),
      ds ∈ powerChoices own ss ↔ powerPaid own ss ds = true
  | [], [] => by simp [powerChoices, powerPaid]
  | [], _ :: _ => by simp [powerChoices, powerPaid]
  | _ :: _, [] => by simp [powerChoices, powerPaid]
  | s :: ss, d :: ds => by
    simp only [powerChoices, powerPaid, List.mem_flatMap, List.mem_map, List.cons.injEq,
      Bool.and_eq_true]
    constructor
    · rintro ⟨e, he, l, hl, rfl, rfl⟩
      exact ⟨(PowerSym.mem_choices own s e).mp he, (mem_powerChoices own ss l).mp hl⟩
    · rintro ⟨h1, h2⟩
      exact ⟨d, (PowerSym.mem_choices own s d).mpr h1, ds, (mem_powerChoices own ss ds).mpr h2,
        rfl, rfl⟩

/-- The payment pays the cost (CR 357.1). -/
def Cost.paidBy (own : List Domain) (c : Cost) (pay : RunePool.Payment) : Bool :=
  c.energy == pay.energy && powerPaid own c.power pay.power

/-- Every payment that pays the cost. -/
def Cost.payments (own : List Domain) (c : Cost) : List RunePool.Payment :=
  (powerChoices own c.power).map (fun ds => ⟨c.energy, ds⟩)

/-- The payments listed are exactly the payments that pay. -/
theorem Cost.mem_payments (own : List Domain) (c : Cost) (pay : RunePool.Payment) :
    pay ∈ c.payments own ↔ c.paidBy own pay = true := by
  obtain ⟨e, ds⟩ := pay
  simp only [payments, paidBy, List.mem_map, Bool.and_eq_true, beq_iff_eq,
    RunePool.Payment.mk.injEq]
  constructor
  · rintro ⟨l, hl, rfl, rfl⟩
    exact ⟨rfl, (mem_powerChoices own _ _).mp hl⟩
  · rintro ⟨rfl, h⟩
    exact ⟨ds, (mem_powerChoices own _ _).mpr h, rfl, rfl⟩

/-- A payment that pays a cost takes out as much as the cost's total (CR 357.1). -/
theorem Cost.total_of_paidBy {own : List Domain} {c : Cost} {pay : RunePool.Payment}
    (h : c.paidBy own pay = true) : pay.energy + pay.power.length = c.total := by
  unfold Cost.paidBy at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hl : ∀ (ss : List PowerSym) (ds : List Domain), powerPaid own ss ds = true →
      ds.length = ss.length := by
    intro ss
    induction ss with
    | nil => intro ds hds; cases ds <;> simp_all [powerPaid]
    | cons s ss ih =>
      intro ds hds
      cases ds with
      | nil => simp [powerPaid] at hds
      | cons d ds =>
        simp only [powerPaid, Bool.and_eq_true] at hds
        simp [ih ds hds.2]
  unfold Cost.total
  rw [← h1, hl _ _ h2]

end Riftbound

end
