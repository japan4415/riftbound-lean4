module

public import Riftbound.Core.Domain

/-!
# The Rune Pool

Energy and the Power of each domain a player has (CR 166), and how they are added and paid
(CR 430, 445). The Pool holds natural numbers, so it can never go negative; what is to be proved is
that adding and paying account for exactly what they say.
-/

@[expose] public section

namespace Riftbound

/-- A player's Rune Pool (CR 166): Energy, and Power of each domain. -/
structure RunePool where
  /-- Unrestricted Energy. -/
  energy : Nat := 0
  /-- Energy available only for Units' plays and activated abilities (CR 166, 445). -/
  unitEnergy : Nat := 0
  /-- Fury Power. -/
  fury : Nat := 0
  /-- Calm Power. -/
  calm : Nat := 0
  /-- Mind Power. -/
  mind : Nat := 0
  /-- Body Power. -/
  body : Nat := 0
  /-- Chaos Power. -/
  chaos : Nat := 0
  /-- Order Power. -/
  order : Nat := 0
  /-- Power of any domain (an `[Add]` of the rainbow Power): it can pay a Power symbol of any
  domain, when the Power of that domain is not there. -/
  any : Nat := 0
  /-- How much Power was paid out of the Pool since it was last emptied (a count, not a
  resource). -/
  spent : Nat := 0
deriving DecidableEq, Repr

namespace RunePool

/-- The empty Pool: where each turn starts and ends (CR 167). -/
def empty : RunePool := {}

/-- The Power of a domain. -/
def get (p : RunePool) : Domain → Nat
  | .fury => p.fury
  | .calm => p.calm
  | .mind => p.mind
  | .body => p.body
  | .chaos => p.chaos
  | .order => p.order

/-- Add Power of a domain (CR 430). -/
def addPower (p : RunePool) (d : Domain) (n : Nat) : RunePool :=
  match d with
  | .fury => { p with fury := p.fury + n }
  | .calm => { p with calm := p.calm + n }
  | .mind => { p with mind := p.mind + n }
  | .body => { p with body := p.body + n }
  | .chaos => { p with chaos := p.chaos + n }
  | .order => { p with order := p.order + n }

/-- Add Power of any domain (CR 430). -/
def addAny (p : RunePool) (n : Nat) : RunePool := { p with any := p.any + n }

/-- Add Energy (CR 430). -/
def addEnergy (p : RunePool) (n : Nat) : RunePool := { p with energy := p.energy + n }

/-- Add Energy that can be spent only on playing a Unit or its activated ability. -/
def addUnitEnergy (p : RunePool) (n : Nat) : RunePool :=
  { p with unitEnergy := p.unitEnergy + n }

/-- The Energy available for a payment, given whether it can use the Unit-only Energy. -/
def energyFor (p : RunePool) (unit : Bool) : Nat :=
  p.energy + if unit then p.unitEnergy else 0

/-- Take one Power of a domain out, if there is one: Power of that domain, or else Power of any
domain. -/
def takePower (p : RunePool) (d : Domain) : Option RunePool :=
  if 0 < p.get d then
    some (match d with
      | .fury => { p with fury := p.fury - 1 }
      | .calm => { p with calm := p.calm - 1 }
      | .mind => { p with mind := p.mind - 1 }
      | .body => { p with body := p.body - 1 }
      | .chaos => { p with chaos := p.chaos - 1 }
      | .order => { p with order := p.order - 1 })
  else if 0 < p.any then some { p with any := p.any - 1 }
  else none

/-- All the Power in the Pool, over every domain. -/
def totalPower (p : RunePool) : Nat :=
  p.fury + p.calm + p.mind + p.body + p.chaos + p.order + p.any

/-- Everything in the Pool: Energy and Power. -/
def total (p : RunePool) : Nat := p.energy + p.unitEnergy + p.totalPower

/-- What a payment takes out of the Pool: Energy, and one Power for each domain listed
(CR 357.1, 445). The domains are the ones the player chose for `[A]` symbols. -/
structure Payment where
  /-- Energy to pay. -/
  energy : Nat
  /-- The Power to pay, one entry for each. -/
  power : List Domain
deriving DecidableEq, Repr

/-- Take the Power of the listed domains, one each. `none` if the Pool lacks any. -/
def takePowers : RunePool → List Domain → Option RunePool
  | p, [] => some p
  | p, d :: ds =>
    match p.takePower d with
    | some p' => takePowers p' ds
    | none => none

/-- Pay (CR 445). Use eligible restricted Energy before unrestricted Energy. Return `none`
if the Pool cannot cover the payment. -/
def spend (p : RunePool) (pay : Payment) (unit : Bool := false) : Option RunePool :=
  if pay.energy ≤ p.energyFor unit then
    let restricted := if unit then min p.unitEnergy pay.energy else 0
    let reduced := { p with
      energy := p.energy - (pay.energy - restricted)
      unitEnergy := p.unitEnergy - restricted }
    (takePowers reduced pay.power).map
      (fun q => { q with spent := q.spent + pay.power.length })
  else none

/-- Adding Energy adds exactly that much (CR 430). -/
theorem total_addEnergy (p : RunePool) (n : Nat) : (p.addEnergy n).total = p.total + n := by
  simp only [addEnergy, total, totalPower]
  omega

/-- Restricted Energy counts toward the Pool total (CR 166). -/
theorem total_addUnitEnergy (p : RunePool) (n : Nat) :
    (p.addUnitEnergy n).total = p.total + n := by
  simp only [addUnitEnergy, total, totalPower]
  omega

/-- Adding Power adds exactly that much, to that domain (CR 430). -/
theorem total_addPower (p : RunePool) (d : Domain) (n : Nat) :
    (p.addPower d n).total = p.total + n := by
  cases d <;> simp only [addPower, total, totalPower] <;> omega

/-- The Power added is in the domain asked. -/
theorem get_addPower_self (p : RunePool) (d : Domain) (n : Nat) :
    (p.addPower d n).get d = p.get d + n := by
  cases d <;> simp [addPower, get]

/-- The Power of the other domains does not change. -/
theorem get_addPower_ne (p : RunePool) {d e : Domain} (h : e ≠ d) (n : Nat) :
    (p.addPower d n).get e = p.get e := by
  cases d <;> cases e <;> simp_all [addPower, get]

/-- Adding Power leaves the Energy alone. -/
theorem energy_addPower (p : RunePool) (d : Domain) (n : Nat) :
    (p.addPower d n).energy = p.energy := by
  cases d <;> simp [addPower]

/-- Taking one Power takes exactly one (CR 445). -/
theorem total_takePower {p p' : RunePool} {d : Domain} (h : p.takePower d = some p') :
    p'.total + 1 = p.total := by
  unfold takePower at h
  split at h
  · rename_i hp
    cases d <;> simp only [get] at hp <;> simp only [Option.some.injEq] at h <;> subst h <;>
      simp only [total, totalPower] <;> omega
  · split at h
    · rename_i hp
      simp only [Option.some.injEq] at h
      subst h
      simp only [total, totalPower]
      omega
    · exact absurd h (by simp)

/-- Taking the listed Powers takes exactly that many (CR 445). -/
theorem total_takePowers :
    ∀ (ds : List Domain) {p p' : RunePool}, takePowers p ds = some p' →
      p'.total + ds.length = p.total
  | [], p, p', h => by
    simp only [takePowers, Option.some.injEq] at h
    subst h
    simp
  | d :: ds, p, p', h => by
    unfold takePowers at h
    split at h
    · rename_i p1 hp1
      have h1 := total_takePower hp1
      have h2 := total_takePowers ds h
      simp only [List.length_cons]
      omega
    · exact absurd h (by simp)

/-- **Paying takes out exactly what it says** (CR 445, 357.1): the Pool loses the Energy and one
Power for each domain listed, and nothing else. The Pool cannot go below nothing, because a payment
it cannot cover is refused. -/
theorem total_spend {p p' : RunePool} {pay : Payment} {unit : Bool}
    (h : p.spend pay unit = some p') :
    p'.total + (pay.energy + pay.power.length) = p.total := by
  unfold spend at h
  split at h
  · rename_i hle
    let restricted := if unit then min p.unitEnergy pay.energy else 0
    let reduced := { p with
      energy := p.energy - (pay.energy - restricted)
      unitEnergy := p.unitEnergy - restricted }
    change ((takePowers reduced pay.power).map _) = some p' at h
    cases hq : takePowers reduced pay.power with
    | none => simp [hq] at h
    | some q =>
      simp only [hq, Option.map_some, Option.some.injEq] at h
      have := total_takePowers pay.power hq
      subst h
      dsimp only [total, totalPower, reduced] at this ⊢
      cases unit <;> simp [energyFor, restricted] at hle this <;> omega
  · exact absurd h (by simp)

/-- A payment is refused when the Energy is short. -/
theorem spend_eq_none_of_energy {p : RunePool} {pay : Payment} (h : p.energy < pay.energy) :
    p.spend pay = none := by
  have : ¬ pay.energy ≤ p.energy := by omega
  simp [spend, energyFor, this]

/-- Paying nothing changes nothing. -/
theorem spend_zero (p : RunePool) (unit : Bool := false) : p.spend ⟨0, []⟩ unit = some p := by
  cases unit <;> simp [spend, takePowers]

/-- A successful payment covers the amount of Energy from sources eligible for it. -/
theorem spend_energy_le {p q : RunePool} {pay : Payment} {unit : Bool}
    (h : p.spend pay unit = some q) : pay.energy ≤ p.energyFor unit := by
  unfold spend at h
  split at h
  · assumption
  · simp at h

/-- Spending Power never spends Unit-only Energy. -/
theorem unitEnergy_takePower {p q : RunePool} {domain : Domain}
    (h : p.takePower domain = some q) : q.unitEnergy = p.unitEnergy := by
  unfold takePower at h
  split at h
  · cases domain <;> injection h with h' <;> subst q <;> rfl
  · split at h
    · injection h with h'
      subst q
      rfl
    · cases h

/-- Taking any list of Power symbols preserves Unit-only Energy. -/
theorem unitEnergy_takePowers :
    ∀ (domains : List Domain) {p q : RunePool}, p.takePowers domains = some q →
      q.unitEnergy = p.unitEnergy
  | [], _, _, h => by cases h; rfl
  | domain :: domains, p, _, h => by
    unfold takePowers at h
    cases hpower : p.takePower domain with
    | none => simp [hpower] at h
    | some remaining =>
      rw [hpower] at h
      exact (unitEnergy_takePowers domains h).trans (unitEnergy_takePower hpower)

/-- A payment for an ineligible action cannot lower the Unit-only balance. -/
theorem spend_preserves_unitEnergy {p q : RunePool} {pay : Payment}
    (h : p.spend pay = some q) : q.unitEnergy = p.unitEnergy := by
  unfold spend at h
  split at h
  · obtain ⟨r, hr, hq⟩ := Option.map_eq_some_iff.mp h
    subst q
    simpa using unitEnergy_takePowers pay.power hr
  · simp at h

end RunePool

end Riftbound

end
