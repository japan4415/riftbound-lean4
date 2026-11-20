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
  /-- Energy. -/
  energy : Nat := 0
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

/-- Add Energy (CR 430). -/
def addEnergy (p : RunePool) (n : Nat) : RunePool := { p with energy := p.energy + n }

/-- Take one Power of a domain out, if there is one. -/
def takePower (p : RunePool) (d : Domain) : Option RunePool :=
  if 0 < p.get d then
    some (match d with
      | .fury => { p with fury := p.fury - 1 }
      | .calm => { p with calm := p.calm - 1 }
      | .mind => { p with mind := p.mind - 1 }
      | .body => { p with body := p.body - 1 }
      | .chaos => { p with chaos := p.chaos - 1 }
      | .order => { p with order := p.order - 1 })
  else none

/-- All the Power in the Pool, over every domain. -/
def totalPower (p : RunePool) : Nat := p.fury + p.calm + p.mind + p.body + p.chaos + p.order

/-- Everything in the Pool: Energy and Power. -/
def total (p : RunePool) : Nat := p.energy + p.totalPower

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

/-- Pay (CR 445): `none` when the Pool cannot cover the payment. -/
def spend (p : RunePool) (pay : Payment) : Option RunePool :=
  if pay.energy ≤ p.energy then takePowers { p with energy := p.energy - pay.energy } pay.power
  else none

/-- Adding Energy adds exactly that much (CR 430). -/
theorem total_addEnergy (p : RunePool) (n : Nat) : (p.addEnergy n).total = p.total + n := by
  simp only [addEnergy, total, totalPower]
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
theorem total_spend {p p' : RunePool} {pay : Payment} (h : p.spend pay = some p') :
    p'.total + (pay.energy + pay.power.length) = p.total := by
  unfold spend at h
  split at h
  · rename_i hle
    have := total_takePowers pay.power h
    simp only [total, totalPower] at this ⊢
    omega
  · exact absurd h (by simp)

/-- A payment is refused when the Energy is short. -/
theorem spend_eq_none_of_energy {p : RunePool} {pay : Payment} (h : p.energy < pay.energy) :
    p.spend pay = none := by
  have : ¬ pay.energy ≤ p.energy := by omega
  simp [spend, this]

/-- Paying nothing changes nothing. -/
theorem spend_zero (p : RunePool) : p.spend ⟨0, []⟩ = some p := by
  simp [spend, takePowers]

end RunePool

end Riftbound

end
