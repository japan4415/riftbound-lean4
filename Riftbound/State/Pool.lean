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
  /-- Power spent in ordinary payments since the Pool was emptied. -/
  spent : Nat := 0
  /-- Energy available only for playing Spells (CR 166, 445). -/
  spellEnergy : Nat := 0
  /-- Power spent paying separate Deflect surcharges since the Pool was emptied. -/
  deflectSpent : Nat := 0
deriving DecidableEq

/-- Preserve the historical Pool fingerprint. The archive records separate Deflect spending
alongside that fingerprint. -/
instance : Repr RunePool where
  reprPrec p _ :=
    let field (name : String) (value : Nat) :=
      Std.Format.text name ++ " := " ++ repr value
    let fields := [
      field "energy" p.energy, field "unitEnergy" p.unitEnergy,
      field "fury" p.fury, field "calm" p.calm, field "mind" p.mind, field "body" p.body,
      field "chaos" p.chaos, field "order" p.order, field "any" p.any, field "spent" p.spent]
    let fields := if p.spellEnergy == 0 then fields else fields ++ [field "spellEnergy" p.spellEnergy]
    Std.Format.bracket "{ " (Std.Format.joinSep fields (Std.Format.text "," ++ Std.Format.line)) " }"

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

/-- Add Energy that can be spent only on playing a Spell. -/
def addSpellEnergy (p : RunePool) (n : Nat) : RunePool :=
  { p with spellEnergy := p.spellEnergy + n }

/-- The Energy available for a payment, including the restricted balance eligible for it. -/
def energyFor (p : RunePool) (unit : Bool) (spell : Bool := false) : Nat :=
  p.energy + if spell then p.spellEnergy else if unit then p.unitEnergy else 0

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

/-- All Power the player has spent, including separate Deflect payments. -/
def powerSpent (p : RunePool) : Nat := p.spent + p.deflectSpent

/-- Count the actual Power removed by a separate surcharge. -/
def recordDeflectDebit (before after : RunePool) : RunePool :=
  { after with deflectSpent := before.deflectSpent + (before.totalPower - after.totalPower) }

/-- Everything in the Pool: Energy and Power. -/
def total (p : RunePool) : Nat := p.energy + p.unitEnergy + p.spellEnergy + p.totalPower

/-- The available Power in one actual source. -/
def powerIn (p : RunePool) : PowerBucket → Nat
  | .domain d => p.get d
  | .flexible => p.any

/-- Spend from exactly the named source, failing when it cannot cover the whole amount. -/
def takeBucket (p : RunePool) (bucket : PowerBucket) (amount : Nat) : Option RunePool :=
  if amount ≤ p.powerIn bucket then
    some (match bucket with
      | .domain .fury => { p with fury := p.fury - amount }
      | .domain .calm => { p with calm := p.calm - amount }
      | .domain .mind => { p with mind := p.mind - amount }
      | .domain .body => { p with body := p.body - amount }
      | .domain .chaos => { p with chaos := p.chaos - amount }
      | .domain .order => { p with order := p.order - amount }
      | .flexible => { p with any := p.any - amount })
  else none

/-- The selected source alone determines whether the amount can be paid. -/
theorem takeBucket_eq_none (p : RunePool) (bucket : PowerBucket) (amount : Nat) :
    p.takeBucket bucket amount = none ↔ p.powerIn bucket < amount := by
  unfold takeBucket
  split <;> simp_all

/-- Deduct the amount from the chosen source while preserving each other source. -/
theorem powerIn_takeBucket {p q : RunePool} {source : PowerBucket} {amount : Nat}
    (paid : p.takeBucket source amount = some q) (bucket : PowerBucket) :
    q.powerIn bucket + (if bucket = source then amount else 0) = p.powerIn bucket := by
  unfold takeBucket at paid
  split at paid
  · rename_i budget
    cases source with
    | flexible =>
      injection paid with eq
      subst q
      cases bucket with
      | flexible =>
        have covers : amount ≤ p.any := budget
        simpa [powerIn] using Nat.sub_add_cancel covers
      | domain domain => cases domain <;> simp [powerIn, get]
    | domain source =>
      cases source <;> injection paid with eq <;> subst q
      all_goals
        cases bucket with
        | flexible => simp [powerIn]
        | domain domain => cases domain <;> simp_all [powerIn, get] <;> omega
  · cases paid

/-- An exact Power deduction accounts for its whole amount in the Pool total. -/
theorem total_takeBucket {p q : RunePool} {bucket : PowerBucket} {amount : Nat}
    (paid : p.takeBucket bucket amount = some q) : q.total + amount = p.total := by
  unfold takeBucket at paid
  split at paid
  · rename_i budget
    cases bucket with
    | domain domain =>
      cases domain <;> simp only [powerIn, get] at budget <;> injection paid with eq <;> subst q <;>
        simp only [total, totalPower] <;> omega
    | flexible =>
      simp only [powerIn] at budget
      injection paid with eq
      subst q
      simp only [total, totalPower]
      omega
  · cases paid

/-- An exact Power deduction accounts for its whole amount in the Power balance. -/
theorem totalPower_takeBucket {p q : RunePool} {bucket : PowerBucket} {amount : Nat}
    (paid : p.takeBucket bucket amount = some q) : q.totalPower + amount = p.totalPower := by
  have total := total_takeBucket paid
  have energy : p.energy + p.unitEnergy + p.spellEnergy = q.energy + q.unitEnergy + q.spellEnergy := by
    unfold takeBucket at paid
    split at paid
    · cases bucket with
      | domain domain => cases domain <;> injection paid with eq <;> subst q <;> rfl
      | flexible =>
        injection paid with eq
        subst q
        rfl
    · cases paid
  unfold RunePool.total at total
  omega

/-- Spend one Power from each listed source, including repeated uses of a source. -/
def takeBuckets (p : RunePool) : List PowerBucket → Option RunePool
  | [] => some p
  | source :: rest => (p.takeBucket source 1).bind (fun next => next.takeBuckets rest)

/-- An explicit allocation accounts for every use of each source separately. -/
theorem powerIn_takeBuckets {p q : RunePool} {sources : List PowerBucket}
    (paid : p.takeBuckets sources = some q) (bucket : PowerBucket) :
    q.powerIn bucket + sources.count bucket = p.powerIn bucket := by
  induction sources generalizing p with
  | nil =>
    have same : p = q := Option.some.inj paid
    simp [same]
  | cons source rest ih =>
    cases one : p.takeBucket source 1 with
    | none => simp [takeBuckets, one] at paid
    | some next =>
      have left : next.takeBuckets rest = some q := by simpa [takeBuckets, one] using paid
      have first := powerIn_takeBucket one bucket
      have remaining := ih left
      by_cases same : source = bucket
      · subst source
        simp only [List.count_cons_self, ite_true] at *
        omega
      · have different := Ne.symm same
        simp only [List.count_cons_of_ne same, different, ite_false] at first ⊢
        omega

/-- An allocation fits the Pool exactly when each source can cover its recorded uses. -/
theorem takeBuckets_isSome_iff (p : RunePool) (sources : List PowerBucket) :
    (p.takeBuckets sources).isSome = true ↔ ∀ bucket, sources.count bucket ≤ p.powerIn bucket := by
  constructor
  · intro existsPaid bucket
    obtain ⟨q, paid⟩ := Option.isSome_iff_exists.mp existsPaid
    have balanced := powerIn_takeBuckets paid bucket
    omega
  · induction sources generalizing p with
    | nil => intro _; rfl
    | cons source rest ih =>
      intro budget
      have available := budget source
      simp only [List.count_cons_self] at available
      cases first : p.takeBucket source 1 with
      | none => have impossible := (takeBucket_eq_none p source 1).mp first; omega
      | some next =>
        simp only [takeBuckets, first, Option.bind_some]
        apply ih
        intro bucket
        have before := budget bucket
        have after := powerIn_takeBucket first bucket
        by_cases same : source = bucket
        · subst source
          simp only [List.count_cons_self, ite_true] at before after
          omega
        · have different := Ne.symm same
          simp only [List.count_cons_of_ne same, different, ite_false] at before after
          omega

/-- Spending the listed units removes exactly one unit of total resources per entry. -/
theorem total_takeBuckets {p q : RunePool} {sources : List PowerBucket}
    (paid : p.takeBuckets sources = some q) : q.total + sources.length = p.total := by
  induction sources generalizing p with
  | nil =>
    have same : p = q := Option.some.inj paid
    simp [same]
  | cons source rest ih =>
    cases first : p.takeBucket source 1 with
    | none => simp [takeBuckets, first] at paid
    | some next =>
      have left : next.takeBuckets rest = some q := by simpa [takeBuckets, first] using paid
      have one := total_takeBucket first
      have more := ih left
      simp only [List.length_cons]
      omega

/-- Deducting a list of exact sources removes one Power per entry and leaves the existing
ordinary spend count alone. -/
theorem takeBuckets_counts {p q : RunePool} {sources : List PowerBucket}
    (paid : p.takeBuckets sources = some q) :
    q.totalPower + sources.length = p.totalPower ∧ q.spent = p.spent := by
  induction sources generalizing p with
  | nil =>
    have same : p = q := Option.some.inj paid
    simp [same]
  | cons source rest ih =>
    cases first : p.takeBucket source 1 with
    | none => simp [takeBuckets, first] at paid
    | some next =>
      have left : next.takeBuckets rest = some q := by simpa [takeBuckets, first] using paid
      have one := totalPower_takeBucket first
      obtain ⟨more, ordinary⟩ := ih left
      have kept : next.spent = p.spent := by
        unfold takeBucket at first
        split at first
        · cases source with
          | flexible => injection first with equal; subst next; rfl
          | domain d => cases d <;> injection first with equal <;> subst next <;> rfl
        · cases first
      exact ⟨by simp only [List.length_cons]; omega, ordinary.trans kept⟩

/-- A separately recorded payment counts each spent Power once. -/
theorem powerSpent_recordDeflectDebit {p q : RunePool} {sources : List PowerBucket}
    (paid : p.takeBuckets sources = some q) :
    (p.recordDeflectDebit q).powerSpent = p.powerSpent + sources.length := by
  obtain ⟨removed, ordinary⟩ := takeBuckets_counts paid
  simp only [recordDeflectDebit, powerSpent, ordinary]
  omega

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
def spend (p : RunePool) (pay : Payment) (unit : Bool := false)
    (spell : Bool := false) : Option RunePool :=
  if pay.energy ≤ p.energyFor unit spell then
    let fromSpell := if spell then min p.spellEnergy pay.energy else 0
    let fromUnit := if unit && !spell then min p.unitEnergy pay.energy else 0
    let reduced := { p with
      energy := p.energy - (pay.energy - fromSpell - fromUnit)
      unitEnergy := p.unitEnergy - fromUnit
      spellEnergy := p.spellEnergy - fromSpell }
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

/-- Spell-only Energy counts toward the Pool total (CR 166). -/
theorem total_addSpellEnergy (p : RunePool) (n : Nat) :
    (p.addSpellEnergy n).total = p.total + n := by
  simp only [addSpellEnergy, total, totalPower]
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
theorem total_spend {p p' : RunePool} {pay : Payment} {unit spell : Bool}
    (h : p.spend pay unit spell = some p') :
    p'.total + (pay.energy + pay.power.length) = p.total := by
  unfold spend at h
  split at h
  · rename_i hle
    let fromSpell := if spell then min p.spellEnergy pay.energy else 0
    let fromUnit := if unit && !spell then min p.unitEnergy pay.energy else 0
    let reduced := { p with
      energy := p.energy - (pay.energy - fromSpell - fromUnit)
      unitEnergy := p.unitEnergy - fromUnit
      spellEnergy := p.spellEnergy - fromSpell }
    change ((takePowers reduced pay.power).map _) = some p' at h
    cases hq : takePowers reduced pay.power with
    | none => simp [hq] at h
    | some q =>
      simp only [hq, Option.map_some, Option.some.injEq] at h
      have := total_takePowers pay.power hq
      subst h
      dsimp only [total, totalPower, reduced] at this ⊢
      cases spell <;> cases unit <;> simp [energyFor, fromSpell, fromUnit] at hle this <;> omega
  · exact absurd h (by simp)

/-- A payment is refused when the Energy is short. -/
theorem spend_eq_none_of_energy {p : RunePool} {pay : Payment} (h : p.energy < pay.energy) :
    p.spend pay = none := by
  have : ¬ pay.energy ≤ p.energy := by omega
  simp [spend, energyFor, this]

/-- Paying nothing changes nothing. -/
theorem spend_zero (p : RunePool) (unit : Bool := false) (spell : Bool := false) :
    p.spend ⟨0, []⟩ unit spell = some p := by
  cases spell <;> cases unit <;> simp [spend, takePowers]

/-- A successful payment covers the amount of Energy from sources eligible for it. -/
theorem spend_energy_le {p q : RunePool} {pay : Payment} {unit spell : Bool}
    (h : p.spend pay unit spell = some q) : pay.energy ≤ p.energyFor unit spell := by
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

/-- Taking Power preserves Spell-only Energy. -/
theorem spellEnergy_takePowers :
    ∀ (domains : List Domain) {p q : RunePool}, p.takePowers domains = some q →
      q.spellEnergy = p.spellEnergy
  | [], _, _, h => by cases h; rfl
  | domain :: domains, p, _, h => by
    unfold takePowers at h
    cases hpower : p.takePower domain with
    | none => simp [hpower] at h
    | some remaining =>
      rw [hpower] at h
      refine (spellEnergy_takePowers domains h).trans ?_
      unfold takePower at hpower
      split at hpower
      · cases domain <;> injection hpower with same <;> subst remaining <;> rfl
      · split at hpower
        · injection hpower with same
          subst remaining
          rfl
        · cases hpower

/-- A payment outside Spell play leaves the Spell-only balance intact. -/
theorem spend_preserves_spellEnergy {p q : RunePool} {pay : Payment} {unit : Bool}
    (h : p.spend pay unit = some q) : q.spellEnergy = p.spellEnergy := by
  unfold spend at h
  split at h
  · obtain ⟨r, hr, hq⟩ := Option.map_eq_some_iff.mp h
    subst q
    simpa using spellEnergy_takePowers pay.power hr
  · simp at h

end RunePool

end Riftbound

end
