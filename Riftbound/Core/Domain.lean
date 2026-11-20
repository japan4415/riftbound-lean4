module

/-!
# Domains

The six domains (CR 134).
-/

@[expose] public section

namespace Riftbound

/-- A domain (CR 134). -/
inductive Domain where
  /-- Fury. -/
  | fury
  /-- Calm. -/
  | calm
  /-- Mind. -/
  | mind
  /-- Body. -/
  | body
  /-- Chaos. -/
  | chaos
  /-- Order. -/
  | order
deriving DecidableEq, Repr, Hashable

/-- All six domains. -/
def Domain.all : List Domain := [.fury, .calm, .mind, .body, .chaos, .order]

/-- Every domain is in `Domain.all`. -/
theorem Domain.mem_all (d : Domain) : d ∈ Domain.all := by
  cases d <;> decide

/-- There are exactly six domains (CR 134). -/
theorem Domain.all_length : Domain.all.length = 6 := by decide

/-- `Domain.all` lists each domain once. -/
theorem Domain.all_nodup : Domain.all.Nodup := by decide

end Riftbound

end
