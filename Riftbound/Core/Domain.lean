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

/-- The actual source of Power in the Pool. Flexible Power is separate from every domain. -/
inductive PowerBucket where
  /-- Power that has already been assigned to a domain. -/
  | domain (value : Domain)
  /-- Power that can be spent as any domain. -/
  | flexible
deriving DecidableEq, Repr, Hashable

/-- All typed sources, followed by the flexible source. -/
def PowerBucket.all : List PowerBucket := Domain.all.map .domain ++ [.flexible]

/-- Every Power source is in the list. -/
theorem PowerBucket.mem_all (bucket : PowerBucket) : bucket ∈ PowerBucket.all := by
  cases bucket <;> simp [PowerBucket.all, Domain.mem_all]

end Riftbound

end
