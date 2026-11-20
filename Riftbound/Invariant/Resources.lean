module

public import Riftbound.Invariant.Turn

/-!
# Resources

The accounting of the Rune Pool (invariant I8, roadmap.md): an Add ability adds exactly one resource
and no more, a payment takes exactly what it says (`RunePool.total_spend`), and the Pool is empty at
the start of the Main Phase and at the end of the turn (CR 167). The Pool holds natural numbers, so
it cannot be negative.
-/

@[expose] public section

namespace Riftbound

/-- **The Rune Pool is empty when the Main Phase starts** (CR 167): every player's Pool. -/
theorem microStep_main_pools {s s' : GameState} {es : List Event} {rest : List Frame}
    (hp : s.pending = .phase .main :: rest) (h : microStep s = some (s', es)) (p : PlayerId) :
    s'.poolOf p = RunePool.empty := by
  unfold microStep at h
  rw [hp] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp [GameState.poolOf, RunePool.empty]

/-- **The Rune Pool is empty at the end of the turn** (CR 167, 317.2). -/
theorem microStep_ending_pools {s s' : GameState} {es : List Event} {rest : List Frame}
    (hp : s.pending = .phase .ending :: rest) (h : microStep s = some (s', es)) (p : PlayerId) :
    s'.poolOf p = RunePool.empty := by
  unfold microStep at h
  rw [hp] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp [GameState.poolOf, RunePool.empty]

/-- **An Add ability adds exactly one resource** (I8) (CR 164.2, 430): the player's Pool grows by
one, Energy or Power of the Rune's domain, and every other Pool stays. -/
theorem applyRune_adds_one {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (h : applyRune s p c ab = some (s', es)) :
    (s'.poolOf p).total = (s.poolOf p).total + 1 ∧
      ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  cases ab with
  | exhaust =>
    obtain ⟨h1, h2⟩ := applyRune_exhaust_pool h
    exact ⟨by rw [h1, RunePool.total_addEnergy], h2⟩
  | recycle =>
    obtain ⟨d, h1, h2⟩ := applyRune_recycle_pool h
    exact ⟨by rw [h1, RunePool.total_addPower], h2⟩

end Riftbound

end
