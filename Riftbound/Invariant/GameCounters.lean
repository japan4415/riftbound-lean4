module

public import Riftbound.Rules.Effects

/-! # Game counters (CR 702, 729-730) -/

public section

namespace Riftbound

/-- Buffing a Unit that already has its allowed Buff preserves the Unit and produces no event
(CR 702.3). Effects that explicitly allow additional Buffs are handled separately. -/
theorem buffObj_no_second_buff {s : GameState} {id : ObjId} {o : Object}
    (selected : s.obj? id = some o) (present : o.buffed = true)
    (single : (s.activeMods id).contains .anyBuffs = false) (giver : Option PlayerId) :
    (buffObj s id giver).1.obj? id = some o ∧ (buffObj s id giver).2 = [] := by
  have unchanged : { o with buffed := true } = o := by cases o; simp_all
  simp only [buffObj, selected, present, Bool.true_and, single, Bool.false_eq_true, ite_false,
    ite_true, GameState.obj?_modObj]
  simp [unchanged]

/-- Updating XP sets exactly one seat's counter, including when it is reset to zero. -/
theorem GameState.xpOf_setXP (s : GameState) (p q : PlayerId) (amount : Nat) :
    (s.setXP p amount).xpOf q = if p = q then amount else s.xpOf q := by
  by_cases same : p = q
  · subst q
    by_cases zero : amount = 0 <;> simp [GameState.setXP, GameState.xpOf, zero]
  · have distinct : compare p.n q.n ≠ .eq := by
      intro equal
      have sameSeat := Nat.compare_eq_eq.mp equal
      cases p; cases q; cases sameSeat
      exact same rfl
    by_cases zero : amount = 0 <;>
      simp [GameState.setXP, GameState.xpOf, zero, same, distinct,
        Std.ExtTreeMap.getD_insert, Std.ExtTreeMap.getD_erase]

/-- Gaining XP adds it to the gaining seat and preserves everyone else's counter (CR 730.1). -/
theorem xpOf_gainXPOf (s : GameState) (p q : PlayerId) (amount : Nat) :
    (gainXPOf amount s p).xpOf q = s.xpOf q + if p = q then amount else 0 := by
  unfold gainXPOf
  by_cases positive : 0 < amount
  · simp only [positive, ite_true]
    change (s.setXP p (s.xpOf p + amount)).xpOf q = _
    rw [GameState.xpOf_setXP]
    by_cases same : p = q
    · subst q; simp
    · simp [same]
  · have zero : amount = 0 := by omega
    subst amount
    simp

/-- Spending XP deducts it only from the paying seat (CR 730.2). -/
theorem GameState.xpOf_spendXP (s : GameState) (p q : PlayerId) (amount : Nat) :
    (s.spendXP p amount).xpOf q = s.xpOf q - if p = q then amount else 0 := by
  rw [GameState.spendXP, GameState.xpOf_setXP]
  by_cases same : p = q
  · subst q; simp
  · simp [same]

end Riftbound

end
