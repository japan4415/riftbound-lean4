module

/-!
# List lemmas

Generic facts about `List.flatMap` and permutations, used to reason about the zones of a game.
Nothing here depends on the rules.
-/

@[expose] public section

namespace Riftbound

/-- `flatMap` only depends on `f` at the members of the list. -/
theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- `filterMap` only depends on `f` at the members of the list. -/
theorem filterMap_congr_mem {α β : Type} (l : List α) (f g : α → Option β)
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    rw [h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Pull one member out of a `flatMap`. -/
theorem flatMap_split {α β : Type} [DecidableEq α] (L : List α) (f : α → List β) (z : α)
    (hz : z ∈ L) : (L.flatMap f).Perm (f z ++ (L.erase z).flatMap f) := by
  have h := List.Perm.flatMap_right f (List.perm_cons_erase hz)
  simpa using h

/-- Pull two different members out of a `flatMap`. -/
theorem flatMap_two {α β : Type} [DecidableEq α] (L : List α)
    (f : α → List β) (a b : α) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    (L.flatMap f).Perm (f a ++ (f b ++ ((L.erase a).erase b).flatMap f)) := by
  refine (flatMap_split L f a ha).trans ?_
  refine List.Perm.append_left _ ?_
  exact flatMap_split (L.erase a) f b ((List.mem_erase_of_ne (Ne.symm hab)).mpr hb)

/-- The rest of a `flatMap` is unchanged when `f` changes only at the two pulled-out members. -/
theorem flatMap_two_congr {α β : Type} [DecidableEq α] (L : List α) (hnd : L.Nodup)
    (f g : α → List β) (a b : α)
    (hg : ∀ x ∈ L, x ≠ a → x ≠ b → g x = f x) :
    ((L.erase a).erase b).flatMap g = ((L.erase a).erase b).flatMap f := by
  apply flatMap_congr_mem
  intro x hx
  have h1 := List.mem_of_mem_erase hx
  have h2 := List.mem_of_mem_erase h1
  have hxb : x ≠ b := fun e => by
    subst e
    exact ((List.Nodup.mem_erase_iff (hnd.erase a)).mp hx).1 rfl
  have hxa : x ≠ a := fun e => by
    subst e
    exact ((List.Nodup.mem_erase_iff hnd).mp h1).1 rfl
  exact hg x h2 hxa hxb

end Riftbound

end
