module

public import Riftbound.Rules.Owner

/-!
# Changing the attributes of objects

Awaken readies the objects of the turn player (CR 315.1, 416) and the Expiration Step heals every
Unit (CR 317.2). Both change attributes of objects and nothing else: no object is made, lost or
moved, and neither owner nor physical card changes.
-/

@[expose] public section

namespace Riftbound

/-- Change every object by `f`. -/
def GameState.mapObjects (s : GameState) (f : Object → Object) : GameState :=
  { s with objects := s.objects.map (fun _ o => f o) }

/-- Ready the objects the player controls (CR 416). -/
def readyOf (p : PlayerId) (o : Object) : Object :=
  if o.controller = p then { o with exhausted := false } else o

/-- Heal an object: remove its damage (CR 419). -/
def healObj (o : Object) : Object := { o with damage := 0 }

namespace GameState

/-- The same objects are in the table. -/
theorem mem_mapObjects (s : GameState) (f : Object → Object) (k : Nat) :
    k ∈ (s.mapObjects f).objects ↔ k ∈ s.objects := by
  simp [mapObjects, Std.ExtTreeMap.mem_map]

/-- An object after the change is the changed object. -/
theorem obj?_mapObjects (s : GameState) (f : Object → Object) (id : ObjId) :
    (s.mapObjects f).obj? id = (s.obj? id).map f := by
  simp [mapObjects, obj?, Std.ExtTreeMap.getElem?_map]

/-- The zones do not change. -/
theorem zone_mapObjects (s : GameState) (f : Object → Object) (z : Zone) :
    (s.mapObjects f).zone z = s.zone z := rfl

/-- Nothing but the object table changes. -/
theorem sameMeta_mapObjects (s : GameState) (f : Object → Object) : SameMeta s (s.mapObjects f) :=
  rfl

/-- Changing attributes keeps the game well formed. -/
theorem wf_mapObjects {s : GameState} (hwf : s.WF) (f : Object → Object) :
    (s.mapObjects f).WF :=
  hwf.congr_mem rfl (mem_mapObjects s f) rfl rfl

/-- Changing attributes that are not the owner keeps `OwnerOk`. -/
theorem ownerOk_mapObjects {s : GameState} (hown : s.OwnerOk) {f : Object → Object}
    (hf : ∀ o, (f o).owner = o.owner) : (s.mapObjects f).OwnerOk := by
  refine ⟨fun p k hk id hid o ho => ?_⟩
  rw [obj?_mapObjects] at ho
  rw [zone_mapObjects] at hid
  cases hs : s.obj? id with
  | none => rw [hs] at ho; simp at ho
  | some o0 =>
    rw [hs] at ho
    simp only [Option.map_some, Option.some.injEq] at ho
    subst ho
    rw [hf]
    exact hown.owner p k hk id hid o0 hs

/-- Changing attributes that are not the kind keeps the physical cards. -/
theorem physIds_mapObjects (s : GameState) {f : Object → Object}
    (hf : ∀ o, (f o).kind = o.kind) : (s.mapObjects f).physIds = s.physIds := by
  unfold physIds
  apply filterMap_congr_mem
  intro id _
  rw [obj?_mapObjects]
  cases s.obj? id with
  | none => rfl
  | some o => simp [hf]

end GameState

/-- Readying does not change the owner. -/
theorem readyOf_owner (p : PlayerId) (o : Object) : (readyOf p o).owner = o.owner := by
  unfold readyOf; split <;> rfl

/-- Readying does not change the kind. -/
theorem readyOf_kind (p : PlayerId) (o : Object) : (readyOf p o).kind = o.kind := by
  unfold readyOf; split <;> rfl

/-- Healing does not change the owner. -/
theorem healObj_owner (o : Object) : (healObj o).owner = o.owner := rfl

/-- Healing does not change the kind. -/
theorem healObj_kind (o : Object) : (healObj o).kind = o.kind := rfl

/-- Readying twice is readying once (CR 416.1.b). -/
theorem readyOf_idem (p : PlayerId) (o : Object) : readyOf p (readyOf p o) = readyOf p o := by
  unfold readyOf; split <;> simp_all

/-- Healing twice is healing once. -/
theorem healObj_idem (o : Object) : healObj (healObj o) = healObj o := rfl

/-- Readying the objects of a player twice is readying them once. -/
theorem mapObjects_ready_idem (s : GameState) (p : PlayerId) :
    (s.mapObjects (readyOf p)).mapObjects (readyOf p) = s.mapObjects (readyOf p) := by
  simp only [GameState.mapObjects, Std.ExtTreeMap.map_map, readyOf_idem]

/-- Readying makes an object of the player ready. -/
theorem readyOf_ready {p : PlayerId} {o : Object} (h : o.controller = p) :
    (readyOf p o).exhausted = false := by
  simp [readyOf, h]

/-- Readying leaves the objects of the other players as they were. -/
theorem readyOf_other {p : PlayerId} {o : Object} (h : o.controller ≠ p) : readyOf p o = o := by
  simp [readyOf, h]

/-- Exhaust an object (CR 415). -/
def exhaustOf (o : Object) : Object := { o with exhausted := true }

/-- Exhaust one object. -/
def GameState.exhaustObj (s : GameState) (id : ObjId) : GameState :=
  { s with objects := s.objects.modify id.n exhaustOf }

namespace GameState

/-- The same objects are in the table. -/
theorem mem_exhaustObj (s : GameState) (id : ObjId) (k : Nat) :
    k ∈ (s.exhaustObj id).objects ↔ k ∈ s.objects := by
  simp [exhaustObj, Std.ExtTreeMap.mem_modify]

/-- The object exhausted is exhausted; the others are as they were. -/
theorem obj?_exhaustObj (s : GameState) (id x : ObjId) :
    (s.exhaustObj id).obj? x = if id.n = x.n then (s.obj? id).map exhaustOf else s.obj? x := by
  simp only [exhaustObj, obj?, Std.ExtTreeMap.getElem?_modify]
  by_cases h : id.n = x.n
  · simp [h]
  · have : ¬ compare id.n x.n = .eq := fun e => h (Nat.compare_eq_eq.mp e)
    simp [h, this]

/-- Exhausting changes nothing but the object table. -/
theorem sameMeta_exhaustObj (s : GameState) (id : ObjId) : SameMeta s (s.exhaustObj id) := rfl

/-- The zones do not change. -/
theorem zone_exhaustObj (s : GameState) (id : ObjId) (z : Zone) :
    (s.exhaustObj id).zone z = s.zone z := rfl

/-- Exhausting keeps the game well formed. -/
theorem wf_exhaustObj {s : GameState} (hwf : s.WF) (id : ObjId) : (s.exhaustObj id).WF :=
  hwf.congr_mem rfl (mem_exhaustObj s id) rfl rfl

/-- Exhausting keeps `OwnerOk`. -/
theorem ownerOk_exhaustObj {s : GameState} (hown : s.OwnerOk) (id : ObjId) :
    (s.exhaustObj id).OwnerOk := by
  refine ⟨fun p k hk id2 hid2 o ho => ?_⟩
  rw [obj?_exhaustObj] at ho
  rw [zone_exhaustObj] at hid2
  split at ho
  · cases hs : s.obj? id with
    | none => rw [hs] at ho; simp at ho
    | some o0 =>
      rw [hs] at ho
      simp only [Option.map_some, Option.some.injEq] at ho
      subst ho
      have h2 : id2 = id := by
        rename_i hn
        cases id2; cases id; simp_all
      subst h2
      exact hown.owner p k hk id2 hid2 o0 hs
  · exact hown.owner p k hk id2 hid2 o ho

/-- Exhausting keeps the physical cards. -/
theorem physIds_exhaustObj (s : GameState) (id : ObjId) :
    (s.exhaustObj id).physIds = s.physIds := by
  unfold physIds
  apply filterMap_congr_mem
  intro x _
  rw [obj?_exhaustObj]
  by_cases h : id.n = x.n
  · have hx : id = x := by cases id; cases x; simp_all
    subst hx
    cases s.obj? id <;> simp [exhaustOf]
  · simp [h]

end GameState

/-- Change one object by `f`. -/
def GameState.modObj (s : GameState) (id : ObjId) (f : Object → Object) : GameState :=
  { s with objects := s.objects.modify id.n f }

namespace GameState

/-- The same objects are in the table. -/
theorem mem_modObj (s : GameState) (id : ObjId) (f : Object → Object) (k : Nat) :
    k ∈ (s.modObj id f).objects ↔ k ∈ s.objects := by
  simp [modObj, Std.ExtTreeMap.mem_modify]

/-- The object changed is the changed object; the others are as they were. -/
theorem obj?_modObj (s : GameState) (id x : ObjId) (f : Object → Object) :
    (s.modObj id f).obj? x = if id.n = x.n then (s.obj? id).map f else s.obj? x := by
  simp only [modObj, obj?, Std.ExtTreeMap.getElem?_modify]
  by_cases h : id.n = x.n
  · simp [h]
  · have : ¬ compare id.n x.n = .eq := fun e => h (Nat.compare_eq_eq.mp e)
    simp [h, this]

/-- Changing an object changes nothing but the object table. -/
theorem sameMeta_modObj (s : GameState) (id : ObjId) (f : Object → Object) :
    SameMeta s (s.modObj id f) := rfl

/-- The zones do not change. -/
theorem zone_modObj (s : GameState) (id : ObjId) (f : Object → Object) (z : Zone) :
    (s.modObj id f).zone z = s.zone z := rfl

/-- Changing an object keeps the game well formed. -/
theorem wf_modObj {s : GameState} (hwf : s.WF) (id : ObjId) (f : Object → Object) :
    (s.modObj id f).WF :=
  hwf.congr_mem rfl (mem_modObj s id f) rfl rfl

/-- Changing an object but not its owner keeps `OwnerOk`. -/
theorem ownerOk_modObj {s : GameState} (hown : s.OwnerOk) (id : ObjId) {f : Object → Object}
    (hf : ∀ o, (f o).owner = o.owner) : (s.modObj id f).OwnerOk := by
  refine ⟨fun p k hk id2 hid2 o ho => ?_⟩
  rw [obj?_modObj] at ho
  rw [zone_modObj] at hid2
  split at ho
  · cases hs : s.obj? id with
    | none => rw [hs] at ho; simp at ho
    | some o0 =>
      rw [hs] at ho
      simp only [Option.map_some, Option.some.injEq] at ho
      subst ho
      have h2 : id2 = id := by
        rename_i hn
        cases id2; cases id; simp_all
      subst h2
      rw [hf]
      exact hown.owner p k hk id2 hid2 o0 hs
  · exact hown.owner p k hk id2 hid2 o ho

/-- Changing an object but not its kind keeps the physical cards. -/
theorem physIds_modObj (s : GameState) (id : ObjId) {f : Object → Object}
    (hf : ∀ o, (f o).kind = o.kind) : (s.modObj id f).physIds = s.physIds := by
  unfold physIds
  apply filterMap_congr_mem
  intro x _
  rw [obj?_modObj]
  by_cases h : id.n = x.n
  · have hx : id = x := by cases id; cases x; simp_all
    subst hx
    cases s.obj? id <;> simp [hf]
  · simp [h]

end GameState

end Riftbound

end
