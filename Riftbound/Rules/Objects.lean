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

end Riftbound

end
