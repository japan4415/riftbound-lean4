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

/-- Remove healed damage from the corresponding marks (CR 419). -/
def healDamageMarks (amount : Nat) : List (Option PlayerId × Nat) → List (Option PlayerId × Nat)
  | [] => []
  | (who, damage) :: rest =>
    if amount < damage then (who, damage - amount) :: rest
    else healDamageMarks (amount - damage) rest

/-- Keep the damage marks in step with an object whose damage was reduced. -/
def reduceObjectDamageMarks (marks : Std.ExtTreeMap Nat (List (Option PlayerId × Nat)))
    (id before after : Nat) : Std.ExtTreeMap Nat (List (Option PlayerId × Nat)) :=
  if after < before then
    if after == 0 then marks.erase id
    else match healDamageMarks (before - after) (marks[id]?.getD []) with
      | [] => marks.erase id
      | kept => marks.insert id kept
  else marks

/-- Change every object by `f`, with access to its identifier. -/
def GameState.mapObjectsAt (s : GameState) (f : ObjId → Object → Object) : GameState :=
  let objects := s.objects.map (fun k o => f ⟨k⟩ o)
  let marks := s.damageMarks.toList.foldl (fun marks (id, _) =>
    reduceObjectDamageMarks marks id ((s.objects[id]?).map (·.damage) |>.getD 0)
      ((objects[id]?).map (·.damage) |>.getD 0)) s.damageMarks
  { s with objects, damageMarks := marks }

/-- Change every object by `f`. -/
def GameState.mapObjects (s : GameState) (f : Object → Object) : GameState :=
  s.mapObjectsAt (fun _ => f)

/-- Ready the objects the player controls (CR 416). -/
def readyOf (p : PlayerId) (o : Object) : Object :=
  if o.controller = p && !o.cantReady then { o with exhausted := false } else o

/-- Heal an object: remove its damage (CR 419). -/
def healObj (o : Object) : Object := { o with damage := 0 }

/-- What the end of the turn does to an object: it is healed, and the changes of Might that last
until the end of the turn end (CR 317.2, 478). -/
def endTurnObj (o : Object) : Object :=
  { healObj o with
    baseMightThisTurn := none
    mightMods := o.mightMods.filter (fun m => m.ends == EndPoint.never)
    stunned := false
    tempActivations := []
    tempKws := o.tempKws.filter (fun k => k.2 == EndPoint.never) }

/-- What the end of a combat does to an object: it is healed, and the changes of Might that last
until the end of the combat end. -/
def endCombatObj (o : Object) : Object :=
  { healObj o with mightMods := o.mightMods.filter (fun m => m.ends != EndPoint.combat),
                   tempKws := o.tempKws.filter (fun k => k.2 != EndPoint.combat) }

/-- What the end of a Showdown does to an object: the changes that last until the end of the
combat end (a Showdown that is not a Combat ends them too); nothing is healed. -/
def endShowdownObj (o : Object) : Object :=
  { o with mightMods := o.mightMods.filter (fun m => m.ends != EndPoint.combat),
           tempKws := o.tempKws.filter (fun k => k.2 != EndPoint.combat) }

namespace GameState

/-- The same objects are in the table. -/
theorem mem_mapObjects (s : GameState) (f : Object → Object) (k : Nat) :
    k ∈ (s.mapObjects f).objects ↔ k ∈ s.objects := by
  simp [mapObjects, mapObjectsAt, Std.ExtTreeMap.mem_map]

/-- An object after the change is the changed object. -/
theorem obj?_mapObjects (s : GameState) (f : Object → Object) (id : ObjId) :
    (s.mapObjects f).obj? id = (s.obj? id).map f := by
  simp [mapObjects, mapObjectsAt, obj?, Std.ExtTreeMap.getElem?_map]

/-- The zones do not change. -/
theorem zone_mapObjects (s : GameState) (f : Object → Object) (z : Zone) :
    (s.mapObjects f).zone z = s.zone z := rfl

/-- Nothing but the object table changes. -/
theorem sameMeta_mapObjects (s : GameState) (f : Object → Object) : SameMeta s (s.mapObjects f) :=
  rfl

/-- Changing attributes keeps the game well formed. -/
theorem wf_mapObjectsAt {s : GameState} (hwf : s.WF) (f : ObjId → Object → Object) :
    (s.mapObjectsAt f).WF :=
  hwf.congr_mem rfl (fun k => by simp [mapObjectsAt, Std.ExtTreeMap.mem_map]) rfl rfl

theorem wf_mapObjects {s : GameState} (hwf : s.WF) (f : Object → Object) :
    (s.mapObjects f).WF := wf_mapObjectsAt hwf (fun _ => f)

/-- Looking up a transformed object supplies its identifier to the transformation. -/
theorem obj?_mapObjectsAt (s : GameState) (f : ObjId → Object → Object) (id : ObjId) :
    (s.mapObjectsAt f).obj? id = (s.obj? id).map (f id) := by
  cases id
  simp [mapObjectsAt, obj?, Std.ExtTreeMap.getElem?_map]

/-- Changing attributes that are not the owner keeps `OwnerOk`. -/
theorem ownerOk_mapObjectsAt {s : GameState} (hown : s.OwnerOk) {f : ObjId → Object → Object}
    (hf : ∀ id o, (f id o).owner = o.owner) : (s.mapObjectsAt f).OwnerOk := by
  refine ⟨fun p k hk id hid o ho => ?_⟩
  rw [obj?_mapObjectsAt] at ho
  cases hs : s.obj? id with
  | none => rw [hs] at ho; simp at ho
  | some o0 =>
    rw [hs] at ho
    simp only [Option.map_some, Option.some.injEq] at ho
    subst ho
    rw [hf]
    exact hown.owner p k hk id hid o0 hs

theorem ownerOk_mapObjects {s : GameState} (hown : s.OwnerOk) {f : Object → Object}
    (hf : ∀ o, (f o).owner = o.owner) : (s.mapObjects f).OwnerOk :=
  ownerOk_mapObjectsAt (f := fun _ => f) hown (fun _ => hf)

/-- Changing attributes that are not the kind keeps the physical cards. -/
theorem physIds_mapObjectsAt (s : GameState) {f : ObjId → Object → Object}
    (hf : ∀ id o, (f id o).kind = o.kind) : (s.mapObjectsAt f).physIds = s.physIds := by
  unfold physIds
  apply filterMap_congr_mem
  intro id _
  rw [obj?_mapObjectsAt]
  cases s.obj? id with
  | none => rfl
  | some o => simp [hf]

theorem physIds_mapObjects (s : GameState) {f : Object → Object}
    (hf : ∀ o, (f o).kind = o.kind) : (s.mapObjects f).physIds = s.physIds :=
  physIds_mapObjectsAt s (f := fun _ => f) (fun _ => hf)

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

/-- Ending a Showdown leaves the card of an object alone. -/
theorem endShowdownObj_kind (o : Object) : (endShowdownObj o).kind = o.kind := rfl

/-- Ending a Showdown leaves the owner of an object alone. -/
theorem endShowdownObj_owner (o : Object) : (endShowdownObj o).owner = o.owner := rfl

/-- Ending a combat leaves the card of an object alone. -/
theorem endCombatObj_kind (o : Object) : (endCombatObj o).kind = o.kind := rfl

/-- Ending a combat leaves the owner of an object alone. -/
theorem endCombatObj_owner (o : Object) : (endCombatObj o).owner = o.owner := rfl

/-- The end of the turn keeps the owner. -/
theorem endTurnObj_owner (o : Object) : (endTurnObj o).owner = o.owner := rfl

/-- The end of the turn keeps the kind. -/
theorem endTurnObj_kind (o : Object) : (endTurnObj o).kind = o.kind := rfl

/-- Readying twice is readying once (CR 416.1.b). -/
theorem readyOf_idem (p : PlayerId) (o : Object) : readyOf p (readyOf p o) = readyOf p o := by
  unfold readyOf; split <;> simp_all

/-- Healing twice is healing once. -/
theorem healObj_idem (o : Object) : healObj (healObj o) = healObj o := rfl

private theorem damageMarks_mapObjects (s : GameState) (f : Object → Object)
    (preserves : ∀ o, (f o).damage = o.damage) : (s.mapObjects f).damageMarks = s.damageMarks := by
  have amounts (id : Nat) : ((s.objects.map (fun _ o => f o))[id]?.map (·.damage)).getD 0 =
      (s.objects[id]?.map (·.damage)).getD 0 := by
    rw [Std.ExtTreeMap.getElem?_map]
    cases s.objects[id]? <;> simp [preserves]
  unfold GameState.mapObjects GameState.mapObjectsAt
  dsimp only
  simp only [amounts, reduceObjectDamageMarks, Nat.lt_irrefl, ite_false]
  generalize s.damageMarks.toList = entries
  induction entries with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Readying the objects of a player twice is readying them once. -/
theorem mapObjects_ready_idem (s : GameState) (p : PlayerId) :
    (s.mapObjects (readyOf p)).mapObjects (readyOf p) = s.mapObjects (readyOf p) := by
  have preserved (o : Object) : (readyOf p o).damage = o.damage := by
    unfold readyOf
    split <;> rfl
  have marks := damageMarks_mapObjects (s.mapObjects (readyOf p)) (readyOf p) preserved
  simp only [GameState.mapObjects, GameState.mapObjectsAt, Std.ExtTreeMap.map_map, readyOf_idem] at marks ⊢
  rw [marks]

/-- Readying makes an object of the player ready. -/
theorem readyOf_ready {p : PlayerId} {o : Object} (h : o.controller = p) (hc : o.cantReady = false) :
    (readyOf p o).exhausted = false := by
  simp [readyOf, h, hc]

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
  let objects := s.objects.modify id.n f
  let marks := if s.damageMarks.isEmpty then s.damageMarks else
    reduceObjectDamageMarks s.damageMarks id.n ((s.obj? id).map (·.damage) |>.getD 0)
      ((objects[id.n]?).map (·.damage) |>.getD 0)
  { s with objects, damageMarks := marks }

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
