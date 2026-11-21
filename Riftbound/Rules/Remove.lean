module

public import Riftbound.Rules.Add

/-!
# Making and removing objects that are not cards

An ability on the Chain is an object (design.md §5.2): it goes on the Chain zone when the ability
is used, and it ceases to exist when it has resolved (CR 337, 340). It has no physical card, so
adding and removing it keeps the physical cards of the game.
-/

@[expose] public section

namespace Riftbound

/-- Remove an object from the game: it leaves its zone and the object table. `none` if it is on no
zone. Only what is not a physical card is removed this way (`removeObj_physIds`). -/
def removeObj (s : GameState) (id : ObjId) : Option GameState :=
  match s.locate id with
  | some z => some { s.setZone z ((s.zone z).erase id) with objects := s.objects.erase id.n }
  | none => none

/-- What removing an object does: it is taken out of the zone it is on, and out of the table. -/
theorem removeObj_spec {s s' : GameState} {id : ObjId} (h : removeObj s id = some s') :
    ∃ z, z ∈ allZones s.playerCount ∧ id ∈ s.zone z ∧
      s' = { s.setZone z ((s.zone z).erase id) with objects := s.objects.erase id.n } := by
  unfold removeObj at h
  split at h
  · rename_i z hz
    obtain ⟨hzm, hid⟩ := GameState.locate_spec hz
    simp only [Option.some.injEq] at h
    exact ⟨z, hzm, hid, h.symm⟩
  · exact absurd h (by simp)

/-- The identifiers on the zones after a removal are those before, without the one removed. -/
theorem removeObj_zoneIds {s s' : GameState} {id : ObjId} (h : removeObj s id = some s') :
    s'.zoneIds.Perm (s.zoneIds.erase id) := by
  obtain ⟨z, hz, hid, rfl⟩ := removeObj_spec h
  have hnd := allZones_nodup s.playerCount
  obtain ⟨L, hL⟩ : ∃ L, L = allZones s.playerCount := ⟨_, rfl⟩
  rw [← hL] at hnd hz
  have e1 := flatMap_split L s.zone z hz
  have e2 : (L.flatMap (s.setZone z ((s.zone z).erase id)).zone).Perm
      ((s.zone z).erase id ++ (L.erase z).flatMap s.zone) := by
    have e := flatMap_split L (s.setZone z ((s.zone z).erase id)).zone z hz
    have hrest : (L.erase z).flatMap (s.setZone z ((s.zone z).erase id)).zone =
        (L.erase z).flatMap s.zone := by
      apply flatMap_one_congr L hnd
      intro x _ hx
      exact GameState.zone_setZone_ne s hx _
    rw [hrest, GameState.zone_setZone_self] at e
    exact e
  have hzs : s.zoneIds = L.flatMap s.zone := by
    unfold GameState.zoneIds
    rw [← hL]
  have e3 : (s.zoneIds.erase id).Perm ((s.zone z ++ (L.erase z).flatMap s.zone).erase id) := by
    rw [hzs]
    exact e1.erase id
  rw [List.erase_append_left _ hid] at e3
  show ((allZones s.playerCount).flatMap _).Perm _
  rw [← hL]
  exact e2.trans e3.symm

/-- Removing an object keeps the game well formed. -/
theorem removeObj_wf {s s' : GameState} {id : ObjId} (hwf : s.WF) (h : removeObj s id = some s') :
    s'.WF := by
  have hperm := removeObj_zoneIds h
  obtain ⟨z, hz, hid, hs'⟩ := removeObj_spec h
  have hnd : (s.zoneIds.erase id).Nodup := hwf.nodup.erase id
  have hsub : ∀ x ∈ s'.zoneIds, x ∈ s.zoneIds ∧ x ≠ id := fun x hx => by
    have := hperm.mem_iff.mp hx
    exact ⟨List.mem_of_mem_erase this, ((List.Nodup.mem_erase_iff hwf.nodup).mp this).1⟩
  have hne : ∀ x : ObjId, x ≠ id → x.n ≠ id.n := fun x hx e => by
    exact hx (by cases x; cases id; simp_all)
  refine ⟨hperm.nodup_iff.mpr hnd, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hsub x hx
    rw [hs']
    show x.n ∈ s.objects.erase id.n
    rw [Std.ExtTreeMap.mem_erase]
    refine ⟨?_, hwf.table_of_zone x h1⟩
    intro e
    exact hne x h2 (Nat.compare_eq_eq.mp e).symm
  · intro k hk
    rw [hs'] at hk
    have hk' : k ∈ s.objects.erase id.n := hk
    rw [Std.ExtTreeMap.mem_erase] at hk'
    obtain ⟨hk1, hk2⟩ := hk'
    obtain ⟨x, hx, hxk⟩ := hwf.zone_of_table k hk2
    refine ⟨x, hperm.symm.mem_iff.mp ?_, hxk⟩
    refine (List.Nodup.mem_erase_iff hwf.nodup).mpr ⟨fun e => ?_, hx⟩
    subst e
    exact hk1 (by rw [← hxk]; exact Nat.compare_eq_eq.mpr rfl)
  · intro x hx
    rw [hs']
    exact hwf.lt_nextId x (hsub x hx).1
  · intro k hk
    rw [hs'] at hk
    have hk' : k ∈ (s.setZone z ((s.zone z).erase id)).zones := hk
    simp only [GameState.setZone, Std.ExtTreeMap.mem_insert] at hk'
    show ∃ z' ∈ allZones s'.playerCount, z'.key = k
    have hcnt : s'.playerCount = s.playerCount := by rw [hs']; rfl
    rw [hcnt]
    rcases hk' with hk' | hk'
    · exact ⟨z, hz, Nat.compare_eq_eq.mp hk'⟩
    · exact hwf.zones_valid k hk'

/-- Removing an object keeps the physical cards, when the object is not a physical card. -/
theorem removeObj_physIds {s s' : GameState} {id : ObjId} {o : Object} (hwf : s.WF)
    (h : removeObj s id = some s') (ho : s.obj? id = some o) (hk : o.kind.phys? = none) :
    s'.physIds.Perm s.physIds := by
  have hperm := removeObj_zoneIds h
  obtain ⟨z, hz, hid, hs'⟩ := removeObj_spec h
  have hsub : ∀ x ∈ s.zoneIds.erase id, x ≠ id := fun x hx =>
    ((List.Nodup.mem_erase_iff hwf.nodup).mp hx).1
  have hne : ∀ x : ObjId, x ≠ id → x.n ≠ id.n := fun x hx e => by
    exact hx (by cases x; cases id; simp_all)
  have hobj : ∀ x ∈ s.zoneIds.erase id, s'.obj? x = s.obj? x := fun x hx => by
    rw [hs']
    simp only [GameState.obj?]
    rw [Std.ExtTreeMap.getElem?_erase]
    have : ¬ compare id.n x.n = .eq := fun e => hne x (hsub x hx) (Nat.compare_eq_eq.mp e).symm
    simp [this]
  have hidmem : id ∈ s.zoneIds := GameState.mem_zoneIds hz hid
  have h1 : (s.zoneIds.erase id).filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) =
      (s.zoneIds.erase id).filterMap (fun x => (s.obj? x).bind (·.kind.phys?)) := by
    apply filterMap_congr_mem
    intro x hx
    rw [hobj x hx]
  have p2 : s.physIds.Perm
      ((s.zoneIds.erase id).filterMap (fun x => (s.obj? x).bind (·.kind.phys?))) := by
    have p := (List.perm_cons_erase hidmem).filterMap (fun x => (s.obj? x).bind (·.kind.phys?))
    have hid0 : ((s.obj? id).bind (·.kind.phys?)) = none := by simp [ho, hk]
    simp only [List.filterMap_cons, hid0] at p
    exact p
  have p1 := List.Perm.filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) hperm
  rw [h1] at p1
  exact p1.trans p2.symm

/-- What adding an object does: it goes to a zone of the game that can hold it, under the next
identifier. -/
theorem addObject_spec {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (h : addObject s o z pos = some (s', id)) :
    z ∈ allZones s.playerCount ∧ id = ⟨s.nextId⟩ ∧
      s' = { s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z)) with
        objects := s.objects.insert s.nextId { o with timestamp := ⟨s.nextTimestamp⟩ },
        nextId := s.nextId + 1, nextTimestamp := s.nextTimestamp + 1 } := by
  unfold addObject at h
  split at h
  · rename_i hzc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hzc.1, rfl, rfl⟩
  · exact absurd h (by simp)

/-- The identifiers on the zones after adding an object are those before, and the new one. -/
theorem addObject_zoneIds {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (h : addObject s o z pos = some (s', id)) : s'.zoneIds.Perm (id :: s.zoneIds) := by
  obtain ⟨hz, rfl, rfl⟩ := addObject_spec h
  have hnd := allZones_nodup s.playerCount
  obtain ⟨L, hL⟩ : ∃ L, L = allZones s.playerCount := ⟨_, rfl⟩
  rw [← hL] at hnd hz
  have e1 := flatMap_split L s.zone z hz
  show ((allZones s.playerCount).flatMap _).Perm _
  rw [← hL]
  have e2 := flatMap_split L (s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z))).zone z hz
  have hrest : (L.erase z).flatMap (s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z))).zone =
      (L.erase z).flatMap s.zone := by
    apply flatMap_one_congr L hnd
    intro x _ hx
    exact GameState.zone_setZone_ne s hx _
  rw [hrest, GameState.zone_setZone_self] at e2
  refine e2.trans ?_
  refine ((Pos.insert_perm pos _ _).append_right _).trans ?_
  have hzs : s.zoneIds = L.flatMap s.zone := by
    unfold GameState.zoneIds
    rw [← hL]
  rw [hzs]
  exact List.Perm.cons _ e1.symm

/-- Adding an object that is not a physical card keeps the physical cards. -/
theorem addObject_physIds {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (hwf : s.WF) (h : addObject s o z pos = some (s', id)) (hk : o.kind.phys? = none) :
    s'.physIds.Perm s.physIds := by
  have hperm := addObject_zoneIds h
  obtain ⟨hz, hid, hs'⟩ := addObject_spec h
  have hobj : ∀ x ∈ s.zoneIds, s'.obj? x = s.obj? x := fun x hx => by
    have hlt := hwf.lt_nextId x hx
    rw [hs']
    simp only [GameState.obj?]
    rw [Std.ExtTreeMap.getElem?_insert]
    have : ¬ compare s.nextId x.n = .eq := fun e => by
      have := Nat.compare_eq_eq.mp e
      omega
    simp [this]
  have hnew : ((s'.obj? id).bind (·.kind.phys?)) = none := by
    rw [hid, hs']
    simp [GameState.obj?, hk]
  have h1 : s.zoneIds.filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) =
      s.zoneIds.filterMap (fun x => (s.obj? x).bind (·.kind.phys?)) := by
    apply filterMap_congr_mem
    intro x hx
    rw [hobj x hx]
  unfold GameState.physIds
  have p1 := List.Perm.filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) hperm
  simp only [List.filterMap_cons, hnew] at p1
  rw [h1] at p1
  exact p1

/-- Adding an object changes nothing outside the zones, the table and the counters. -/
theorem addObject_sameMeta {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (h : addObject s o z pos = some (s', id)) : SameMeta s s' := by
  obtain ⟨-, -, rfl⟩ := addObject_spec h
  rfl

/-- Adding an object to a zone leaves the other zones as they were. -/
theorem addObject_zone_other {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (h : addObject s o z pos = some (s', id)) {z' : Zone} (hne : z' ≠ z) :
    s'.zone z' = s.zone z' := by
  obtain ⟨-, -, rfl⟩ := addObject_spec h
  exact GameState.zone_setZone_ne s hne _

/-- Removing an object changes nothing outside the zones, the table and the counters. -/
theorem removeObj_sameMeta {s s' : GameState} {id : ObjId} (h : removeObj s id = some s') :
    SameMeta s s' := by
  obtain ⟨-, -, -, rfl⟩ := removeObj_spec h
  rfl

/-- Removing an object keeps `OwnerOk`. -/
theorem removeObj_ownerOk {s s' : GameState} {id : ObjId} (hwf : s.WF) (hown : s.OwnerOk)
    (h : removeObj s id = some s') : s'.OwnerOk := by
  have hperm := removeObj_zoneIds h
  obtain ⟨z, hz, hid, hs'⟩ := removeObj_spec h
  refine ⟨fun p k hk x hx o2 ho2 => ?_⟩
  have hxz : x ∈ s.zone (.player p k) := by
    by_cases hzz : Zone.player p k = z
    · subst hzz
      have e : s'.zone (Zone.player p k) = (s.zone (Zone.player p k)).erase id := by
        rw [hs']
        exact GameState.zone_setZone_self s _ _
      rw [e] at hx
      exact List.mem_of_mem_erase hx
    · have e : s'.zone (Zone.player p k) = s.zone (Zone.player p k) := by
        rw [hs']
        exact GameState.zone_setZone_ne s hzz _
      rwa [e] at hx
  have hxid : x ≠ id := by
    have hxm : x ∈ s'.zoneIds := GameState.mem_zoneIds
      (GameState.zone_valid_of_mem (removeObj_wf hwf h) hx) hx
    exact ((List.Nodup.mem_erase_iff hwf.nodup).mp (hperm.mem_iff.mp hxm)).1
  have hne : x.n ≠ id.n := fun e => hxid (by cases x; cases id; simp_all)
  have ho1 : s.obj? x = some o2 := by
    rw [hs'] at ho2
    simp only [GameState.obj?] at ho2 ⊢
    rw [Std.ExtTreeMap.getElem?_erase] at ho2
    have : ¬ compare id.n x.n = .eq := fun e => hne (Nat.compare_eq_eq.mp e).symm
    simpa [this] using ho2
  exact hown.owner p k hk x hxz o2 ho1

end Riftbound

end
