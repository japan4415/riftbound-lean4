module

public import Riftbound.Rules.Move

/-!
# Rearranging a zone

A shuffle, or the order chosen for a Recycle, replaces the contents of a zone by an
arrangement of the same objects. Nothing is made or lost, so the game stays well formed and the
physical cards stay the same.
-/

@[expose] public section

namespace Riftbound

namespace GameState

/-- Replace the contents of a zone by an arrangement of them. -/
def reorder (s : GameState) (z : Zone) (l : List ObjId) : GameState := s.setZone z l

/-- The objects on zones stay the same, up to order. -/
theorem zoneIds_reorder {s : GameState} {z : Zone} {l : List ObjId}
    (hz : z ∈ allZones s.playerCount) (hp : l.Perm (s.zone z)) :
    (s.reorder z l).zoneIds.Perm s.zoneIds := by
  have hnd := allZones_nodup s.playerCount
  have hcount : (s.reorder z l).playerCount = s.playerCount := rfl
  unfold zoneIds
  rw [hcount]
  obtain ⟨L, hL⟩ : ∃ L, L = allZones s.playerCount := ⟨_, rfl⟩
  rw [← hL] at hnd hz
  have e1 := flatMap_split L (s.reorder z l).zone z hz
  have e2 := flatMap_split L s.zone z hz
  have hrest : (L.erase z).flatMap (s.reorder z l).zone = (L.erase z).flatMap s.zone := by
    apply flatMap_one_congr L hnd
    intro x _ hx
    exact zone_setZone_ne s hx l
  rw [hrest] at e1
  have hz' : (s.reorder z l).zone z = l := zone_setZone_self s z l
  rw [hz'] at e1
  rw [← hL]
  exact e1.trans ((hp.append_right _).trans e2.symm)

/-- Rearranging a zone keeps the game well formed. -/
theorem wf_reorder {s : GameState} (hwf : s.WF) {z : Zone} {l : List ObjId}
    (hz : z ∈ allZones s.playerCount) (hp : l.Perm (s.zone z)) : (s.reorder z l).WF := by
  have hperm := zoneIds_reorder hz hp
  have hmem : ∀ x, x ∈ (s.reorder z l).zoneIds ↔ x ∈ s.zoneIds := fun x => hperm.mem_iff
  refine ⟨hperm.nodup_iff.mpr hwf.nodup, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hwf.table_of_zone x ((hmem x).mp hx)
  · intro k hk
    obtain ⟨x, hx, hxk⟩ := hwf.zone_of_table k hk
    exact ⟨x, (hmem x).mpr hx, hxk⟩
  · intro x hx
    exact hwf.lt_nextId x ((hmem x).mp hx)
  · intro k hk
    simp only [reorder, setZone, Std.ExtTreeMap.mem_insert] at hk
    rcases hk with hk | hk
    · exact ⟨z, hz, Nat.compare_eq_eq.mp hk⟩
    · exact hwf.zones_valid k hk

/-- **I1** (rearranging). The physical cards stay the same, up to order. -/
theorem physIds_reorder {s : GameState} {z : Zone} {l : List ObjId}
    (hz : z ∈ allZones s.playerCount) (hp : l.Perm (s.zone z)) :
    (s.reorder z l).physIds.Perm s.physIds := by
  unfold physIds
  exact List.Perm.filterMap _ (zoneIds_reorder hz hp)

end GameState

end Riftbound

end
