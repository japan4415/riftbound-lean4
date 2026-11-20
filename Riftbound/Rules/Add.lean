module

public import Riftbound.Rules.Move
public import Riftbound.Rules.Owner

/-!
# Creating objects

Used to lay out the objects of a new game (CR 110-113): each card of the decks becomes an
object with a fresh identifier. During the game, objects are only moved (`moveObj`), apart from
tokens (milestone M4).
-/

@[expose] public section

namespace Riftbound

/-- The state with no objects, for the given rules. -/
def GameState.empty (config : GameConfig) : GameState :=
  { config, objects := {}, zones := {}, points := {}, nextId := 0, nextTimestamp := 0,
    pending := [], turnOrder := [], phase := .setup, turn := 0, active := none, result := none }

/-- The zone can hold an object of this owner: a Non-Board zone of a player holds only that player's
cards (CR 056). -/
def Zone.fits (z : Zone) (owner : PlayerId) : Bool :=
  match z with
  | .player q k => k.isBoard || q == owner
  | _ => true

/-- Add a new object to a zone. Its identifier and timestamp are the next ones. `none` if the zone
is not a zone of the game, or cannot hold an object of this owner. -/
def addObject (s : GameState) (o : Object) (z : Zone) (pos : Pos := .top) :
    Option (GameState × ObjId) :=
  if z.Valid s.playerCount ∧ z.fits o.owner = true then
    let id : ObjId := ⟨s.nextId⟩
    some ({ s.setZone z (pos.insert id (s.zone z)) with
            objects := s.objects.insert id.n { o with timestamp := ⟨s.nextTimestamp⟩ },
            nextId := s.nextId + 1, nextTimestamp := s.nextTimestamp + 1 }, id)
  else none

/-- A game with no objects is well formed. -/
theorem GameState.wf_empty (config : GameConfig) : (GameState.empty config).WF := by
  have hz : ∀ z, (GameState.empty config).zone z = [] := fun z => by
    simp [GameState.zone, GameState.empty]
  have hids : (GameState.empty config).zoneIds = [] := by
    unfold GameState.zoneIds
    simp [hz]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hids]; exact List.nodup_nil
  · intro x hx; rw [hids] at hx; simp at hx
  · intro k hk; simp [GameState.empty] at hk
  · intro x hx; rw [hids] at hx; simp at hx
  · intro k hk; simp [GameState.empty] at hk

/-- Adding an object keeps the game well formed. -/
theorem addObject_wf {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (hwf : s.WF) (h : addObject s o z pos = some (s', id)) : s'.WF := by
  unfold addObject at h
  split at h
  · rename_i hzc
    have hz : z.Valid s.playerCount := hzc.1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hz' : z ∈ allZones s.playerCount := hz
    have hnd := allZones_nodup s.playerCount
    obtain ⟨L, hL⟩ : ∃ L, L = allZones s.playerCount := ⟨_, rfl⟩
    rw [← hL] at hnd hz'
    have e1 := flatMap_split L s.zone z hz'
    have hperm : (GameState.zoneIds { s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z)) with
          objects := s.objects.insert s.nextId { o with timestamp := ⟨s.nextTimestamp⟩ },
          nextId := s.nextId + 1, nextTimestamp := s.nextTimestamp + 1 }).Perm
        (⟨s.nextId⟩ :: s.zoneIds) := by
      unfold GameState.zoneIds
      show (allZones s.playerCount).flatMap _ |>.Perm _
      rw [← hL]
      have e2 := flatMap_split L (s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z))).zone z hz'
      have hrest : (L.erase z).flatMap (s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z))).zone =
          (L.erase z).flatMap s.zone := by
        apply flatMap_one_congr L hnd
        intro x _ hx
        exact GameState.zone_setZone_ne s hx _
      rw [hrest, GameState.zone_setZone_self] at e2
      refine e2.trans ?_
      refine ((Pos.insert_perm pos _ _).append_right _).trans ?_
      exact List.Perm.cons _ e1.symm
    have hlt : ∀ x ∈ s.zoneIds, x.n < s.nextId := hwf.lt_nextId
    have hfresh : (⟨s.nextId⟩ : ObjId) ∉ s.zoneIds := fun hm => by
      have := hlt _ hm
      simp at this
    have hmem : ∀ x, x ∈ GameState.zoneIds
        { s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z)) with
          objects := s.objects.insert s.nextId { o with timestamp := ⟨s.nextTimestamp⟩ },
          nextId := s.nextId + 1, nextTimestamp := s.nextTimestamp + 1 } ↔
        (x = ⟨s.nextId⟩ ∨ x ∈ s.zoneIds) := fun x => by
      rw [hperm.mem_iff, List.mem_cons]
    refine ⟨hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh, hwf.nodup⟩), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show x.n ∈ s.objects.insert s.nextId _
      rw [Std.ExtTreeMap.mem_insert]
      rcases (hmem x).mp hx with rfl | hm
      · exact Or.inl (Nat.compare_eq_eq.mpr rfl)
      · exact Or.inr (hwf.table_of_zone x hm)
    · intro k hk
      have hk' : k ∈ s.objects.insert s.nextId _ := hk
      rw [Std.ExtTreeMap.mem_insert] at hk'
      rcases hk' with hk' | hk'
      · exact ⟨⟨s.nextId⟩, (hmem _).mpr (Or.inl rfl), Nat.compare_eq_eq.mp hk'⟩
      · obtain ⟨x, hx, hxk⟩ := hwf.zone_of_table k hk'
        exact ⟨x, (hmem x).mpr (Or.inr hx), hxk⟩
    · intro x hx
      show x.n < s.nextId + 1
      rcases (hmem x).mp hx with rfl | hm
      · simp
      · have := hlt x hm
        omega
    · intro k hk
      have hk' : k ∈ (s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z))).zones := hk
      simp only [GameState.setZone, Std.ExtTreeMap.mem_insert] at hk'
      show ∃ z' ∈ allZones s.playerCount, z'.key = k
      rcases hk' with hk' | hk'
      · exact ⟨z, hz, Nat.compare_eq_eq.mp hk'⟩
      · exact hwf.zones_valid k hk'
  · exact absurd h (by simp)

/-- Adding an object keeps `OwnerOk`. -/
theorem addObject_ownerOk {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (hwf : s.WF) (hown : s.OwnerOk) (h : addObject s o z pos = some (s', id)) :
    s'.OwnerOk := by
  unfold addObject at h
  split at h
  · rename_i hzc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun p k hk id2 hid2 o2 ho2 => ?_⟩
    by_cases hzz : Zone.player p k = z
    · have hz2 : id2 ∈ (pos.insert ⟨s.nextId⟩ (s.zone z)) := by
        have : ({ s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z)) with
            objects := s.objects.insert s.nextId { o with timestamp := ⟨s.nextTimestamp⟩ },
            nextId := s.nextId + 1, nextTimestamp := s.nextTimestamp + 1 } : GameState).zone
            (.player p k) = pos.insert ⟨s.nextId⟩ (s.zone z) := by
          rw [hzz]
          exact GameState.zone_setZone_self s z _
        rwa [this] at hid2
      rcases List.mem_cons.mp ((Pos.insert_perm pos _ _).mem_iff.mp hz2) with rfl | hold2
      · -- the new object
        simp only [GameState.obj?] at ho2
        rw [Std.ExtTreeMap.getElem?_insert_self] at ho2
        have := Option.some.inj ho2
        subst this
        have hf := hzc.2
        rw [← hzz] at hf
        simp only [Zone.fits, hk, Bool.false_or, beq_iff_eq] at hf
        exact hf.symm
      · -- an old object
        have hlt := hwf.lt_nextId id2 (GameState.mem_zoneIds
          (GameState.zone_valid_of_mem hwf hold2) hold2)
        have hne : id2.n ≠ s.nextId := by omega
        simp only [GameState.obj?] at ho2
        rw [Std.ExtTreeMap.getElem?_insert] at ho2
        have hcmp : ¬ compare s.nextId id2.n = .eq := fun e => hne (Nat.compare_eq_eq.mp e).symm
        simp only [hcmp, ite_false] at ho2
        rw [← hzz] at hold2
        exact hown.owner p k hk id2 hold2 o2 ho2
    · have hzone : id2 ∈ s.zone (.player p k) := by
        have : ({ s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z)) with
            objects := s.objects.insert s.nextId { o with timestamp := ⟨s.nextTimestamp⟩ },
            nextId := s.nextId + 1, nextTimestamp := s.nextTimestamp + 1 } : GameState).zone
            (.player p k) = s.zone (.player p k) := GameState.zone_setZone_ne s hzz _
        rwa [this] at hid2
      have hlt := hwf.lt_nextId id2 (GameState.mem_zoneIds
        (GameState.zone_valid_of_mem hwf hzone) hzone)
      have hne : id2.n ≠ s.nextId := by omega
      simp only [GameState.obj?] at ho2
      rw [Std.ExtTreeMap.getElem?_insert] at ho2
      have hcmp : ¬ compare s.nextId id2.n = .eq := fun e => hne (Nat.compare_eq_eq.mp e).symm
      simp only [hcmp, ite_false] at ho2
      exact hown.owner p k hk id2 hzone o2 ho2
  · exact absurd h (by simp)

end Riftbound

end
