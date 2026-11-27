module

public import Riftbound.Rules.Remove

/-!
# Ordered references

Object identifiers and timestamps are counters. Renaming them in a loop comparison must
preserve their order and allow future allocations (design.md §8, TR 505).
-/

@[expose] public section

namespace Riftbound

/-- An order isomorphism on the identifiers that two states actually reference. Values
outside the given lists do not participate in the comparison. -/
structure OrderedReferenceBijection (left right : List Nat) where
  /-- Rename a reference in the left state. -/
  forward : Nat → Nat
  /-- Rename a reference in the right state. -/
  backward : Nat → Nat
  /-- A left-state reference has a matching reference in the right state. -/
  forward_mem : ∀ x ∈ left, forward x ∈ right
  /-- A right-state reference has a matching reference in the left state. -/
  backward_mem : ∀ y ∈ right, backward y ∈ left
  /-- A left-state reference survives a round trip. -/
  backward_forward : ∀ x ∈ left, backward (forward x) = x
  /-- A right-state reference survives a round trip. -/
  forward_backward : ∀ y ∈ right, forward (backward y) = y
  /-- All relative ages survive the rename. -/
  order : ∀ {x y}, x ∈ left → y ∈ left → (forward x < forward y ↔ x < y)

namespace OrderedReferenceBijection

/-- Add the next allocation in both states. Fresh counters are larger than all
references in their respective states, so extending the bijection preserves its order. -/
def extendFresh {left right : List Nat} (rename : OrderedReferenceBijection left right)
    {leftFresh rightFresh : Nat} (leftBound : ∀ x ∈ left, x < leftFresh)
    (rightBound : ∀ y ∈ right, y < rightFresh) :
    OrderedReferenceBijection (leftFresh :: left) (rightFresh :: right) where
  forward x := if x = leftFresh then rightFresh else rename.forward x
  backward y := if y = rightFresh then leftFresh else rename.backward y
  forward_mem x member := by
    rcases List.mem_cons.mp member with rfl | known
    · simp
    · have old := rename.forward_mem x known
      simp [Nat.ne_of_lt (leftBound x known), old]
  backward_mem y member := by
    rcases List.mem_cons.mp member with rfl | known
    · simp
    · have old := rename.backward_mem y known
      simp [Nat.ne_of_lt (rightBound y known), old]
  backward_forward x member := by
    rcases List.mem_cons.mp member with rfl | known
    · simp
    · have old := rename.forward_mem x known
      simp [Nat.ne_of_lt (leftBound x known), Nat.ne_of_lt (rightBound _ old),
        rename.backward_forward x known]
  forward_backward y member := by
    rcases List.mem_cons.mp member with rfl | known
    · simp
    · have old := rename.backward_mem y known
      simp [Nat.ne_of_lt (rightBound y known), Nat.ne_of_lt (leftBound _ old),
        rename.forward_backward y known]
  order first second := by
    rcases List.mem_cons.mp first with rfl | olderFirst <;>
      rcases List.mem_cons.mp second with rfl | olderSecond
    · simp
    · have leftOlder := leftBound _ olderSecond
      have rightOlder := rightBound _ (rename.forward_mem _ olderSecond)
      simp [Nat.ne_of_lt leftOlder, Nat.not_lt_of_ge (Nat.le_of_lt leftOlder),
        Nat.not_lt_of_ge (Nat.le_of_lt rightOlder)]
    · have leftOlder := leftBound _ olderFirst
      have rightOlder := rightBound _ (rename.forward_mem _ olderFirst)
      simp [Nat.ne_of_lt leftOlder, leftOlder, rightOlder]
    · simp only [Nat.ne_of_lt (leftBound _ olderFirst), Nat.ne_of_lt (leftBound _ olderSecond),
        ite_false]
      exact rename.order olderFirst olderSecond

/-- The extended bijection pairs the two new references. -/
theorem extendFresh_forward {left right : List Nat} (rename : OrderedReferenceBijection left right)
    {leftFresh rightFresh : Nat} (leftBound : ∀ x ∈ left, x < leftFresh)
    (rightBound : ∀ y ∈ right, y < rightFresh) :
    (rename.extendFresh leftBound rightBound).forward leftFresh = rightFresh := by
  simp [extendFresh]

/-- Earlier references keep the same partners when a later identifier is allocated. -/
theorem extendFresh_forward_of_mem {left right : List Nat} (rename : OrderedReferenceBijection left right)
    {leftFresh rightFresh x : Nat} (leftBound : ∀ y ∈ left, y < leftFresh)
    (rightBound : ∀ y ∈ right, y < rightFresh) (member : x ∈ left) :
    (rename.extendFresh leftBound rightBound).forward x = rename.forward x := by
  simp [extendFresh, Nat.ne_of_lt (leftBound x member)]

/-- Every current zone identifier precedes the counter that will assign the next one. -/
theorem zoneReferences_belowCounter {s : GameState} (wf : s.WF) :
    ∀ n ∈ s.zoneIds.map ObjId.n, n < s.nextId := by
  intro n member
  obtain ⟨id, known, rfl⟩ := List.mem_map.mp member
  exact wf.lt_nextId id known

/-- The counters of two well-formed game states can be paired when their current zone
identifiers are related. Historical references can be included using `extendFresh`. -/
def extendZoneReferences {s t : GameState} (left : s.WF) (right : t.WF)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n)) :
    OrderedReferenceBijection (s.nextId :: s.zoneIds.map ObjId.n) (t.nextId :: t.zoneIds.map ObjId.n) :=
  rename.extendFresh (zoneReferences_belowCounter left) (zoneReferences_belowCounter right)

/-- A bijection depends on the membership of its support, independently of how it is listed. -/
def congrSupport {left right left' right' : List Nat} (rename : OrderedReferenceBijection left right)
    (leftView : ∀ x, x ∈ left' ↔ x ∈ left) (rightView : ∀ y, y ∈ right' ↔ y ∈ right) :
    OrderedReferenceBijection left' right' where
  forward := rename.forward
  backward := rename.backward
  forward_mem x member := (rightView _).mpr (rename.forward_mem x ((leftView x).mp member))
  backward_mem y member := (leftView _).mpr (rename.backward_mem y ((rightView y).mp member))
  backward_forward x member := rename.backward_forward x ((leftView x).mp member)
  forward_backward y member := rename.forward_backward y ((rightView y).mp member)
  order first second := rename.order ((leftView _).mp first) ((leftView _).mp second)

/-- Remove a matched pair from the support, keeping the partners of all remaining
references. -/
def removePair {left right : List Nat} (rename : OrderedReferenceBijection left right)
    {removed : Nat} (member : removed ∈ left) :
    OrderedReferenceBijection (left.filter (· != removed)) (right.filter (· != rename.forward removed)) where
  forward := rename.forward
  backward := rename.backward
  forward_mem x present := by
    obtain ⟨old, different⟩ := List.mem_filter.mp present
    refine List.mem_filter.mpr ⟨rename.forward_mem x old, bne_iff_ne.mpr ?_⟩
    intro same
    have equal := congrArg rename.backward same
    rw [rename.backward_forward x old, rename.backward_forward removed member] at equal
    exact bne_iff_ne.mp different equal
  backward_mem y present := by
    obtain ⟨old, different⟩ := List.mem_filter.mp present
    refine List.mem_filter.mpr ⟨rename.backward_mem y old, bne_iff_ne.mpr ?_⟩
    intro same
    have equal := congrArg rename.forward same
    rw [rename.forward_backward y old] at equal
    exact bne_iff_ne.mp different equal
  backward_forward x present := rename.backward_forward x (List.mem_filter.mp present).1
  forward_backward y present := rename.forward_backward y (List.mem_filter.mp present).1
  order first second := rename.order (List.mem_filter.mp first).1 (List.mem_filter.mp second).1

/-- Performing an object allocation in both games extends the ordered correspondence
on all objects currently in zones. -/
def extendAfterAdd {s t s' t' : GameState} {leftObj rightObj : Object}
    {leftZone rightZone : Zone} {leftPos rightPos : Pos} {leftId rightId : ObjId}
    (left : s.WF) (right : t.WF)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (leftAdded : addObject s leftObj leftZone leftPos = some (s', leftId))
    (rightAdded : addObject t rightObj rightZone rightPos = some (t', rightId)) :
    OrderedReferenceBijection (s'.zoneIds.map ObjId.n) (t'.zoneIds.map ObjId.n) :=
  (rename.extendZoneReferences left right).congrSupport
    (fun n => by simpa only [(addObject_spec leftAdded).2.1, List.map_cons] using
      ((addObject_zoneIds leftAdded).map ObjId.n).mem_iff (a := n))
    (fun n => by simpa only [(addObject_spec rightAdded).2.1, List.map_cons] using
      ((addObject_zoneIds rightAdded).map ObjId.n).mem_iff (a := n))

/-- The two identifiers allocated by the engine are paired in the extended correspondence. -/
theorem extendAfterAdd_newObject {s t s' t' : GameState} {leftObj rightObj : Object}
    {leftZone rightZone : Zone} {leftPos rightPos : Pos} {leftId rightId : ObjId}
    (left : s.WF) (right : t.WF)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (leftAdded : addObject s leftObj leftZone leftPos = some (s', leftId))
    (rightAdded : addObject t rightObj rightZone rightPos = some (t', rightId)) :
    (rename.extendAfterAdd left right leftAdded rightAdded).forward leftId.n = rightId.n := by
  obtain ⟨_, rfl, _⟩ := addObject_spec leftAdded
  obtain ⟨_, rfl, _⟩ := addObject_spec rightAdded
  simp [extendAfterAdd, extendZoneReferences, congrSupport, extendFresh]

/-- Removing an object keeps exactly the other current zone identifiers in the support. -/
theorem zoneReferences_afterRemove {s s' : GameState} {removed : ObjId}
    (wf : s.WF) (done : removeObj s removed = some s') (n : Nat) :
    n ∈ s'.zoneIds.map ObjId.n ↔ n ∈ (s.zoneIds.map ObjId.n).filter (· != removed.n) := by
  rw [((removeObj_zoneIds done).map ObjId.n).mem_iff]
  simp only [List.mem_map, wf.nodup.mem_erase_iff, List.mem_filter, bne_iff_ne]
  constructor
  · rintro ⟨id, ⟨different, old⟩, rfl⟩
    exact ⟨⟨id, old, rfl⟩, fun same => different (congrArg ObjId.mk same)⟩
  · rintro ⟨⟨id, old, rfl⟩, different⟩
    exact ⟨id, ⟨fun same => different (congrArg ObjId.n same), old⟩, rfl⟩

/-- Removing matched objects in both games restricts the correspondence to the remaining zones. -/
def restrictAfterRemove {s t s' t' : GameState} {leftId rightId : ObjId} (left : s.WF) (right : t.WF)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (paired : rename.forward leftId.n = rightId.n)
    (leftRemoved : removeObj s leftId = some s') (rightRemoved : removeObj t rightId = some t') :
    OrderedReferenceBijection (s'.zoneIds.map ObjId.n) (t'.zoneIds.map ObjId.n) := by
  have member : leftId.n ∈ s.zoneIds.map ObjId.n := by
    obtain ⟨zone, valid, wasThere, _⟩ := removeObj_spec leftRemoved
    exact List.mem_map.mpr ⟨leftId, GameState.mem_zoneIds valid wasThere, rfl⟩
  exact (rename.removePair member).congrSupport (zoneReferences_afterRemove left leftRemoved)
    (fun n => by rw [paired]; exact zoneReferences_afterRemove right rightRemoved n)

/-- Moving an object substitutes its destination identifier in the set of zone references. -/
theorem zoneReferences_afterMove {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    (wf : s.WF) (moved : moveObj s id dst pos = some (s', id')) (n : Nat) :
    n ∈ s'.zoneIds.map ObjId.n ↔ n ∈ id'.n :: (s.zoneIds.map ObjId.n).filter (· != id.n) := by
  obtain ⟨src, actualDst, spec⟩ := moveObj_spec moved
  obtain ⟨core, before, after, _⟩ :=
    GameState.zoneIds_move spec.config spec.src_mem spec.id_mem spec.dst_mem spec.ne spec.zones
  have unique := (List.nodup_cons.mp (before.nodup_iff.mp wf.nodup)).1
  have coreDifferent : ∀ x ∈ core.map ObjId.n, x ≠ id.n := by
    intro x hx same
    subst x
    obtain ⟨other, member, same⟩ := List.mem_map.mp hx
    have equal : other = id := by cases other; cases id; simp_all
    exact unique (equal ▸ member)
  rw [(after.map ObjId.n).mem_iff]
  simp only [List.map_cons, List.mem_cons, List.mem_filter, bne_iff_ne]
  rw [(before.map ObjId.n).mem_iff]
  simp only [List.map_cons, List.mem_cons]
  apply or_congr_right
  constructor
  · intro member
    exact ⟨Or.inr member, coreDifferent n member⟩
  · rintro ⟨rfl | member, different⟩
    · exact (different rfl).elim
    · exact member

/-- Paired moves that both retain their identifier also retain the correspondence. -/
def keepAfterMove {s t s' t' : GameState} {leftId rightId : ObjId}
    {leftDst rightDst : Zone} {leftPos rightPos : Pos}
    (left : s.WF) (right : t.WF)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (leftMoved : moveObj s leftId leftDst leftPos = some (s', leftId))
    (rightMoved : moveObj t rightId rightDst rightPos = some (t', rightId)) :
    OrderedReferenceBijection (s'.zoneIds.map ObjId.n) (t'.zoneIds.map ObjId.n) := by
  have retained {game game' : GameState} {id : ObjId} {dst : Zone} {pos : Pos}
      (wf : game.WF) (moved : moveObj game id dst pos = some (game', id)) (n : Nat) :
      n ∈ game'.zoneIds.map ObjId.n ↔ n ∈ game.zoneIds.map ObjId.n := by
    obtain ⟨_, _, spec⟩ := moveObj_spec moved
    have present : id.n ∈ game.zoneIds.map ObjId.n :=
      List.mem_map.mpr ⟨id, GameState.mem_zoneIds spec.src_mem spec.id_mem, rfl⟩
    rw [zoneReferences_afterMove wf moved]
    simp only [List.mem_cons, List.mem_filter, bne_iff_ne]
    by_cases same : n = id.n <;> simp_all
  exact rename.congrSupport (retained left leftMoved) (retained right rightMoved)

/-- When both moves allocate new identifiers, remove the former pair and pair the new counters. -/
def replaceAfterMove {s t s' t' : GameState} {leftId rightId leftNew rightNew : ObjId}
    {leftDst rightDst : Zone} {leftPos rightPos : Pos}
    (left : s.WF) (right : t.WF)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (paired : rename.forward leftId.n = rightId.n)
    (leftMoved : moveObj s leftId leftDst leftPos = some (s', leftNew))
    (rightMoved : moveObj t rightId rightDst rightPos = some (t', rightNew))
    (leftChanged : leftNew ≠ leftId) (rightChanged : rightNew ≠ rightId) :
    OrderedReferenceBijection (s'.zoneIds.map ObjId.n) (t'.zoneIds.map ObjId.n) := by
  have source : leftId.n ∈ s.zoneIds.map ObjId.n := by
    obtain ⟨_, _, spec⟩ := moveObj_spec leftMoved
    exact List.mem_map.mpr ⟨leftId, GameState.mem_zoneIds spec.src_mem spec.id_mem, rfl⟩
  have leftFresh : leftNew.n = s.nextId := by
    obtain ⟨_, _, spec⟩ := moveObj_spec leftMoved
    exact spec.fresh.resolve_left leftChanged
  have rightFresh : rightNew.n = t.nextId := by
    obtain ⟨_, _, spec⟩ := moveObj_spec rightMoved
    exact spec.fresh.resolve_left rightChanged
  refine ((rename.removePair source).extendFresh (leftFresh := s.nextId) (rightFresh := t.nextId)
    (fun n member => zoneReferences_belowCounter left n (List.mem_filter.mp member).1)
    (fun n member => zoneReferences_belowCounter right n (List.mem_filter.mp member).1)).congrSupport ?_ ?_
  · simpa only [leftFresh] using zoneReferences_afterMove left leftMoved
  · simpa only [rightFresh, paired] using zoneReferences_afterMove right rightMoved

/-- The destination identifiers correspond, and every other current identifier keeps its partner. -/
theorem replaceAfterMove_forward {s t s' t' : GameState} {leftId rightId leftNew rightNew : ObjId}
    {leftDst rightDst : Zone} {leftPos rightPos : Pos} (left : s.WF) (right : t.WF)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (paired : rename.forward leftId.n = rightId.n)
    (leftMoved : moveObj s leftId leftDst leftPos = some (s', leftNew))
    (rightMoved : moveObj t rightId rightDst rightPos = some (t', rightNew))
    (leftChanged : leftNew ≠ leftId) (rightChanged : rightNew ≠ rightId) :
    let after := rename.replaceAfterMove left right paired leftMoved rightMoved leftChanged rightChanged
    after.forward leftNew.n = rightNew.n ∧
      ∀ n ∈ s.zoneIds.map ObjId.n, n ≠ leftId.n → after.forward n = rename.forward n := by
  obtain ⟨_, _, leftSpec⟩ := moveObj_spec leftMoved
  obtain ⟨_, _, rightSpec⟩ := moveObj_spec rightMoved
  have leftFresh := leftSpec.fresh.resolve_left leftChanged
  have rightFresh := rightSpec.fresh.resolve_left rightChanged
  constructor
  · simp [replaceAfterMove, congrSupport, extendFresh, leftFresh, rightFresh]
  · intro n member _
    have earlier := Nat.ne_of_lt (zoneReferences_belowCounter left n member)
    simp [replaceAfterMove, congrSupport, extendFresh, removePair, earlier]

end OrderedReferenceBijection

end Riftbound

end
