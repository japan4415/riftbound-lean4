module

public import Riftbound.Rules.Remove

/-!
# Ordered references

Object identifiers and timestamps are counters. Renaming them in a loop comparison must
preserve their order and allow future allocations (TR 505). See also design.md §8.
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

/-- Give each reference the number of distinct references that precede it. -/
def referenceRank (support : List Nat) (reference : Nat) : Nat :=
  (support.eraseDups.filter (fun earlier => decide (earlier < reference))).length

private theorem eraseDups_nodup (references : List Nat) : references.eraseDups.Nodup := by
  cases references with
  | nil => exact List.nodup_nil
  | cons first rest =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, eraseDups_nodup _⟩
    intro contained
    have filtered := List.mem_filter.mp (List.mem_eraseDups.mp contained)
    simp at filtered
termination_by references.length
decreasing_by exact Nat.lt_succ_of_le List.filter_sublist.length_le

private theorem mem_earlier {support : List Nat} {limit candidate : Nat} :
    candidate ∈ support.eraseDups.filter (fun earlier => decide (earlier < limit)) ↔
      candidate ∈ support ∧ candidate < limit := by
  simp [List.mem_eraseDups]

private theorem referenceRank_strict {support : List Nat} {earlier later : Nat}
    (member : earlier ∈ support) (order : earlier < later) :
    referenceRank support earlier < referenceRank support later := by
  let small := support.eraseDups.filter (fun x => decide (x < earlier))
  let large := support.eraseDups.filter (fun x => decide (x < later))
  have filtered : large.filter (fun x => decide (x < earlier)) = small := by
    dsimp only [small, large]
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    by_cases smaller : x < earlier
    · simp [smaller, Nat.lt_trans smaller order]
    · simp [smaller]
  have subset : small.Sublist large := filtered ▸ List.filter_sublist
  have extra : earlier ∈ large := mem_earlier.mpr ⟨member, order⟩
  have absent : earlier ∉ small := fun present => Nat.lt_irrefl _ (mem_earlier.mp present).2
  have distinct : small.length ≠ large.length := fun same =>
    absent ((subset.length_eq.mp same).symm ▸ extra)
  exact Nat.lt_of_le_of_ne subset.length_le distinct

/-- Ranking the supported references preserves and reflects every strict comparison. -/
theorem referenceRank_lt_iff {support : List Nat} {first second : Nat}
    (firstMember : first ∈ support) (secondMember : second ∈ support) :
    referenceRank support first < referenceRank support second ↔ first < second := by
  refine ⟨?_, referenceRank_strict firstMember⟩
  intro rankOrder
  by_cases order : first < second
  · exact order
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt order) with reverse | same
    · have := referenceRank_strict secondMember reverse
      omega
    · simp only [same, Nat.lt_irrefl] at rankOrder

/-- A reference can be recovered uniquely from its rank in the support. -/
theorem referenceRank_eq_iff {support : List Nat} {first second : Nat}
    (firstMember : first ∈ support) (secondMember : second ∈ support) :
    referenceRank support first = referenceRank support second ↔ first = second := by
  refine ⟨?_, congrArg _⟩
  intro equal
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro reverse
    have rankOrder := (referenceRank_lt_iff secondMember firstMember).mpr reverse
    omega
  · apply Nat.le_of_not_lt
    intro reverse
    have rankOrder := (referenceRank_lt_iff firstMember secondMember).mpr reverse
    omega

/-- Every supported rank is smaller than the number of distinct references. -/
theorem referenceRank_bounded {support : List Nat} {reference : Nat}
    (present : reference ∈ support) : referenceRank support reference < support.eraseDups.length := by
  let earlier := support.eraseDups.filter (fun x => decide (x < reference))
  have subset : earlier.Sublist support.eraseDups := List.filter_sublist
  have less := subset.length_le
  have distinct : earlier.length ≠ support.eraseDups.length := by
    intro same
    have earlierMember : reference ∈ earlier :=
      (subset.length_eq.mp same).symm ▸ List.mem_eraseDups.mpr present
    exact Nat.lt_irrefl _ (mem_earlier.mp earlierMember).2
  exact Nat.lt_of_le_of_ne less distinct

private theorem everyReferenceRank {support : List Nat} {rank : Nat}
    (rankInRange : rank < support.eraseDups.length) :
    ∃ reference ∈ support, referenceRank support reference = rank := by
  let ranked := support.eraseDups.map (referenceRank support)
  have distinct : ranked.Nodup := by
    change List.Pairwise (· ≠ ·) (support.eraseDups.map (referenceRank support))
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (eraseDups_nodup support)
    intro a b aMember bMember different equalRanks
    exact different ((referenceRank_eq_iff (List.mem_eraseDups.mp aMember)
      (List.mem_eraseDups.mp bMember)).mp equalRanks)
  have inRange : ranked ⊆ List.range support.eraseDups.length := by
    intro value member
    obtain ⟨reference, present, rfl⟩ := List.mem_map.mp member
    exact List.mem_range.mpr (referenceRank_bounded (List.mem_eraseDups.mp present))
  have member : rank ∈ ranked := by
    by_cases contains : rank ∈ ranked
    · exact contains
    · have extended : (rank :: ranked).Nodup := List.nodup_cons.mpr ⟨contains, distinct⟩
      have subset : rank :: ranked ⊆ List.range support.eraseDups.length := by
        intro value present
        rcases List.mem_cons.mp present with rfl | member
        · exact List.mem_range.mpr rankInRange
        · exact inRange member
      have impossible := extended.length_le_of_subset subset
      simp [ranked] at impossible
      omega
  obtain ⟨reference, present, same⟩ := List.mem_map.mp member
  exact ⟨reference, List.mem_eraseDups.mp present, same⟩

private theorem findReferenceRank {support : List Nat} {rank : Nat}
    (rankInRange : rank ∈ List.range support.eraseDups.length) :
    ∃ reference, support.find? (fun x => referenceRank support x == rank) = some reference ∧
      reference ∈ support ∧ referenceRank support reference = rank := by
  cases found : support.find? (fun x => referenceRank support x == rank) with
  | none =>
    obtain ⟨reference, member, same⟩ := everyReferenceRank (List.mem_range.mp rankInRange)
    exact ((List.find?_eq_none.mp found) reference member (by simp [same])).elim
  | some reference =>
    have equalRank := List.find?_some (p := fun x => referenceRank support x == rank) found
    exact ⟨reference, rfl, List.mem_of_find?_eq_some found, beq_iff_eq.mp equalRank⟩

/-- Rename supported references to consecutive counters, starting at zero. -/
def referenceRanking (support : List Nat) :
    OrderedReferenceBijection support (List.range support.eraseDups.length) where
  forward := referenceRank support
  backward value := (support.find? (fun x => referenceRank support x == value)).getD 0
  forward_mem _ present := List.mem_range.mpr (referenceRank_bounded present)
  backward_mem _ inRange := by
    obtain ⟨_, found, present, _⟩ := findReferenceRank inRange
    simpa only [found, Option.getD_some] using present
  backward_forward reference present := by
    obtain ⟨previous, found, known, equal⟩ :=
      findReferenceRank (List.mem_range.mpr (referenceRank_bounded present))
    simp only [found, Option.getD_some]
    exact (referenceRank_eq_iff known present).mp equal
  forward_backward _ inRange := by
    obtain ⟨_, found, _, equal⟩ := findReferenceRank inRange
    simpa only [found, Option.getD_some] using equal
  order := referenceRank_lt_iff

namespace OrderedReferenceBijection

/-- A reference retains its rank when the correspondence preserves relative order. -/
theorem rank_preserved {left right : List Nat} (rename : OrderedReferenceBijection left right)
    {reference : Nat} (member : reference ∈ left) :
    referenceRank right (rename.forward reference) = referenceRank left reference := by
  let earlierLeft := left.eraseDups.filter (fun x => decide (x < reference))
  let earlierRight := right.eraseDups.filter (fun y => decide (y < rename.forward reference))
  have distinctLeft : earlierLeft.Nodup := (eraseDups_nodup left).filter _
  have distinctRight : earlierRight.Nodup := (eraseDups_nodup right).filter _
  have distinctMapped : (earlierLeft.map rename.forward).Nodup := by
    change List.Pairwise (· ≠ ·) (earlierLeft.map rename.forward)
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ distinctLeft
    intro a b aEarlier bEarlier different equal
    have aSource := (mem_earlier.mp aEarlier).1
    have bSource := (mem_earlier.mp bEarlier).1
    exact different ((rename.backward_forward a aSource).symm.trans
      ((congrArg rename.backward equal).trans (rename.backward_forward b bSource)))
  have sameReferences : earlierRight.Perm (earlierLeft.map rename.forward) := by
    apply (List.perm_ext_iff_of_nodup distinctRight distinctMapped).mpr
    intro next
    rw [List.mem_map]
    constructor
    · intro present
      obtain ⟨present, order⟩ := mem_earlier.mp present
      let previous := rename.backward next
      have previousMem := rename.backward_mem next present
      have pointsTo : rename.forward previous = next := rename.forward_backward next present
      refine ⟨previous, mem_earlier.mpr ⟨previousMem, ?_⟩, pointsTo⟩
      have sameOrder : rename.forward (rename.backward next) < rename.forward reference := by
        rw [rename.forward_backward next present]
        exact order
      exact (rename.order previousMem member).mp sameOrder
    · rintro ⟨previous, earlier, rfl⟩
      obtain ⟨previousMem, order⟩ := mem_earlier.mp earlier
      exact mem_earlier.mpr ⟨rename.forward_mem previous previousMem, (rename.order previousMem member).mpr order⟩
  simpa only [referenceRank, earlierLeft, earlierRight, List.length_map] using sameReferences.length_eq

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
