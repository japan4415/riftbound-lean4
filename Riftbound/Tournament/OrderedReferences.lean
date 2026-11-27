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

/-- Reverse an ordered correspondence. -/
def symm {left right : List Nat} (rename : OrderedReferenceBijection left right) :
    OrderedReferenceBijection right left where
  forward := rename.backward
  backward := rename.forward
  forward_mem := rename.backward_mem
  backward_mem := rename.forward_mem
  backward_forward := rename.forward_backward
  forward_backward := rename.backward_forward
  order {x y} hx hy := by
    have original := rename.order (rename.backward_mem x hx) (rename.backward_mem y hy)
    simpa only [rename.forward_backward x hx, rename.forward_backward y hy] using original.symm

/-- Compose matching ordered correspondences. -/
def trans {left middle right : List Nat} (first : OrderedReferenceBijection left middle)
    (second : OrderedReferenceBijection middle right) : OrderedReferenceBijection left right where
  forward x := second.forward (first.forward x)
  backward y := first.backward (second.backward y)
  forward_mem x hx := second.forward_mem _ (first.forward_mem x hx)
  backward_mem y hy := first.backward_mem _ (second.backward_mem y hy)
  backward_forward x hx := by
    rw [second.backward_forward _ (first.forward_mem x hx), first.backward_forward x hx]
  forward_backward y hy := by
    rw [first.forward_backward _ (second.backward_mem y hy), second.forward_backward y hy]
  order hx hy := (second.order (first.forward_mem _ hx) (first.forward_mem _ hy)).trans (first.order hx hy)

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

/-- Renaming a list of known references preserves its ordered list of ranks. -/
theorem map_ranks {left right : List Nat} (rename : OrderedReferenceBijection left right)
    {references : List Nat} (known : ∀ id ∈ references, id ∈ left) :
    (references.map rename.forward).map (referenceRank right) = references.map (referenceRank left) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro reference member
  exact rename.rank_preserved (known reference member)

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

/-- The ordered contents of every zone, expressed with references ranked across all zones. -/
def GameState.rankedZoneReferences (s : GameState) : List (Zone × List Nat) :=
  (allZones s.playerCount).map fun zone =>
    (zone, ((s.zone zone).map ObjId.n).map (referenceRank (s.zoneIds.map ObjId.n)))

/-- If a correspondence takes every zone to the same ordered contents, both games
have the same projection by reference rank. -/
theorem GameState.rankedZoneReferences_eq {s t : GameState} (players : s.playerCount = t.playerCount)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (sameZones : ∀ z ∈ allZones s.playerCount,
      ((s.zone z).map ObjId.n).map rename.forward = (t.zone z).map ObjId.n) :
    s.rankedZoneReferences = t.rankedZoneReferences := by
  unfold GameState.rankedZoneReferences
  rw [← players]
  apply List.map_congr_left
  intro zone valid
  have known (id : Nat) (member : id ∈ (s.zone zone).map ObjId.n) : id ∈ s.zoneIds.map ObjId.n := by
    obtain ⟨object, found, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨object, GameState.mem_zoneIds valid found, rfl⟩
  have same := (rename.map_ranks known).symm
  rw [sameZones zone valid] at same
  exact congrArg (fun ids => (zone, ids)) same

private theorem GameState.rankedZoneReferences_flatMap (s : GameState) :
    s.rankedZoneReferences.flatMap Prod.snd =
      (s.zoneIds.map ObjId.n).map (referenceRank (s.zoneIds.map ObjId.n)) := by
  simp [GameState.rankedZoneReferences, GameState.zoneIds, List.flatMap_map, List.map_flatMap,
    Function.comp_def]

private theorem mem_rankedReferences {support : List Nat} {rank : Nat} :
    rank ∈ support.map (referenceRank support) ↔ rank ∈ List.range support.eraseDups.length := by
  constructor
  · intro member
    obtain ⟨_, present, rfl⟩ := List.mem_map.mp member
    exact List.mem_range.mpr (referenceRank_bounded present)
  · intro member
    obtain ⟨_, present, same⟩ := everyReferenceRank (List.mem_range.mp member)
    exact List.mem_map.mpr ⟨_, present, same⟩

/-- A matching ranked zone projection also supplies an ordered correspondence between
the original references, preserving the precise order within each zone. -/
theorem GameState.rankedZoneReferences_iff {s t : GameState} (players : s.playerCount = t.playerCount) :
    s.rankedZoneReferences = t.rankedZoneReferences ↔
      ∃ rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n),
        ∀ z ∈ allZones s.playerCount,
          ((s.zone z).map ObjId.n).map rename.forward = (t.zone z).map ObjId.n := by
  refine ⟨?_, fun ⟨rename, zones⟩ => GameState.rankedZoneReferences_eq players rename zones⟩
  intro normalized
  let left := s.zoneIds.map ObjId.n
  let right := t.zoneIds.map ObjId.n
  have allRanks : left.map (referenceRank left) = right.map (referenceRank right) := by
    simpa only [GameState.rankedZoneReferences_flatMap] using
      congrArg (List.flatMap Prod.snd) normalized
  have sameRange (rank : Nat) :
      rank ∈ List.range left.eraseDups.length ↔ rank ∈ List.range right.eraseDups.length := by
    rw [← mem_rankedReferences, ← mem_rankedReferences, allRanks]
  have size : left.eraseDups.length = right.eraseDups.length := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro less
      have impossible := (sameRange _).mp (List.mem_range.mpr less)
      exact (Nat.lt_irrefl _) (List.mem_range.mp impossible)
    · apply Nat.le_of_not_gt
      intro less
      have impossible := (sameRange _).mpr (List.mem_range.mpr less)
      exact (Nat.lt_irrefl _) (List.mem_range.mp impossible)
  let leftRanking : OrderedReferenceBijection left (List.range right.eraseDups.length) :=
    (referenceRanking left).congrSupport (fun _ => Iff.rfl) (fun _ => by rw [size])
  let rightRanking := referenceRanking right
  let rename := leftRanking.trans rightRanking.symm
  refine ⟨rename, ?_⟩
  intro zone valid
  unfold GameState.rankedZoneReferences at normalized
  rw [← players] at normalized
  have sameRanks : ((s.zone zone).map ObjId.n).map (referenceRank left) =
      ((t.zone zone).map ObjId.n).map (referenceRank right) := by
    exact congrArg Prod.snd (List.map_inj_left.mp normalized zone valid)
  have known (id : Nat) (present : id ∈ (t.zone zone).map ObjId.n) : id ∈ right := by
    obtain ⟨object, found, rfl⟩ := List.mem_map.mp present
    exact List.mem_map.mpr ⟨object, GameState.mem_zoneIds (players ▸ valid) found, rfl⟩
  calc
    _ = (((s.zone zone).map ObjId.n).map (referenceRank left)).map rightRanking.backward := by
      simp only [List.map_map, Function.comp_def, rename, leftRanking,
        OrderedReferenceBijection.trans, OrderedReferenceBijection.symm,
        OrderedReferenceBijection.congrSupport, referenceRanking]
    _ = (((t.zone zone).map ObjId.n).map (referenceRank right)).map rightRanking.backward := by
      rw [sameRanks]
    _ = ((t.zone zone).map ObjId.n).map id := by
      rw [List.map_map]
      apply List.map_congr_left
      intro id present
      exact rightRanking.backward_forward id (known id present)
    _ = _ := List.map_id _

private theorem Pos.insert_map_pair (pos : Pos) {left right : List ObjId}
    {leftId rightId : ObjId} {f g : ObjId → Nat}
    (lists : left.map f = right.map g) (paired : f leftId = g rightId) :
    (pos.insert leftId left).map f = (pos.insert rightId right).map g := by
  cases pos <;> simp [Pos.insert, paired, lists, List.map_take, List.map_drop]

/-- Adding objects at the same insertion point in corresponding states preserves the
ranked zone projection, even when their fresh identifiers differ. -/
theorem GameState.rankedZoneReferences_afterAdd {s t s' t' : GameState}
    {leftObject rightObject : Object} {leftId rightId : ObjId} {zone : Zone} {pos : Pos}
    (left : s.WF) (right : t.WF) (players : s.playerCount = t.playerCount)
    (same : s.rankedZoneReferences = t.rankedZoneReferences)
    (leftAdded : addObject s leftObject zone pos = some (s', leftId))
    (rightAdded : addObject t rightObject zone pos = some (t', rightId)) :
    s'.rankedZoneReferences = t'.rankedZoneReferences := by
  obtain ⟨rename, zones⟩ := (GameState.rankedZoneReferences_iff players).mp same
  let after := rename.extendAfterAdd left right leftAdded rightAdded
  have leftCount : s'.playerCount = s.playerCount :=
    congrArg (fun cfg => cfg.mode.players) (addObject_sameMeta leftAdded).config
  have rightCount : t'.playerCount = t.playerCount :=
    congrArg (fun cfg => cfg.mode.players) (addObject_sameMeta rightAdded).config
  have oldMap (z : Zone) (valid : z ∈ allZones s.playerCount) :
      (s.zone z).map (after.forward ∘ ObjId.n) = (t.zone z).map ObjId.n := by
    rw [← zones z valid, List.map_map]
    apply List.map_congr_left
    intro id member
    have known : id.n ∈ s.zoneIds.map ObjId.n :=
      List.mem_map.mpr ⟨id, GameState.mem_zoneIds valid member, rfl⟩
    have earlier := Nat.ne_of_lt (OrderedReferenceBijection.zoneReferences_belowCounter left id.n known)
    simp [after, OrderedReferenceBijection.extendAfterAdd, OrderedReferenceBijection.extendZoneReferences,
      OrderedReferenceBijection.congrSupport, OrderedReferenceBijection.extendFresh, earlier]
  refine GameState.rankedZoneReferences_eq (leftCount.trans (players.trans rightCount.symm)) after ?_
  intro z valid
  have before : z ∈ allZones s.playerCount := by simpa only [leftCount] using valid
  rw [List.map_map]
  by_cases moved : z = zone
  · subst z
    have leftZone : s'.zone zone = pos.insert leftId (s.zone zone) := by
      obtain ⟨_, rfl, rfl⟩ := addObject_spec leftAdded
      exact GameState.zone_setZone_self _ _ _
    have rightZone : t'.zone zone = pos.insert rightId (t.zone zone) := by
      obtain ⟨_, rfl, rfl⟩ := addObject_spec rightAdded
      exact GameState.zone_setZone_self _ _ _
    rw [leftZone, rightZone]
    exact pos.insert_map_pair (oldMap zone before)
      (rename.extendAfterAdd_newObject left right leftAdded rightAdded)
  · rw [addObject_zone_other leftAdded moved, addObject_zone_other rightAdded moved]
    exact oldMap z before

private theorem map_erase_reference {ids : List ObjId} {removed : ObjId} (f : ObjId → Nat)
    (reflects : ∀ id ∈ ids, f id = f removed → id = removed) :
    (ids.erase removed).map f = (ids.map f).erase (f removed) := by
  induction ids with
  | nil => rfl
  | cons id later ih =>
    by_cases same : id = removed
    · subst id
      simp
    · have distinct : f id ≠ f removed := fun equal => same (reflects id (by simp) equal)
      simp [same, distinct, ih (fun other member => reflects other (by simp [member]))]

private theorem map_zone_erase_pair {s t : GameState} {source : Zone} {leftId rightId : ObjId}
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (valid : source ∈ allZones s.playerCount) (member : leftId ∈ s.zone source)
    (preMap : (s.zone source).map (rename.forward ∘ ObjId.n) = (t.zone source).map ObjId.n)
    (paired : rename.forward leftId.n = rightId.n) :
    ((s.zone source).erase leftId).map (rename.forward ∘ ObjId.n) =
      ((t.zone source).erase rightId).map ObjId.n := by
  rw [map_erase_reference (rename.forward ∘ ObjId.n), map_erase_reference ObjId.n]
  · rw [preMap]
    exact congrArg ((t.zone source |>.map ObjId.n).erase) paired
  · intro id _ sameId
    exact congrArg ObjId.mk sameId
  · intro id present sameId
    have known (obj : ObjId) (present : obj ∈ s.zone source) :
        obj.n ∈ s.zoneIds.map ObjId.n :=
      List.mem_map.mpr ⟨obj, GameState.mem_zoneIds valid present, rfl⟩
    have original := congrArg rename.backward sameId
    change rename.backward (rename.forward id.n) = rename.backward (rename.forward leftId.n) at original
    rw [rename.backward_forward _ (known id present),
      rename.backward_forward _ (known leftId member)] at original
    exact congrArg ObjId.mk original

/-- Deleting corresponding objects preserves the ranked projection, including when the deletion
changes the rank of other objects. -/
theorem GameState.rankedZoneReferences_afterRemove {s t s' t' : GameState}
    {leftId rightId : ObjId} (left : s.WF) (right : t.WF) (players : s.playerCount = t.playerCount)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (zones : ∀ z ∈ allZones s.playerCount,
      ((s.zone z).map ObjId.n).map rename.forward = (t.zone z).map ObjId.n)
    (paired : rename.forward leftId.n = rightId.n)
    (leftRemoved : removeObj s leftId = some s') (rightRemoved : removeObj t rightId = some t') :
    s'.rankedZoneReferences = t'.rankedZoneReferences := by
  obtain ⟨source, valid, member, leftShape⟩ := removeObj_spec leftRemoved
  obtain ⟨target, targetValid, targetMember, rightShape⟩ := removeObj_spec rightRemoved
  have mappedMember : rightId.n ∈ ((s.zone source).map ObjId.n).map rename.forward :=
    List.mem_map.mpr ⟨leftId.n, List.mem_map.mpr ⟨leftId, member, rfl⟩, paired⟩
  rw [zones source valid] at mappedMember
  obtain ⟨other, otherMember, otherId⟩ := List.mem_map.mp mappedMember
  have otherIsRight : other = rightId := by cases other; cases rightId; simp_all
  have rightMember : rightId ∈ t.zone source := otherIsRight ▸ otherMember
  have sameLocation := (GameState.locate_eq right targetValid targetMember).symm.trans
    (GameState.locate_eq right (players ▸ valid) rightMember)
  have joined : target = source := Option.some.inj sameLocation
  subst target
  let after := rename.restrictAfterRemove left right paired leftRemoved rightRemoved
  have leftCount : s'.playerCount = s.playerCount :=
    congrArg (fun cfg => cfg.mode.players) (removeObj_sameMeta leftRemoved).config
  have rightCount : t'.playerCount = t.playerCount :=
    congrArg (fun cfg => cfg.mode.players) (removeObj_sameMeta rightRemoved).config
  refine GameState.rankedZoneReferences_eq (leftCount.trans (players.trans rightCount.symm)) after ?_
  intro zone postValid
  have before : zone ∈ allZones s.playerCount := by simpa only [leftCount] using postValid
  change ((s'.zone zone).map ObjId.n).map rename.forward = (t'.zone zone).map ObjId.n
  have preMap : (s.zone zone).map (rename.forward ∘ ObjId.n) = (t.zone zone).map ObjId.n := by
    simpa only [List.map_map] using zones zone before
  rw [List.map_map]
  by_cases affected : zone = source
  · subst zone
    have leftZone : s'.zone source = (s.zone source).erase leftId := by
      rw [leftShape]
      exact GameState.zone_setZone_self _ _ _
    have rightZone : t'.zone source = (t.zone source).erase rightId := by
      rw [rightShape]
      exact GameState.zone_setZone_self _ _ _
    rw [leftZone, rightZone]
    exact map_zone_erase_pair rename valid member preMap paired
  · have leftZone : s'.zone zone = s.zone zone := by
      rw [leftShape]
      exact GameState.zone_setZone_ne _ affected _
    have rightZone : t'.zone zone = t.zone zone := by
      rw [rightShape]
      exact GameState.zone_setZone_ne _ affected _
    rw [leftZone, rightZone]
    exact preMap

private theorem MoveSpec.zone_after {s s' : GameState} {id id' : ObjId} {pos : Pos} {src dst : Zone}
    (moved : MoveSpec s s' id id' pos src dst) (zone : Zone) :
    s'.zone zone = if zone = dst then pos.insert id' (s.zone dst)
      else if zone = src then (s.zone src).erase id else s.zone zone := by
  change s'.zones.getD zone.key [] = _
  rw [moved.zones]
  exact GameState.zone_move moved.ne _ _ _

/-- A paired move through the same source, destination, and insertion position preserves
the ranked contents of all zones. The two moves may keep their identifiers or both allocate
new ones. -/
theorem GameState.rankedZoneReferences_afterMove {s t s' t' : GameState}
    {leftId rightId leftNew rightNew : ObjId} {source destination leftRequest rightRequest : Zone}
    {pos : Pos} (left : s.WF) (right : t.WF) (players : s.playerCount = t.playerCount)
    (rename : OrderedReferenceBijection (s.zoneIds.map ObjId.n) (t.zoneIds.map ObjId.n))
    (zones : ∀ z ∈ allZones s.playerCount,
      ((s.zone z).map ObjId.n).map rename.forward = (t.zone z).map ObjId.n)
    (paired : rename.forward leftId.n = rightId.n)
    (leftMoved : moveObj s leftId leftRequest pos = some (s', leftNew))
    (rightMoved : moveObj t rightId rightRequest pos = some (t', rightNew))
    (leftMove : MoveSpec s s' leftId leftNew pos source destination)
    (rightMove : MoveSpec t t' rightId rightNew pos source destination)
    (retained : leftNew = leftId ↔ rightNew = rightId) :
    s'.rankedZoneReferences = t'.rankedZoneReferences := by
  let leftReferences := s.zoneIds.map ObjId.n
  have continued :
      ∃ after : OrderedReferenceBijection (s'.zoneIds.map ObjId.n) (t'.zoneIds.map ObjId.n),
        after.forward leftNew.n = rightNew.n ∧
          ∀ n ∈ leftReferences, n ≠ leftId.n → after.forward n = rename.forward n := by
    by_cases kept : leftNew = leftId
    · have other := retained.mp kept
      subst leftNew
      subst rightNew
      exact ⟨rename.keepAfterMove left right leftMoved rightMoved, paired, fun _ _ _ => rfl⟩
    · have other : rightNew ≠ rightId := fun eq => kept (retained.mpr eq)
      let after := rename.replaceAfterMove left right paired leftMoved rightMoved kept other
      exact ⟨after, rename.replaceAfterMove_forward left right paired leftMoved rightMoved kept other⟩
  obtain ⟨after, pairedNew, remains⟩ := continued
  have leftCount : s'.playerCount = s.playerCount := congrArg (fun cfg => cfg.mode.players) leftMove.config
  have rightCount : t'.playerCount = t.playerCount := congrArg (fun cfg => cfg.mode.players) rightMove.config
  have preMap (zone : Zone) (valid : zone ∈ allZones s.playerCount) :
      (s.zone zone).map (rename.forward ∘ ObjId.n) = (t.zone zone).map ObjId.n := by
    simpa only [List.map_map] using zones zone valid
  have leftMap {zone : Zone} (valid : zone ∈ allZones s.playerCount) {ids : List ObjId}
      (others : ∀ id ∈ ids, id ∈ s.zone zone ∧ id ≠ leftId) :
      ids.map (after.forward ∘ ObjId.n) = ids.map (rename.forward ∘ ObjId.n) := by
    apply List.map_congr_left
    intro id present
    obtain ⟨located, different⟩ := others id present
    have known : id.n ∈ leftReferences :=
      List.mem_map.mpr ⟨id, GameState.mem_zoneIds valid located, rfl⟩
    exact remains _ known (fun equal => different (congrArg ObjId.mk equal))
  have otherZone {zone : Zone} (valid : zone ∈ allZones s.playerCount) (different : zone ≠ source) :
      (s.zone zone).map (after.forward ∘ ObjId.n) = (t.zone zone).map ObjId.n := by
    rw [leftMap valid]
    · exact preMap zone valid
    · intro id member
      exact ⟨member, fun eq => different
        (GameState.zone_unique left leftMove.src_mem valid leftMove.id_mem (eq ▸ member))⟩
  refine GameState.rankedZoneReferences_eq (leftCount.trans (players.trans rightCount.symm)) after ?_
  intro zone postValid
  have valid : zone ∈ allZones s.playerCount := by simpa only [leftCount] using postValid
  rw [List.map_map, leftMove.zone_after, rightMove.zone_after]
  by_cases dest : zone = destination
  · subst zone
    simp only [ite_true]
    exact pos.insert_map_pair (otherZone valid (Ne.symm leftMove.ne)) pairedNew
  · simp only [dest, ite_false]
    by_cases src : zone = source
    · subst zone
      simp only [ite_true]
      have unique := GameState.zone_nodup left valid
      rw [leftMap valid (fun id member => ⟨(unique.mem_erase_iff.mp member).2,
        (unique.mem_erase_iff.mp member).1⟩)]
      exact map_zone_erase_pair rename valid leftMove.id_mem (preMap source valid) paired
    · simp only [src, ite_false]
      exact otherZone valid src

end Riftbound

end
