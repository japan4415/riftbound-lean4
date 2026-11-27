module

public import Riftbound.State.GameState
public import Riftbound.Basic.ListLemmas

/-!
# Moving objects between zones

`moveObj` is the only primitive that moves an object from one zone to another (design.md §3,
P6). Its properties are proved once here and carry over to everything built on it.

Moving into or out of a Non-Board zone makes a new object with a new `ObjId`, and the
temporary state of the old one (damage, exhaustion, effects) is gone (CR 124, 124.1). A move
between two Board zones keeps the object (CR 124, 448.1). An object never enters the
Non-Board zone of a player who does not own it (CR 056).
-/

@[expose] public section

namespace Riftbound

/-- `simp` normal form of the key comparison of the object table. -/
theorem eq_compare_nat_iff (a k : Nat) : (Ordering.eq = compare a k) ↔ a = k := by
  rw [eq_comm]; exact Nat.compare_eq_eq

/-- Where in the destination list an object goes. For a deck, `top` is the head. -/
inductive Pos where
  /-- At the head: the top of a deck, the newest item of the Chain. -/
  | top
  /-- At the end: the bottom of a deck. -/
  | bottom
  /-- At the index, or at the end when the list is shorter. -/
  | atIndex (index : Nat)
deriving DecidableEq, Repr

/-- Put an object into a list at the given end. -/
def Pos.insert : Pos → ObjId → List ObjId → List ObjId
  | .top, id, l => id :: l
  | .bottom, id, l => l ++ [id]
  | .atIndex index, id, l => l.take index ++ id :: l.drop index

/-- Inserting puts exactly one new member into the list (up to order). -/
theorem Pos.insert_perm (pos : Pos) (id : ObjId) (l : List ObjId) :
    (pos.insert id l).Perm (id :: l) := by
  cases pos
  · exact List.Perm.refl _
  · simp [Pos.insert]
  · rename_i index
    simpa [Pos.insert] using
      (List.perm_middle (a := id) (l₁ := l.take index) (l₂ := l.drop index))

/-- The inserted object is a member of the result. -/
theorem Pos.mem_insert (pos : Pos) (id : ObjId) (l : List ObjId) : id ∈ pos.insert id l := by
  exact (pos.insert_perm id l).mem_iff.mpr (by simp)

/-- Moving between these zones makes a new object: at least one is Non-Board (CR 124). -/
def Zone.crosses (src dst : Zone) : Bool := !(src.isBoard && dst.isBoard)

/-- An object goes to its owner's Non-Board zone, not to another player's (CR 056). -/
def Zone.normalize (owner : PlayerId) : Zone → Zone
  | .player q k => if (Zone.player q k).isBoard then .player q k else .player owner k
  | z => z

/-- A destination already in the owner's zones is unchanged. -/
theorem Zone.normalize_owner (owner : PlayerId) (k : ZoneKind) :
    Zone.normalize owner (.player owner k) = .player owner k := by
  cases k <;> rfl

namespace GameState

/-- The zone an object is on. -/
def locate (s : GameState) (id : ObjId) : Option Zone :=
  (allZones s.playerCount).find? (fun z => (s.zone z).contains id)

/-- A located object is on a zone of the game, and in it. -/
theorem locate_spec {s : GameState} {id : ObjId} {z : Zone} (h : s.locate id = some z) :
    z ∈ allZones s.playerCount ∧ id ∈ s.zone z := by
  unfold locate at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  simpa using List.find?_some h

end GameState

/-- Move an object to `dst`, at `pos`. Returns the new state and the identifier the object has
afterwards, which differs from the old one exactly when `Zone.crosses`. `none` if the object is
not on a zone, or if the destination is not a zone of the game, or if it is where it already is. -/
def moveObj (s : GameState) (id : ObjId) (dst : Zone) (pos : Pos := .top) :
    Option (GameState × ObjId) :=
  match s.locate id, s.obj? id with
  | some src, some o =>
    let dst := Zone.normalize o.owner dst
    if src = dst ∨ ¬ dst.Valid s.playerCount then none
    else if Zone.crosses src dst then
      let id' : ObjId := ⟨s.nextId⟩
      let o' : Object :=
        { o with controller := o.owner, exhausted := false, damage := 0, damagedTurn := none,
                 -- a card in the Trash remembers where it was, for what it does when it dies
                 loc := if dst = .player o.owner .trash then o.loc else none,
                 baseMightThisTurn := none, unitGearEffects := [],
                 leftUnitGearMight := if src.isBoard then o.unitGearEffects.head?.map Prod.snd else none,
                 mightMods := [], tempKws := [], tempActivations := [],
                 attached := none, attachedTurn := none, attachmentCopyStamp := none,
                 reservedBy := none,
                 attachmentTextStamp := none,
                 attachmentTextCopies := if src.isBoard then s.activeAttachmentText id else [],
                 attachmentCopies := [],
                 leftController := if src.isBoard then some o.controller else none,
                 lastAttachmentCopy := if src.isBoard then s.attachmentCopyOf id o else none,
                 buffed := false,
                 extraBuffs := 0,
                 hiddenAt := none, hiddenTurn := none, fromHidden := o.hiddenAt.isSome,
                 moves := 0, movesTurn := none,
                 prevLoc := none, used := [], copiedUses :=
                   if src.isBoard then o.copiedUses else [],
                 namedCard := none,
                 leftBoard := src.isBoard,
                 formerId := some id,
                 stunned := false, flowed := false, limitedSpellExit := .normal, pendingSpellPlay := none,
                 spellPick := .plain, playUntilEnding := none, empowerCount := 0,
                 leftEmpowered := src.isBoard && 0 < o.empowerCount,
                 timestamp := ⟨s.nextTimestamp⟩ }
      some ({ (s.setZone src ((s.zone src).erase id)).setZone dst (pos.insert id' (s.zone dst))
              with objects := (s.objects.erase id.n).insert id'.n o',
                   damageMarks := s.damageMarks.erase id.n,
                   nextId := s.nextId + 1, nextTimestamp := s.nextTimestamp + 1 }, id')
    else
      some ((s.setZone src ((s.zone src).erase id)).setZone dst (pos.insert id (s.zone dst)), id)
  | _, _ => none

namespace GameState

/-- Two zone writes: the contents of every other zone stay. -/
theorem zone_move {s : GameState} {src dst : Zone} (hne : src ≠ dst)
    (l1 l2 : List ObjId) (z : Zone) :
    ((s.setZone src l1).setZone dst l2).zone z =
      if z = dst then l2 else if z = src then l1 else s.zone z := by
  by_cases h1 : z = dst
  · subst h1; simp [zone_setZone_self]
  · by_cases h2 : z = src
    · subst h2
      rw [zone_setZone_ne _ h1, zone_setZone_self]
      simp [h1]
    · rw [zone_setZone_ne _ h1, zone_setZone_ne _ h2]
      simp [h1, h2]

/-- The shape of the identifiers on zones before and after a move: the rest (`core`) is the
same, only the moved object is named differently. -/
theorem zoneIds_move {s s2 : GameState} {id id' : ObjId} {src dst : Zone} {pos : Pos}
    (hcfg : s2.config = s.config)
    (hsrc : src ∈ allZones s.playerCount) (hid : id ∈ s.zone src)
    (hdst : dst ∈ allZones s.playerCount) (hne : src ≠ dst)
    (hzones : s2.zones = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zones) :
    ∃ core : List ObjId, s.zoneIds.Perm (id :: core) ∧ s2.zoneIds.Perm (id' :: core) ∧
      (∀ x ∈ core, x ∈ s.zoneIds) := by
  have hz2 : ∀ z, s2.zone z =
      if z = dst then pos.insert id' (s.zone dst)
      else if z = src then (s.zone src).erase id else s.zone z := by
    intro z
    have : s2.zone z = ((s.setZone src ((s.zone src).erase id)).setZone dst
        (pos.insert id' (s.zone dst))).zone z := by simp [zone, hzones]
    rw [this, zone_move hne]
  have hcount : s2.playerCount = s.playerCount := by simp [playerCount, hcfg]
  have hnd := allZones_nodup s.playerCount
  obtain ⟨L, hL⟩ : ∃ L, L = allZones s.playerCount := ⟨_, rfl⟩
  rw [← hL] at hnd hsrc hdst
  have e1 := flatMap_two L s.zone src dst hsrc hdst hne
  have e2 := flatMap_two L s2.zone src dst hsrc hdst hne
  have hrest : ((L.erase src).erase dst).flatMap s2.zone =
      ((L.erase src).erase dst).flatMap s.zone := by
    apply flatMap_two_congr L hnd
    intro x _ hxa hxb
    rw [hz2 x]
    simp [hxa, hxb]
  rw [hrest] at e2
  have hA2 : s2.zone src = (s.zone src).erase id := by rw [hz2 src]; simp [hne]
  have hB2 : s2.zone dst = pos.insert id' (s.zone dst) := by rw [hz2 dst]; simp
  rw [hA2, hB2] at e2
  obtain ⟨R, hR⟩ : ∃ R, R = ((L.erase src).erase dst).flatMap s.zone := ⟨_, rfl⟩
  rw [← hR] at e1 e2
  have h1 : s.zoneIds.Perm (id :: ((s.zone src).erase id ++ (s.zone dst ++ R))) := by
    unfold zoneIds
    rw [← hL]
    refine e1.trans ?_
    exact (List.perm_cons_erase hid).append_right _
  have h2 : s2.zoneIds.Perm (id' :: ((s.zone src).erase id ++ (s.zone dst ++ R))) := by
    unfold zoneIds
    rw [hcount, ← hL]
    refine e2.trans ?_
    refine (((Pos.insert_perm pos id' (s.zone dst)).append_right R).append_left _).trans ?_
    exact List.perm_middle
  exact ⟨_, h1, h2, fun x hx => h1.symm.subset (List.mem_cons_of_mem _ hx)⟩

end GameState

namespace GameState

/-- A different number means a different object. -/
theorem ObjId_ne_of_n_ne {a b : ObjId} (h : a.n ≠ b.n) : a ≠ b := fun e => h (by rw [e])

/-- Well-formedness after a move, from the shape of the move. The object table loses the old
entry and gains the new one; the counter stays above every identifier in use. -/
theorem wf_of_move {s s2 : GameState} {id id' : ObjId} {src dst : Zone} {pos : Pos}
    (hwf : s.WF) (hcfg : s2.config = s.config)
    (hsrc : src ∈ allZones s.playerCount) (hid : id ∈ s.zone src)
    (hdst : dst ∈ allZones s.playerCount) (hne : src ≠ dst)
    (hzones : s2.zones = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zones)
    (hobj : ∀ k, k ∈ s2.objects ↔ (k ∈ s.objects ∧ k ≠ id.n) ∨ k = id'.n)
    (hid' : id' = id ∨ id'.n = s.nextId)
    (hnext : s.nextId ≤ s2.nextId ∧ (id' = id ∨ id'.n < s2.nextId)) : s2.WF := by
  obtain ⟨core, h1, h2, hcore⟩ := zoneIds_move hcfg hsrc hid hdst hne hzones
  have hcount : s2.playerCount = s.playerCount := by simp [playerCount, hcfg]
  have hnd : (id :: core).Nodup := h1.nodup_iff.mp hwf.nodup
  rw [List.nodup_cons] at hnd
  have hlt : ∀ x ∈ core, x.n < s.nextId := fun x hx => hwf.lt_nextId x (hcore x hx)
  have hid'core : id' ∉ core := by
    rcases hid' with rfl | h
    · exact hnd.1
    · intro hm
      have := hlt id' hm
      omega
  have hne_id : ∀ x ∈ core, x.n ≠ id.n := fun x hx e => by
    have : x = id := by cases x; cases id; simp_all
    exact hnd.1 (this ▸ hx)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h2.nodup_iff.mpr (List.nodup_cons.mpr ⟨hid'core, hnd.2⟩)
  · intro x hx
    rcases List.mem_cons.mp (h2.mem_iff.mp hx) with rfl | hm
    · exact (hobj _).mpr (Or.inr rfl)
    · exact (hobj _).mpr (Or.inl ⟨hwf.table_of_zone x (hcore x hm), hne_id x hm⟩)
  · intro k hk
    rcases (hobj k).mp hk with ⟨hk1, hk2⟩ | rfl
    · obtain ⟨x, hx, hxk⟩ := hwf.zone_of_table k hk1
      rcases List.mem_cons.mp (h1.mem_iff.mp hx) with rfl | hm
      · exact absurd hxk.symm hk2
      · exact ⟨x, h2.mem_iff.mpr (List.mem_cons_of_mem _ hm), hxk⟩
    · exact ⟨id', h2.symm.subset List.mem_cons_self, rfl⟩
  · intro x hx
    rcases List.mem_cons.mp (h2.mem_iff.mp hx) with rfl | hm
    · rcases hnext.2 with h | h
      · have := hwf.lt_nextId id (h1.symm.subset List.mem_cons_self)
        rw [h]
        omega
      · exact h
    · have := hlt x hm
      omega
  · intro k hk
    rw [hzones] at hk
    simp only [setZone, Std.ExtTreeMap.mem_insert] at hk
    rw [hcount]
    rcases hk with hk | hk | hk
    · exact ⟨dst, hdst, Nat.compare_eq_eq.mp hk⟩
    · exact ⟨src, hsrc, Nat.compare_eq_eq.mp hk⟩
    · exact hwf.zones_valid k hk

end GameState

namespace GameState

/-- An object on a zone of the game is among `zoneIds`. -/
theorem mem_zoneIds {s : GameState} {z : Zone} {id : ObjId}
    (hz : z ∈ allZones s.playerCount) (h : id ∈ s.zone z) : id ∈ s.zoneIds := by
  unfold zoneIds
  exact List.mem_flatMap.mpr ⟨z, hz, h⟩

end GameState

/-- The rules, phase, result, and decision stack are unchanged. Objects, resources and
turn bookkeeping may change. -/
def SameMeta (s s' : GameState) : Prop :=
  { s' with objects := s.objects, zones := s.zones,
            nextId := s.nextId, nextTimestamp := s.nextTimestamp, points := s.points,
            turnFx := s.turnFx, pools := s.pools, extraTurns := s.extraTurns,
            turnShift := s.turnShift, drawLog := s.drawLog, experience := s.experience,
            damageMarks := s.damageMarks } = s

namespace SameMeta

/-- A state is like itself. -/
theorem refl (s : GameState) : SameMeta s s := rfl

/-- Chaining. -/
theorem trans {s s' s'' : GameState} (h1 : SameMeta s s') (h2 : SameMeta s' s'') :
    SameMeta s s'' := by
  unfold SameMeta at *
  have := congrArg (fun x : GameState =>
    ({ x with objects := s.objects, zones := s.zones, nextId := s.nextId,
              nextTimestamp := s.nextTimestamp, points := s.points,
              turnFx := s.turnFx, pools := s.pools, extraTurns := s.extraTurns,
              turnShift := s.turnShift, drawLog := s.drawLog, experience := s.experience,
              damageMarks := s.damageMarks } : GameState)) h2
  simp only at this
  rw [← h1]
  exact this

/-- The rules are as they were. -/
theorem config {s s' : GameState} (h : SameMeta s s') : s'.config = s.config := by
  unfold SameMeta at h
  have h2 := congrArg GameState.config h
  exact h2

/-- A change that keeps the game metadata also keeps its list of departed seats. -/
theorem departures {s s' : GameState} (h : SameMeta s s') : s'.departures = s.departures := by
  unfold SameMeta at h
  have projected := congrArg GameState.departures h
  exact projected

/-- The stack is as it was. -/
theorem pending {s s' : GameState} (h : SameMeta s s') : s'.pending = s.pending := by
  unfold SameMeta at h
  have h2 := congrArg GameState.pending h
  exact h2

/-- The turn order is as it was. -/
theorem turnOrder {s s' : GameState} (h : SameMeta s s') : s'.turnOrder = s.turnOrder := by
  unfold SameMeta at h
  have h2 := congrArg GameState.turnOrder h
  exact h2

/-- The phase is as it was. -/
theorem phase {s s' : GameState} (h : SameMeta s s') : s'.phase = s.phase := by
  unfold SameMeta at h
  have h2 := congrArg GameState.phase h
  exact h2

/-- The turn counter is as it was. -/
theorem turn {s s' : GameState} (h : SameMeta s s') : s'.turn = s.turn := by
  unfold SameMeta at h
  have h2 := congrArg GameState.turn h
  exact h2

/-- The player whose turn it is, is as it was. -/
theorem active {s s' : GameState} (h : SameMeta s s') : s'.active = s.active := by
  unfold SameMeta at h
  have h2 := congrArg GameState.active h
  exact h2

/-- The result is as it was. -/
theorem result {s s' : GameState} (h : SameMeta s s') : s'.result = s.result := by
  unfold SameMeta at h
  have h2 := congrArg GameState.result h
  exact h2

end SameMeta

/-- What `moveObj` did, in the terms the proofs need. `src` and `dst` are the zone the object
left and the zone it went to, after `Zone.normalize`. -/
structure MoveSpec (s s' : GameState) (id id' : ObjId) (pos : Pos) (src dst : Zone) : Prop where
  /-- The source is a zone of the game and holds the object. -/
  src_mem : src ∈ allZones s.playerCount
  /-- The object is on the source zone. -/
  id_mem : id ∈ s.zone src
  /-- The destination is a zone of the game. -/
  dst_mem : dst ∈ allZones s.playerCount
  /-- The two zones differ. -/
  ne : src ≠ dst
  /-- The rules of the game stay. -/
  config : s'.config = s.config
  /-- Only the two zones change: the object leaves one and enters the other. -/
  zones : s'.zones = ((s.setZone src ((s.zone src).erase id)).setZone dst
    (pos.insert id' (s.zone dst))).zones
  /-- The object has a new identifier exactly when it crossed a Non-Board zone, and the new
  one is the old counter. -/
  fresh : id' = id ∨ id'.n = s.nextId
  /-- The counter does not go down, and a new identifier is below it. -/
  next : s.nextId ≤ s'.nextId ∧ (id' = id ∨ id'.n < s'.nextId)
  /-- The object table loses the old entry and gains the new one. -/
  objects : ∀ k, k ∈ s'.objects ↔ (k ∈ s.objects ∧ k ≠ id.n) ∨ k = id'.n
  /-- The other entries stay as they were. -/
  objects_other : ∀ k, k ≠ id.n → k ≠ id'.n → s'.objects[k]? = s.objects[k]?
  /-- The new entry is the same kind of object (the same physical card). -/
  kind : (s'.objects[id'.n]?).map (·.kind) = (s.objects[id.n]?).map (·.kind)
  /-- The object is where it was put. -/
  id'_mem : id' ∈ s'.zone dst
  /-- It crossed exactly when it got a new identifier. -/
  crosses : Zone.crosses src dst = true ∨ id' = id
  /-- The source is the zone `locate` finds the object on. -/
  locate : s.locate id = some src
  /-- Points are not touched. -/
  points : s'.points = s.points
  /-- The object keeps its owner. -/
  owner : (s'.objects[id'.n]?).map (·.owner) = (s.objects[id.n]?).map (·.owner)
  /-- The turn order is not touched. -/
  turnOrder : s'.turnOrder = s.turnOrder
  /-- The stack of frames is not touched. -/
  pending : s'.pending = s.pending
  /-- Nothing but the zones, the object table and the counters changes: every other part of the
  state, present or future, is as it was. -/
  other : SameMeta s s'
  /-- The Rune Pools are as they were. -/
  pools : s'.pools = s.pools

/-- The shape of a successful move, with the link between the asked destination and the one the
object went to (CR 056). -/
theorem moveObj_spec_dst {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    (h : moveObj s id dst pos = some (s', id')) :
    ∃ src d, MoveSpec s s' id id' pos src d ∧
      ∃ o, s.obj? id = some o ∧ d = Zone.normalize o.owner dst := by
  unfold moveObj at h
  split at h
  · rename_i src o hloc hobj
    obtain ⟨hsrc, hid⟩ := GameState.locate_spec hloc
    simp only at h
    split at h
    · exact absurd h (by simp)
    · rename_i hcond
      simp only [not_or, Decidable.not_not] at hcond
      obtain ⟨hne, hvalid⟩ := hcond
      have hobj_id : id.n ∈ s.objects := by
        simp only [GameState.obj?] at hobj
        rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hobj]
        rfl
      split at h
      · rename_i hcr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨src, Zone.normalize o.owner dst, ?_, o, hobj, rfl⟩
        refine ⟨hsrc, hid, hvalid, hne, rfl, rfl, Or.inr rfl, ⟨by simp, Or.inr (by simp)⟩,
          ?_, ?_, ?_, ?_, ?_, hloc, rfl, ?_, rfl, rfl, rfl, rfl⟩
        · intro k
          simp only [Std.ExtTreeMap.mem_insert, Std.ExtTreeMap.mem_erase, Nat.compare_eq_eq,
            ne_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inr h.symm
            · exact Or.inl ⟨h2, fun e => h1 e.symm⟩
          · rintro (⟨h1, h2⟩ | h)
            · exact Or.inr ⟨fun e => h2 e.symm, h1⟩
            · exact Or.inl h.symm
        · intro k hk1 hk2
          have hk2' : s.nextId ≠ k := fun e => hk2 e.symm
          have hk1' : id.n ≠ k := fun e => hk1 e.symm
          simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase, hk1', hk2']
        · have hobj' : s.objects[id.n]? = some o := hobj
          simp [hobj']
        · show _ ∈ ((s.setZone _ _).setZone _ _).zone _
          rw [GameState.zone_move hne]
          simpa using Pos.mem_insert pos _ _
        · exact Or.inl hcr
        · have hobj' : s.objects[id.n]? = some o := hobj
          simp [hobj']
      · rename_i hcr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨src, Zone.normalize o.owner dst, ?_, o, hobj, rfl⟩
        refine ⟨hsrc, hid, hvalid, hne, rfl, rfl, Or.inl rfl, ⟨Nat.le_refl _, Or.inl rfl⟩,
          ?_, ?_, rfl, ?_, Or.inr rfl, hloc, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · intro k
          change k ∈ s.objects ↔ _
          by_cases hk : k = id.n
          · subst hk; simp [hobj_id]
          · simp [hk]
        · intro k _ _
          rfl
        · show _ ∈ ((s.setZone _ _).setZone _ _).zone _
          rw [GameState.zone_move hne]
          simpa using Pos.mem_insert pos _ _
  · exact absurd h (by simp)

/-- The shape of a successful move. -/
theorem moveObj_spec {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    (h : moveObj s id dst pos = some (s', id')) :
    ∃ src d, MoveSpec s s' id id' pos src d := by
  obtain ⟨src, d, hs, -⟩ := moveObj_spec_dst h
  exact ⟨src, d, hs⟩

namespace GameState

/-- The physical cards in all zones, zone by zone. Tokens and Chain abilities have none. -/
def physIds (s : GameState) : List PhysId :=
  s.zoneIds.filterMap (fun id => (s.obj? id).bind (·.kind.phys?))

end GameState

/-- Moving an object keeps the game well formed (design.md §8, L1). -/
theorem moveObj_wf {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    (hwf : s.WF) (h : moveObj s id dst pos = some (s', id')) : s'.WF := by
  obtain ⟨src, d, hs⟩ := moveObj_spec h
  exact GameState.wf_of_move hwf hs.config hs.src_mem hs.id_mem hs.dst_mem hs.ne hs.zones
    hs.objects hs.fresh hs.next

/-- The object is on the destination zone afterwards, under its new identifier. -/
theorem moveObj_mem {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    (h : moveObj s id dst pos = some (s', id')) :
    ∃ d, d ∈ allZones s.playerCount ∧ id' ∈ s'.zone d := by
  obtain ⟨src, d, hs⟩ := moveObj_spec h
  exact ⟨d, hs.dst_mem, hs.id'_mem⟩

/-- A new identifier is new: it is not the identifier of any object in the game before the
move (CR 124). The identifier stays only when the move does not cross a Non-Board zone. -/
theorem moveObj_fresh {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    (hwf : s.WF) (h : moveObj s id dst pos = some (s', id')) :
    id' = id ∨ id' ∉ s.zoneIds := by
  obtain ⟨src, d, hs⟩ := moveObj_spec h
  rcases hs.fresh with h1 | h1
  · exact Or.inl h1
  · refine Or.inr (fun hm => ?_)
    have := hwf.lt_nextId id' hm
    omega

/-- **I1** (one step). Moving an object keeps the physical cards: the list of physical cards in
the zones is rearranged, nothing is lost or made (design.md §8, L1). -/
theorem moveObj_physIds {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    (hwf : s.WF) (h : moveObj s id dst pos = some (s', id')) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨src, d, hs⟩ := moveObj_spec h
  obtain ⟨core, h1, h2, hcore⟩ :=
    GameState.zoneIds_move hs.config hs.src_mem hs.id_mem hs.dst_mem hs.ne hs.zones
  have hnd : (id :: core).Nodup := h1.nodup_iff.mp hwf.nodup
  rw [List.nodup_cons] at hnd
  have hne_id : ∀ x ∈ core, x.n ≠ id.n := fun x hx e => by
    have : x = id := by cases x; cases id; simp_all
    exact hnd.1 (this ▸ hx)
  have hne_id' : ∀ x ∈ core, x.n ≠ id'.n := fun x hx e => by
    rcases hs.fresh with h3 | h3
    · exact hne_id x hx (by rw [e, h3])
    · have := hwf.lt_nextId x (hcore x hx)
      omega
  have hobj_eq : ∀ x ∈ core, s'.obj? x = s.obj? x := fun x hx => by
    simp only [GameState.obj?]
    exact hs.objects_other x.n (hne_id x hx) (hne_id' x hx)
  have hid_eq : ((s'.obj? id').bind (·.kind.phys?)) = ((s.obj? id).bind (·.kind.phys?)) := by
    have hk := hs.kind
    simp only [GameState.obj?]
    rcases ha : s.objects[id.n]? with _ | o <;> rcases hb : s'.objects[id'.n]? with _ | o' <;>
      simp_all
  have hfm : core.filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) =
      core.filterMap (fun x => (s.obj? x).bind (·.kind.phys?)) := by
    apply filterMap_congr_mem
    intro x hx
    rw [hobj_eq x hx]
  have heq : (id' :: core).filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) =
      (id :: core).filterMap (fun x => (s.obj? x).bind (·.kind.phys?)) := by
    simp only [List.filterMap_cons, hid_eq, hfm]
  unfold GameState.physIds
  have p1 := List.Perm.filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) h2
  rw [heq] at p1
  exact p1.trans (List.Perm.filterMap _ h1).symm

namespace GameState

/-- In a well-formed game, an object on a zone is on no other zone. -/
theorem zone_unique {s : GameState} (hwf : s.WF) {z z' : Zone} {id : ObjId}
    (hz : z ∈ allZones s.playerCount) (hz' : z' ∈ allZones s.playerCount)
    (h : id ∈ s.zone z) (h' : id ∈ s.zone z') : z' = z := by
  by_cases hne : z' = z
  · exact hne
  exfalso
  have hperm := flatMap_split (allZones s.playerCount) s.zone z hz
  have hnd : (s.zone z ++ ((allZones s.playerCount).erase z).flatMap s.zone).Nodup :=
    (hperm.nodup_iff).mp hwf.nodup
  rw [List.nodup_append] at hnd
  have hmem : id ∈ ((allZones s.playerCount).erase z).flatMap s.zone :=
    List.mem_flatMap.mpr ⟨z', (List.mem_erase_of_ne hne).mpr hz', h'⟩
  exact hnd.2.2 id h id hmem rfl

/-- In a well-formed game, `locate` finds the zone an object is on. -/
theorem locate_eq {s : GameState} (hwf : s.WF) {z : Zone} {id : ObjId}
    (hz : z ∈ allZones s.playerCount) (h : id ∈ s.zone z) : s.locate id = some z := by
  unfold locate
  apply find?_eq_some_of_unique _ _ z hz
  intro x hx
  simp only [List.contains_iff_mem]
  exact ⟨fun hm => zone_unique hwf hz hx h hm, fun e => e ▸ h⟩

end GameState

namespace MoveSpec

variable {s s' : GameState} {id id' : ObjId} {pos : Pos} {src dst : Zone}

/-- After the move, the destination holds the object (under its new identifier) in front of what
was there. -/
theorem zone_dst (hs : MoveSpec s s' id id' pos src dst) :
    s'.zone dst = pos.insert id' (s.zone dst) := by
  have : s'.zone dst = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zone dst := by simp [GameState.zone, hs.zones]
  rw [this, GameState.zone_move hs.ne]
  simp

/-- After the move, the source no longer holds the object. -/
theorem zone_src (hs : MoveSpec s s' id id' pos src dst) :
    s'.zone src = (s.zone src).erase id := by
  have : s'.zone src = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zone src := by simp [GameState.zone, hs.zones]
  rw [this, GameState.zone_move hs.ne]
  simp [hs.ne]

/-- Every other zone is unchanged. -/
theorem zone_other (hs : MoveSpec s s' id id' pos src dst) {z : Zone} (h1 : z ≠ src)
    (h2 : z ≠ dst) : s'.zone z = s.zone z := by
  have : s'.zone z = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zone z := by simp [GameState.zone, hs.zones]
  rw [this, GameState.zone_move hs.ne]
  simp [h1, h2]

end MoveSpec

end Riftbound

end
