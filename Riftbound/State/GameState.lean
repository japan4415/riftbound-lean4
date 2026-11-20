module

public import Riftbound.State.Zone
public import Riftbound.State.Object
public import Riftbound.State.GameConfig
public import Std.Data.ExtTreeMap

/-!
# Game state

The zones, the objects, the scores and the counters (design.md §5.2-5.3), and the structural
invariant `WF` (design.md §5.2). The decision frames and the turn state are added with the
engine (milestone M2b).
-/

@[expose] public section

namespace Riftbound

/-- The state of a game. The lists in `zones` are the source of truth for where objects are. -/
structure GameState where
  /-- The rules of this game. -/
  config : GameConfig
  /-- The attributes of every object, keyed by `ObjId.n`. -/
  objects : Std.ExtTreeMap Nat Object
  /-- The contents of the zones, keyed by `Zone.key`. A missing zone is empty. -/
  zones : Std.ExtTreeMap Nat (List ObjId)
  /-- The points of each player, keyed by `PlayerId.n`. A missing player has 0 (CR 194). -/
  points : Std.ExtTreeMap Nat Nat
  /-- The next `ObjId` to hand out (CR 124). -/
  nextId : Nat
  /-- The next `Timestamp` to hand out (CR 482). -/
  nextTimestamp : Nat
deriving DecidableEq, Repr

/-- Every zone of a game with `n` players. -/
def allZones (n : Nat) : List Zone :=
  Zone.battlefieldZone :: Zone.chain ::
    (List.range n).flatMap (fun i => ZoneKind.all.map (Zone.player ⟨i⟩))

/-- A zone of a game with `n` players is in `allZones n`. -/
def Zone.Valid (n : Nat) (z : Zone) : Prop := z ∈ allZones n

instance Zone.decidableValid (n : Nat) (z : Zone) : Decidable (z.Valid n) := by unfold Zone.Valid; infer_instance

/-- Each zone is listed once. -/
theorem allZones_nodup (n : Nat) : (allZones n).Nodup := by
  unfold allZones
  rw [List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · show List.Pairwise (· ≠ ·) _
    rw [List.pairwise_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · show List.Pairwise (· ≠ ·) _
      refine List.Pairwise.map (Zone.player ⟨i⟩) ?_ ZoneKind.all_nodup
      intro a b hab h
      simp only [Zone.player.injEq, true_and] at h
      exact hab h
    · refine List.Pairwise.imp ?_ List.nodup_range
      intro a b hab x hxa y hxb
      simp only [List.mem_map] at hxa hxb
      obtain ⟨k, -, rfl⟩ := hxa
      obtain ⟨l, -, rfl⟩ := hxb
      intro h
      simp only [Zone.player.injEq, PlayerId.mk.injEq] at h
      exact hab h.1

/-- Every zone of a player is valid in a game with enough players. -/
theorem Zone.valid_player {n : Nat} {p : PlayerId} (h : p.n < n) (k : ZoneKind) :
    (Zone.player p k).Valid n := by
  unfold Zone.Valid allZones
  simp only [List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map]
  right; right
  exact ⟨p.n, h, k, ZoneKind.mem_all k, rfl⟩

/-- The shared zones are valid. -/
theorem Zone.valid_battlefieldZone (n : Nat) : Zone.battlefieldZone.Valid n := by
  simp [Zone.Valid, allZones]

/-- The Chain is valid. -/
theorem Zone.valid_chain (n : Nat) : Zone.chain.Valid n := by
  simp [Zone.Valid, allZones]

namespace GameState

/-- The number of players. -/
def playerCount (s : GameState) : Nat := s.config.mode.players

/-- The contents of a zone. -/
def zone (s : GameState) (z : Zone) : List ObjId := s.zones.getD z.key []

/-- Replace the contents of a zone. -/
def setZone (s : GameState) (z : Zone) (l : List ObjId) : GameState :=
  { s with zones := s.zones.insert z.key l }

/-- The attributes of an object. -/
def obj? (s : GameState) (id : ObjId) : Option Object := s.objects[id.n]?

/-- The points of a player. -/
def pointsOf (s : GameState) (p : PlayerId) : Nat := s.points.getD p.n 0

/-- Every object on any zone, zone by zone. -/
def zoneIds (s : GameState) : List ObjId :=
  (allZones s.playerCount).flatMap s.zone

/-- Reading a zone just written gives what was written. -/
theorem zone_setZone_self (s : GameState) (z : Zone) (l : List ObjId) :
    (s.setZone z l).zone z = l := by
  simp [zone, setZone]

/-- Writing a zone does not change another zone. -/
theorem zone_setZone_ne (s : GameState) {z z' : Zone} (h : z' ≠ z) (l : List ObjId) :
    (s.setZone z l).zone z' = s.zone z' := by
  have hk : z'.key ≠ z.key := fun e => h (Zone.key_inj e)
  have hk' : z.key ≠ z'.key := fun e => hk e.symm
  simp [zone, setZone, Std.ExtTreeMap.getD_insert, hk']

/-- Structural well-formedness: it holds in every intermediate state (design.md §5.2).
1. each object is on exactly one zone (`zoneIds` has no repeats);
2. the object table has an entry for exactly the objects on zones;
3. every identifier on a zone is below `nextId`;
4. only the zones of the game hold anything. -/
structure WF (s : GameState) : Prop where
  /-- Each object is in one place (design.md §5.2, position uniqueness). -/
  nodup : s.zoneIds.Nodup
  /-- Every object on a zone has attributes. -/
  table_of_zone : ∀ id ∈ s.zoneIds, id.n ∈ s.objects
  /-- Every entry of the table is on a zone. -/
  zone_of_table : ∀ k, k ∈ s.objects → ∃ id ∈ s.zoneIds, id.n = k
  /-- Identifiers are below the counter. -/
  lt_nextId : ∀ id ∈ s.zoneIds, id.n < s.nextId
  /-- No zone outside the game holds an object. -/
  zones_valid : ∀ k, k ∈ s.zones → ∃ z ∈ allZones s.playerCount, z.key = k

end GameState

end Riftbound

end
