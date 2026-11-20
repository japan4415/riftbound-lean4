module

public import Riftbound.State.Zone
public import Riftbound.State.Object
public import Riftbound.State.GameConfig
public import Riftbound.State.Decision
public import Riftbound.State.Phase
public import Riftbound.State.Pool
public import Riftbound.Card.CardDB
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
  /-- The cards of this game. It is part of the game as the rules are: the engine reads the
  definitions of the cards from it and never changes it (design.md §6.1). -/
  cards : CardDB
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
  /-- The stack of frames; the head is the current one (design.md §6.2). -/
  pending : List Frame
  /-- The turn order, first player first (CR 115). Empty until it has been decided. -/
  turnOrder : List PlayerId
  /-- The phase the game is in (CR 314-317). -/
  phase : Phase
  /-- How many turns have begun. -/
  turn : Nat
  /-- The player whose turn it is, once a turn has begun (CR 301). -/
  active : Option PlayerId
  /-- How the game ended, if it has (CR 193-196). -/
  result : Option GameResult
  /-- The Rune Pool of each player, keyed by `PlayerId.n`. A missing player has an empty Pool
  (CR 166). -/
  pools : Std.ExtTreeMap Nat RunePool
deriving DecidableEq, Repr

/-- Every zone of a game with `n` players. -/
def allZones (n : Nat) : List Zone :=
  Zone.battlefieldZone :: Zone.chain ::
    (List.range n).flatMap (fun i => ZoneKind.all.map (Zone.player ⟨i⟩))

/-- A zone of a game with `n` players is in `allZones n`. -/
def Zone.Valid (n : Nat) (z : Zone) : Prop := z ∈ allZones n

instance Zone.decidableValid (n : Nat) (z : Zone) : Decidable (z.Valid n) := by
  unfold Zone.Valid; infer_instance

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

/-- The Rune Pool of a player (CR 166). -/
def poolOf (s : GameState) (p : PlayerId) : RunePool := s.pools.getD p.n RunePool.empty

/-- Replace the Rune Pool of a player. -/
def setPool (s : GameState) (p : PlayerId) (pool : RunePool) : GameState :=
  { s with pools := s.pools.insert p.n pool }

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

/-- `WF` only looks at the rules, which objects are in the object table, the zones and the
identifier counter. States that agree on these are well formed together. -/
theorem WF.congr_mem {s s2 : GameState} (hwf : s.WF) (hc : s2.config = s.config)
    (ho : ∀ k, k ∈ s2.objects ↔ k ∈ s.objects) (hz : s2.zones = s.zones)
    (hn : s2.nextId = s.nextId) : s2.WF := by
  have hcount : s2.playerCount = s.playerCount := by simp [playerCount, hc]
  have hzone : ∀ z, s2.zone z = s.zone z := fun z => by simp [zone, hz]
  have hids : s2.zoneIds = s.zoneIds := by
    unfold zoneIds
    rw [hcount]
    have : s2.zone = s.zone := funext hzone
    rw [this]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hids]; exact hwf.nodup
  · intro x hx; rw [hids] at hx; exact (ho _).mpr (hwf.table_of_zone x hx)
  · intro k hk; rw [hids]; exact hwf.zone_of_table k ((ho k).mp hk)
  · intro x hx; rw [hids] at hx; rw [hn]; exact hwf.lt_nextId x hx
  · intro k hk; rw [hz] at hk; rw [hcount]; exact hwf.zones_valid k hk

/-- `WF` for a state with the same object table. -/
theorem WF.congr {s s2 : GameState} (hwf : s.WF) (hc : s2.config = s.config)
    (ho : s2.objects = s.objects) (hz : s2.zones = s.zones) (hn : s2.nextId = s.nextId) :
    s2.WF :=
  WF.congr_mem hwf hc (fun k => by rw [ho]) hz hn

/-- The owner of every card in a Non-Board zone of a player is that player (CR 056): a card never
sits in the Non-Board zone of someone who does not own it. -/
structure OwnerOk (s : GameState) : Prop where
  /-- The owner of an object in a Non-Board zone of player `p` is `p`. -/
  owner : ∀ (p : PlayerId) (k : ZoneKind), k.isBoard = false →
    ∀ id ∈ s.zone (.player p k), ∀ o, s.obj? id = some o → o.owner = p

/-- `OwnerOk` only looks at the object table and the zones. -/
theorem OwnerOk.congr {s s2 : GameState} (h : s.OwnerOk) (ho : s2.objects = s.objects)
    (hz : s2.zones = s.zones) : s2.OwnerOk := by
  refine ⟨fun p k hk id hid o hobj => ?_⟩
  have hzone : s2.zone (.player p k) = s.zone (.player p k) := by simp [zone, hz]
  have hobj' : s2.obj? id = s.obj? id := by simp [obj?, ho]
  rw [hzone] at hid
  rw [hobj'] at hobj
  exact h.owner p k hk id hid o hobj

end GameState

end Riftbound

end
