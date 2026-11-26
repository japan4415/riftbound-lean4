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

/-- A lasting effect for the rest of a turn: whose it is, the turn, the timestamp counter when it
was made, and what it is. -/
structure TurnFx where
  /-- The player the effect is for. -/
  who : PlayerId
  /-- The turn it lasts through. -/
  turn : Nat
  /-- The timestamp counter then: what the player plays later has a greater `playedStamp`. -/
  stamp : Nat
  /-- What it is. -/
  kind : TurnEffect
  /-- The object it is about, if it is about one. -/
  target : Option ObjId := none
  /-- The number of cards the player had finalized when a next-card discount was created. -/
  playCount : Nat := 0
deriving DecidableEq, Repr

/-- The sides and all Unit objects that participated in the current Combat (CR 466, 468). -/
structure CombatParticipation where
  /-- Where the Combat took place. -/
  battlefield : ObjId
  /-- The attacking player. -/
  attacker : PlayerId
  /-- The defending player. -/
  defender : PlayerId
  /-- Units that received a designation, including those that have since moved away. -/
  units : List ObjId
  /-- The Combat Cleanup recalled at least one attacker, giving the Combat no result (CR 468.3.d). -/
  recalled : Bool := false
deriving DecidableEq, Repr

/-- The point of a play that history records (CR 420.4). -/
inductive PlayMoment where
  /-- Choices and costs have been finalized, even if the card is later countered. -/
  | finalized
  /-- The permanent or Spell has resolved. -/
  | resolved
deriving DecidableEq, Repr

/-- A completed part of a card's play, independent of the object's later zones or controller. -/
structure CardPlay where
  /-- The player who performed this part of the play. -/
  who : PlayerId
  /-- The object identifier at this point of the play. -/
  object : ObjId
  /-- The types of the card at that point, including both types of a Unit Gear. -/
  types : List CardType
  /-- The turn in which it happened. -/
  turn : Nat
  /-- Whether this is a finalization or a resolved play. -/
  moment : PlayMoment
deriving DecidableEq, Repr

/-- Withdrawn seats and the regular turn positions already skipped because of a withdrawal. -/
structure SeatDepartures where
  /-- Seats that have already left, in departure order. Their registration and zones remain. -/
  seats : List PlayerId := []
  /-- How many regular turn positions were skipped in the original turn order. -/
  skippedTurns : Nat := 0
deriving DecidableEq, Repr

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
  /-- The schedule and end-of-match procedure once the tournament clock has been called
  (TR 408.2, 408.4). -/
  clock : Option RoundClock := none
  /-- What spells and abilities made true for the rest of a turn (CR 389-393). -/
  turnFx : List TurnFx := []
  /-- The cards drawn in the current turn: the player who drew, and the turn (older ones are
  dropped as a card is drawn). -/
  drawLog : List (PlayerId × Nat) := []
  /-- Finalizations and resolved permanent plays, newest first (CR 420.4). -/
  playLog : List CardPlay := []
  /-- The players who take an extra turn next, in order (Time Warp). -/
  extraTurns : List PlayerId := []
  /-- How many of the turns taken were extra turns: the turn order goes on as if they were not. -/
  turnShift : Nat := 0
  /-- Who took each extra turn already begun, newest first (CR 301). -/
  extraTurnsTaken : List PlayerId := []
  /-- The current Combat, including Units that left its Battlefield (CR 466, 468). -/
  combat : Option CombatParticipation := none
  /-- Seat withdrawals do not change zone numbering or the original turn order (CR 652.5). -/
  departures : SeatDepartures := {}
  /-- Public XP by seat. A missing player has 0 (CR 729, 732). -/
  experience : Std.ExtTreeMap Nat Nat := {}
deriving DecidableEq

/-- Game archives hashed the printed state before withdrawals were added. Preserve that format
for games before their first withdrawal and include the new state once a seat has left. -/
instance : Repr GameState where
  reprPrec s _ :=
    let field (name : String) (value : Std.Format) :=
      Std.Format.text name ++ " := " ++ (Std.Format.nest (name.length + 4) value).group
    let fields := [
      field "config" (repr s.config), field "cards" (repr s.cards),
      field "objects" (repr s.objects), field "zones" (repr s.zones),
      field "points" (repr s.points), field "nextId" (repr s.nextId),
      field "nextTimestamp" (repr s.nextTimestamp), field "pending" (repr s.pending),
      field "turnOrder" (repr s.turnOrder), field "phase" (repr s.phase),
      field "turn" (repr s.turn), field "active" (repr s.active),
      field "result" (repr s.result), field "pools" (repr s.pools),
      field "clock" (repr s.clock), field "turnFx" (repr s.turnFx),
      field "drawLog" (repr s.drawLog), field "playLog" (repr s.playLog),
      field "extraTurns" (repr s.extraTurns), field "turnShift" (repr s.turnShift),
      field "extraTurnsTaken" (repr s.extraTurnsTaken), field "combat" (repr s.combat)]
    let fields := if s.departures.seats.isEmpty && s.departures.skippedTurns == 0 then fields
      else fields ++ [field "departures" (repr s.departures)]
    let fields := if s.experience.isEmpty then fields
      else fields ++ [field "experience" (repr s.experience)]
    Std.Format.bracket "{ " (Std.Format.joinSep fields (Std.Format.text "," ++ Std.Format.line)) " }"

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

/-- A registered seat still taking part in the game (CR 651.3). -/
def participates (s : GameState) (p : PlayerId) : Bool :=
  decide (p.n < s.playerCount) && !s.departures.seats.contains p

/-- The seats that still take part, in registration order. -/
def participatingSeats (s : GameState) : List PlayerId :=
  ((List.range s.playerCount).map (fun i => (⟨i⟩ : PlayerId))).filter s.participates

/-- The original turn order with departed seats removed (CR 652.5.a). -/
def participatingOrder (s : GameState) : List PlayerId :=
  s.turnOrder.filter s.participates

/-- The number of seats whose passes are needed to close a Chain or Showdown. -/
def participatingCount (s : GameState) : Nat :=
  if s.departures.seats.isEmpty then s.playerCount else s.participatingSeats.length

/-- Read an established handoff ring from the seat immediately after the holder.
The current holder is last. -/
def _root_.Riftbound.seatOrderAfter (order : List PlayerId) (holder : PlayerId) : List PlayerId :=
  match order.idxOf? holder with
  | none => []
  | some index => order.drop (index + 1) ++ order.take (index + 1)

/-- The next regular position in the original turn order. Extra turns do not advance it. -/
def regularTurnPosition (s : GameState) : Nat :=
  s.turn - s.turnShift + s.departures.skippedTurns

/-- The original turn-order position with the next eligible turn player and any skipped seats. -/
def nextRegularTurn (s : GameState) : PlayerId × Nat :=
  let start := s.regularTurnPosition % s.playerCount
  if s.departures.seats.isEmpty then (s.turnOrder.getD start ⟨0⟩, 0) else
    let cycle := s.turnOrder.drop start ++ s.turnOrder.take start
    let offset := (cycle.findIdx? s.participates).getD 0
    (cycle.getD offset ⟨0⟩, offset)

/-- The contents of a zone. -/
def zone (s : GameState) (z : Zone) : List ObjId := s.zones.getD z.key []

/-- Replace the contents of a zone. -/
def setZone (s : GameState) (z : Zone) (l : List ObjId) : GameState :=
  { s with zones := s.zones.insert z.key l }

/-- The attributes of an object. -/
def obj? (s : GameState) (id : ObjId) : Option Object := s.objects[id.n]?

/-- A copy effect applies for the same occurrence of the attachment that created it. -/
def attachmentCopyActive (s : GameState) (unit : ObjId) (copy : AttachmentCopy) : Bool :=
  (s.obj? copy.gear).any (fun o =>
    o.attached == some unit && o.attachmentCopyStamp == some copy.stamp)

/-- The last applied copy whose Equipment is still attached (CR 479.1, 482). -/
def attachmentCopyOf (s : GameState) (unit : ObjId) (o : Object) : Option AttachmentCopy :=
  o.attachmentCopies.find? (s.attachmentCopyActive unit)

/-- Check that the Effect Text belongs to this occurrence of the attachment (CR 436, 482). -/
def attachmentTextActive (s : GameState) (unit : ObjId) (copy : AttachmentCopy) : Bool :=
  (s.obj? copy.gear).any (fun o =>
    o.attached == some unit && o.attachmentTextStamp == some copy.stamp)

/-- The active Effect Text copies currently appended to a Unit's rules text (CR 719.1, 479.3.c). -/
def activeAttachmentText (s : GameState) (unit : ObjId) : List AttachmentCopy :=
  ((s.obj? unit).map (·.attachmentTextCopies)).getD [] |>.filter (s.attachmentTextActive unit)

/-- The instance of the object's current copied rules text, if any. -/
def copyStamp? (s : GameState) (unit : ObjId) : Option Timestamp :=
  (s.obj? unit).bind (fun o => (s.attachmentCopyOf unit o).map (·.stamp))

/-- The Rune Pool of a player (CR 166). -/
def poolOf (s : GameState) (p : PlayerId) : RunePool := s.pools.getD p.n RunePool.empty

/-- Replace the Rune Pool of a player. -/
def setPool (s : GameState) (p : PlayerId) (pool : RunePool) : GameState :=
  { s with pools := s.pools.insert p.n pool }

/-- The points of a player or their team (CR 491.8.d). -/
def pointsOf (s : GameState) (p : PlayerId) : Nat :=
  s.points.getD (s.config.mode.scoringSeat p).n 0

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
