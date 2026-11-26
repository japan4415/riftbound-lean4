module

public import Riftbound.Core.Ids

/-!
# Zones

The zones of the game (CR 105-109). Every zone holds a list of object identifiers. For an
ordered zone (a deck, the Chain) the head of the list is the top.

Facedown Zones (CR 107.3) arrive with Hidden (milestone M6).
-/

@[expose] public section

namespace Riftbound

/-- The kinds of zone every player has. `setAside` and `outOfGame` are zones of the engine
itself: cards set aside by a mulligan (CR 117.1), and physical cards outside the game
(design.md §5.2). -/
inductive ZoneKind where
  /-- Base (CR 105). Board. -/
  | base
  /-- Trash. Non-Board. -/
  | trash
  /-- Champion Zone. Non-Board. -/
  | championZone
  /-- Main Deck. Non-Board, ordered. -/
  | mainDeck
  /-- Rune Deck. Non-Board, ordered. -/
  | runeDeck
  /-- Banishment. Non-Board. -/
  | banishment
  /-- Hand. Non-Board. -/
  | hand
  /-- Legend Zone. Board. -/
  | legendZone
  /-- Cards set aside by a mulligan (CR 117.1). Non-Board. -/
  | setAside
  /-- Physical cards outside the game. Non-Board. -/
  | outOfGame
  /-- Cards hidden face down at a Battlefield (CR 811). Non-Board. -/
  | hidden
  /-- Additional Legends registered during deckbuilding (CR 103.1). Non-Board. -/
  | reserveLegends
deriving DecidableEq, Repr, Hashable

/-- Every zone kind. -/
def ZoneKind.all : List ZoneKind :=
  [.base, .trash, .championZone, .mainDeck, .runeDeck, .banishment, .hand, .legendZone,
    .setAside, .outOfGame, .hidden, .reserveLegends]

/-- A distinct number for each kind, below 12. -/
def ZoneKind.idx : ZoneKind → Nat
  | .base => 0
  | .trash => 1
  | .championZone => 2
  | .mainDeck => 3
  | .runeDeck => 4
  | .banishment => 5
  | .hand => 6
  | .legendZone => 7
  | .setAside => 8
  | .outOfGame => 9
  | .hidden => 10
  | .reserveLegends => 11

/-- The numbers of the kinds are below 12. -/
theorem ZoneKind.idx_lt (k : ZoneKind) : k.idx < 12 := by
  cases k <;> decide

/-- Different kinds have different numbers. -/
theorem ZoneKind.idx_inj {a b : ZoneKind} (h : a.idx = b.idx) : a = b := by
  cases a <;> cases b <;> simp_all [ZoneKind.idx]

/-- Board kinds of zone (CR 105-109). The others are Non-Board. -/
def ZoneKind.isBoard : ZoneKind → Bool
  | .base => true
  | .legendZone => true
  | _ => false

/-- Every kind is in `ZoneKind.all`. -/
theorem ZoneKind.mem_all (k : ZoneKind) : k ∈ ZoneKind.all := by
  cases k <;> decide

/-- `ZoneKind.all` lists each kind once. -/
theorem ZoneKind.all_nodup : ZoneKind.all.Nodup := by decide

/-- A zone of the game. -/
inductive Zone where
  /-- A zone of a player. -/
  | player (p : PlayerId) (k : ZoneKind)
  /-- The Battlefield Zone (CR 106), shared. Board. -/
  | battlefieldZone
  /-- The Chain (CR 330), shared. Non-Board, ordered, the head is the newest item. -/
  | chain
deriving DecidableEq, Repr, Hashable

namespace Zone

/-- Board zones (CR 105-109). Everything else is Non-Board. -/
def isBoard : Zone → Bool
  | .player _ .base => true
  | .player _ .legendZone => true
  | .battlefieldZone => true
  | _ => false

/-- A zone of a player is Board exactly when its kind is. -/
theorem isBoard_player (p : PlayerId) (k : ZoneKind) : (Zone.player p k).isBoard = k.isBoard := by
  cases k <;> rfl

/-- A number for each zone: 0 and 1 for the shared zones, then twelve per seat. -/
def key : Zone → Nat
  | .battlefieldZone => 0
  | .chain => 1
  | .player p k => 2 + p.n * 12 + k.idx

/-- Different zones have different keys. -/
theorem key_inj {a b : Zone} (h : a.key = b.key) : a = b := by
  cases a with
  | battlefieldZone => cases b <;> simp only [key] at h <;> first | rfl | omega
  | chain => cases b <;> simp only [key] at h <;> first | rfl | omega
  | player p k =>
    cases b with
    | battlefieldZone => simp only [key] at h; omega
    | chain => simp only [key] at h; omega
    | player q l =>
      have hk := k.idx_lt
      have hl := l.idx_lt
      simp only [key] at h
      have h1 : p.n = q.n := by omega
      have h2 : k.idx = l.idx := by omega
      obtain ⟨pn⟩ := p
      obtain ⟨qn⟩ := q
      simp only at h1
      subst h1
      rw [ZoneKind.idx_inj h2]

end Zone

end Riftbound

end
