module

import Riftbound.Rules.Actions.Draw
import Riftbound.Rules.Actions.Channel
import Riftbound.Rules.Actions.BurnOut
meta import Riftbound.Rules.Actions.Draw
meta import Riftbound.Rules.Actions.Channel
meta import Riftbound.Rules.Actions.BurnOut

/-!
# Tests: zones and the primitives (CR 124, 414, 417, 431, 432)

A two-player state is written out by hand: objects 0-2 are player 0's Main Deck (0 on top),
3 is in hand, 4 and 5 are in the Trash, 6 and 7 are the Rune Deck, 8 is in player 1's Main Deck.
-/

namespace RiftboundTest

open Riftbound

meta def p0 : PlayerId := ⟨0⟩
meta def p1 : PlayerId := ⟨1⟩

meta def card (i : Nat) (owner : PlayerId) : Object :=
  { kind := .card ⟨i⟩ ⟨s!"c{i}"⟩, owner := owner, controller := owner,
    timestamp := ⟨i⟩ }

meta def put (z : Zone) (l : List Nat) : Nat × List ObjId := (z.key, l.map (⟨·⟩))

meta def s0 : GameState :=
  { config := { ruleSet := .coreOnly, mode := Mode.duel }
    objects := Std.ExtTreeMap.ofList
      ((List.range 8).map (fun i => (i, card i p0)) ++ [(8, card 8 p1)])
    zones := Std.ExtTreeMap.ofList
      [ put (.player p0 .mainDeck) [0, 1, 2], put (.player p0 .hand) [3],
        put (.player p0 .trash) [4, 5], put (.player p0 .runeDeck) [6, 7],
        put (.player p1 .mainDeck) [8] ]
    points := {}
    nextId := 9
    nextTimestamp := 9
    pending := []
    turnOrder := []
    phase := .setup
    turn := 0
    active := none
    result := none }

meta def ids (l : List Nat) : List ObjId := l.map (⟨·⟩)

meta def z (p : PlayerId) (k : ZoneKind) (s : GameState) : List Nat :=
  (s.zone (.player p k)).map (·.n)

-- draw: the top card goes to the hand, under a new identifier (CR 414, 124)
#guard match drawOne s0 p0 with
  | some (s, _) => z p0 .mainDeck s == [1, 2] && z p0 .hand s == [9, 3] && s.nextId == 10
  | none => false
-- the drawn card's attributes: a fresh object, not exhausted, same physical card
#guard match drawOne s0 p0 with
  | some (s, _) => match s.obj? ⟨9⟩ with
      | some o => o.kind.phys? == some ⟨0⟩ && o.owner == p0 && o.timestamp.n == 9
      | none => false
  | none => false
-- the old identifier is gone
#guard match drawOne s0 p0 with
  | some (s, _) => (s.obj? ⟨0⟩).isNone
  | none => false
-- an empty Main Deck cannot be drawn from (it is a Burn Out, CR 432)
#guard (drawOne { s0 with zones := s0.zones.insert (Zone.player p0 .mainDeck).key [] } p0).isNone

-- channel: the top Rune goes to the Base, ready (CR 431)
#guard match channelOne s0 p0 with
  | some (s, _) => z p0 .runeDeck s == [7] && z p0 .base s == [9]
  | none => false
-- channeling more Runes than there are never fails (CR 431.3)
#guard (let r := channel p0 5 s0; z p0 .runeDeck r.1 == [] && (z p0 .base r.1).length == 2)
#guard (let r := channel p0 0 s0; r.1 == s0)

-- Burn Out: the Trash goes to the bottom in the given order; the opponent gains 1 (CR 432.2)
#guard match burnOut s0 p0 (ids [5, 4]) p1 with
  | some (s, _) => z p0 .trash s == [] && (z p0 .mainDeck s).length == 5 &&
      s.pointsOf p1 == 1 && s.pointsOf p0 == 0
  | none => false
-- the order must be an arrangement of the Trash; the opponent must be another player
#guard (burnOut s0 p0 (ids [4]) p1).isNone
#guard (burnOut s0 p0 (ids [4, 5]) p0).isNone
#guard (burnOut s0 p0 (ids [4, 5]) ⟨7⟩).isNone

-- CR 056: an object never enters the Non-Board zone of a player who does not own it
#guard match moveObj s0 ⟨3⟩ (.player p1 .trash) with
  | some (s, _) => z p0 .trash s == [9, 4, 5] && z p1 .trash s == []
  | none => false
-- a move between two Board zones keeps the object (CR 124): Base to Battlefield Zone
#guard match channelOne s0 p0 with
  | some (s, _) => match moveObj s ⟨9⟩ .battlefieldZone with
      | some (s', id') => id' == ⟨9⟩ && s'.zone .battlefieldZone == [⟨9⟩]
      | none => false
  | none => false
-- an unknown object, and a move to where it already is
#guard (moveObj s0 ⟨99⟩ (.player p0 .hand)).isNone
#guard (moveObj s0 ⟨3⟩ (.player p0 .hand)).isNone

end RiftboundTest
