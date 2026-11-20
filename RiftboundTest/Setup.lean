module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: the setup of a game and the engine (CR 110-118, design.md §6)

Two players with the fixture deck. The setup is run through `step`, with the driver answering
the chance decisions from a seed.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def cfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

meta def start : Option GameState := GameState.initial cfg [goodDeck, goodDeck]

meta def count (p : PlayerId) (k : ZoneKind) (s : GameState) : Nat := (s.zone (.player p k)).length

meta def finished (seed : Nat) : Option GameState :=
  match start with
  | none => none
  | some s => match runAuto 100 200 (Rng.ofSeed seed) s with
      | .ok s => some s
      | .error _ => none

meta def p0 : PlayerId := ⟨0⟩
meta def p1 : PlayerId := ⟨1⟩

-- the starting layout (CR 111-113): 56 objects per player
#guard match start with
  | some s => count p0 .legendZone s == 1 && count p0 .championZone s == 1 &&
      count p0 .mainDeck s == 39 && count p0 .runeDeck s == 12 && count p0 .outOfGame s == 3 &&
      count p1 .mainDeck s == 39 && s.nextId == 112 && s.pending.length == 8
  | none => false
-- the number of decks must be the number of players
#guard (GameState.initial cfg [goodDeck]).isNone

-- after the setup, for several seeds: every question is answered, and
#guard (List.range 8).all fun seed => match finished seed with
  | some s =>
    s.pending.isEmpty &&
    -- opening hands of 4 (CR 116)
    count p0 .hand s == 4 && count p1 .hand s == 4 &&
    -- the decks are the rest
    count p0 .mainDeck s == 35 && count p1 .mainDeck s == 35 &&
    count p0 .runeDeck s == 12 &&
    -- one Battlefield each in play (CR 113, 487.5), the other two out of the game
    (s.zone .battlefieldZone).length == 2 && count p0 .outOfGame s == 2 &&
    count p1 .outOfGame s == 2 &&
    -- the turn order is a permutation of the players
    s.turnOrder.length == 2 && s.turnOrder.contains p0 && s.turnOrder.contains p1
  | none => false

-- the same seed gives the same game (replay, design.md §6.4)
#guard finished 5 == finished 5
-- different seeds can give different orders of the deck
#guard (finished 1).map (fun s => s.zone (.player p0 .mainDeck)) !=
  (finished 2).map (fun s => s.zone (.player p0 .mainDeck))

-- the physical cards are conserved from the start to the end (I1): the same multiset of cards
#guard match start, finished 3 with
  | some s0, some s1 =>
    ((s0.zoneIds.filterMap (fun id => (s0.obj? id).bind (·.kind.phys?))).map (·.n)).mergeSort ==
      ((s1.zoneIds.filterMap (fun id => (s1.obj? id).bind (·.kind.phys?))).map (·.n)).mergeSort &&
    s1.zoneIds.length == s0.zoneIds.length
  | _, _ => false

-- the legal answers at the first mulligan
meta def atMulligan : Option GameState :=
  match start with
  | none => none
  | some s =>
    -- run the chance decisions, stop when a player must decide
    let rec go (n : Nat) (r : Rng) (s : GameState) : Option GameState :=
      match n with
      | 0 => none
      | n + 1 =>
        match s.pending with
        | .mulligan _ _ :: _ => some s
        | _ => match autoAnswer r s with
          | some (a, r') => match step 100 s a with
            | .ok (s', _) => go n r' s'
            | .error _ => none
          | none => none
    go 100 (Rng.ofSeed 7) s

#guard match atMulligan with
  | some s =>
    -- four hand cards may be set aside, or the player may finish
    (legalActions s).length == 5 &&
    (legalActions s).all (fun a => a.actor.isPlayer) &&
    -- each listed answer is legal, and a chance answer is not
    (legalActions s).all (fun a => decide (Legal s a)) &&
    !decide (Legal s ⟨.chance, .mulliganDone⟩)
  | none => false

-- a mulligan of two cards: they are set aside, two are drawn, the two go to the bottom
#guard match atMulligan with
  | some s =>
    match s.pending with
    | .mulligan p _ :: _ =>
      let hand := s.zone (.player p .hand)
      match hand with
      | c1 :: c2 :: _ =>
        match step 100 s ⟨.player p, .mulliganPick c1⟩ with
        | .ok (s1, _) => match step 100 s1 ⟨.player p, .mulliganPick c2⟩ with
          | .ok (s2, _) =>
            -- a third pick is refused, finishing is allowed
            (match step 100 s2 ⟨.player p, .mulliganPick (hand.getD 2 c1)⟩ with
              | .error .illegal => true | _ => false) &&
            (match step 100 s2 ⟨.player p, .mulliganDone⟩ with
              | .ok (s3, _) =>
                -- a chance decision comes next: the order of the two set-aside cards
                (match s3.pending with
                  | .chanceRecycle q cards :: _ => q == p && cards.length == 2
                  | _ => false) &&
                count p .hand s3 == 4 && count p .setAside s3 == 2 &&
                count p .mainDeck s3 == count p .mainDeck s - 2
              | .error _ => false)
          | .error _ => false
        | .error _ => false
      | _ => false
    | _ => false
  | none => false

-- illegal answers are refused
#guard match start with
  | some s => (match step 100 s ⟨.player p0, .mulliganDone⟩ with
      | .error .illegal => true | _ => false) &&
    -- an arrangement that is not a permutation of the zone
    (match step 100 s ⟨.chance, .arrange []⟩ with
      | .error .illegal => true | _ => false)
  | none => false

-- fuel (design.md §6.1): too little fuel stops the work between the turn order and the hands
#guard match start with
  | some s => (match runAuto 0 200 (Rng.ofSeed 1) s with
      | .error .fuelExhausted => true | _ => false) &&
    (match runAuto 1 200 (Rng.ofSeed 1) s with
      | .error .fuelExhausted => true | _ => false) &&
    -- the opening draws and mulligan frames need 1 + 2 * 5 steps; with more fuel they run
    (match runAuto 11 200 (Rng.ofSeed 1) s with
      | .ok s' => s'.pending.isEmpty | _ => false)
  | none => false

end RiftboundTest
