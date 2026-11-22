module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests: Origins, first batch (scenario tests of single cards)

Each test puts the cards it needs in the lab (the Main Phase of the first turn), plays the card
for exactly its cost, lets the Chain resolve, and reads what happened. A card that goes to another
zone is a new object, so the tests look for the card by its identifier.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- Run a scenario in the lab; it must say `true`. -/
meta def t (f : GameState → Option Bool) : Bool :=
  match lab with
  | some s => (f s).getD false
  | none => false

-- Rebuke (OGN-172): a unit at a battlefield goes back to its owner's hand
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-172" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let s3 ← play s2 s.me c [u]
  return s3.countIn s.you .hand "OGN-001" == 1 && s3.where? u != some .battlefieldZone

-- Gust (OGN-169): only a unit with 3 Might or less; Blazing Scorcher has 5, Shieldbearer has 2
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-169" .hand
  let (s2, u) ← putAt s1 s.you "OGN-051" s.bf0
  let s3 ← play s2 s.me c [u]
  return s3.countIn s.you .hand "OGN-051" == 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-169" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  return (play s2 s.me c [u]).isNone

-- Retreat (OGN-104): a friendly unit returns to its owner's hand, who channels 1 rune exhausted
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-104" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let s3 ← play s2 s.me c [u]
  return s3.countIn s.me .hand "OGN-051" == 1 &&
    (s3.zone (.player s.me .runeDeck)).length + 1 == (s2.zone (.player s.me .runeDeck)).length &&
    (s3.zone (.player s.me .base)).length == (s2.zone (.player s.me .base)).length

-- Rune Prison (OGN-050): the unit is stunned
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-050" .hand
  let (s2, u) ← put s1 s.you "OGN-001" .base
  let s3 ← play s2 s.me c [u]
  return (s3.obj? u).map (·.stunned) == some true

-- Solari Shieldbearer (OGN-051): when played, stun a unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-051" .hand
  let (s2, v) ← put s1 s.you "OGN-001" .base
  let s3 ← play s2 s.me c [] (pick := fun ts => ts.contains v)
  return (s3.obj? v).map (·.stunned) == some true

-- First Mate (OGN-132): when played, ready another unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-132" .hand
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let s2 := s2.tire v
  let s3 ← play s2 s.me c [] (pick := fun ts => ts.contains v)
  return (s2.obj? v).map (·.exhausted) == some true && (s3.obj? v).map (·.exhausted) == some false

-- Pit Rookie (OGN-136): when played, buff another friendly unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-136" .hand
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let s3 ← play s2 s.me c [] (pick := fun ts => ts.contains v)
  return (s3.obj? v).map (·.buffed) == some true

-- Grand Strategem (OGN-233): friendly units get +5 Might this turn, enemy units do not
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-233" .hand
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let (s3, w) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-001" .base
  let s5 ← play s4 s.me c
  return s5.mightNow v == (s4.mightNow v).map (· + 5) &&
    s5.mightNow w == (s4.mightNow w).map (· + 5) && s5.mightNow e == s4.mightNow e

-- Unchecked Power (OGN-123): friendly units are exhausted, units at battlefields take 12
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-123" .hand
  let (s2, home) ← put s1 s.me "OGN-001" .base
  let (s3, mine) ← putAt s2 s.me "OGN-001" s.bf0
  let (s4, theirs) ← putAt s3 s.you "OGN-001" s.bf0
  let s5 ← play s4 s.me c
  return (s5.obj? home).map (·.exhausted) == some true &&
    (s5.obj? home).map (·.damage) == some 0 &&
    (s5.unitsAt s.bf0).isEmpty && (s4.unitsAt s.bf0).length == 2 &&
    s5.obj? mine == none && s5.obj? theirs == none

-- Flurry of Blades (OGN-133): 1 damage to all units at battlefields
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-133" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, home) ← put s2 s.you "OGN-001" .base
  let s4 ← play s3 s.me c
  return (s4.obj? u).map (·.damage) == some 1 && (s4.obj? home).map (·.damage) == some 0

-- Thermo Beam (OGN-022): all gear are killed
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-022" .hand
  let (s2, g) ← put s1 s.me "OGN-017" .base
  let (s3, h) ← put s2 s.you "OGN-017" .base
  let (s4, u) ← put s3 s.me "OGN-001" .base
  let s5 ← play s4 s.me c
  return s5.countIn s.me .base "OGN-017" == 0 && s5.countIn s.you .base "OGN-017" == 0 &&
    s5.countIn s.me .trash "OGN-017" == 1 && s5.countIn s.me .base "OGN-001" == 1 &&
    s5.obj? g == none && s5.obj? h == none && s4.obj? u != none

end RiftboundTest
