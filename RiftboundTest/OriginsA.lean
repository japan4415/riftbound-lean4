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

-- Rebuke cannot take a unit on a base
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-172" .hand
  let (s2, u) ← put s1 s.you "OGN-001" .base
  return (play s2 s.me c [u]).isNone

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
-- 3 Might is "3 or less"; a buff makes it 4 (CR 701)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-169" .hand
  let (s2, u) ← putAt s1 s.you "OGN-132" s.bf0
  let s3 ← play s2 s.me c [u]
  return s3.countIn s.you .hand "OGN-132" == 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-169" .hand
  let (s2, u) ← putAt s1 s.you "OGN-132" s.bf0
  let s3 := s2.modObj u (fun o => { o with buffed := true })
  return (play s3 s.me c [u]).isNone

-- Retreat (OGN-104): a friendly unit returns to its owner's hand, who channels 1 rune exhausted
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-104" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let s3 ← play s2 s.me c [u]
  return s3.countIn s.me .hand "OGN-051" == 1 &&
    (s3.zone (.player s.me .runeDeck)).length + 1 == (s2.zone (.player s.me .runeDeck)).length &&
    (s3.zone (.player s.me .base)).length == (s2.zone (.player s.me .base)).length &&
    -- the rune that came is exhausted
    ((s3.zone (.player s.me .base)).filter (fun r => (s2.zone (.player s.me .base)).all (· != r) &&
      (s3.cardDef? r).any (·.hasType .rune)) |>.all (fun r => s3.tired r == some true)) &&
    ((s3.zone (.player s.me .base)).filter (fun r => (s2.zone (.player s.me .base)).all (· != r) &&
      (s3.cardDef? r).any (·.hasType .rune))).length == 1

-- Retreat takes a friendly unit only
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-104" .hand
  let (s2, u) ← put s1 s.you "OGN-001" .base
  return (play s2 s.me c [u]).isNone

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
  let s3 ← play s2 s.me c [] ({ pick := fun ts => ts.contains v } : Says)
  return (s3.obj? v).map (·.stunned) == some true

-- First Mate (OGN-132): when played, ready another unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-132" .hand
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let s2 := s2.tire v
  let s3 ← play s2 s.me c [] ({ pick := fun ts => ts.contains v } : Says)
  return (s2.obj? v).map (·.exhausted) == some true && (s3.obj? v).map (·.exhausted) == some false

-- "another unit": the ability may pick any other unit, friendly or not, but not First Mate itself
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-132" .hand
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let (s3, e) ← put s2 s.you "OGN-001" .base
  let s4 ← castStop s3 s.me c
  let me ← s4.firstOf s.me .base "OGN-132"
  return s4.trigPicks.contains v && s4.trigPicks.contains e && !s4.trigPicks.contains me

-- Pit Rookie (OGN-136): when played, buff another friendly unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-136" .hand
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let s3 ← play s2 s.me c [] ({ pick := fun ts => ts.contains v } : Says)
  return (s3.obj? v).map (·.buffed) == some true

-- "another friendly unit": only a friendly unit, not Pit Rookie itself
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-136" .hand
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let (s3, e) ← put s2 s.you "OGN-001" .base
  let s4 ← castStop s3 s.me c
  let me ← s4.firstOf s.me .base "OGN-136"
  return s4.trigPicks.contains v && !s4.trigPicks.contains e && !s4.trigPicks.contains me

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
    s5.countIn s.you .trash "OGN-017" == 1 && s5.obj? g == none && s5.obj? h == none &&
    s5.obj? u != none

-- Wizened Elder (OGN-065): while buffed, an additional +1 Might (the buff itself is +1)
#guard t fun s => do
  let (s1, u) ← put s s.me "OGN-065" .base
  let s2 := s1.buff u
  return s2.mightNow u == (s1.mightNow u).map (· + 2)

-- Sett (OGN-240): +1 Might for each buffed friendly unit at my battlefield (itself included)
#guard t fun s => do
  let (s1, u) ← putAt s s.me "OGN-240" s.bf0
  let (s2, v) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let one := s3.buff v
  let two := one.buff u
  let enemy := two.buff e
  return one.mightNow u == (s3.mightNow u).map (· + 1) &&
    two.mightNow u == (s3.mightNow u).map (· + 3) &&
    -- a buffed enemy unit is not counted
    enemy.mightNow u == two.mightNow u

-- Lee Sin (OGN-151): other buffed friendly units at my battlefield have +2 Might
#guard t fun s => do
  let (s1, u) ← putAt s s.me "OGN-151" s.bf0
  let (s2, v) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, w) ← putAt s2 s.me "OGN-051" s.bf0
  let (s4, e) ← putAt s3 s.you "OGN-001" s.bf0
  let b := (s4.buff v).buff e
  return b.mightNow v == (s4.mightNow v).map (· + 3) && b.mightNow w == s4.mightNow w &&
    b.mightNow e == (s4.mightNow e).map (· + 1) && b.mightNow u == s4.mightNow u

-- Arena Bar (OGN-124): exhaust it to buff an exhausted friendly unit
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-124" .base
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let (s3, w) ← put s2 s.me "OGN-051" .base
  let s4 := s3.tire v
  let s5 ← activate s4 s.me g 0 [v]
  return (s5.obj? v).map (·.buffed) == some true && s5.tired g == some true &&
    (s5.obj? w).map (·.buffed) == some false && (activate s4 s.me g 0 [w]).isNone

-- Cithria of Cloudfield (OGN-139): when you play another unit, buff Cithria; not for itself
#guard t fun s => do
  let (s1, u) ← put s s.me "OGN-139" .base
  let (s2, c) ← put s1 s.me "V0" .hand
  let s3 ← play s2 s.me c
  return (s3.obj? u).map (·.buffed) == some true
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-139" .hand
  let s2 ← play s1 s.me c
  let u ← s2.firstOf s.me .base "OGN-139"
  return (s2.obj? u).map (·.buffed) == some false

-- Peak Guardian (OGN-223): when played, buff itself
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-223" .hand
  let s2 ← play s1 s.me c
  let u ← s2.firstOf s.me .base "OGN-223"
  return (s2.obj? u).map (·.buffed) == some true

-- Cithria reacts to units only, and only to the plays of its player's side
#guard t fun s => do
  let (s1, u) ← put s s.me "OGN-139" .base
  let (s2, c) ← put s1 s.me "SP0" .hand
  let s3 ← play s2 s.me c
  return (s3.obj? u).map (·.buffed) == some false
#guard t fun s => do
  let (s1, u) ← put s s.me "OGN-139" .base
  let (s2, e) ← put s1 s.you "V0" .base
  return (watchersOf s2 e s.you .play).isEmpty && (watchersOf s2 e s.me .play).length == 1 &&
    (s2.obj? u).isSome

-- Lee Sin gives himself nothing (he has the buff only); Sett on a base counts nobody
#guard t fun s => do
  let (s1, u) ← putAt s s.me "OGN-151" s.bf0
  let s2 := s1.buff u
  return s2.mightNow u == (s1.mightNow u).map (· + 1)
#guard t fun s => do
  let (s1, u) ← put s s.me "OGN-240" .base
  let (s2, v) ← putAt s1 s.me "OGN-001" s.bf0
  let s3 := s2.buff v
  return s3.mightNow u == s1.mightNow u

-- Peak Guardian at a battlefield: it buffs itself and the other friendly units there (the
-- ability is put on the stack by hand: a unit cannot be played to a battlefield yet)
#guard t fun s => do
  let (s1, g) ← putAt s s.me "OGN-223" s.bf0
  let (s2, v) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, w) ← put s2 s.me "OGN-001" .base
  let (s4, e) ← putAt s3 s.you "OGN-001" s.bf0
  let pend := detectOne s4 (.played s.me g)
  let s5 := { s4 with pending := .triggers pend :: s4.pending }
  let s6 := settleChain {} 12 (← (advance 100 s5 []).toOption).1
  return pend.length == 1 && (s6.obj? g).map (·.buffed) == some true &&
    (s6.obj? v).map (·.buffed) == some true && (s6.obj? w).map (·.buffed) == some false &&
    (s6.obj? e).map (·.buffed) == some false

-- Salvage (OGN-224): you may kill a gear (you choose which when there are two), then draw 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-224" .hand
  let (s2, g) ← put s1 s.me "OGN-017" .base
  let (s3, h) ← put s2 s.you "OGN-017" .base
  let s4 ← play s3 s.me c [] ({ obj := fun o => o == g } : Says)
  return s4.countIn s.me .base "OGN-017" == 0 && s4.countIn s.you .base "OGN-017" == 1 &&
    s4.countIn s.me .trash "OGN-017" == 1 && s4.handN s.me == s3.handN s.me && s4.obj? h != none
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-224" .hand
  let (s2, g) ← put s1 s.me "OGN-017" .base
  let s3 ← play s2 s.me c [] ({ yes := false } : Says)
  return s3.countIn s.me .base "OGN-017" == 1 && s3.handN s.me == s2.handN s.me &&
    s3.obj? g != none
-- one gear only: there is nothing to choose, and the player still may decline
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-224" .hand
  let (s2, _) ← put s1 s.me "OGN-017" .base
  let s3 ← play s2 s.me c
  return s3.countIn s.me .base "OGN-017" == 0 && s3.countIn s.me .trash "OGN-017" == 1

-- Maddened Marauder (OGN-191): when played, move a unit from a battlefield to its base
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-191" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let s3 ← play s2 s.me c
  return (s3.unitsAt s.bf0).isEmpty && s3.countIn s.you .base "OGN-001" == 1 && s2.obj? u != none

-- Zaunite Bouncer (OGN-188): when played, return another unit at a battlefield to its owner's hand
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-188" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, v) ← put s2 s.you "OGN-051" .base
  let s4 ← castStop s3 s.me c
  let s5 ← play s3 s.me c
  return s4.trigPicks.contains u && !s4.trigPicks.contains v &&
    s5.countIn s.you .hand "OGN-001" == 1 && (s5.unitsAt s.bf0).isEmpty

-- Clockwork Keeper (OGN-044): draw 1 only if the additional calm Power was paid
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-044" .hand
  let s2 := s1.rich s.me
  let base := payOf s2 c
  let plain ← cast s2 s.me c base
  let extra ← cast s2 s.me c ⟨base.energy, base.power ++ [.calm]⟩
  return plain.handN s.me + 1 == s2.handN s.me && extra.handN s.me == s2.handN s.me

-- Salvage: the player chooses the enemy's gear instead; with no gear at all the player still draws
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-224" .hand
  let (s2, g) ← put s1 s.me "OGN-017" .base
  let (s3, h) ← put s2 s.you "OGN-017" .base
  let s4 ← play s3 s.me c [] ({ obj := fun o => o == h } : Says)
  return s4.countIn s.me .base "OGN-017" == 1 && s4.countIn s.you .base "OGN-017" == 0 &&
    s4.countIn s.you .trash "OGN-017" == 1 && s4.obj? g != none
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-224" .hand
  let s2 ← play s1 s.me c
  return s2.handN s.me == s1.handN s.me

-- Zaunite Bouncer may return a friendly unit too; Keeper cannot be paid with another Power
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-188" .hand
  let (s2, u) ← putAt s1 s.me "OGN-001" s.bf0
  let s3 ← castStop s2 s.me c
  return s3.trigPicks.contains u
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-044" .hand
  let s2 := s1.rich s.me
  let base := payOf s2 c
  return (cast s2 s.me c ⟨base.energy, base.power ++ [.fury]⟩).isNone

-- Cleave (OGN-004): a unit has Assault 3 this turn, and only that unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, v) ← put s1 s.me "OGN-136" .base
  let (s3, w) ← put s2 s.me "OGN-136" .base
  let s4 ← play s3 s.me c [v]
  return s4.kwAmount v .assault == 3 && s4.kwAmount w .assault == 0 &&
    s3.kwAmount v .assault == 0 &&
    (s4.mapObjects endTurnObj).kwAmount v .assault == 0

-- Smoke Screen (OGN-093) and Stupefy (OGN-095): less Might, never below 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-093" .hand
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let (s3, w) ← put s2 s.me "OGN-136" .base
  let (s4, x) ← put s3 s.me "OGN-216" .base
  let a ← play s4 s.me c [v]
  let (s5, c2) ← put s4 s.me "OGN-093" .hand
  let b ← play s5 s.me c2 [w]
  let (s6, c3) ← put s4 s.me "OGN-093" .hand
  let d ← play s6 s.me c3 [x]
  return a.mightNow v == some 1 && b.mightNow w == some 1 && d.mightNow x == some 1 &&
    a.mightNow w == some 2 && (a.mapObjects endTurnObj).mightNow v == some 5 &&
    (b.mapObjects endTurnObj).mightNow w == some 2
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-095" .hand
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let (s3, w) ← put s2 s.me "OGN-216" .base
  let a ← play s3 s.me c [v]
  let (s4, c2) ← put s3 s.me "OGN-095" .hand
  let b ← play s4 s.me c2 [w]
  -- the spell leaves the hand and one card is drawn
  return a.mightNow v == some 4 && a.handN s.me == s3.handN s.me &&
    b.mightNow w == some 1 && b.handN s.me == s4.handN s.me

-- Orb of Regret (OGN-090): exhaust it, a unit has 1 less Might this turn, to a minimum of 1
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-090" .base
  let (s2, v) ← put s1 s.me "OGN-001" .base
  let (s3, w) ← put s2 s.me "OGN-216" .base
  let a ← activate s3 s.me g 0 [v]
  let b ← activate s3 s.me g 0 [w]
  return a.mightNow v == some 4 && a.tired g == some true && b.mightNow w == some 1 &&
    (activate a s.me g 0 [v]).isNone

-- Bilgewater Bully (OGN-125): Ganking only while it is buffed
#guard t fun s => do
  let (s1, u) ← put s s.me "OGN-125" .base
  return !s1.hasKw u .ganking && (s1.buff u).hasKw u .ganking

-- Taric (OGN-074): other friendly units here have Shield 1, not those elsewhere, not the enemy's
#guard t fun s => do
  let (s1, t) ← putAt s s.me "OGN-074" s.bf0
  let (s2, v) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, w) ← put s2 s.me "OGN-136" .base
  let (s4, e) ← putAt s3 s.you "OGN-136" s.bf0
  return s4.kwAmount v .shield == 1 && s4.kwAmount w .shield == 0 && s4.kwAmount e .shield == 0 &&
    s4.kwAmount t .shield == 1

-- Captain Farron (OGN-015): other friendly units here have Assault 1
#guard t fun s => do
  let (s1, t) ← putAt s s.me "OGN-015" s.bf0
  let (s2, v) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, w) ← put s2 s.me "OGN-136" .base
  return s3.kwAmount v .assault == 1 && s3.kwAmount w .assault == 0 && s3.kwAmount t .assault == 0

end RiftboundTest
