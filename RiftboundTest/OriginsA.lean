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

-- the floor reads the Might the rules read: a passive bonus counts (Lee Sin gives +2 to a buffed
-- unit here), and a unit already below the floor is not changed
#guard t fun s => do
  let (s1, _) ← putAt s s.me "OGN-151" s.bf0
  let (s2, v) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, c) ← put s2 s.me "OGN-093" .hand
  let s4 := s3.buff v
  let a ← play s4 s.me c [v]
  return s4.mightNow v == some 5 && a.mightNow v == some 1
#guard t fun s => do
  let (s1, v) ← put s s.me "OGN-001" .base
  let (s2, c) ← put s1 s.me "OGN-093" .hand
  let (s3, c2) ← put s2 s.me "OGN-093" .hand
  let a ← play s3 s.me c [v]
  let b ← play a s.me c2 [v]
  return a.mightNow v == some 1 && b.mightNow v == some 1

-- the keywords count in combat, and a unit that leaves play loses them
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, v) ← putAt s1 s.me "OGN-136" s.bf0
  let a ← play s2 s.me c [v]
  return a.combatMight v true == s2.combatMight v true + 3 &&
    a.combatMight v false == s2.combatMight v false
#guard t fun s => do
  let (s1, v) ← putAt s s.me "OGN-136" s.bf0
  let (s2, _) ← putAt s1 s.me "OGN-074" s.bf0
  return s2.combatMight v false == s1.combatMight v false + 1 &&
    s2.combatMight v true == s1.combatMight v true
-- a Taric in the hand gives nothing
#guard t fun s => do
  let (s1, v) ← putAt s s.me "OGN-136" s.bf0
  let (s2, _) ← put s1 s.me "OGN-074" .hand
  return s2.kwAmount v .shield == 0

-- Leona (OGN-238) stuns an enemy unit here when she attacks, not one elsewhere
#guard t fun s => do
  let (s1, l) ← putAt s s.me "OGN-238" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-136" s.bf0
  let (s3, f) ← put s2 s.you "OGN-136" .base
  let a ← fire s3 [.combatStarted s.bf0 s.me]
  let b ← fire s3 [.combatStarted s.bf0 s.you]
  return (a.obj? e).map (·.stunned) == some true && (a.obj? f).map (·.stunned) == some false &&
    (a.obj? l).map (·.stunned) == some false && (b.obj? e).map (·.stunned) == some false

-- Ahri (OGN-119): -2 Might to an enemy unit here, to a minimum of 1, when she attacks or defends
#guard t fun s => do
  let (s1, _) ← putAt s s.me "OGN-119" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, f) ← putAt s2 s.you "OGN-136" s.bf0
  let a ← fire s3 [.combatStarted s.bf0 s.me] { pick := fun ts => ts.contains e }
  let b ← fire s3 [.combatStarted s.bf0 s.you] { pick := fun ts => ts.contains f }
  return a.mightNow e == (s3.mightNow e).map (· - 2) && a.mightNow f == s3.mightNow f &&
    b.mightNow f == some 1 && b.mightNow e == s3.mightNow e

-- Anivia (OGN-148): 3 damage to every enemy unit here when she attacks
#guard t fun s => do
  let (s1, v) ← putAt s s.me "OGN-148" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, f) ← put s2 s.you "OGN-001" .base
  let (s4, w) ← putAt s3 s.me "OGN-001" s.bf0
  let a ← fire s4 [.combatStarted s.bf0 s.me]
  let b ← fire s4 [.combatStarted s.bf0 s.you]
  return (a.obj? e).map (·.damage) == some 3 && (a.obj? f).map (·.damage) == some 0 &&
    (a.obj? w).map (·.damage) == some 0 && (a.obj? v).map (·.damage) == some 0 &&
    (b.obj? e).map (·.damage) == some 0

-- Yasuo (OGN-076): damage equal to his Might to an enemy unit here when he attacks
#guard t fun s => do
  let (s1, y) ← putAt s s.me "OGN-076" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-116" s.bf0
  let a ← fire s2 [.combatStarted s.bf0 s.me]
  let s3 := s2.modObj y (fun o => { o with mightMods := [⟨-2, .turn⟩] })
  let b ← fire s3 [.combatStarted s.bf0 s.me]
  return (a.obj? e).map (·.damage) == (s2.mightNow y).map Int.toNat && (s2.mightNow y).isSome &&
    (b.obj? e).map (·.damage) == some 4

-- Dune Drake (OGN-131): +2 Might when it attacks, only if a ready enemy unit is here
#guard t fun s => do
  let (s1, d) ← putAt s s.me "OGN-131" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-136" s.bf0
  let a ← fire s2 [.combatStarted s.bf0 s.me]
  let b ← fire (s2.tire e) [.combatStarted s.bf0 s.me]
  return a.mightNow d == (s2.mightNow d).map (· + 2) && b.mightNow d == s2.mightNow d

-- Grove of the God-Willow (OGN-280), Zaun Warrens (OGN-298): the holder draws, the conqueror
-- discards and draws
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-280"
  let a ← fire s1 [.scored s.me bf false]
  return a.handN s.me == s1.handN s.me + 1 && a.handN s.you == s1.handN s.you
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let a ← fire s1 [.scored s.me bf true]
  let b ← fire s1 [.scored s.me bf false]
  return a.handN s.me == s1.handN s.me && (a.zone (.player s.me .trash)).length ==
    (s1.zone (.player s.me .trash)).length + 1 && b.handN s.me == s1.handN s.me

-- Altar to Unity (OGN-275): a Recruit token comes to my base when I hold here
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let a ← fire s1 [.scored s.me bf false]
  let b ← fire s1 [.scored s.me bf true]
  let tk ← a.firstOf s.me .base "TKN-Recruit" <|> (a.zone (.player s.me .base)).find? (fun u =>
    (a.cardDef? u).any (·.name == "Recruit"))
  return a.countNamed s.me .base "Recruit" == 1 && b.countNamed s.me .base "Recruit" == 0 &&
    a.tired tk == some true

-- Navori Fighting Pit (OGN-283): buff a unit here when I hold
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-283"
  let (s2, u) ← putAt s1 s.me "OGN-136" bf
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let a ← fire s3 [.scored s.me bf false]
  return (a.obj? u).map (·.buffed) == some true && (a.obj? v).map (·.buffed) == some false

-- Startipped Peak (OGN-288): I may channel a rune exhausted when I hold
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-288"
  let a ← fire s1 [.scored s.me bf false]
  let b ← fire s1 [.scored s.me bf false] { yes := false }
  let runes (x : GameState) := (x.zone (.player s.me .runeDeck)).length
  return runes a + 1 == runes s1 && runes b == runes s1

-- Trifarian War Camp (OGN-294), Windswept Hillock (OGN-297): every unit here
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-294"
  let (s2, u) ← putAt s1 s.me "OGN-136" bf
  let (s3, v) ← putAt s2 s.you "OGN-136" bf
  let (s4, w) ← put s3 s.me "OGN-136" .base
  return s4.mightNow u == some 3 && s4.mightNow v == some 3 && s4.mightNow w == some 2
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-297"
  let (s2, u) ← putAt s1 s.me "OGN-136" bf
  let (s3, v) ← putAt s2 s.you "OGN-136" bf
  let (s4, w) ← put s3 s.me "OGN-136" .base
  return s4.hasKw u .ganking && s4.hasKw v .ganking && !s4.hasKw w .ganking

-- Darius (OGN-243): other friendly units here have +1 Might; Legion readies him
#guard t fun s => do
  let (s1, d) ← putAt s s.me "OGN-243" s.bf0
  let (s2, u) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-136" s.bf0
  return s3.mightNow u == some 3 && s3.mightNow e == some 2 && s3.mightNow d == (s2.mightNow d)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-243" .hand
  let (s2, k) ← put s1 s.me "OGN-058" .hand
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let a ← play s3 s.me c
  let b ← play (← play s3 s.me k [v]) s.me c
  let da ← a.firstOf s.me .base "OGN-243"
  let db ← b.firstOf s.me .base "OGN-243"
  return a.tired da == some true && b.tired db == some false

-- Block (OGN-057): a unit has Shield 3 and Tank this turn
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-057" .hand
  let (s2, v) ← put s1 s.me "OGN-136" .base
  let (s3, w) ← put s2 s.me "OGN-136" .base
  let a ← play s3 s.me c [v]
  return a.kwAmount v .shield == 3 && a.hasKw v .tank && !a.hasKw w .tank &&
    a.kwAmount w .shield == 0 && !(a.mapObjects endTurnObj).hasKw v .tank

-- Blastcone Fae (OGN-097) and Teemo (OGN-197): when played
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-097" .hand
  let (s2, e) ← put s1 s.you "OGN-001" .base
  let (s3, f) ← put s2 s.you "OGN-136" .base
  let a ← play s3 s.me c [] { pick := fun ts => ts.contains e }
  let b ← play s3 s.me c [] { pick := fun ts => ts.contains f }
  return a.mightNow e == some 3 && a.mightNow f == some 2 && b.mightNow f == some 1 &&
    b.mightNow e == some 5
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-197" .hand
  let a ← play s1 s.me c
  let t ← a.firstOf s.me .base "OGN-197"
  return a.mightNow t == some 4 && (a.mapObjects endTurnObj).mightNow t == some 1

-- Fight or Flight (OGN-168): a unit at a battlefield goes to its base; one at a base cannot
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-168" .hand
  let (s2, u) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, w) ← put s2 s.me "OGN-136" .base
  let a ← play s3 s.me c [u]
  return (s3.obj? u).bind (·.loc) == some s.bf0 && (a.obj? u).map (·.loc) == some none &&
    (play s3 s.me c [w]).isNone

-- Iron Ballista (OGN-017): enters exhausted; exhaust it to deal 2 to a unit at a battlefield
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-017" .hand
  let (s2, e) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, f) ← put s2 s.you "OGN-136" .base
  let a ← play s1 s.me c
  let g ← a.firstOf s.me .base "OGN-017"
  let b := s3.rich s.me
  let (b1, g2) ← put b s.me "OGN-017" .base
  let x ← activate b1 s.me g2 1 [e]
  return a.tired g == some true && (activate a s.me g 1 [e]).isNone &&
    (x.obj? e).map (·.damage) == some 2 && x.tired g2 == some true &&
    (activate b1 s.me g2 1 [f]).isNone

-- Ravenbloom Student (OGN-103) and Pit Crew (OGN-091): when I play a spell, a gear
#guard t fun s => do
  let (s1, r) ← put s s.me "OGN-103" .base
  let (s2, c) ← put s1 s.me "OGN-004" .hand
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let (s4, d) ← put s3 s.me "OGN-136" .hand
  let a ← play s4 s.me c [v]
  let b ← play s4 s.me d
  return a.mightNow r == (s4.mightNow r).map (· + 1) && b.mightNow r == s4.mightNow r
#guard t fun s => do
  let (s1, p) ← put s s.me "OGN-091" .base
  let (s2, g) ← put s1 s.me "OGN-124" .hand
  let (s3, d) ← put s2 s.me "OGN-136" .hand
  let a ← play (s3.tire p) s.me g
  let b ← play (s3.tire p) s.me d
  return a.tired p == some false && b.tired p == some true

-- Viktor (OGN-117): a Recruit token comes to my base when I play a card on an opponent's turn
#guard t fun s => do
  let (s1, _) ← put s s.you "OGN-117" .base
  let (s2, x) ← put s1 s.you "OGN-136" .base
  let (s3, _) ← put s2 s.me "OGN-117" .base
  let (s4, y) ← put s3 s.me "OGN-136" .base
  let a ← fire s4 [.played s.you x]
  let b ← fire s4 [.played s.me y]
  return a.countNamed s.you .base "Recruit" == 1 && a.countNamed s.me .base "Recruit" == 0 &&
    b.countNamed s.me .base "Recruit" == 0 && b.countNamed s.you .base "Recruit" == 0

-- Noxian Drummer (OGN-222): a Recruit token comes here when it moves to a battlefield
#guard t fun s => do
  let (s1, d) ← putAt s s.me "OGN-222" s.bf0
  let (s2, e) ← put s1 s.me "OGN-222" .base
  let recruits (x : GameState) := (x.zone .battlefieldZone).filter (fun o =>
    (x.cardDef? o).any (·.name == "Recruit")) |>.length
  let a ← fire s2 [.standardMoved d (some s.bf0)]
  let b ← fire s2 [.standardMoved e none]
  return recruits a == 1 && recruits b == 0 && recruits s2 == 0

-- Bounty Hunter (OGN-267), a Legend: exhaust it, a unit has Ganking this turn
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-267" .legendZone
  let (s2, v) ← put s1 s.me "OGN-136" .base
  let a ← activate s2 s.me g 0 [v]
  return !s2.hasKw v .ganking && a.hasKw v .ganking && a.tired g == some true &&
    (activate a s.me g 0 [v]).isNone

-- a Battlefield trigger with a condition asks it for the player who holds, not for the owner:
-- The Grand Plaza (OGN-293) wins for the holder with seven units here
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-293"
  let seven (p : PlayerId) (x : GameState) : Option GameState :=
    (List.range 7).foldl (fun acc _ => acc.bind fun y => (putAt y p "OGN-136" bf).map (·.1))
      (some x)
  let a ← seven s.you s1
  let b ← seven s.me s1
  return (a.detect [.scored s.you bf false]).length == 1 &&
    (a.detect [.scored s.me bf false]).isEmpty &&
    (b.detect [.scored s.me bf false]).length == 1 && (b.detect [.scored s.you bf false]).isEmpty

-- Poro Herder (OGN-061): with a Poro, it buffs itself and I draw 1; without one, nothing
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-061" .hand
  let (s2, _) ← put s1 s.me "OGN-013" .base
  let a ← play s2 s.me c
  let b ← play s1 s.me c
  let ha ← a.firstOf s.me .base "OGN-061"
  let hb ← b.firstOf s.me .base "OGN-061"
  return (a.obj? ha).map (·.buffed) == some true && a.handN s.me == s2.handN s.me &&
    (b.obj? hb).map (·.buffed) == some false && b.handN s.me == s1.handN s.me - 1

-- Solari Chief (OGN-225): an enemy unit is stunned, or killed if it already is
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-225" .hand
  let (s2, e) ← put s1 s.you "OGN-001" .base
  let a ← play s2 s.me c [] { pick := fun ts => ts.contains e }
  let (t1, e2) ← put s1 s.you "OGN-001" .base
  let t2 := t1.modObj e2 (fun o => { o with stunned := true })
  let b ← play t2 s.me c [] { pick := fun ts => ts.contains e2 }
  return (a.obj? e).map (·.stunned) == some true && a.countIn s.you .trash "OGN-001" == 0 &&
    (b.obj? e2).isNone && b.countIn s.you .trash "OGN-001" == 1

-- Last Breath (OGN-260), Challenge (OGN-128), Carnivorous Snapvine (OGN-149): damage by Might
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-260" .hand
  let (s2, f) ← put s1 s.me "OGN-001" .base
  let (s3, e) ← putAt s2 s.you "OGN-116" s.bf0
  let (s4, g) ← put s3 s.you "OGN-116" .base
  let a ← play (s4.tire f) s.me c [f, e]
  return a.tired f == some false && (a.obj? e).map (·.damage) == some 5 &&
    (a.obj? g).map (·.damage) == some 0 && (a.obj? f).map (·.damage) == some 0 &&
    (play s4 s.me c [f, g]).isNone
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-128" .hand
  let (s2, f) ← put s1 s.me "OGN-001" .base
  let (s3, e) ← put s2 s.you "OGN-116" .base
  let a ← play s3 s.me c [f, e]
  -- each deals its Might to the other; the friendly unit (Might 5) takes 7 and dies
  return (a.obj? e).map (·.damage) == some 5 && (a.obj? f).isNone &&
    (play s3 s.me c [e, f]).isNone
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-149" .hand
  let (s2, e) ← putAt s1 s.you "OGN-116" s.bf0
  let (s3, g) ← put s2 s.you "OGN-116" .base
  let a ← play s3 s.me c [] { pick := fun ts => ts.contains e }
  -- each deals its Might to the other; Snapvine (Might 6) takes 7 and dies
  return (a.obj? e).map (·.damage) == (s3.mightNow c).map Int.toNat && (s3.mightNow c) == some 6 &&
    a.countIn s.me .trash "OGN-149" == 1 && (a.obj? g).map (·.damage) == some 0

-- Challenge: the damage is each unit's Might (the survivor shows it), and two units of Might 5
-- kill each other
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-128" .hand
  let (s2, f) ← put s1 s.me "OGN-116" .base
  let (s3, e) ← put s2 s.you "OGN-001" .base
  let a ← play s3 s.me c [f, e]
  let (t1, d) ← put s1 s.me "OGN-001" .base
  let (t2, g) ← put t1 s.you "OGN-001" .base
  let b ← play t2 s.me c [d, g]
  return (a.obj? f).map (·.damage) == some 5 && (a.obj? e).isNone &&
    (b.obj? d).isNone && (b.obj? g).isNone

-- Poro Herder: a unit that is not a Poro, or a Poro of the opponent, is not enough
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-061" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let (s3, _) ← put s1 s.you "OGN-013" .base
  let a ← play s2 s.me c
  let b ← play s3 s.me c
  let ha ← a.firstOf s.me .base "OGN-061"
  let hb ← b.firstOf s.me .base "OGN-061"
  return (a.obj? ha).map (·.buffed) == some false && a.handN s.me == s2.handN s.me - 1 &&
    (b.obj? hb).map (·.buffed) == some false && b.handN s.me == s3.handN s.me - 1

-- Eclipse Herald (OGN-059) and Radiant Dawn (OGN-261): when an enemy unit is stunned
#guard t fun s => do
  let (s1, h) ← put s s.me "OGN-059" .base
  let (s2, c) ← put s1 s.me "OGN-225" .hand
  let (s3, e) ← put s2 s.you "OGN-001" .base
  let (s4, f) ← put s3 s.me "OGN-001" .base
  let a ← play (s4.tire h) s.me c [] { pick := fun ts => ts.contains e }
  let b ← fire (s4.tire h) [.stunned f]
  return a.tired h == some false && a.mightNow h == (s4.mightNow h).map (· + 1) &&
    b.tired h == some true && b.mightNow h == s4.mightNow h
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-261" .legendZone
  let (s2, c) ← put s1 s.me "OGN-225" .hand
  let (s3, e) ← put s2 s.you "OGN-001" .base
  let (s4, f) ← put s3 s.me "OGN-136" .base
  let a ← play s4 s.me c [] { pick := fun ts => ts.contains f }
  let b ← fire s4 [.stunned f]
  return (a.obj? f).map (·.buffed) == some true && (b.obj? f).map (·.buffed) == some false &&
    (a.obj? e).map (·.stunned) == some true

-- Scrapheap (OGN-182): draw 1 when it is played, discarded, or killed
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-182" .hand
  let a ← play s1 s.me c
  let (t1, x) ← put s s.me "OGN-182" .trash
  let b ← fire t1 [.discarded s.me x true]
  let c' ← fire t1 [.died x s.me]
  return a.handN s.me == s1.handN s.me && b.handN s.me == t1.handN s.me + 1 &&
    c'.handN s.me == t1.handN s.me + 1
-- ... and the discard that an effect makes sets it off (Zaun Warrens makes me discard 1, draw 1)
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let s2 := s1.setZone (.player s.me .hand) []
  let (s3, _) ← put s2 s.me "OGN-182" .hand
  let a ← fire s3 [.scored s.me bf true]
  return a.handN s.me == 2 && a.countIn s.me .trash "OGN-182" == 1

-- Jinx (OGN-202): when I discard, Jinx is readied and has +1 Might this turn; not for the opponent
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let s2 := s1.setZone (.player s.me .hand) []
  let (s3, j) ← put s2 s.me "OGN-202" .base
  let (s4, _) ← put s3 s.me "OGN-136" .hand
  let (s5, y) ← put s4 s.you "OGN-136" .trash
  let a ← fire (s4.tire j) [.scored s.me bf true]
  let b ← fire (s5.tire j) [.discarded s.you y true]
  return a.tired j == some false && a.mightNow j == (s4.mightNow j).map (· + 1) &&
    b.tired j == some true && b.mightNow j == s4.mightNow j

-- "one or more": discarding 2 cards readies Jinx once, with +1 Might only (not +2)
#guard t fun s => do
  let (s1, j) ← put s s.me "OGN-202" .base
  let (s2, _) ← put s1 s.me "OGN-136" .hand
  let (s3, _) ← put s2 s.me "OGN-136" .hand
  let (s4, x) ← put s3 s.me "OGN-136" .trash
  let (s5, y) ← put s4 s.me "OGN-136" .trash
  let a ← fire (s5.tire j) [.discarded s.me x false, .discarded s.me y true]
  let b ← fire (s5.tire j) [.discarded s.me x false]
  return a.mightNow j == (s5.mightNow j).map (· + 1) && b.mightNow j == s5.mightNow j &&
    b.tired j == some true

-- Radiant Dawn: only my units can be buffed (the opponent's unit is not offered)
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-261" .legendZone
  let (s2, e) ← put s1 s.you "OGN-001" .base
  let (s3, f) ← put s2 s.me "OGN-136" .base
  let (s4, g) ← put s3 s.me "OGN-001" .base
  let picks ← firePicks s4 [.stunned e]
  return picks.contains f && picks.contains g && !picks.contains e

-- Wielder of Water (OGN-055): +2 Might only while it attacks or defends alone
#guard t fun s => do
  let (s1, w) ← putAt s s.me "OGN-055" s.bf0
  let (s2, _) ← putAt s1 s.you "OGN-136" s.bf0
  let (s3, v) ← putAt s2 s.me "OGN-136" s.bf0
  let b := s3.inCombatAt s.bf0 s.me
  let c := s2.inCombatAt s.bf0 s.you
  return c.mightNow w == (s2.mightNow w).map (· + 2) && b.mightNow w == s3.mightNow w &&
    s2.mightNow w == (s1.mightNow w) && s3.mightNow v == some 2

-- Mask of Foresight (OGN-060): +1 Might for a friendly unit that attacks (a) or defends (b)
-- alone; not when it has company (c), not an enemy unit
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-060" .base
  let (s2, u) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-136" s.bf0
  let (s4, v) ← putAt s3 s.me "OGN-136" s.bf0
  let a ← startCombatNow s3 s.bf0 s.me
  let b ← startCombatNow s3 s.bf0 s.you
  let c ← startCombatNow s4 s.bf0 s.me
  let up := (s3.mightNow u).map (· + 1)
  return a.mightNow u == up && b.mightNow u == up &&
    a.mightNow e == s3.mightNow e && c.mightNow u == s4.mightNow u && c.mightNow v == s4.mightNow v

-- Cannon Barrage (OGN-127): 2 damage to every enemy unit in the combat, not elsewhere
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-127" .hand
  let (s2, a) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, f) ← put s3 s.you "OGN-001" .base
  let r ← play (s4.inShowdownAt s.bf0 s.me) s.me c
  let q ← play s4 s.me c
  return (r.obj? e).map (·.damage) == some 2 && (r.obj? f).map (·.damage) == some 0 &&
    (r.obj? a).map (·.damage) == some 0 && (q.obj? e).map (·.damage) == some 0

-- Kadregrin the Infernal (OGN-038): draw 1 for each of my Mighty units
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-038" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let (s3, _) ← put s2 s.me "OGN-136" .base
  let (s4, _) ← put s3 s.you "OGN-001" .base
  let a ← play s1 s.me c
  let b ← play s4 s.me c
  -- Kadregrin itself (Might 9) is Mighty and counts
  return a.handN s.me == s1.handN s.me - 1 + 1 && b.handN s.me == s4.handN s.me - 1 + 2

-- Fiora (OGN-232): Deflect, Ganking and Shield only while she is Mighty (Might 4, buffed 5)
#guard t fun s => do
  let (s1, f) ← put s s.me "OGN-232" .base
  let s2 := s1.buff f
  let s3 := s1.modObj f (fun o => { o with mightMods := [⟨1, .turn⟩] })
  return s3.hasKw f .ganking && s3.kwAmount f .shield == 1 && !s1.hasKw f .ganking &&
    s1.kwAmount f .shield == 0 && s1.deflectOf f == 0 &&
    s2.hasKw f .ganking && s2.kwAmount f .shield == 1 && s2.deflectOf f == 1

-- Mighty counts an Equipment too (Fiora 4 + Long Sword 2), and the Showdown of a Combat is a
-- combat for Wielder of Water
#guard t fun s => do
  let (s1, f) ← put s s.me "OGN-232" .base
  let (s2, sw) ← put s1 s.me "SFD-022" .base
  let s3 := s2.modObj sw (fun o => { o with attached := some f })
  return !s2.hasKw f .ganking && s3.hasKw f .ganking && s3.mightNow f == some 6
#guard t fun s => do
  let (s1, w) ← putAt s s.me "OGN-055" s.bf0
  let (s2, _) ← putAt s1 s.you "OGN-136" s.bf0
  let b := s2.inShowdownAt s.bf0 s.me
  return b.mightNow w == (s2.mightNow w).map (· + 2)

-- Disintegrate (OGN-005): 3 damage to a unit at a battlefield; draw 1 if that is lethal
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-005" .hand
  let (s2, e) ← putAt s1 s.you "OGN-136" s.bf0
  let (s3, g) ← putAt s2 s.you "OGN-116" s.bf0
  let (s4, b) ← put s3 s.you "OGN-136" .base
  let a ← play s4 s.me c [e]
  let d ← play s4 s.me c [g]
  return a.handN s.me == s4.handN s.me && d.handN s.me == s4.handN s.me - 1 &&
    (d.obj? g).map (·.damage) == some 3 && (play s4 s.me c [b]).isNone

-- Adaptatron (OGN-056): when it conquers I may kill a gear; if I do, it is buffed
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let (s2, u) ← putAt s1 s.me "OGN-056" bf
  let (s3, _) ← put s2 s.you "OGN-017" .base
  let a ← fire s3 [.scored s.me bf true]
  let b ← fire s3 [.scored s.me bf true] { yes := false }
  let c ← fire s2 [.scored s.me bf true]
  return (a.obj? u).map (·.buffed) == some true && a.countIn s.you .trash "OGN-017" == 1 &&
    (b.obj? u).map (·.buffed) == some false && b.countIn s.you .base "OGN-017" == 1 &&
    (c.obj? u).map (·.buffed) == some false

-- Ahri (OGN-066): I score 1 point when she holds, not when she conquers
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let (s2, _) ← putAt s1 s.me "OGN-066" bf
  let a ← fire s2 [.scored s.me bf false]
  let b ← fire s2 [.scored s.me bf true]
  return a.pointsOf s.me == s2.pointsOf s.me + 1 && b.pointsOf s.me == s2.pointsOf s.me &&
    a.pointsOf s.you == s2.pointsOf s.you

-- Mobilize (OGN-134) and Catalyst of Aeons (OGN-138): channel exhausted, or draw if I cannot
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-134" .hand
  let runes (x : GameState) := (x.zone (.player s.me .runeDeck)).length
  let empty := s1.setZone (.player s.me .runeDeck) []
  let a ← play s1 s.me c
  let b ← play empty s.me c
  return runes a + 1 == runes s1 && a.handN s.me == s1.handN s.me - 1 &&
    b.handN s.me == empty.handN s.me && runes s1 > 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-138" .hand
  let runes (x : GameState) := (x.zone (.player s.me .runeDeck)).length
  let one := s1.setZone (.player s.me .runeDeck) ((s1.zone (.player s.me .runeDeck)).take 1)
  let a ← play s1 s.me c
  let b ← play one s.me c
  return runes a + 2 == runes s1 && a.handN s.me == s1.handN s.me - 1 &&
    runes b == 0 && b.handN s.me == one.handN s.me

-- the channeled runes are exhausted (Mobilize, Catalyst); Catalyst with an empty Rune Deck draws 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-134" .hand
  let (s2, d) ← put s s.me "OGN-138" .hand
  let tired (x : GameState) :=
    ((x.zone (.player s.me .base)).filter (fun u => x.tired u == some true)).length
  let a ← play s1 s.me c
  let b ← play s2 s.me d
  let e ← play (s2.setZone (.player s.me .runeDeck) []) s.me d
  return tired a == tired s1 + 1 && tired b == tired s2 + 2 && e.handN s.me == s2.handN s.me

-- Disintegrate: damage that is already there counts; a buff keeps a unit from being lethal
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-005" .hand
  let (s2, hurt) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, strong) ← putAt s2 s.you "OGN-136" s.bf0
  let h := s3.modObj hurt (fun o => { o with damage := 2 })
  let b := s3.buff strong |>.modObj strong (fun o => { o with mightMods := [⟨1, .turn⟩] })
  let a ← play h s.me c [hurt]
  let d ← play b s.me c [strong]
  return a.handN s.me == h.handN s.me && d.handN s.me == b.handN s.me - 1

-- Adaptatron kills a gear of mine too; Ahri's hold can reach the Victory Score
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let (s2, u) ← putAt s1 s.me "OGN-056" bf
  let (s3, g) ← put s2 s.me "OGN-017" .base
  let a ← fire s3 [.scored s.me bf true]
  return (a.obj? u).map (·.buffed) == some true && a.countIn s.me .trash "OGN-017" == 1 &&
    (a.obj? g).isNone
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let (s2, _) ← putAt s1 s.me "OGN-066" bf
  let near := s2.gainPoints s.me (s2.config.mode.victoryScore - 1)
  let a ← fire near [.scored s.me bf false]
  return a.pointsOf s.me == s2.config.mode.victoryScore

-- Acceptable Losses (OGN-179) and Cull the Weak (OGN-209): each player kills one of their own
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-179" .hand
  let (s2, _) ← put s1 s.me "OGN-017" .base
  let (s3, _) ← put s2 s.me "OGN-017" .base
  let (s4, _) ← put s3 s.you "OGN-017" .base
  let (s5, _) ← put s4 s.you "OGN-001" .base
  let a ← play s5 s.me c
  return a.countIn s.me .trash "OGN-017" == 1 && a.countIn s.me .base "OGN-017" == 1 &&
    a.countIn s.you .trash "OGN-017" == 1 && a.countIn s.you .base "OGN-001" == 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-209" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let (s3, _) ← put s2 s.me "OGN-136" .base
  let (s4, _) ← put s3 s.you "OGN-001" .base
  let a ← play s4 s.me c
  let b ← play s3 s.me c
  return a.countIn s.me .trash "OGN-001" + a.countIn s.me .trash "OGN-136" == 1 &&
    a.countIn s.you .trash "OGN-001" == 1 && b.countIn s.you .trash "OGN-001" == 0

-- Invert Timelines (OGN-201): each player discards their hand, then draws 4
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-201" .hand
  let a ← play s1 s.me c
  return a.handN s.me == 4 && a.handN s.you == 4 && a.countIn s.me .trash "OGN-201" == 1 &&
    (a.zone (.player s.you .trash)).length ==
      (s1.zone (.player s.you .trash)).length + s1.handN s.you &&
    (a.zone (.player s.me .trash)).length == (s1.zone (.player s.me .trash)).length + s1.handN s.me

-- Whirlwind (OGN-187): starting with the next player, each player may return a unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-187" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, _) ← put s2 s.you "OGN-136" .base
  let (s4, e2) ← put s3 s.you "OGN-001" .base
  -- the opponent chooses first, among all three units; then I choose among what is left
  let a ← play s4 s.me c [] { obj := fun o => o == e2 }
  let b ← play s4 s.me c [] { yes := false }
  return a.countIn s.you .hand "OGN-001" == s4.countIn s.you .hand "OGN-001" + 1 &&
    a.countIn s.you .base "OGN-136" == 1 && a.handN s.me == s4.handN s.me - 1 + 1 &&
    b.handN s.you == s4.handN s.you && b.countIn s.you .base "OGN-001" == 1 && (b.obj? u).isSome

-- each player kills a gear of their own: the opponent, with two gear, is asked and chooses
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-179" .hand
  let (s2, _) ← put s1 s.me "OGN-017" .base
  let (s3, g) ← put s2 s.you "OGN-017" .base
  let (s4, h) ← put s3 s.you "OGN-124" .base
  let a ← play s4 s.me c [] { obj := fun o => o == h }
  let b ← play (s4.setZone (.player s.you .base) []) s.me c
  return a.countIn s.you .trash "OGN-124" == 1 && a.countIn s.you .base "OGN-017" == 1 &&
    (a.obj? g).isSome && a.countIn s.me .trash "OGN-017" == 1 &&
    b.countIn s.me .trash "OGN-017" == 1

-- Loose Cannon (OGN-251), at the start of my Beginning Phase: draw 1 with one card or fewer in hand
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-251" .legendZone
  let one := s1.setZone (.player s.me .hand) ((s1.zone (.player s.me .hand)).take 1)
  let a ← fire one [.phaseStarted s.me .beginning]
  let b ← fire s1 [.phaseStarted s.me .beginning]
  let c ← fire one [.phaseStarted s.you .beginning]
  let d ← fire one [.phaseStarted s.me .main]
  return a.handN s.me == one.handN s.me + 1 && b.handN s.me == s1.handN s.me &&
    c.handN s.me == one.handN s.me && d.handN s.me == one.handN s.me
-- ... and the Beginning Phase of the game itself sets it off
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-251" .legendZone
  let one := { s1.setZone (.player s.me .hand) ((s1.zone (.player s.me .hand)).take 1) with
    pending := [.phase .beginning] }
  match advance 100 one [] with
  | .ok (s2, es) =>
    let s3 := settleChain {} 12 s2
    return es.contains (.phaseStarted s.me .beginning) && s3.handN s.me == one.handN s.me + 1
  | .error _ => none

-- The Arena's Greatest (OGN-290) and Obelisk of Power (OGN-284): in each player's first Beginning
-- Phase, that player gains 1 point / channels 1 rune; not in the second
#guard t fun s => do
  let (s1, _) ← putBf s s.me "OGN-290"
  let first := { s1 with turn := 1 }
  let second := { s1 with turn := 3 }
  let a ← fire first [.phaseStarted s.me .beginning]
  let b ← fire second [.phaseStarted s.me .beginning]
  return a.pointsOf s.me == s1.pointsOf s.me + 1 && b.pointsOf s.me == s1.pointsOf s.me
#guard t fun s => do
  let (s1, _) ← putBf s s.me "OGN-284"
  let first := { s1 with turn := 1 }
  let second := { s1 with turn := 3 }
  let runes (x : GameState) := (x.zone (.player s.me .runeDeck)).length
  let a ← fire first [.phaseStarted s.me .beginning]
  let b ← fire second [.phaseStarted s.me .beginning]
  return runes a + 1 == runes s1 && runes b == runes s1

-- Loose Cannon at the edge: no card in hand draws, two cards do not
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-251" .legendZone
  let none := s1.setZone (.player s.me .hand) []
  let two := s1.setZone (.player s.me .hand) ((s1.zone (.player s.me .hand)).take 2)
  let a ← fire none [.phaseStarted s.me .beginning]
  let b ← fire two [.phaseStarted s.me .beginning]
  return a.handN s.me == 1 && b.handN s.me == 2

-- the Battlefield of the opponent works for the player whose first Beginning Phase it is
-- (the second player's first turn is turn 2)
#guard t fun s => do
  let (s1, _) ← putBf s s.you "OGN-284"
  let runes (x : GameState) (p : PlayerId) := (x.zone (.player p .runeDeck)).length
  let first := { s1 with turn := 2 }
  let a ← fire first [.phaseStarted s.you .beginning]
  let b ← fire { s1 with turn := 4 } [.phaseStarted s.you .beginning]
  return runes a s.you + 1 == runes s1 s.you && runes a s.me == runes s1 s.me &&
    runes b s.you == runes s1 s.you
#guard t fun s => do
  let (s1, _) ← putBf s s.you "OGN-290"
  let a ← fire { s1 with turn := 2 } [.phaseStarted s.you .beginning]
  return a.pointsOf s.you == s1.pointsOf s.you + 1 && a.pointsOf s.me == s1.pointsOf s.me

-- Dark Child (OGS-017) now sets off its end-of-turn ability; a choice of two runes is not
-- understood yet, so the game goes on without it
#guard t fun s => do
  let (s1, _) ← put s s.me "OGS-017" .base
  let a ← fire s1 [.phaseStarted s.me .ending]
  return a.pending.length ≤ s1.pending.length + 1

-- Zenith Blade (OGN-262): stun an enemy unit at a battlefield; I may move a friendly unit there
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-262" .hand
  let (s2, e) ← putAt s1 s.you "OGN-116" s.bf0
  let (s3, f) ← put s2 s.me "OGN-136" .base
  let a ← play s3 s.me c [e]
  let b ← play s3 s.me c [e] { yes := false }
  return (a.obj? e).map (·.stunned) == some true && (a.obj? f).bind (·.loc) == some s.bf0 &&
    (a.obj? f).map (·.exhausted) == some false && (b.obj? f).bind (·.loc) == none &&
    (b.obj? e).map (·.stunned) == some true &&
    -- the Battlefield is Contested by me, and the Showdown starts at it
    (a.obj? s.bf0).bind (·.contested) == some s.me &&
    a.pending.any (fun f => match f with | .showdown bf _ _ => bf == s.bf0 | _ => false)

-- Blitzcrank (OGN-067): played to a battlefield, I may move an enemy unit to here; it returns to
-- my hand when it holds
#guard t fun s => do
  let (s1, b) ← putAt s s.me "OGN-067" s.bf0
  let (s2, e) ← put s1 s.you "OGN-136" .base
  let a ← fire s2 [.played s.me b]
  let n ← fire s2 [.played s.me b] { yes := false }
  let h ← fire s2 [.scored s.me s.bf0 false]
  return (a.obj? e).bind (·.loc) == some s.bf0 && (n.obj? e).bind (·.loc) == none &&
    h.countIn s.me .hand "OGN-067" == s2.countIn s.me .hand "OGN-067" + 1 &&
    (h.obj? b).isNone
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-067" .hand
  let (s2, e) ← put s1 s.you "OGN-136" .base
  let a ← play s2 s.me c
  return (a.obj? e).bind (·.loc) == none

-- Blitzcrank: the enemy unit moved there makes the Battlefield Contested by its controller; a
-- Conquer, or a Hold elsewhere, does not send Blitzcrank home
#guard t fun s => do
  let (s1, b) ← putAt s s.me "OGN-067" s.bf0
  let (s2, e) ← put s1 s.you "OGN-136" .base
  let a ← fire s2 [.played s.me b]
  let other := (s.battlefields.filter (· != s.bf0)).head?.getD ⟨0⟩
  let c ← fire s2 [.scored s.me s.bf0 true]
  let d ← fire s2 [.scored s.me other false]
  return (a.obj? e).bind (·.loc) == some s.bf0 &&
    (a.obj? s.bf0).bind (·.contested) == some s.you && (c.obj? b).isSome && (d.obj? b).isSome

-- Blazing Scorcher (OGN-001), [Accelerate]: paying 1 Energy and a Fury Power more, it enters ready
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-001" .hand
  let base := payOf s1 c
  let a ← cast (s1.rich s.me) s.me c base
  let b ← cast (s1.rich s.me) s.me c ⟨base.energy + 1, base.power ++ [.fury]⟩
  let ua ← a.firstOf s.me .base "OGN-001"
  let ub ← b.firstOf s.me .base "OGN-001"
  return a.tired ua == some true && b.tired ub == some false

-- Cemetery Attendant (OGN-165) and Morbid Return (OGN-170): return a unit from my Trash to my hand;
-- not a card that is not a unit, not the opponent's
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-165" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .trash
  let (s3, v) ← put s2 s.me "OGN-001" .trash
  let (s4, _) ← put s3 s.me "OGN-004" .trash
  let (s5, _) ← put s4 s.you "OGN-016" .trash
  let a ← play s5 s.me c [] { obj := fun o => o == v }
  let b ← play (s5.setZone (.player s.me .trash) []) s.me c
  return a.countIn s.me .hand "OGN-001" == s5.countIn s.me .hand "OGN-001" + 1 &&
    a.countIn s.me .trash "OGN-001" == 0 && a.countIn s.me .trash "OGN-136" == 1 &&
    a.countIn s.you .hand "OGN-016" == s5.countIn s.you .hand "OGN-016" &&
    b.handN s.me == s5.handN s.me - 1 && (a.obj? u).isSome
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-170" .hand
  let (s2, _) ← put s1 s.me "OGN-136" .trash
  let (s3, _) ← put s2 s.me "OGN-004" .trash
  let (s4, _) ← put s3 s.you "OGN-001" .trash
  let a ← play s4 s.me c
  return a.countIn s.me .hand "OGN-136" == 1 && a.countIn s.me .hand "OGN-004" == 0 &&
    a.countIn s.you .hand "OGN-001" == s4.countIn s.you .hand "OGN-001"

-- Possession (OGN-203): take control of an enemy unit at a battlefield, and recall it to my Base
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-203" .hand
  let (s2, e) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, f) ← put s2 s.you "OGN-001" .base
  let a ← play s3 s.me c [e]
  return (a.obj? e).map (·.controller) == some s.me && (a.zone (.player s.me .base)).contains e &&
    (a.obj? e).bind (·.loc) == none && (a.obj? f).map (·.controller) == some s.you &&
    (play s3 s.me c [f]).isNone

-- The Grand Plaza (OGN-293): with 7 units here when I hold, I win; with 6, I do not
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-293"
  let units (n : Nat) (x : GameState) : Option GameState :=
    (List.range n).foldl (fun acc _ => acc.bind fun y => (putAt y s.me "OGN-136" bf).map (·.1))
      (some x)
  let seven ← units 7 s1
  let six ← units 6 s1
  let a ← fire seven [.scored s.me bf false]
  let b ← fire six [.scored s.me bf false]
  let v := s.config.mode.victoryScore
  return v ≤ a.pointsOf s.me && b.pointsOf s.me < v

-- Possession keeps the damage and the status of the unit it takes (Ready stays Ready, Exhausted
-- stays Exhausted)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-203" .hand
  let (s2, e) ← putAt s1 s.you "OGN-116" s.bf0
  let (s3, h) ← putAt s2 s.you "OGN-116" s.bf0
  let hurt := (s3.modObj e (fun o => { o with damage := 2 })).tire h
  let a ← play hurt s.me c [e]
  let b ← play hurt s.me c [h]
  return (a.obj? e).map (·.damage) == some 2 && (a.obj? e).map (·.exhausted) == some false &&
    (b.obj? h).map (·.exhausted) == some true && !(a.zone (.player s.you .base)).contains e &&
    (a.obj? s.bf0).bind (·.control) == (hurt.obj? s.bf0).bind (·.control)

-- The Grand Plaza: the game is won, and an enemy unit, or my units at another battlefield, are
-- not counted
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-293"
  let other := (s.battlefields.filter (· != s.bf0)).head?.getD ⟨0⟩
  let add (n : Nat) (p : PlayerId) (at_ : ObjId) (x : GameState) : Option GameState :=
    (List.range n).foldl (fun acc _ => acc.bind fun y => (putAt y p "OGN-136" at_).map (·.1))
      (some x)
  let mixed ← add 4 s.me bf s1 >>= add 3 s.you bf
  let elsewhere ← add 4 s.me bf s1 >>= add 3 s.me other
  let a ← fire mixed [.scored s.me bf false]
  let b ← fire elsewhere [.scored s.me bf false]
  let v := s.config.mode.victoryScore
  return a.pointsOf s.me < v && b.pointsOf s.me < v

-- Mystic Poro (OGN-171), [Vision]: when I play it, I may recycle the top card of my Main Deck
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-171" .hand
  let deck (x : GameState) := x.zone (.player s.me .mainDeck)
  let top ← (deck s1).head?
  let a ← play s1 s.me c
  let b ← play s1 s.me c [] { yes := false }
  let n := (deck s1).length
  return (deck a).length == n && (deck a).getLast? == some top && (deck a).head? != some top &&
    (deck b).head? == some top && (deck b).length == n

-- Vision rotates the deck: the rest keeps its order, the opponent's deck is untouched, and an
-- empty deck is fine; Jeweled Colossus (OGN-086) has it too
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-086" .hand
  let deck (x : GameState) (p : PlayerId) := x.zone (.player p .mainDeck)
  let a ← play s1 s.me c
  let e ← play (s1.setZone (.player s.me .mainDeck) []) s.me c
  let top ← (deck s1 s.me).head?
  return deck a s.me == (deck s1 s.me).tail ++ [top] && deck a s.you == deck s1 s.you &&
    (deck e s.me).isEmpty && a.countIn s.me .base "OGN-086" == 1

-- En Garde (OGN-046): +1 Might, and one more if it is the only unit I control there
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-046" .hand
  let (s2, u) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let (s4, w) ← putAt s3 s.me "OGN-136" s.bf0
  let alone ← play s3 s.me c [u]
  let crowd ← play s4 s.me c [u]
  let atBase ← play s3 s.me c [v]
  let (t1, x) ← put s3 s.me "OGN-136" .base
  let baseCrowd ← play t1 s.me c [v]
  return alone.mightNow u == (s3.mightNow u).map (· + 2) &&
    crowd.mightNow u == (s4.mightNow u).map (· + 1) && crowd.mightNow w == s4.mightNow w &&
    atBase.mightNow v == (s3.mightNow v).map (· + 2) &&
    baseCrowd.mightNow v == (t1.mightNow v).map (· + 1) && baseCrowd.mightNow x == t1.mightNow x

-- Siphon Power (OGN-266): friendly units at the chosen battlefield +1, enemy units there -1 (min 1)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-266" .hand
  let (s2, f) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, g) ← put s3 s.me "OGN-136" .base
  let (s5, h) ← put s4 s.you "OGN-001" .base
  let a ← play s5 s.me c [s.bf0]
  return a.mightNow f == (s5.mightNow f).map (· + 1) &&
    a.mightNow e == (s5.mightNow e).map (· - 1) &&
    a.mightNow g == s5.mightNow g && a.mightNow h == s5.mightNow h

-- Last Stand (OGN-069): double a friendly unit's Might this turn, and it becomes Temporary
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-069" .hand
  let (s2, u) ← put s1 s.me "OGN-001" .base
  let a ← play s2 s.me c [u]
  let e := a.mapObjects endTurnObj
  return a.mightNow u == (s2.mightNow u).map (· * 2) && a.hasKw u .temporary &&
    e.mightNow u == s2.mightNow u && e.hasKw u .temporary

-- Convergent Mutation (OGN-108): increase a friendly unit's Might to that of another
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-108" .hand
  let (s2, a) ← put s1 s.me "OGN-136" .base
  let (s3, b) ← put s2 s.me "OGN-001" .base
  let up ← play s3 s.me c [a, b]
  -- the second unit is not stronger: nothing changes (the Might is only raised); the same unit
  -- twice changes nothing either
  let lower ← play s3 s.me c [b, a]
  let twice ← play s3 s.me c [a, a]
  return up.mightNow a == s3.mightNow b && up.mightNow b == s3.mightNow b &&
    lower.mightNow b == s3.mightNow b && lower.mightNow a == s3.mightNow a &&
    twice.mightNow a == s3.mightNow a

-- Showstopper (OGN-270): buff a friendly unit in my base, then move it to a battlefield I choose
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-270" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, w) ← putAt s2 s.me "OGN-136" s.bf0
  let other := (s.battlefields.filter (· != s.bf0)).head?.getD ⟨0⟩
  let a ← play s3 s.me c [u] { obj := fun o => o == other }
  let b ← play s3 s.me c [u] { obj := fun o => o == s.bf0 }
  return (a.obj? u).map (·.buffed) == some true && (a.obj? u).bind (·.loc) == some other &&
    (b.obj? u).bind (·.loc) == some s.bf0 && (play s3 s.me c [w]).isNone

-- Siphon Power: a unit at another battlefield is not touched, and an enemy of Might 1 stays at 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-266" .hand
  let other := (s.battlefields.filter (· != s.bf0)).head?.getD ⟨0⟩
  let (s2, f) ← putAt s1 s.me "OGN-136" other
  let (s3, e) ← putAt s2 s.you "OGN-216" s.bf0
  let (s4, g) ← putAt s3 s.you "OGN-001" other
  let a ← play s4 s.me c [s.bf0]
  return a.mightNow f == s4.mightNow f && a.mightNow g == s4.mightNow g && a.mightNow e == some 1

-- En Garde counts only my units there; Showstopper cannot move an enemy unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-046" .hand
  let (s2, u) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, _) ← putAt s2 s.you "OGN-136" s.bf0
  let other := (s.battlefields.filter (· != s.bf0)).head?.getD ⟨0⟩
  let (s4, _) ← putAt s3 s.me "OGN-136" other
  let a ← play s4 s.me c [u]
  let (t1, d) ← put s s.me "OGN-270" .hand
  let (t2, e) ← put t1 s.you "OGN-136" .base
  return a.mightNow u == (s4.mightNow u).map (· + 2) && (play t2 s.me d [e]).isNone

-- Wraith of Echoes (OGN-118): the first time a friendly unit dies each turn, draw 1
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-118" .base
  let (s2, x) ← put s1 s.me "OGN-136" .trash
  let (s3, y) ← put s2 s.me "OGN-136" .trash
  let (s4, z) ← put s3 s.you "OGN-136" .trash
  let (s5, g) ← put s4 s.me "OGN-017" .trash
  let a ← fire s5 [.died x s.me]
  let b ← fire a [.died y s.me]
  let c ← fire s5 [.died z s.you]
  let d ← fire s5 [.died g s.me]
  return a.handN s.me == s5.handN s.me + 1 && b.handN s.me == a.handN s.me &&
    c.handN s.me == s5.handN s.me && d.handN s.me == s5.handN s.me

-- Miss Fortune (OGN-162): the first time she moves each turn, I may ready something else that is
-- exhausted
#guard t fun s => do
  let (s1, m) ← putAt s s.me "OGN-162" s.bf0
  let (s2, e) ← put s1 s.me "OGN-136" .base
  let (s3, f) ← put s2 s.me "OGN-136" .base
  let tired := ((s3.tire e).tire f).tire m
  let a ← fire tired [.standardMoved m (some s.bf0)] { obj := fun o => o == e }
  let b ← fire a [.standardMoved m (some s.bf0)] { obj := fun o => o == f }
  let c ← fire tired [.standardMoved m (some s.bf0)] { yes := false }
  return a.tired e == some false && a.tired m == some true && b.tired f == some true &&
    c.tired e == some true

-- Viktor (OGN-246): a Recruit token comes to my base when another non-Recruit unit I control dies
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-246" .base
  let (s2, x) ← put s1 s.me "OGN-136" .trash
  let (s3, y) ← put s2 s.you "OGN-136" .trash
  let (s4, bf) ← putBf s3 s.me "OGN-275"
  let tk ← fire s4 [.scored s.me bf false]
  let token ← (tk.zone (.player s.me .base)).find? (fun u =>
    (tk.cardDef? u).any (·.name == "Recruit"))
  let a ← fire s4 [.died x s.me]
  let b ← fire s4 [.died y s.you]
  let c ← fire tk [.died token s.me]
  return a.countNamed s.me .base "Recruit" == 1 && b.countNamed s.me .base "Recruit" == 0 &&
    c.countNamed s.me .base "Recruit" == tk.countNamed s.me .base "Recruit"

-- Draven (OGN-028): his Might is increased by my points
#guard t fun s => do
  let (s1, d) ← put s s.me "OGN-028" .base
  let more := (s1.gainPoints s.me 3).gainPoints s.you 2
  return more.mightNow d == (s1.mightNow d).map (· + 3) &&
    (s1.gainPoints s.you 2).mightNow d == s1.mightNow d

-- Relentless Storm (OGN-249), a Legend: when I play a Mighty unit, I may exhaust it to channel 1
-- rune exhausted
#guard t fun s => do
  let (s1, l) ← put s s.me "OGN-249" .legendZone
  let (s2, big) ← put s1 s.me "OGN-001" .hand
  let (s3, small) ← put s2 s.me "OGN-136" .hand
  let runes (x : GameState) := (x.zone (.player s.me .runeDeck)).length
  let a ← play s3 s.me big
  let b ← play s3 s.me small
  let c ← play (s3.tire l) s.me big
  let d ← play s3 s.me big [] { yes := false }
  return a.tired l == some true && runes a + 1 == runes s3 && b.tired l == some false &&
    runes b == runes s3 && runes c == runes s3 && d.tired l == some false

-- Dr. Mundo (OGN-109): his Might is increased by the cards in my Trash; at the start of my
-- Beginning Phase I recycle 3 from it
#guard t fun s => do
  let (s1, d) ← put s s.me "OGN-109" .base
  let (s2, _) ← put s1 s.me "OGN-136" .trash
  let (s3, _) ← put s2 s.me "OGN-136" .trash
  let (s4, _) ← put s3 s.me "OGN-136" .trash
  let (s5, _) ← put s4 s.me "OGN-136" .trash
  let trash (x : GameState) := (x.zone (.player s.me .trash)).length
  let deck (x : GameState) := (x.zone (.player s.me .mainDeck)).length
  let a ← fire s5 [.phaseStarted s.me .beginning]
  let (t1, _) ← put s1 s.me "OGN-136" .trash
  let b ← fire t1 [.phaseStarted s.me .beginning]
  return s5.mightNow d == (s1.mightNow d).map (· + 4) && trash a + 3 == trash s5 &&
    deck a == deck s5 + 3 && trash b == 0 && deck b == deck t1 + 1

-- Wraith of Echoes: two friendly units dying at once draw 1, not 2; two Wraiths draw 1 each
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-118" .base
  let (s2, x) ← put s1 s.me "OGN-136" .trash
  let (s3, y) ← put s2 s.me "OGN-136" .trash
  let a ← fire s3 [.died x s.me, .died y s.me]
  let (t1, _) ← put s3 s.me "OGN-118" .base
  let b ← fire t1 [.died x s.me]
  return a.handN s.me == s3.handN s.me + 1 && b.handN s.me == t1.handN s.me + 2

-- Dr. Mundo recycles the cards the player chooses, and not in the opponent's Beginning Phase
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-109" .base
  let (s2, _) ← put s1 s.me "OGN-136" .trash
  let (s3, _) ← put s2 s.me "OGN-001" .trash
  let (s4, _) ← put s3 s.me "OGN-004" .trash
  let (s5, d) ← put s4 s.me "OGN-016" .trash
  let x ← fire s5 [.phaseStarted s.me .beginning] { obj := fun o => o != d }
  let y ← fire s5 [.phaseStarted s.you .beginning]
  return x.countIn s.me .trash "OGN-016" == 1 && (x.zone (.player s.me .trash)).length == 1 &&
    (y.zone (.player s.me .trash)).length == 4

-- Qiyana (OGN-155): when she conquers, draw 1 or channel 1 rune exhausted
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let (s2, _) ← putAt s1 s.me "OGN-155" bf
  let runes (x : GameState) := (x.zone (.player s.me .runeDeck)).length
  let a ← fire s2 [.scored s.me bf true]
  let b ← fire s2 [.scored s.me bf true] { yes := false }
  let c ← fire s2 [.scored s.me bf false]
  return a.handN s.me == s2.handN s.me + 1 && runes a == runes s2 &&
    b.handN s.me == s2.handN s.me && runes b + 1 == runes s2 && c.handN s.me == s2.handN s.me

-- Charm (OGN-043): move an enemy unit, to its base or to a battlefield I choose
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-043" .hand
  let (s2, e) ← putAt s1 s.you "OGN-136" s.bf0
  let (s3, f) ← put s2 s.you "OGN-136" .base
  let other := (s.battlefields.filter (· != s.bf0)).head?.getD ⟨0⟩
  let toBase ← play s3 s.me c [e]
  let toBf ← play s3 s.me c [f] { yes := false, obj := fun o => o == other }
  return (toBase.obj? e).bind (·.loc) == none && (toBase.zone (.player s.you .base)).contains e &&
    (toBf.obj? f).bind (·.loc) == some other

-- Ride the Wind (OGN-173): move a friendly unit and ready it
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-173" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let tiredU := s2.tire u
  let a ← play tiredU s.me c [u] { yes := false, obj := fun o => o == s.bf0 }
  return (a.obj? u).bind (·.loc) == some s.bf0 && a.tired u == some false

-- Unforgiven (OGN-259), a Legend: for 2 Energy and exhausting it, move a friendly unit to or from
-- my base
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-259" .legendZone
  let (s2, u) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let down ← activate s3 s.me g 0 [u] ⟨2, []⟩
  let up ← activate s3 s.me g 0 [v] ⟨2, []⟩ { yes := false, obj := fun o => o == s.bf0 }
  return (down.obj? u).bind (·.loc) == none && down.tired g == some true &&
    (up.obj? v).bind (·.loc) == some s.bf0 && (activate down s.me g 0 [u] ⟨2, []⟩).isNone

-- Dragon's Rage (OGN-258): move an enemy unit, then it and another enemy unit there deal damage
-- equal to their Mights to each other
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-258" .hand
  let (s2, f) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, e) ← put s2 s.you "OGN-116" .base
  let (s4, g) ← put s3 s.you "OGN-001" .base
  let a ← play s4 s.me c [e] { yes := false, obj := fun o => o == s.bf0 || o == f }
  return (a.obj? e).bind (·.loc) == some s.bf0 && (a.obj? e).map (·.damage) == some 5 &&
    (a.obj? f).isNone && (a.obj? g).map (·.damage) == some 0

-- Dragon's Rage with no other enemy unit at the destination: the moved unit is not damaged;
-- Unforgiven moves a unit at a battlefield only to the base; Charm cannot take a friendly unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-258" .hand
  let (s2, e) ← put s1 s.you "OGN-116" .base
  let a ← play s2 s.me c [e] { yes := false, obj := fun o => o == s.bf0 }
  return (a.obj? e).bind (·.loc) == some s.bf0 && (a.obj? e).map (·.damage) == some 0
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-259" .legendZone
  let (s2, u) ← putAt s1 s.me "OGN-136" s.bf0
  let other := (s.battlefields.filter (· != s.bf0)).head?.getD ⟨0⟩
  let a ← activate s2 s.me g 0 [u] ⟨2, []⟩ { yes := false, obj := fun o => o == other }
  return (a.obj? u).bind (·.loc) == none && (a.zone (.player s.me .base)).contains u
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-043" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  return (play s2 s.me c [u]).isNone

-- Singularity (OGN-105): 6 damage to each of up to two units (two different units)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-105" .hand
  let (s2, a) ← put s1 s.you "OGN-116" .base
  let (s3, b) ← put s2 s.you "OGN-116" .base
  let (s4, d) ← put s3 s.you "OGN-116" .base
  let x ← play s4 s.me c [] { obj := fun o => o == a }
  let n ← play s4 s.me c [] { yes := false }
  let dmg (y : GameState) (u : ObjId) := (y.obj? u).map (·.damage)
  return dmg x a == some 6 && (dmg x b == some 6 || dmg x d == some 6) &&
    !(dmg x b == some 6 && dmg x d == some 6) && dmg n a == some 0 && dmg n b == some 0

-- Kinkou Monk (OGN-141): buff up to two other friendly units, different ones, not itself
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-141" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let (s4, w) ← put s3 s.me "OGN-136" .base
  let (s5, e) ← put s4 s.you "OGN-136" .base
  let a ← play s5 s.me c [] { obj := fun o => o == u }
  let m ← a.firstOf s.me .base "OGN-141"
  let bf (y : GameState) (o : ObjId) := (y.obj? o).map (·.buffed)
  let count := [u, v, w].filter (fun o => bf a o == some true) |>.length
  return count == 2 && bf a u == some true && bf a m == some false && bf a e == some false

-- Back to Back (OGN-206): two friendly units get +2 Might each; with one unit, only +2
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-206" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let a ← play s3 s.me c [] { obj := fun o => o == u }
  let b ← play s2 s.me c
  return a.mightNow u == (s3.mightNow u).map (· + 2) &&
    a.mightNow v == (s3.mightNow v).map (· + 2) && b.mightNow u == (s2.mightNow u).map (· + 2)

-- the edges of the two-pick cards: one unit only, my own units, only friendly units, and the
-- bonus ends with the turn
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-105" .hand
  let (s2, a) ← put s1 s.me "OGN-116" .base
  let x ← play s2 s.me c
  return (x.obj? a).map (·.damage) == some 6
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-141" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let a ← play s2 s.me c
  let m ← a.firstOf s.me .base "OGN-141"
  return (a.obj? u).map (·.buffed) == some true && (a.obj? m).map (·.buffed) == some false
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-206" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let (s4, w) ← put s3 s.me "OGN-136" .base
  let (s5, e) ← put s4 s.you "OGN-136" .base
  let a ← play s5 s.me c
  let up := [u, v, w].filter (fun o => a.mightNow o == (s5.mightNow o).map (· + 2)) |>.length
  return up == 2 && a.mightNow e == s5.mightNow e &&
    [u, v, w].all (fun o => (a.mapObjects endTurnObj).mightNow o == s5.mightNow o)

-- Aspirant's Climb (OGN-276): one more point is needed to win
#guard t fun s => do
  let (s1, _) ← putBf s s.me "OGN-276"
  let v := s.config.mode.victoryScore
  let at8 := s.gainPoints s.me v
  let with8 := s1.gainPoints s.me v
  let with9 := s1.gainPoints s.me (v + 1)
  return s1.victoryScore == v + 1 && s.victoryScore == v && at8.winner == some s.me &&
    with8.winner == none && with9.winner == some s.me

-- Shakedown (OGN-033): the enemy unit's controller has me draw 2, or the unit is dealt 6
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-033" .hand
  let (s2, e) ← put s1 s.you "OGN-116" .base
  let draw ← play s2 s.me c [e]
  let hit ← play s2 s.me c [e] { yes := false }
  return draw.handN s.me == s2.handN s.me - 1 + 2 && (draw.obj? e).map (·.damage) == some 0 &&
    hit.handN s.me == s2.handN s.me - 1 && (hit.obj? e).map (·.damage) == some 6

-- Spirit's Refuge (OGN-063): buffed friendly units have Deflect unless they print it already
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-063" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let (s4, p) ← put s3 s.me "OGN-013" .base
  let (s5, e) ← put s4 s.you "OGN-136" .base
  let a ← play s5 s.me c [] { pick := fun ts => ts.contains u }
  let both := (a.buff p).buff e
  return a.deflectOf u == 1 && a.deflectOf v == 0 && both.deflectOf p == s5.deflectOf p &&
    both.deflectOf e == 0 && (a.obj? u).map (·.buffed) == some true

-- Shakedown kills a unit of Might 6 or less; Spirit's Refuge's Deflect ends with the buff
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-033" .hand
  let (s2, e) ← put s1 s.you "OGN-001" .base
  let hit ← play s2 s.me c [e] { yes := false }
  return (hit.obj? e).isNone && hit.countIn s.you .trash "OGN-001" == 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-063" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let a ← play s2 s.me c [] { pick := fun ts => ts.contains u }
  let unbuffed := a.modObj u (fun o => { o with buffed := false })
  return a.deflectOf u == 1 && unbuffed.deflectOf u == 0

-- Hidden (CR 811): hide a card for one Power at a Battlefield I control; from the next turn, play
-- it as a Reaction without paying
-- Pakaa Cub (OGN-135): a unit; hidden, then played from hiding on the next turn
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-135" .hand
  let mine := s1.control s.me s.bf0
  let hide ← activate mine s.me c 0 [s.bf0] ⟨0, [.fury]⟩
  let h ← (hide.zone (.player s.me .hidden)).head?
  let same := activate hide s.me h 1 [] ⟨0, []⟩
  let next := { hide with turn := hide.turn + 1 }
  let played ← activate next s.me h 1 [] ⟨0, []⟩
  return (hide.zone (.player s.me .hand)).length + 1 == (mine.zone (.player s.me .hand)).length &&
    (hide.obj? h).bind (·.hiddenAt) == some s.bf0 && same.isNone &&
    played.countIn s.me .base "OGN-135" == 1 && played.countIn s.me .hidden "OGN-135" == 0
-- ... only at a Battlefield I control, and only with one Power
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-135" .hand
  let mine := s1.control s.me s.bf0
  return (activate s1 s.me c 0 [s.bf0] ⟨0, [.fury]⟩).isNone &&
    (activate mine s.me c 0 [s.bf0] ⟨0, []⟩).isNone &&
    (activate mine s.me c 0 [s.bf0] ⟨0, [.fury, .calm]⟩).isNone

-- Block (OGN-057), a spell: hidden, then played from hiding: Shield 3 and Tank, and into my Trash
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-057" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let mine := s2.control s.me s.bf0
  let hide ← activate mine s.me c 0 [s.bf0] ⟨0, [.fury]⟩
  let h ← (hide.zone (.player s.me .hidden)).head?
  let next := { hide with turn := hide.turn + 1 }
  let played ← activate next s.me h 1 [u] ⟨0, []⟩
  return played.kwAmount u .shield == 3 && played.hasKw u .tank &&
    played.countIn s.me .trash "OGN-057" == 1 && played.countIn s.me .hidden "OGN-057" == 0

-- Blastcone Fae (OGN-097): played from hiding, its "when you play me" fires
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-097" .hand
  let (s2, e) ← put s1 s.you "OGN-001" .base
  let mine := s2.control s.me s.bf0
  let hide ← activate mine s.me c 1 [s.bf0] ⟨0, [.fury]⟩
  let h ← (hide.zone (.player s.me .hidden)).head?
  let next := { hide with turn := hide.turn + 1 }
  let played ← activate next s.me h 2 [] ⟨0, []⟩ { pick := fun ts => ts.contains e }
  return played.mightNow e == some 3 && played.countIn s.me .base "OGN-097" == 1

-- Sprite Call (OGN-094) and Facebreaker (OGN-220), Hidden spells
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-094" .hand
  let a ← play s1 s.me c
  let sp ← a.firstOf s.me .base "TKN-Sprite" <|> (a.zone (.player s.me .base)).find? (fun u =>
    (a.cardDef? u).any (·.name == "Sprite"))
  return a.tired sp == some false && a.hasKw sp .temporary && a.mightNow sp == some 3
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-220" .hand
  let (s2, f) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-136" s.bf0
  let other := (s.battlefields.filter (· != s.bf0)).head?.getD ⟨0⟩
  let (s4, g) ← putAt s3 s.you "OGN-136" other
  let a ← play s4 s.me c
  let (t1, c2) ← put s s.me "OGN-220" .hand
  let (t2, f2) ← putAt t1 s.me "OGN-136" s.bf0
  let (t3, g2) ← putAt t2 s.you "OGN-136" other
  let b ← play t3 s.me c2
  let st (x : GameState) (u : ObjId) := (x.obj? u).map (·.stunned)
  return st a f == some true && st a e == some true && st a g == some false &&
    st b f2 == some true && st b g2 == some false

-- An ordinary ability of a card in my hand cannot be used (Iron Ballista, OGN-017); the ability to
-- play a hidden card cannot be used from the hand either
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-017" .hand
  let (s2, e) ← putAt s1 s.you "OGN-136" s.bf0
  let (s3, c) ← put s2 s.me "OGN-135" .hand
  return (activate s3 s.me g 1 [e]).isNone && (activate s3 s.me c 1 [] ⟨0, []⟩).isNone

-- A hidden spell used twice while its first use is still on the Chain has its effect once
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-057" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let mine := s2.control s.me s.bf0
  let hide ← activate mine s.me c 0 [s.bf0] ⟨0, [.fury]⟩
  let h ← (hide.zone (.player s.me .hidden)).head?
  let next := { hide with turn := hide.turn + 1 }
  match step 100 (next.rich s.me) ⟨.player s.me, .activate h 1 ⟨0, []⟩ [u]⟩ with
  | .ok (a1, _) =>
    let twice := match step 100 a1 ⟨.player s.me, .activate h 1 ⟨0, []⟩ [u]⟩ with
      | .ok (a2, _) => a2
      | .error _ => a1
    let done := settleChain {} 12 twice
    return done.kwAmount u .shield == 3 && done.countIn s.me .trash "OGN-057" == 1
  | .error _ => none

-- Vi (OGN-036): recycle 1 from my Trash: +1 Might this turn; with an empty Trash nothing happens
#guard t fun s => do
  let (s1, v) ← put s s.me "OGN-036" .base
  let (s2, _) ← put s1 s.me "OGN-136" .trash
  let trash (x : GameState) := (x.zone (.player s.me .trash)).length
  let a ← activate s2 s.me v 0
  -- with an empty Trash the ability cannot be used
  return trash a + 1 == trash s2 && a.mightNow v == (s2.mightNow v).map (· + 1) &&
    (activate (s1.setZone (.player s.me .trash) []) s.me v 0).isNone

-- Garbage Grabber (OGN-099): for 1 Energy and exhausting it, recycle 3 from my Trash and draw 1
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-099" .base
  let (s2, _) ← put s1 s.me "OGN-136" .trash
  let (s3, _) ← put s2 s.me "OGN-001" .trash
  let (s4, _) ← put s3 s.me "OGN-004" .trash
  let trash (x : GameState) := (x.zone (.player s.me .trash)).length
  let a ← activate s4 s.me g 0 [] ⟨1, []⟩
  let two := s3
  -- with fewer than 3 cards in the Trash the ability cannot be used
  return trash a == trash s4 - 3 && a.handN s.me == s4.handN s.me + 1 && a.tired g == some true &&
    (activate two s.me g 0 [] ⟨1, []⟩).isNone && (activate a s.me g 0 [] ⟨1, []⟩).isNone

-- Sett (OGN-164): buffed when played; spend the buff for +4 Might this turn (nothing without one)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-164" .hand
  let a ← play s1 s.me c
  let sett ← a.firstOf s.me .base "OGN-164"
  let spent ← activate a s.me sett 2
  let (t1, plain) ← put s s.me "OGN-164" .base
  return (a.obj? sett).map (·.buffed) == some true &&
    (spent.obj? sett).map (·.buffed) == some false &&
    spent.mightNow sett == (a.mightNow sett).map (· + 4 - 1) &&
    (activate t1 s.me plain 2).isNone

-- Forge of the Future (OGN-212): a Recruit token when played; kill it to recycle up to 4 cards
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-212" .hand
  let a ← play s1 s.me c
  let (t1, f) ← put s s.me "OGN-212" .base
  let (t2, _) ← put t1 s.me "OGN-136" .trash
  let (t3, _) ← put t2 s.you "OGN-001" .trash
  let k ← activate t3 s.me f 1
  let trashes (x : GameState) := (x.zone (.player s.me .trash)).length +
    (x.zone (.player s.you .trash)).length
  let deck (x : GameState) (p : PlayerId) := (x.zone (.player p .mainDeck)).length
  -- the Forge itself, my card and the opponent's card are recycled: three cards, up to four
  return a.countNamed s.me .base "Recruit" == 1 && trashes k == 0 &&
    deck k s.me == deck t3 s.me + 2 && deck k s.you == deck t3 s.you + 1

-- Monastery of Hirana (OGN-282) and Wildclaw Shaman (OGN-147): spend a buff
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-282"
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let buffed := s2.buff u
  let a ← fire buffed [.scored s.me bf true]
  let b ← fire s2 [.scored s.me bf true]
  let n ← fire buffed [.scored s.me bf true] { yes := false }
  return a.handN s.me == buffed.handN s.me + 1 && (a.obj? u).map (·.buffed) == some false &&
    b.handN s.me == s2.handN s.me && n.handN s.me == buffed.handN s.me
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-147" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let a ← play (s2.buff u) s.me c
  let w ← a.firstOf s.me .base "OGN-147"
  let b ← play s2 s.me c
  let wb ← b.firstOf s.me .base "OGN-147"
  return (a.obj? u).map (·.buffed) == some false && (a.obj? w).map (·.buffed) == some true &&
    a.tired w == some false && (b.obj? wb).map (·.buffed) == some false && b.tired wb == some true

-- Overt Operation (OGN-153): spend the buffs to ready the units, then buff all
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-153" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let start := (s3.buff u).tire u |>.tire v
  let a ← play start s.me c
  let b ← play start s.me c [] { yes := false }
  return a.tired u == some false && a.tired v == some true &&
    (a.obj? u).map (·.buffed) == some true && (a.obj? v).map (·.buffed) == some true &&
    b.tired u == some true && (b.obj? u).map (·.buffed) == some true

-- Sneaky Deckhand (OGN-176), Sai Scout (OGN-174): play to an open battlefield; Deadbloom Predator
-- (OGN-161): play to an occupied enemy battlefield
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-176" .hand
  let a ← activate s1 s.me c 0 [s.bf0] (payOf s1 c)
  let d ← a.firstOf s.me .base "OGN-176" <|> (a.zone .battlefieldZone).find? (fun u =>
    (a.cardDef? u).any (·.id == cid "OGN-176"))
  let owned := s1.control s.you s.bf0
  return (a.obj? d).bind (·.loc) == some s.bf0 &&
    (a.obj? s.bf0).bind (·.contested) == some s.me &&
    (activate owned s.me c 0 [s.bf0] (payOf owned c)).isNone
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-161" .hand
  let (s2, _) ← putAt s1 s.you "OGN-136" s.bf0
  let a ← activate s2 s.me c 0 [s.bf0] (payOf s2 c)
  return (a.zone .battlefieldZone).any (fun u => (a.cardDef? u).any (·.id == cid "OGN-161")) &&
    (activate s1 s.me c 0 [s.bf0] (payOf s1 c)).isNone

-- Sabotage (OGN-156): recycle a non-unit card of the opponent's hand; Mindsplitter (OGN-192):
-- the opponent discards a card I choose
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-156" .hand
  let (s2, sp) ← put s1 s.you "OGN-004" .hand
  let (s3, un) ← put s2 s.you "OGN-136" .hand
  let a ← play s3 s.me c
  return a.countIn s.you .hand "OGN-004" == 0 && a.countIn s.you .hand "OGN-136" ==
    s3.countIn s.you .hand "OGN-136" && (a.zone (.player s.you .mainDeck)).length ==
    (s3.zone (.player s.you .mainDeck)).length + 1 && (a.obj? sp).isNone && (a.obj? un).isSome
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-192" .hand
  let (s2, x) ← put s1 s.you "OGN-001" .hand
  let a ← play s2 s.me c [] { obj := fun o => o == x }
  return a.countIn s.you .hand "OGN-001" == s2.countIn s.you .hand "OGN-001" - 1 &&
    a.countIn s.you .trash "OGN-001" == 1 && a.handN s.me == s2.handN s.me - 1

-- Mushroom Pouch (OGN-101): draw 1 at the start of my Beginning Phase if I have a hidden card
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-101" .base
  let (s2, _) ← put s1 s.me "OGN-135" .hidden
  let a ← fire s2 [.phaseStarted s.me .beginning]
  let b ← fire s1 [.phaseStarted s.me .beginning]
  return a.handN s.me == s2.handN s.me + 1 && b.handN s.me == s1.handN s.me

-- Sona (OGN-073): ready 4 of my runes at the end of my turn while she is at a battlefield
#guard t fun s => do
  let (s1, _) ← putAt s s.me "OGN-073" s.bf0
  let (s2, r1) ← put s1 s.me "R1" .base
  let (s3, r2) ← put s2 s.me "R1" .base
  let tired := (s3.tire r1).tire r2
  let a ← fire tired [.phaseStarted s.me .ending]
  let (t1, _) ← put s s.me "OGN-073" .base
  let (t2, q1) ← put t1 s.me "R1" .base
  let b ← fire (t2.tire q1) [.phaseStarted s.me .ending]
  return a.tired r1 == some false && a.tired r2 == some false && b.tired q1 == some true

-- Ekko (OGN-110): when he dies, recycle him and ready my runes
#guard t fun s => do
  let (s1, x) ← put s s.me "OGN-110" .trash
  let (s2, r1) ← put s1 s.me "R1" .base
  let a ← fire (s2.tire r1) [.died x s.me]
  return a.tired r1 == some false && a.countIn s.me .trash "OGN-110" == 0 &&
    (a.zone (.player s.me .mainDeck)).length == (s2.zone (.player s.me .mainDeck)).length + 1

-- more edges of the cards of this batch: Sai Scout (Vision when played to a battlefield), Deadbloom
-- Predator (where it goes, and not to a battlefield with only my units), Sona (exactly 4 runes,
-- only in my turn), Mushroom Pouch (only my hidden cards, only my Beginning Phase), Ekko (only my
-- runes)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-174" .hand
  let deck (x : GameState) := x.zone (.player s.me .mainDeck)
  let top ← (deck s1).head?
  let a ← activate s1 s.me c 0 [s.bf0] (payOf s1 c)
  return (deck a).getLast? == some top && (deck a).length == (deck s1).length
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-161" .hand
  let (s2, _) ← putAt s1 s.you "OGN-136" s.bf0
  let (s3, _) ← putAt s1 s.me "OGN-136" s.bf0
  let a ← activate s2 s.me c 0 [s.bf0] (payOf s2 c)
  let d ← (a.zone .battlefieldZone).find? (fun u => (a.cardDef? u).any (·.id == cid "OGN-161"))
  return (a.obj? d).bind (·.loc) == some s.bf0 && (a.obj? d).map (·.exhausted) == some true &&
    (activate s3 s.me c 0 [s.bf0] (payOf s3 c)).isNone
#guard t fun s => do
  let (s1, _) ← putAt s s.me "OGN-073" s.bf0
  let rune (x : GameState × ObjId) := x.2
  let (s2, r1) ← put s1 s.me "R1" .base
  let (s3, r2) ← put s2 s.me "R1" .base
  let (s4, r3) ← put s3 s.me "R1" .base
  let (s5, r4) ← put s4 s.me "R1" .base
  let (s6, r5) ← put s5 s.me "R1" .base
  let all := [r1, r2, r3, r4, r5]
  let tired := all.foldl (fun x r => x.tire r) s6
  let a ← fire tired [.phaseStarted s.me .ending]
  let b ← fire tired [.phaseStarted s.you .ending]
  return (all.filter (fun r => a.tired r == some false)).length == 4 &&
    (all.filter (fun r => b.tired r == some false)).length == 0 && rune (s1, r1) == r1
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-101" .base
  let (s2, _) ← put s1 s.you "OGN-135" .hidden
  let a ← fire s2 [.phaseStarted s.me .beginning]
  let (t1, _) ← put s1 s.me "OGN-135" .hidden
  let b ← fire t1 [.phaseStarted s.you .beginning]
  return a.handN s.me == s2.handN s.me && b.handN s.me == t1.handN s.me
#guard t fun s => do
  let (s1, x) ← put s s.me "OGN-110" .trash
  let (s2, m) ← put s1 s.me "R1" .base
  let (s3, o) ← put s2 s.you "R1" .base
  let tired := (s3.tire m).tire o
  let a ← fire tired [.died x s.me]
  return a.tired m == some false && a.tired o == some true

-- Get Excited! (OGN-008): discard a card, and its Energy cost is dealt to a unit at a battlefield;
-- the discard sets off Scrapheap (OGN-182); with an empty hand nothing is dealt
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-008" .hand
  let (s2, x) ← put s1 s.me "OGN-051" .hand
  let (s3, e) ← putAt s2 s.you "OGN-116" s.bf0
  let a ← play s3 s.me c [e] { obj := fun o => o == x }
  let cost := ((s3.cardDef? x).bind (·.cost)).map (·.energy)
  let might := (s3.cardDef? x).bind (·.might)
  let (t1, sc) ← put s3 s.me "OGN-182" .hand
  let b ← play (t1.setZone (.player s.me .hand) [c, sc]) s.me c [e] { obj := fun o => o == sc }
  let empty ← play (s3.setZone (.player s.me .hand) [c]) s.me c [e]
  return (a.obj? e).map (·.damage) == cost && cost.isSome && cost.map Int.ofNat != might &&
    a.countIn s.me .trash "OGN-051" == 1 && b.handN s.me == 1 &&
    (empty.obj? e).map (·.damage) == some 0

-- Stacked Deck (OGN-183): one of the top 3 cards into my hand, the other two recycled
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-183" .hand
  let deck (x : GameState) := x.zone (.player s.me .mainDeck)
  let d := deck s1
  let a0 ← d[0]?
  let b0 ← d[1]?
  let c0 ← d[2]?
  let d4 ← d[3]?
  let r ← play s1 s.me c [] { obj := fun o => o == b0 }
  let tail2 := (deck r).reverse.take 2
  -- the played card leaves the hand and one card of the deck comes into it
  return r.handN s.me == s1.handN s.me && (deck r).length == d.length - 1 &&
    !(deck r).contains b0 &&
    (deck r).head? == some d4 && tail2.contains a0 && tail2.contains c0

-- Fading Memories (OGN-180): a unit at a battlefield or a gear gets Temporary
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-180" .hand
  let (s2, u) ← putAt s1 s.you "OGN-136" s.bf0
  let (s3, g) ← put s2 s.me "OGN-017" .base
  let a ← play s3 s.me c
  let b ← play s3 s.me c [] { yes := false }
  return a.hasKw u .temporary && !a.hasKw g .temporary && b.hasKw g .temporary &&
    !b.hasKw u .temporary

-- Pack of Wonders (OGN-181): exhaust it to return another friendly gear, unit or hidden card
#guard t fun s => do
  let (s1, p) ← put s s.me "OGN-181" .base
  let (s2, g) ← put s1 s.me "OGN-017" .base
  let (s3, _) ← put s2 s.me "OGN-135" .hidden
  let a ← activate s3 s.me p 0
  let b ← activate s3 s.me p 0 [] ⟨0, []⟩ { yes := false }
  return a.countIn s.me .hand "OGN-017" == s3.countIn s.me .hand "OGN-017" + 1 &&
    a.tired p == some true && a.countIn s.me .base "OGN-181" == 1 &&
    b.countIn s.me .hand "OGN-135" == s3.countIn s.me .hand "OGN-135" + 1 &&
    (b.obj? g).isSome

-- Hidden Blade (OGN-213): kill a unit at a battlefield; its controller draws 2
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-213" .hand
  let (s2, e) ← putAt s1 s.you "OGN-136" s.bf0
  let (s3, m) ← putAt s2 s.me "OGN-136" s.bf0
  let a ← play s3 s.me c [e]
  let b ← play s3 s.me c [m]
  return (a.obj? e).isNone && (b.obj? m).isNone &&
    a.handN s.you == s3.handN s.you + 2 && a.handN s.me == s3.handN s.me - 1 &&
    b.handN s.me == s3.handN s.me - 1 + 2 && b.handN s.you == s3.handN s.you

-- Reaver's Row (OGN-285): when I defend here, I may move a friendly unit here to my base
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-285"
  let (s2, u) ← putAt s1 s.me "OGN-136" bf
  let (s3, _) ← putAt s2 s.you "OGN-136" bf
  let a ← fire s3 [.combatStarted bf s.you]
  let n ← fire s3 [.combatStarted bf s.you] { yes := false }
  let att ← fire s3 [.combatStarted bf s.me]
  return (a.obj? u).bind (·.loc) == none && (n.obj? u).bind (·.loc) == some bf &&
    (att.obj? u).bind (·.loc) == some bf

-- Cost changes
/-- The Energy cost the card is played for now. -/
meta def energyNow (s : GameState) (p : PlayerId) (c : ObjId) : Option Nat :=
  (s.cardDef? c).bind fun d => (s.effCost p c d).map (·.energy)

/-- The printed Energy cost of the card. -/
meta def energyPrinted (s : GameState) (c : ObjId) : Option Nat :=
  ((s.cardDef? c).bind (·.cost)).map (·.energy)

-- Noxus Hopeful (OGN-012): 2 less after another card was played this turn (Legion)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-012" .hand
  let (s2, k) ← put s1 s.me "OGN-004" .hand
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let after ← play s3 s.me k [v]
  let played ← play after s.me c
  return energyNow s3 s.me c == energyPrinted s3 c &&
    energyNow after s.me c == (energyPrinted after c).map (· - 2) &&
    played.countIn s.me .base "OGN-012" == 1 &&
    (cast (after.rich s.me) s.me c ⟨energyPrinted after c |>.getD 0, []⟩).isNone

-- Rhasa the Sunderer (OGN-195): 1 less for each card in my Trash, not the opponent's
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-195" .hand
  let (s2, _) ← put s1 s.me "OGN-136" .trash
  let (s3, _) ← put s2 s.me "OGN-136" .trash
  let (s4, _) ← put s3 s.you "OGN-136" .trash
  let played ← play s3 s.me c
  return energyNow s1 s.me c == energyPrinted s1 c &&
    energyNow s3 s.me c == (energyPrinted s3 c).map (· - 2) &&
    energyNow s4 s.me c == energyNow s3 s.me c &&
    played.countIn s.me .base "OGN-195" == 1

-- Eager Apprentice (OGN-084): my spells cost 1 less (at least 1) while it is at a battlefield
#guard t fun s => do
  let (s1, k) ← put s s.me "OGN-093" .hand
  let (s2, k2) ← put s1 s.me "OGN-095" .hand
  let (base, _) ← put s2 s.me "OGN-084" .base
  let (hand, _) ← put s2 s.me "OGN-084" .hand
  let (at_, _) ← putAt s2 s.me "OGN-084" s.bf0
  let (theirs, _) ← putAt s2 s.you "OGN-084" s.bf0
  return energyNow base s.me k == energyPrinted s2 k &&
    energyNow hand s.me k == energyPrinted s2 k &&
    energyNow at_ s.me k == (energyPrinted s2 k).map (· - 1) &&
    energyNow at_ s.me k2 == energyPrinted s2 k2 && energyNow theirs s.me k == energyPrinted s2 k

-- Herald of Scales (OGN-140): my Dragons cost 2 less (at least 1), other units do not
#guard t fun s => do
  let (s1, dragon) ← put s s.me "OGN-001" .hand
  let (s2, other) ← put s1 s.me "OGN-136" .hand
  let (s3, _) ← put s2 s.me "OGN-140" .base
  return energyNow s3 s.me dragon == (energyPrinted s2 dragon).map (· - 2) &&
    energyNow s3 s.me other == energyPrinted s2 other

-- more on cost changes: only another card counts for Legion (not the opponent's, not itself played
-- earlier and returned to the hand), and a card cannot be played for its printed cost when it costs
-- less
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-012" .hand
  let (s2, x) ← put s1 s.you "OGN-136" .hand
  let theirs := s2.modObj x (fun o => { o with playedTurn := some s2.turn })
  let (t1, y) ← put s1 s.me "OGN-136" .hand
  let mine := t1.modObj y (fun o => { o with playedTurn := some t1.turn })
  let own := s1.modObj c (fun o => { o with playedTurn := some s1.turn })
  return energyNow theirs s.me c == energyPrinted s1 c &&
    energyNow mine s.me c == (energyPrinted s1 c).map (· - 2) &&
    energyNow own s.me c == energyPrinted s1 c &&
    (cast (s1.rich s.me) s.me c ⟨(energyPrinted s1 c).getD 0 - 2, []⟩).isNone
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-195" .hand
  let trash (x : GameState) (n : Nat) : Option GameState :=
    (List.range n).foldl (fun acc _ => acc.bind fun y => (put y s.me "OGN-136" .trash).map (·.1))
      (some x)
  let ten ← trash s1 10
  let d ← s1.cardDef? c
  return energyNow ten s.me c == some 0 &&
    (cast (ten.rich s.me) s.me c (payOf s1 c)).isNone && (play ten s.me c).isSome &&
    (ten.effCost s.me c d).isSome

-- Meditation (OGN-048): exhaust a ready friendly unit to draw 2, or else draw 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-048" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let yes ← play s2 s.me c [] { yes := true }
  let no ← play s2 s.me c [] { yes := false }
  let tired ← play (s2.tire u) s.me c [] { yes := true }
  let alone ← play s1 s.me c [] { yes := true }
  return yes.tired u == some true && yes.handN s.me == s2.handN s.me + 1 &&
    no.tired u == some false && no.handN s.me == s2.handN s.me &&
    tired.handN s.me == s2.handN s.me && alone.handN s.me == s2.handN s.me

-- Thousand-Tailed Watcher (OGN-116): enemy units get -3 Might this turn, to a minimum of 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-116" .hand
  let (s2, big) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, small) ← putAt s2 s.you "OGN-136" s.bf0
  let (s4, mine) ← put s3 s.me "OGN-001" .base
  let a ← play s4 s.me c
  return a.mightNow big == some 2 && a.mightNow small == some 1 && a.mightNow mine == some 5

-- Kog'Maw, Caustic (OGN-190): when it dies, 4 damage to every unit at its battlefield
-- (Challenge: Kog'Maw deals 1 to the unit of Might 7 and takes 7)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-128" .hand
  let (s2, k) ← putAt s1 s.me "OGN-190" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-116" s.bf0
  let (s4, f) ← putAt s3 s.me "OGN-001" s.bf0
  let (s5, far) ← put s4 s.you "OGN-001" .base
  let a ← play s5 s.me c [k, e]
  return (a.obj? e).map (·.damage) == some 5 && (a.obj? f).map (·.damage) == some 4 &&
    (a.obj? far).map (·.damage) == some 0 && a.countIn s.me .trash "OGN-190" == 1

-- Sigil of the Storm (OGN-287): when I conquer here, recycle one of my runes (to the Rune Deck)
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-287"
  let isRune (x : GameState) (r : ObjId) := (x.cardDef? r).any (·.hasType .rune)
  let runes := (s1.zone (.player s.me .base)).filter (isRune s1)
  let deck := (s1.zone (.player s.me .runeDeck)).length
  let a ← fire s1 [.scored s.me bf true]
  let b ← fire s1 [.scored s.you bf true]
  let here := (a.zone (.player s.me .base)).filter (isRune a)
  return !runes.isEmpty && here.length + 1 == runes.length &&
    (a.zone (.player s.me .runeDeck)).length == deck + 1 &&
    (b.zone (.player s.me .runeDeck)).length == deck

-- Party Favors (OGN-071): the opponent chooses Cards (both draw 1) or Runes (both channel 1
-- exhausted)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-071" .hand
  let cards ← play s1 s.me c [] { yes := true }
  let runes ← play s1 s.me c [] { yes := false }
  let runeN (x : GameState) (p : PlayerId) :=
    ((x.zone (.player p .base)).filter (fun r => (x.cardDef? r).any (·.hasType .rune))).length
  return cards.handN s.me == s1.handN s.me && cards.handN s.you == s1.handN s.you + 1 &&
    runeN cards s.me == runeN s1 s.me &&
    runes.handN s.me == s1.handN s.me - 1 && runes.handN s.you == s1.handN s.you &&
    runeN runes s.me == runeN s1 s.me + 1 && runeN runes s.you == runeN s1 s.you + 1

-- Soulgorger (OGN-196), The Harrowing (OGN-198), Spectral Matron (OGN-226), Portal Rescue
-- (OGN-102): play a unit from the Trash, or a unit on the board, for free
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-196" .hand
  let (s2, _) ← put s1 s.me "OGN-136" .trash
  let a ← play s2 s.me c [] { yes := true }
  let b ← play s2 s.me c [] { yes := false }
  let (t1, h) ← put s s.me "OGN-198" .hand
  let (t2, _) ← put t1 s.me "OGN-136" .trash
  let (t3, _) ← put t2 s.you "OGN-136" .trash
  let d ← play t3 s.me h
  return a.countIn s.me .base "OGN-136" == 1 && a.countIn s.me .trash "OGN-136" == 0 &&
    b.countIn s.me .base "OGN-136" == 0 && b.countIn s.me .trash "OGN-136" == 1 &&
    d.countIn s.me .base "OGN-136" == 1 && d.countIn s.you .trash "OGN-136" == 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-226" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .trash
  let (s3, _) ← put s2 s.me "OGN-150" .trash
  let nothing ← play s3 s.me c
  let (s4, _) ← put s3 s.me "OGN-136" .trash
  let a ← play s4 s.me c
  return nothing.countIn s.me .trash "OGN-001" == 1 &&
    nothing.countIn s.me .trash "OGN-150" == 1 &&
    a.countIn s.me .base "OGN-136" == 1 && a.countIn s.me .trash "OGN-001" == 1 &&
    a.countIn s.me .trash "OGN-150" == 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-102" .hand
  let (s2, u) ← putAt s1 s.me "OGN-001" s.bf0
  let hurt := (s2.modObj u (fun o => { o with damage := 2 })).buff u
  let a ← play hurt s.me c
  let w ← a.firstOf s.me .base "OGN-001"
  -- a unit at the Base is played again where it is
  let (t1, v) ← put s1 s.me "OGN-001" .base
  let b ← play ((t1.modObj v (fun o => { o with damage := 2 })).buff v) s.me c
  let x ← b.firstOf s.me .base "OGN-001"
  return a.where? w == some (.player s.me .base) && a.tired w == some true &&
    (a.obj? w).map (·.damage) == some 0 && (a.obj? w).map (·.buffed) == some false &&
    (a.obj? w).map (·.loc) == some none && s2.where? u == some .battlefieldZone &&
    a.countIn s.me .base "OGN-001" == 1 &&
    b.tired x == some true && (b.obj? x).map (·.damage) == some 0 &&
    b.countIn s.me .base "OGN-001" == 1
-- Soulgorger and Spectral Matron put the unit in exhausted
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-196" .hand
  let (s2, _) ← put s1 s.me "OGN-136" .trash
  let a ← play s2 s.me c
  let w ← a.firstOf s.me .base "OGN-136"
  let (t1, m) ← put s s.me "OGN-226" .hand
  let (t2, _) ← put t1 s.me "OGN-136" .trash
  let b ← play t2 s.me m
  let y ← b.firstOf s.me .base "OGN-136"
  return a.tired w == some true && b.tired y == some true

-- Turn effects
/-- The ready units of the player at the Base. -/
meta def readyUnits (x : GameState) (p : PlayerId) : Nat :=
  ((x.zone (.player p .base)).filter (fun u =>
    x.tired u == some false && (x.cardDef? u).any (·.hasType .unit))).length

-- Sun Disc (OGN-021): with another card played this turn, the next unit enters ready
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-021" .base
  let (s2, other) ← put s1 s.me "OGN-136" .base
  let (s3, a) ← put s2 s.me "OGN-136" .hand
  let (s4, b) ← put s3 s.me "OGN-136" .hand
  let played := s4.modObj other (fun o => { o with playedTurn := some s4.turn })
  let on ← activate played s.me g 0
  let first ← play on s.me a
  let second ← play first s.me b
  return readyUnits first s.me == readyUnits on s.me + 1 &&
    readyUnits second s.me == readyUnits first s.me && (activate s4 s.me g 0).isNone

-- Confront (OGN-129): the units played this turn enter ready, and draw 1
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-129" .hand
  let (s2, a) ← put s1 s.me "OGN-136" .hand
  let (s3, b) ← put s2 s.me "OGN-136" .hand
  let on ← play s3 s.me c
  let first ← play on s.me a
  let second ← play first s.me b
  let (t1, d) ← put s2 s.me "OGN-136" .hand
  let plain ← play t1 s.me d
  return readyUnits second s.me == readyUnits on s.me + 2 && on.handN s.me == s3.handN s.me &&
    readyUnits plain s.me == readyUnits t1 s.me

-- Raging Firebrand (OGN-031): the next spell this turn costs 5 less, only that one, this turn
-- (The Harrowing costs 6)
#guard t fun s => do
  let (s1, f) ← put s s.me "OGN-031" .hand
  let (s2, sp) ← put s1 s.me "OGN-198" .hand
  let (s3, sq) ← put s2 s.me "OGN-198" .hand
  let on ← play s3 s.me f
  let cut (x : GameState) (p : PlayerId) (c : ObjId) : Option Nat :=
    (x.cardDef? c).bind (fun d => (x.effCost p c d).map (·.energy))
  let cheap ← cast (on.rich s.me) s.me sp ⟨1, [.chaos, .chaos]⟩
  let next := { on with turn := on.turn + 1 }
  return cut on s.me sp == some 1 && cut s3 s.me sp == some 6 && cut cheap s.me sq == some 6 &&
    cut on s.you sp == some 6 && cut next s.me sp == some 6

-- ... a card played earlier that is played again counts as the next card: Sun Disc
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-021" .base
  let (s2, other) ← put s1 s.me "OGN-136" .base
  let (s3, again) ← put s2 s.me "OGN-136" .hand
  let (s4, b) ← put s3 s.me "OGN-136" .hand
  let marked := s4.modObj other (fun o => { o with playedTurn := some s4.turn })
  let old := marked.modObj again
    (fun o => { o with playedTurn := some s4.turn, playedStamp := some 0 })
  let on ← activate old s.me g 0
  let x ← play on s.me again
  let y ← play x s.me b
  return readyUnits x s.me == readyUnits on s.me + 1 && readyUnits y s.me == readyUnits x s.me

-- Unyielding Spirit (OGN-145): spells and abilities deal no damage this turn (Hextech Ray deals 3)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-145" .hand
  let (s2, h) ← put s1 s.me "OGN-009" .hand
  let (s3, mine) ← putAt s2 s.me "OGN-001" s.bf0
  let on ← play s3 s.me c
  let hit ← play (s3.addTurnFx s.me .preventEffectDamage) s.me h [mine]
  let free ← play s3 s.me h [mine]
  return on.turnFx.length == 1 && s3.turnFx.isEmpty && on.damageOff && !s3.damageOff &&
    (hit.obj? mine).map (·.damage) == some 0 && (free.obj? mine).map (·.damage) == some 3

-- Counters
/-- The player passes priority. -/
meta def passBy (s : GameState) (p : PlayerId) : Option GameState :=
  match step 100 s ⟨.player p, .pass⟩ with
  | .ok (s1, _) => some s1
  | .error _ => none

/-- The player plays the card for its cost with the targets, and the Chain stays. -/
meta def castOpen (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId) :
    Option GameState :=
  match step 100 (s.rich p) ⟨.player p, .playCard c (payOf s c) ts⟩ with
  | .ok (x, _) => some x
  | .error _ => none

-- Wind Wall (OGN-064): counter a spell on the Chain (Confront would draw 1)
#guard t fun s => do
  let (s1, conf) ← put s s.me "OGN-129" .hand
  let (s2, wind) ← put s1 s.you "OGN-064" .hand
  let on ← passBy (← castStop s2 s.me conf) s.me
  let tgt ← (on.zone .chain).head?
  let after ← play on s.you wind [tgt]
  let plain ← play s2 s.me conf
  return after.countIn s.me .trash "OGN-129" == 1 && after.turnFx.isEmpty &&
    after.handN s.me == s2.handN s.me - 1 && after.countIn s.you .trash "OGN-064" == 1 &&
    plain.turnFx.length == 1 && (on.zone .chain).length == 1
-- Defy (OGN-045): only a spell that costs at most 4 Energy and 1 Power (The Harrowing costs 2
-- Power, Falling Comet 5 Energy)
#guard t fun s => do
  let (s1, conf) ← put s s.me "OGN-129" .hand
  let (s2, big) ← put s1 s.me "OGN-198" .hand
  let (s3, defy) ← put s2 s.you "OGN-045" .hand
  let (s4, comet) ← put s3 s.me "OGN-085" .hand
  let (s4b, star) ← put s4 s.me "OGN-029" .hand
  let (s5, u) ← putAt s4b s.you "OGN-136" s.bf0
  let small ← passBy (← castStop s5 s.me conf) s.me
  let large ← passBy (← castStop s5 s.me big) s.me
  let pricey ← passBy (← castOpen s5 s.me comet [u]) s.me
  let twoPower ← passBy (← castOpen s5 s.me star [u, u]) s.me
  let a ← play small s.you defy [← (small.zone .chain).head?]
  let refused3 := play twoPower s.you defy [← (twoPower.zone .chain).head?]
  let refused := play large s.you defy [← (large.zone .chain).head?]
  let refused2 := play pricey s.you defy [← (pricey.zone .chain).head?]
  return a.countIn s.me .trash "OGN-129" == 1 && a.turnFx.isEmpty && refused.isNone &&
    refused2.isNone && refused3.isNone

-- Stormbringer, Volibear (OGN-250): damage equal to my unit's Might to the enemy units at a
-- battlefield, then my unit moves there
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-250" .hand
  let (s2, mine) ← put s1 s.me "OGN-001" .base
  let (s3, e1) ← putAt s2 s.you "OGN-136" s.bf0
  let (s4, e2) ← putAt s3 s.you "OGN-116" s.bf0
  let (s5, f) ← putAt s4 s.me "OGN-136" s.bf0
  let a ← play s5 s.me c [mine, s.bf0]
  return (a.obj? e1).isNone && (a.obj? e2).map (·.damage) == some 5 &&
    (a.obj? f).map (·.damage) == some 0 && (a.obj? mine).map (·.loc) == some (some s.bf0)

-- Counters need a spell on the Chain, and a spell does not counter itself; Stormbringer needs a
-- unit of mine in the Base and takes a Battlefield
#guard t fun s => do
  let (s1, wind) ← put s s.me "OGN-064" .hand
  let (s2, defy) ← put s1 s.me "OGN-045" .hand
  let (s3, conf) ← put s2 s.me "OGN-129" .hand
  let alone := play s3 s.me wind [conf]
  let selfTarget := play s3 s.me wind [wind]
  let nothing := play s3 s.me defy []
  let (t1, c) ← put s s.me "OGN-250" .hand
  let (t2, mine) ← put t1 s.me "OGN-001" .base
  let (t3, away) ← putAt t2 s.me "OGN-001" s.bf0
  let (t4, foe) ← put t3 s.you "OGN-001" .base
  let onBf := play t4 s.me c [away, s.bf0]
  let enemy := play t4 s.me c [foe, s.bf0]
  let fine ← play t4 s.me c [mine, s.bf0]
  return alone.isNone && selfTarget.isNone && nothing.isNone && onBf.isNone && enemy.isNone &&
    (fine.obj? foe).map (·.damage) == some 0

-- Find Your Center (OGN-047): costs 2 less when an opponent is within 3 points of the Victory
-- Score; draw 1 and channel 1 exhausted
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-047" .hand
  let vs := s.config.mode.victoryScore
  let near := s1.gainPoints s.you (vs - 3)
  let far := s1.gainPoints s.you (vs - 4)
  let mine := s1.gainPoints s.me (vs - 3)
  let a ← play near s.me c
  let runes (x : GameState) :=
    (x.zone (.player s.me .base)).filter (fun u => (x.cardDef? u).any (·.hasType .rune))
  let runeN (x : GameState) := (runes x).length
  let newRune := (runes a).filter (fun u => !(runes near).contains u)
  return energyNow near s.me c == (energyPrinted s1 c).map (· - 2) &&
    energyNow far s.me c == energyPrinted s1 c && energyNow mine s.me c == energyPrinted s1 c &&
    a.handN s.me == near.handN s.me && runeN a == runeN near + 1 &&
    newRune.all (fun u => a.tired u == some true) && newRune.length == 1 &&
    (cast (near.rich s.me) s.me c ⟨energyPrinted s1 c |>.getD 0, []⟩).isNone

-- Magma Wurm (OGN-011): my other units enter ready; the opponent's units and the Wurm itself do not
#guard t fun s => do
  let (s1, w) ← put s s.me "OGN-011" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .hand
  let (s3, v) ← put s2 s.you "OGN-136" .hand
  let (s4, _) ← put s3 s.me "OGN-011" .base
  let first ← play s4 s.me u
  let foe := (s4.cardDef? v).map (fun d => s4.readyNow s.you v d)
  let self ← play s2 s.me w
  return readyUnits first s.me == readyUnits s4 s.me + 1 &&
    foe == some false &&
    readyUnits self s.me == readyUnits s2 s.me

-- Leona, Zealot (OGN-079): enters ready when an opponent is within 3 points of the Victory Score;
-- stunned enemy units at her battlefield have -8 Might, to a minimum of 1
#guard t fun s => do
  let (s1, l) ← put s s.me "OGN-079" .hand
  let vs := s.config.mode.victoryScore
  let a ← play (s1.gainPoints s.you (vs - 3)) s.me l
  let b ← play s1 s.me l
  let (t1, _) ← putAt s s.me "OGN-079" s.bf0
  let (t2, big) ← putAt t1 s.you "OGN-116" s.bf0
  let (t3, small) ← putAt t2 s.you "OGN-136" s.bf0
  let (t4, far) ← put t3 s.you "OGN-116" .base
  let stun (x : GameState) (u : ObjId) := x.modObj u (fun o => { o with stunned := true })
  let st := stun (stun (stun t4 big) small) far
  return readyUnits a s.me == readyUnits s1 s.me + 1 && readyUnits b s.me == readyUnits s1 s.me &&
    st.mightNow big == some 1 && st.mightNow small == some 1 && st.mightNow far == some 7 &&
    t4.mightNow big == some 7

-- ... the Victory Score the passive abilities leave is the one it reads (Aspirant's Climb adds 1),
-- and a Magma Wurm helps a second Wurm that is played, not itself
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-047" .hand
  let (s2, _) ← put s1 s.me "OGN-276" .base
  let vs := s.config.mode.victoryScore
  return energyNow (s2.gainPoints s.you (vs - 3)) s.me c == energyPrinted s2 c &&
    energyNow (s2.gainPoints s.you (vs - 2)) s.me c == (energyPrinted s2 c).map (· - 2)
#guard t fun s => do
  let (s1, w) ← put s s.me "OGN-011" .hand
  let (s2, _) ← put s1 s.me "OGN-011" .base
  let a ← play s2 s.me w
  let (t1, u) ← put s s.me "OGN-136" .hand
  let (t2, e) ← put t1 s.you "OGN-011" .base
  let enemyWurm := (t2.cardDef? u).map (fun d => t2.readyNow s.me u d)
  return readyUnits a s.me == readyUnits s2 s.me + 1 && enemyWurm == some false && e == e

-- Sky Splitter (OGN-014): costs less by the highest Might among my units (not below 0); 5 damage
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-014" .hand
  let (s2, _) ← put s1 s.me "OGN-136" .base
  let (s3, _) ← put s2 s.me "OGN-001" .base
  let (s4, _) ← put s3 s.me "OGN-116" .base
  let (s5, _) ← put s4 s.you "OGN-116" .base
  let (s6, e) ← putAt s3 s.you "OGN-116" s.bf0
  let (s7, _) ← put s2 s.you "OGN-001" .base
  let a ← play s6 s.me c [e]
  return energyNow s1 s.me c == energyPrinted s1 c &&
    energyNow s2 s.me c == (energyPrinted s1 c).map (· - 2) &&
    energyNow s3 s.me c == (energyPrinted s1 c).map (· - 5) &&
    energyNow s4 s.me c == some 1 && energyNow s5 s.me c == some 1 &&
    energyNow s7 s.me c == (energyPrinted s1 c).map (· - 2) &&
    (a.obj? e).map (·.damage) == some 5

-- Darius, Trifarian (OGN-027): when I play my second card in a turn, +2 Might this turn and ready
#guard t fun s => do
  let (s1, d) ← put s s.me "OGN-027" .base
  let (s2, a) ← put (s1.tire d) s.me "OGN-136" .hand
  let (s3, b) ← put s2 s.me "OGN-136" .hand
  let (s4, c) ← put s3 s.me "OGN-136" .hand
  let one ← play s4 s.me a
  let two ← play one s.me b
  let three ← play two s.me c
  return one.tired d == some true && one.mightNow d == some 6 &&
    two.tired d == some false && two.mightNow d == some 8 && three.mightNow d == some 8

-- Stand United (OGN-053): buff a friendly unit; buffs give friendly units +1 Might more this turn
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-053" .hand
  let (s2, mine) ← put s1 s.me "OGN-136" .base
  let (s3, old) ← put s2 s.me "OGN-136" .base
  let (s4, foe) ← put s3 s.you "OGN-136" .base
  let plain := (s4.buff old).buff foe
  let a ← play (s4.buff old |>.buff foe) s.me c [mine]
  return plain.mightNow old == some 3 && a.mightNow mine == some 4 && a.mightNow old == some 4 &&
    a.mightNow foe == some 3

-- ... the extra Might is the same for every read of Might (the filters too), it counts for a unit
-- that is buffed later, and two such effects add up
#guard t fun s => do
  let (s1, u) ← put s s.me "OGN-136" .base
  let (s2, foe) ← put s1 s.you "OGN-136" .base
  let on := s2.addTurnFx s.me .buffsExtraMight
  let two := on.addTurnFx s.me .buffsExtraMight
  let le3 (x : GameState) (id : ObjId) :=
    Filter.holds x id {} id (.might .le (.const 3))
  return (on.buff u).mightNow u == some 4 && (two.buff u).mightNow u == some 5 &&
    ((on.buff foe).buff u).mightNow foe == some 3 && on.mightNow u == some 2 &&
    le3 (s2.buff u) u == some true && le3 (on.buff u) u == some false &&
    le3 (two.buff u) u == some false

-- Albus Ferros (OGN-230): when I play him, I may spend any number of buffs, a rune channeled
-- exhausted for each
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-230" .hand
  let (s2, a) ← put s1 s.me "OGN-136" .base
  let (s3, b) ← put s2 s.me "OGN-136" .base
  let (s4, e) ← put s3 s.you "OGN-136" .base
  let buffed := ((s4.buff a).buff b).buff e
  let yes ← play buffed s.me c [] { yes := true }
  let no ← play buffed s.me c [] { yes := false }
  let runeN (x : GameState) :=
    ((x.zone (.player s.me .base)).filter (fun u => (x.cardDef? u).any (·.hasType .rune))).length
  return (yes.obj? a).map (·.buffed) == some false && (yes.obj? b).map (·.buffed) == some false &&
    (yes.obj? e).map (·.buffed) == some true && runeN yes == runeN buffed + 2 &&
    (no.obj? a).map (·.buffed) == some true && runeN no == runeN buffed &&
    ((yes.zone (.player s.me .base)).filter (fun u => (yes.cardDef? u).any (·.hasType .rune) &&
      !(buffed.zone (.player s.me .base)).contains u)).all (fun u => yes.tired u == some true)

-- The Candlelit Sanctum (OGN-291): when I conquer here, I may recycle either of the top two cards
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-291"
  let deck := s1.zone (.player s.me .mainDeck)
  let yes ← fire s1 [.scored s.me bf true] { yes := true }
  let no ← fire s1 [.scored s.me bf true] { yes := false }
  let other ← fire s1 [.scored s.you bf true] { yes := true }
  let held ← fire s1 [.scored s.me bf false] { yes := true }
  return deck.length > 3 && (no.zone (.player s.me .mainDeck)) == deck &&
    (yes.zone (.player s.me .mainDeck)).take (deck.length - 2) == deck.drop 2 &&
    ((yes.zone (.player s.me .mainDeck)).drop (deck.length - 2)).length == 2 &&
    (other.zone (.player s.me .mainDeck)) == deck &&
    (other.zone (.player s.you .mainDeck)) != s1.zone (.player s.you .mainDeck) &&
    (held.zone (.player s.me .mainDeck)) == deck

-- Fortified Position (OGN-279): when I defend here, a unit gains Shield 2
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-279"
  let (s2, u) ← putAt s1 s.me "OGN-136" bf
  let a ← fire s2 [.combatStarted bf s.you]
  let att ← fire s2 [.combatStarted bf s.me]
  let has (x : GameState) := (x.grantedKws u).any (fun k => k.keyword == .shield)
  return has a && !has att && !has s2

-- Paying as an effect resolves. Flame Chompers (OGN-006): when it is discarded, I may pay Fury to
-- play it (with no Fury in the Pool, or if I decline, it stays in the Trash)
#guard t fun s => do
  let (s1, x) ← put s s.me "OGN-006" .trash
  let funded := s1.fund s.me 0 (fury := 1)
  let a ← fire funded [.discarded s.me x true] { yes := true }
  let no ← fire funded [.discarded s.me x true] { yes := false }
  let broke ← fire (s1.fund s.me 5) [.discarded s.me x true] { yes := true }
  return a.countIn s.me .base "OGN-006" == 1 && (a.poolOf s.me).fury == 0 &&
    no.countIn s.me .trash "OGN-006" == 1 && (no.poolOf s.me).fury == 1 &&
    broke.countIn s.me .trash "OGN-006" == 1 && (broke.poolOf s.me).energy == 5

-- Ava Achiever (OGN-107): when I attack, I may pay Mind to play a card with Hidden from my hand
-- here
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let (s2, _) ← putAt s1 s.me "OGN-107" bf
  let (s3, _) ← put s2 s.me "OGN-199" .hand
  let (s4, _) ← put s3 s.me "OGN-136" .hand
  let funded := s4.fund s.me 0 (mind := 1)
  let a ← fire funded [.combatStarted bf s.me] { yes := true }
  let no ← fire funded [.combatStarted bf s.me] { yes := false }
  let defend ← fire funded [.combatStarted bf s.you] { yes := true }
  let empty ← fire s4 [.combatStarted bf s.me] { yes := true }
  let (u1, _) ← putAt s1 s.me "OGN-107" bf
  let (u2, _) ← put u1 s.me "OGN-057" .hand
  let spellOnly ← fire (u2.fund s.me 0 (mind := 1)) [.combatStarted bf s.me] { yes := true }
  let (v1, _) ← put u1 s.me "OGN-136" .hand
  let noHidden ← fire (v1.fund s.me 0 (mind := 1)) [.combatStarted bf s.me] { yes := true }
  let there (x : GameState) :=
    ((x.zone .battlefieldZone).filter (fun u => (x.cardDef? u).any (·.id == cid "OGN-199") &&
      (x.obj? u).any (·.loc == some bf))).length
  return there a == 1 && (a.poolOf s.me).mind == 0 && a.countIn s.me .hand "OGN-136" == 1 &&
    a.countIn s.me .hand "OGN-199" == 0 && there no == 0 && (no.poolOf s.me).mind == 1 &&
    there defend == 0 && there empty == 0 && (spellOnly.poolOf s.me).mind == 1 &&
    spellOnly.countIn s.me .hand "OGN-057" == 1 && (noHidden.poolOf s.me).mind == 1

-- Vayne, Hunter (OGN-035): enters ready if an opponent controls a battlefield; when I conquer, I
-- may pay 1 Energy to return her to my hand
#guard t fun s => do
  let (s1, v) ← put s s.me "OGN-035" .hand
  let theirs := s1.modObj s.bf0 (fun o => { o with control := some s.you })
  let mine := s1.modObj s.bf0 (fun o => { o with control := some s.me })
  let a ← play theirs s.me v
  let b ← play mine s.me v
  let c ← play s1 s.me v
  let (t1, u) ← putAt s s.me "OGN-035" s.bf0
  let yes ← fire (t1.fund s.me 1) [.scored s.me s.bf0 true] { yes := true }
  let no ← fire (t1.fund s.me 1) [.scored s.me s.bf0 true] { yes := false }
  let broke ← fire (t1.fund s.me 0) [.scored s.me s.bf0 true] { yes := true }
  return readyUnits a s.me == readyUnits theirs s.me + 1 &&
    readyUnits b s.me == readyUnits mine s.me && readyUnits c s.me == readyUnits s1 s.me &&
    yes.countIn s.me .hand "OGN-035" == 1 &&
    (yes.poolOf s.me).energy == 0 && no.countIn s.me .hand "OGN-035" == 0 &&
    (no.poolOf s.me).energy == 1 && (no.obj? u).map (·.loc) == some (some s.bf0) &&
    broke.countIn s.me .hand "OGN-035" == 0 && (broke.obj? u).map (·.loc) == some (some s.bf0)

-- Standard Moves counted in the turn. Yasuo, Windrider (OGN-205): the third time he moves in a
-- turn, I score 1 point
/-- Move the unit by a Standard Move; the state and the events. -/
meta def moveTo (s : GameState) (p : PlayerId) (u : ObjId) (d : MoveDest) :
    Option (GameState × List Event) :=
  applyMove s p u d

#guard t fun s => do
  let bf1 ← s.battlefields[1]?
  let (s1, y) ← put s s.me "OGN-205" .base
  let (a, _) ← moveTo s1 s.me y (.battlefield s.bf0)
  let (b, _) ← moveTo a s.me y (.battlefield bf1)
  let (c, ev) ← moveTo b s.me y (.battlefield s.bf0)
  let (d, ev4) ← moveTo c s.me y (.battlefield bf1)
  let (_, ev2) ← moveTo a s.me y (.battlefield bf1)
  let third ← fire c ev
  let second ← fire b ev2
  let fourth ← fire d ev4
  return third.pointsOf s.me == c.pointsOf s.me + 1 && second.pointsOf s.me == b.pointsOf s.me &&
    fourth.pointsOf s.me == d.pointsOf s.me && (c.obj? y).map (·.moves) == some 3

-- Kayn, Unleashed (OGN-189): if I have moved twice this turn, I take no damage
#guard t fun s => do
  let bf1 ← s.battlefields[1]?
  let (s1, k) ← put s s.me "OGN-189" .base
  let (a, _) ← moveTo s1 s.me k (.battlefield s.bf0)
  let (b, _) ← moveTo a s.me k (.battlefield bf1)
  let hit (x : GameState) := ((dealObj 3 x k).1.obj? k).map (·.damage)
  let next := { b with turn := b.turn + 1 }
  return hit s1 == some 3 && hit a == some 3 && hit b == some 0 && hit next == some 3

-- ... a move by an effect counts too, and a unit that leaves play starts again
#guard t fun s => do
  let bf1 ← s.battlefields[1]?
  let (s1, y) ← put s s.me "OGN-205" .base
  let (a, _) ← moveTo s1 s.me y (.battlefield s.bf0)
  let (b, _) ← moveTo a s.me y (.battlefield bf1)
  let (c, ev) := sendToBf s.bf0 b y
  let third ← fire c ev
  let (back, id') ← moveObj b y (.player s.me .hand)
  return third.pointsOf s.me == c.pointsOf s.me + 1 && (c.obj? y).map (·.moves) == some 3 &&
    (back.obj? id').map (·.moves) == some 0

-- Additional costs, paid as the card is played: the cost they save is given back to the Pool
-- Brazen Buccaneer (OGN-002): discard a card, 2 Energy back
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-002" .hand
  let (s2, _) ← put s1 s.me "OGN-136" .hand
  let yes ← play s2 s.me c [] { yes := true }
  let no ← play s2 s.me c [] { yes := false }
  let alone ← play (s1.setZone (.player s.me .hand) [c]) s.me c [] { yes := true }
  return yes.countIn s.me .trash "OGN-136" == 1 && (yes.poolOf s.me).energy == 12 - 6 + 2 &&
    no.countIn s.me .hand "OGN-136" == 1 && (no.poolOf s.me).energy == 12 - 6 &&
    (alone.poolOf s.me).energy == 12 - 6

-- Wallop (OGN-146) and Call to Glory (OGN-207): spend a buff, and the spell costs nothing
#guard t fun s => do
  let (s1, w) ← put s s.me "OGN-146" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let buffed := s3.buff v |>.tire u
  let yes ← play buffed s.me w [u] { yes := true }
  let no ← play buffed s.me w [u] { yes := false }
  let none_ ← play (s3.tire u) s.me w [u] { yes := true }
  let (t1, g) ← put s s.me "OGN-207" .hand
  let (t2, a) ← put t1 s.me "OGN-136" .base
  let (t3, b) ← put t2 s.me "OGN-136" .base
  let glory ← play (t3.buff b) s.me g [a] { yes := true }
  let paid ← play t3 s.me g [a] { yes := true }
  return yes.tired u == some false && (yes.obj? v).map (·.buffed) == some false &&
    (yes.poolOf s.me).energy == 12 && (no.poolOf s.me).energy == 10 &&
    (no.obj? v).map (·.buffed) == some true && (none_.poolOf s.me).energy == 10 &&
    (glory.poolOf s.me).energy == 12 && glory.mightNow a == some 5 &&
    (paid.poolOf s.me).energy == 9

-- Kraken Hunter (OGN-150): spend buffs, 1 Body each back; Cruel Patron (OGN-208): kill a friendly
-- unit; Commander Ledros (OGN-231): kill units, 1 Order each back
#guard t fun s => do
  let (s1, k) ← put s s.me "OGN-150" .hand
  let (s2, a) ← put s1 s.me "OGN-136" .base
  let (s3, b) ← put s2 s.me "OGN-136" .base
  let buffed := (s3.buff a).buff b
  let yes ← play buffed s.me k [] { yes := true }
  let no ← play buffed s.me k [] { yes := false }
  let (t1, p) ← put s s.me "OGN-208" .hand
  let (t2, u) ← put t1 s.me "OGN-136" .base
  let sac ← play t2 s.me p
  let lone ← play t1 s.me p
  let (v1, l) ← put s s.me "OGN-231" .hand
  let (v2, c) ← put v1 s.me "OGN-136" .base
  let (v3, d) ← put v2 s.me "OGN-136" .base
  let (v4, e) ← put v3 s.you "OGN-136" .base
  let led ← play v4 s.me l [] { yes := true }
  let keep ← play v4 s.me l [] { yes := false }
  return (yes.obj? a).map (·.buffed) == some false && (yes.obj? b).map (·.buffed) == some false &&
    (yes.poolOf s.me).body == (no.poolOf s.me).body + 2 &&
    (no.obj? a).map (·.buffed) == some true &&
    (sac.obj? u).isNone && sac.countIn s.me .base "OGN-208" == 1 &&
    lone.countIn s.me .base "OGN-208" == 0 && lone.countIn s.me .trash "OGN-208" == 1 &&
    (led.obj? c).isNone && (led.obj? d).isNone && (led.obj? e).isSome &&
    (led.poolOf s.me).order == (keep.poolOf s.me).order + 2 && (keep.obj? c).isSome

-- ... what is given back never exceeds what was paid: Wallop played for nothing gives nothing
-- back, Kraken Hunter gives back at most its 2 Body, and Ledros at most its 4 Order
#guard t fun s => do
  let (s1, w) ← put s s.me "OGN-146" .hand
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let free := (s3.buff v).addTurnFx s.me (.nextSpellCostMinus 5)
  let a ← play free s.me w [u] { yes := true }
  let (t1, k) ← put s s.me "OGN-150" .hand
  let (t2, x) ← put t1 s.me "OGN-136" .base
  let (t3, y) ← put t2 s.me "OGN-136" .base
  let (t4, z) ← put t3 s.me "OGN-136" .base
  let three := ((t4.buff x).buff y).buff z
  let yes ← play three s.me k [] { yes := true }
  let no ← play three s.me k [] { yes := false }
  let (v1, l) ← put s s.me "OGN-231" .hand
  let units ← (List.range 5).foldlM
    (fun acc _ => (put acc.1 s.me "OGN-136" .base).map (fun r => (r.1, ()))) (v1, ())
  let led ← play units.1 s.me l [] { yes := true }
  let keep ← play units.1 s.me l [] { yes := false }
  return (a.poolOf s.me).energy == 12 && (yes.obj? x).map (·.buffed) == some false &&
    (yes.poolOf s.me).body == (no.poolOf s.me).body + 2 &&
    (led.poolOf s.me).order == (keep.poolOf s.me).order + 4

-- Hand of Noxus (OGN-253): exhaust, Legion: add 1 Energy (only after another card was played)
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-253" .base
  let (s2, other) ← put s1 s.me "OGN-136" .base
  let played := s2.modObj other (fun o => { o with playedTurn := some s2.turn })
  let pool0 := (s2.poolOf s.me).energy
  let use (x : GameState) : Option GameState :=
    match step 100 x ⟨.player s.me, .manaAbility g 0 ⟨0, []⟩⟩ with
    | .ok (y, _) => some y
    | .error _ => none
  let on ← use played
  let again := use on
  let old := s2.modObj other (fun o => { o with playedTurn := some (s2.turn + 1) })
  let (s3, f) ← put s2 s.you "OGN-136" .base
  let theirs := s3.modObj f (fun o => { o with playedTurn := some s3.turn })
  let (s4, c) ← put s2 s.me "OGN-136" .hand
  let real ← play s4 s.me c
  return (on.poolOf s.me).energy == pool0 + 1 && on.tired g == some true && (use s2).isNone &&
    (use old).isNone && (use theirs).isNone && (use real).isSome && (use (s2.tire g)).isNone &&
    again.isNone && !((legalActions s2).contains ⟨.player s.me, .manaAbility g 0 ⟨0, []⟩⟩) &&
    (legalActions played).contains ⟨.player s.me, .manaAbility g 0 ⟨0, []⟩⟩

-- What happened this turn is noted by the game. Spoils of War (OGN-144): costs 2 less if an enemy
-- unit has died this turn (not a friendly one, not one that was only discarded, also when it is
-- no longer in the Trash, and by who controlled it as it died); draw 2
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-144" .hand
  let (s2, foe) ← put s1 s.you "OGN-136" .base
  let (s3, mine) ← put s2 s.me "OGN-136" .base
  let (s4, disc) ← put s3 s.you "OGN-136" .hand
  let killedFoe := (killObj s3 foe).1
  let killedMine := (killObj s3 mine).1
  let discarded := (discardObj s4 disc).1
  let later := { killedFoe with turn := killedFoe.turn + 1 }
  -- my unit, which the opponent controls, dies: it is an enemy unit as it dies
  let stolen := (setController s.you s3 mine).1
  let killedStolen := (killObj stolen mine).1
  -- the dead unit is recycled: it is still noted
  let gone := match (killedFoe.zone (.player s.you .trash)).head? with
    | some t => (removeObj killedFoe t).getD killedFoe
    | none => killedFoe
  let a ← play killedFoe s.me c
  return energyNow killedFoe s.me c == (energyPrinted s1 c).map (· - 2) &&
    energyNow s1 s.me c == energyPrinted s1 c &&
    energyNow killedMine s.me c == energyPrinted s1 c &&
    energyNow discarded s.me c == energyPrinted s1 c &&
    energyNow later s.me c == energyPrinted s1 c &&
    energyNow killedStolen s.me c == (energyPrinted s1 c).map (· - 2) &&
    energyNow gone s.me c == (energyPrinted s1 c).map (· - 2) &&
    a.handN s.me == killedFoe.handN s.me + 1

-- Raging Soul (OGN-019): with a discarded card this turn, it has Assault and Ganking
#guard t fun s => do
  let (s1, soul) ← put s s.me "OGN-019" .base
  let (s2, x) ← put s1 s.me "OGN-136" .hand
  let (s3, y) ← put s2 s.you "OGN-136" .hand
  let has (g : GameState) (k : Keyword) := (g.grantedKws soul).any (fun i => i.keyword == k)
  let mine := (discardObj s3 x).1
  let theirs := (discardObj s3 y).1
  let later := { mine with turn := mine.turn + 1 }
  -- the discard of the hand limit counts too
  let waiting := { s3 with pending := [.discard s.me 1] }
  let limit ← match step 100 waiting ⟨.player s.me, .discardPick x⟩ with
    | .ok (g, _) => some g
    | .error _ => none
  return !has s3 .assault && !has s3 .ganking && has mine .assault && has mine .ganking &&
    !has theirs .assault && !has later .ganking && has limit .ganking

-- Imperial Decree (OGN-221): a unit that takes damage this turn is killed
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-221" .hand
  let (s2, u) ← put s1 s.me "OGN-001" .base
  let (s3, v) ← put s2 s.you "OGN-001" .base
  let on ← play s3 s.me c
  let hit := (dealObj 1 on u).1
  let hitFoe := (dealObj 1 on v).1
  let none_ := (dealObj 1 s3 u).1
  let zero := (dealObj 0 on u).1
  let later := (dealObj 1 { on with turn := on.turn + 1 } u).1
  return (hit.obj? u).isNone && hit.countIn s.me .trash "OGN-001" == 1 && (hitFoe.obj? v).isNone &&
    (none_.obj? u).map (·.damage) == some 1 && (zero.obj? u).map (·.damage) == some 0 &&
    (later.obj? u).map (·.damage) == some 1

-- Noxian Guillotine (OGN-254): the chosen unit is killed the next time it takes damage this turn;
-- with Legion, it is killed now
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-254" .hand
  let (s2, u) ← put s1 s.you "OGN-001" .base
  let (s3, w) ← put s2 s.you "OGN-001" .base
  let (s4, other) ← put s3 s.me "OGN-136" .base
  let marked ← play s4 s.me c [u]
  let legion ← play (s4.modObj other (fun o => { o with playedTurn := some s4.turn })) s.me c [u]
  return (marked.obj? u).isSome && ((dealObj 1 marked u).1.obj? u).isNone &&
    ((dealObj 1 marked w).1.obj? w).map (·.damage) == some 1 && (legion.obj? u).isNone &&
    ((dealObj 0 marked u).1.obj? u).isSome

-- ... also for the damage of a combat (`dealAll`), which sets off the deaths; a unit that takes no
-- damage is not killed
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-221" .hand
  let (s2, a) ← put s1 s.me "OGN-190" .base
  let (s3, b) ← put s2 s.you "OGN-116" .base
  let on ← play s3 s.me c
  let (done, evs) := dealAll on [(a, 1), (b, 2)]
  let (plain, _) := dealAll s3 [(a, 1), (b, 2)]
  let died := evs.filterMap (fun e => match e with | .died n _ => some n | _ => none)
  return (done.obj? a).isNone && (done.obj? b).isNone && died.length == 2 &&
    (plain.obj? a).isSome && (plain.obj? b).map (·.damage) == some 2

-- Bonus Damage. Ravenborn Tome (OGN-032): the next spell I play this turn deals 1 more with each
-- instance of damage (Hextech Ray deals 3)
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-032" .base
  let (s2, h) ← put s1 s.me "OGN-009" .hand
  let (s3, u) ← putAt s2 s.you "OGN-001" s.bf0
  let on ← activate s3 s.me g 0
  let ready := s3.addTurnFx s.me (.nextSpellBonus 1)
  let boosted ← play ready s.me h [u]
  let plain ← play s3 s.me h [u]
  let (t1, h2) ← put s s.me "OGN-009" .hand
  let (t2, v) ← putAt t1 s.you "OGN-001" s.bf0
  let mine ← play (t2.addTurnFx s.you (.nextSpellBonus 1)) s.me h2 [v]
  return (boosted.obj? u).map (·.damage) == some 4 && (plain.obj? u).map (·.damage) == some 3 &&
    on.tired g == some true && on.turnFx.map (·.kind) == [TurnEffect.nextSpellBonus 1] &&
    (mine.obj? v).map (·.damage) == some 3

-- Void Gate (OGN-296): spells and abilities that affect the units at it deal 1 more
#guard t fun s => do
  let (s1, gate) ← putBf s s.me "OGN-296"
  let (s2, h) ← put s1 s.me "OGN-009" .hand
  let (s3, here) ← putAt s2 s.you "OGN-001" gate
  let (s4, far) ← putAt s3 s.you "OGN-001" s.bf0
  let a ← play s4 s.me h [here]
  let b ← play s4 s.me h [far]
  let (t1, h2) ← put s s.me "OGN-009" .hand
  let (t2, v) ← putAt t1 s.you "OGN-001" s.bf0
  let c ← play t2 s.me h2 [v]
  return (a.obj? here).map (·.damage) == some 4 && (b.obj? far).map (·.damage) == some 3 &&
    (c.obj? v).map (·.damage) == some 3

-- Brynhir Thundersong (OGN-026): when I play her, my opponents cannot play cards this turn
#guard t fun s => do
  let (s1, b) ← put s s.me "OGN-026" .hand
  let (s2, mine) ← put s1 s.me "OGN-136" .hand
  let (s3, theirs) ← put s2 s.you "OGN-136" .hand
  let on ← play s3 s.me b
  let rich := on.rich s.me |>.rich s.you
  let pay (c : ObjId) := payOf rich c
  let next := { rich with turn := rich.turn + 1 }
  return !s3.cantPlay s.you && on.cantPlay s.you && !on.cantPlay s.me &&
    playable rich s.me mine (pay mine) && !playable rich s.you theirs (pay theirs) &&
    playable (s3.rich s.you) s.you theirs (payOf s3 theirs) && !next.cantPlay s.you

-- ... a spell is stopped too (Hextech Ray), and a player who cannot play is offered no play
#guard t fun s => do
  let (s1, b) ← put s s.me "OGN-026" .hand
  let (s2, ray) ← put s1 s.you "OGN-009" .hand
  let (s3, u) ← putAt s2 s.me "OGN-001" s.bf0
  let on ← play s3 s.me b
  let rich := on.rich s.you
  let free := s3.rich s.you
  return !castable rich s.you ray (payOf rich ray) [u] &&
    castable free s.you ray (payOf free ray) [u] &&
    !(legalPlays rich s.you).any
      (fun a => match a.kind with | .playCard c _ _ => c == ray | _ => false)

-- The ability that watches an object gets it as its last slot. Pirate's Haven (OGN-143): when I
-- ready a friendly unit, it gets +1 Might this turn
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-143" .base
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.you "OGN-136" .base
  let tired := (s3.tire u).tire v
  let (mine, ev) := setExhausted false tired u
  let a ← fire mine ev
  let (theirs, ev2) := setExhausted false tired v
  let b ← fire theirs ev2
  return a.mightNow u == some 3 && a.tired u == some false && b.mightNow v == some 2 &&
    tired.mightNow u == some 2

-- ... a unit that is ready already is not readied again, and the units the Awaken readies count
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-143" .base
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (readyAlready, ev) := setExhausted false s2 u
  let a ← fire readyAlready ev
  let tired := s2.tire u
  let waking := { tired with pending := [.phase .awaken] }
  let (s3, evs) ← microStep0 waking
  let b ← fire s3 evs
  return ev.isEmpty && a.mightNow u == some 2 && b.tired u == some false && b.mightNow u == some 3

-- Nine-Tailed Fox (OGN-255): when an enemy unit attacks a battlefield I control, it gets -1 Might
-- this turn, to a minimum of 1
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-255" .legendZone
  let held := s1.modObj s.bf0 (fun o => { o with control := some s.me })
  let (s2, big) ← putAt held s.you "OGN-001" s.bf0
  let (s3, small) ← putAt s2 s.you "OGN-136" s.bf0
  let (s3b, one) ← putAt s3 s.you "OGN-190" s.bf0
  let (s4, mine) ← putAt s3b s.me "OGN-136" s.bf0
  let a ← fire s4 [.combatStarted s.bf0 s.you]
  let free := s4.modObj s.bf0 (fun o => { o with control := none })
  let lost ← fire free [.combatStarted s.bf0 s.you]
  let mineAttacks ← fire s4 [.combatStarted s.bf0 s.me]
  return a.mightNow big == some 4 && a.mightNow small == some 1 && a.mightNow one == some 1 &&
    a.mightNow mine == some 2 &&
    lost.mightNow big == some 5 && mineAttacks.mightNow big == some 5

-- Volibear, Imposing (OGN-158): when an opponent moves to a battlefield other than mine, I draw 1
-- (the watched unit is in the condition as slot 0)
#guard t fun s => do
  let bf1 ← s.battlefields[1]?
  let (s1, _) ← putAt s s.me "OGN-158" s.bf0
  let (s2, foe) ← put s1 s.you "OGN-136" .base
  let (s3, foe2) ← put s2 s.you "OGN-136" .base
  let (s4, mine) ← put s3 s.me "OGN-136" .base
  let (other, ev) ← moveTo s4 s.you foe (.battlefield bf1)
  let (same, ev2) ← moveTo s4 s.you foe2 (.battlefield s.bf0)
  let (own, ev3) ← moveTo s4 s.me mine (.battlefield bf1)
  let (home, ev4) ← moveTo other s.you foe .base
  let a ← fire other ev
  let b ← fire same ev2
  let c ← fire own ev3
  let d ← fire home ev4
  -- Volibear in his Base: every battlefield is another one
  let (t1, _) ← put s s.me "OGN-158" .base
  let (t2, foe3) ← put t1 s.you "OGN-136" .base
  let (inBase, ev5) ← moveTo t2 s.you foe3 (.battlefield s.bf0)
  let e ← fire inBase ev5
  return a.handN s.me == other.handN s.me + 1 && b.handN s.me == same.handN s.me &&
    c.handN s.me == own.handN s.me && d.handN s.me == home.handN s.me &&
    e.handN s.me == inBase.handN s.me + 1

-- Reinforce (OGN-062): look at the top 5 cards, you may play a unit (Energy cost 5 or less) from
-- among them, and recycle the rest
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-062" .hand
  let empty := s1.setZone (.player s.me .mainDeck) []
  -- the deck, from the bottom: a sixth card, then five cards of which the top one is the unit
  let (d1, six) ← put empty s.me "OGN-004" .mainDeck
  let (d2, _) ← put d1 s.me "OGN-011" .mainDeck
  let (d3, _) ← put d2 s.me "OGN-004" .mainDeck
  let (d4, _) ← put d3 s.me "OGN-004" .mainDeck
  let (d5, _) ← put d4 s.me "OGN-004" .mainDeck
  let (d6, u) ← put d5 s.me "OGN-136" .mainDeck
  let deck (g : GameState) := g.zone (.player s.me .mainDeck)
  let go ← play d6 s.me c [] { yes := true, obj := fun o => o == u }
  let no ← play d6 s.me c [] { yes := false }
  let (e1, _) ← put empty s.me "OGN-011" .mainDeck
  let blocked ← play e1 s.me c [] { yes := true }
  -- a unit below the top 5 is not played; of two units in the top 5 only the cheap one can be
  let (f1, _) ← put empty s.me "OGN-136" .mainDeck
  let (f2, _) ← put f1 s.me "OGN-004" .mainDeck
  let (f3, _) ← put f2 s.me "OGN-004" .mainDeck
  let (f4, _) ← put f3 s.me "OGN-004" .mainDeck
  let (f5, _) ← put f4 s.me "OGN-004" .mainDeck
  let (f6, _) ← put f5 s.me "OGN-004" .mainDeck
  let deep ← play f6 s.me c [] { yes := true }
  let (g1, _) ← put empty s.me "OGN-136" .mainDeck
  let (g2, _) ← put g1 s.me "OGN-011" .mainDeck
  let two ← play g2 s.me c [] { yes := true }
  return go.countIn s.me .base "OGN-136" == 1 && (deck go).length == (deck d6).length - 1 &&
    (deck go).head? == some six && go.countIn s.me .hand "OGN-136" == 0 &&
    (deck no).length == (deck d6).length && (deck no).head? == some six &&
    no.countIn s.me .base "OGN-136" == 0 && (deck blocked).length == 1 &&
    deep.countIn s.me .base "OGN-136" == 0 && two.countIn s.me .base "OGN-136" == 1 &&
    two.countIn s.me .base "OGN-011" == 0

-- Dazzling Aurora (OGN-160): at the end of my turn, reveal cards until a unit; play it for free and
-- recycle the rest
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-160" .base
  let empty := s1.setZone (.player s.me .mainDeck) []
  let (d1, last) ← put empty s.me "OGN-004" .mainDeck
  let (d2, _) ← put d1 s.me "OGN-136" .mainDeck
  let (d3, a) ← put d2 s.me "OGN-004" .mainDeck
  let (d4, b) ← put d3 s.me "OGN-004" .mainDeck
  let deck (g : GameState) := g.zone (.player s.me .mainDeck)
  let go ← fire d4 [.phaseStarted s.me .ending]
  let theirs ← fire d4 [.phaseStarted s.you .ending]
  let (e1, _) ← put empty s.me "OGN-004" .mainDeck
  let (e2, _) ← put e1 s.me "OGN-004" .mainDeck
  let none_ ← fire e2 [.phaseStarted s.me .ending]
  return go.countIn s.me .base "OGN-136" == 1 && (deck go).length == 3 &&
    (deck go).head? == some last && (deck go).drop 1 == [b, a] && (deck theirs) == deck d4 &&
    (deck none_).length == 2 && none_.countIn s.me .base "OGN-136" == 0

-- Twisted Fate, Gambler (OGN-200): when I attack, reveal the top rune and recycle it; by its
-- domain: Fury 2 to an enemy unit here and 1 to the other enemy units here, Mind draw 1, Order stun
-- an enemy unit
#guard t fun s => do
  let (s1, _) ← putAt s s.me "OGN-200" s.bf0
  let (s2, big) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, small) ← putAt s2 s.you "OGN-136" s.bf0
  let (s4, far) ← put s3 s.you "OGN-001" .base
  let withTop (card : String) : Option GameState := do
    let (d1, _) ← put (s4.setZone (.player s.me .runeDeck) []) s.me "OGN-166" .runeDeck
    let (d2, _) ← put d1 s.me card .runeDeck
    pure d2
  let fury ← withTop "OGN-007"
  let mind ← withTop "OGN-089"
  let order ← withTop "OGN-214"
  let calm ← withTop "OGN-042"
  let go (g : GameState) := fire g [.combatStarted s.bf0 s.me] { obj := fun o => o == big }
  let f ← go fury
  let m ← go mind
  let o ← go order
  let c ← go calm
  let runes (g : GameState) := (g.zone (.player s.me .runeDeck)).length
  return (f.obj? big).map (·.damage) == some 2 && (f.obj? small).map (·.damage) == some 1 &&
    (f.obj? far).map (·.damage) == some 0 && runes f == runes fury &&
    m.handN s.me == mind.handN s.me + 1 && (m.obj? big).map (·.damage) == some 0 &&
    (o.obj? big).map (·.stunned) == some true && (o.obj? small).map (·.stunned) == some false &&
    (m.obj? small).map (·.stunned) == some false &&
    (f.obj? small).map (·.stunned) == some false &&
    (f.zone (.player s.me .runeDeck)).getLast?.isSome &&
    (f.zone (.player s.me .runeDeck)).getLast? !=
      (fury.zone (.player s.me .runeDeck)).getLast? &&
    c.handN s.me == calm.handN s.me && (c.obj? big).map (·.damage) == some 0 &&
    (c.obj? big).map (·.stunned) == some false

-- Karthus, Eternal (OGN-236): my Deathknell abilities trigger an additional time
#guard t fun s => do
  let (s1, k) ← putAt s s.me "OGN-190" s.bf0
  let (s2, _) ← put s1 s.me "OGN-236" .base
  let (s3, plain) ← putAt s s.me "OGN-190" s.bf0
  let (s4, other) ← putAt s2 s.me "OGN-136" s.bf0
  let (theirs, foe) ← putAt s s.you "OGN-190" s.bf0
  let (withK, evK) := killObj s2 k
  let (without, ev) := killObj s3 plain
  let (noKw, evO) := killObj s4 other
  let (foeK, evF) := killObj theirs foe
  let (t2, _) ← put theirs s.me "OGN-236" .base
  let (foeK2, evF2) := killObj t2 foe
  -- a card that has a trigger for its death but not the keyword (Scrapheap) is not doubled, and
  -- two Karthus still make it twice
  let (u1, scrap) ← putAt s2 s.me "OGN-182" s.bf0
  let (scrapK, evS) := killObj u1 scrap
  let (u2, _) ← put s2 s.me "OGN-236" .base
  let (twoK, ev2) := killObj u2 k
  let a2 := (twoK.detect ev2).length
  return (scrapK.detect evS).length == 1 && a2 == 2 &&
    (withK.detect evK).length == 2 && (without.detect ev).length == 1 &&
    (noKw.detect evO).length == 0 && (foeK.detect evF).length == 1 &&
    (foeK2.detect evF2).length == 1

-- Vilemaw's Lair (OGN-295): units cannot move from here to the Base
#guard t fun s => do
  let (s1, lair) ← putBf s s.me "OGN-295"
  let (s2, u) ← putAt s1 s.me "OGN-136" lair
  let (s3, v) ← putAt s2 s.me "OGN-136" s.bf0
  let (s4, w) ← putAt s3 s.you "OGN-136" lair
  let home (g : GameState) (x : ObjId) := (moveHome g x).1.where? x
  -- ... also a move by an effect, and of the units of either player
  return !moveOk s3 s.me u .base && moveOk s3 s.me v .base && home s4 u == some .battlefieldZone &&
    home s4 w == some .battlefieldZone && home s4 v == some (.player s.me .base)

-- Noxus Saboteur (OGN-018): the Hidden cards of my opponents cannot be revealed at its battlefield
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-135" .hand
  let mine := s1.control s.me s.bf0
  let hide ← activate mine s.me c 0 [s.bf0] ⟨0, [.fury]⟩
  let h ← (hide.zone (.player s.me .hidden)).head?
  let (foe, _) ← putAt hide s.you "OGN-018" s.bf0
  let (own, _) ← putAt hide s.me "OGN-018" s.bf0
  let bf1 ← s.battlefields[1]?
  let (away, _) ← putAt hide s.you "OGN-018" bf1
  let later (g : GameState) := { g with turn := g.turn + 1 }
  let go (g : GameState) := activate (later g) s.me h 1 [] ⟨0, []⟩
  return foe.hiddenBlocked s.me h && !hide.hiddenBlocked s.me h && !own.hiddenBlocked s.me h &&
    !away.hiddenBlocked s.me h && (go foe).isNone && (go hide).isSome && (go own).isSome &&
    (go away).isSome

-- Treasure Trove (OGN-186): when it dies, draw 1 and channel 1 rune exhausted; Chaos, exhaust:
-- kill it
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-186" .base
  let on ← activate s1 s.me g 1 [] ⟨0, [.chaos]⟩
  let none_ := activate (s1.tire g) s.me g 1 [] ⟨0, [.chaos]⟩
  let broke := activate s1 s.me g 1
  let runeN (x : GameState) :=
    ((x.zone (.player s.me .base)).filter (fun u => (x.cardDef? u).any (·.hasType .rune))).length
  return on.countIn s.me .trash "OGN-186" == 1 && on.handN s.me == s1.handN s.me + 1 &&
    runeN on == runeN s1 + 1 && none_.isNone && broke.isNone

-- Targon's Peak (OGN-289): when I conquer here, ready 2 runes at the end of this turn
#guard t fun s => do
  let (s0, bf) ← putBf s s.me "OGN-289"
  let (s1, _) ← put s0 s.me "OGN-007" .base
  let runes := (s1.zone (.player s.me .base)).filter
    (fun u => (s1.cardDef? u).any (·.hasType .rune))
  let tired := runes.foldl (fun g u => g.tire u) s1
  let ready (g : GameState) := ((g.zone (.player s.me .base)).filter (fun u =>
    (g.cardDef? u).any (·.hasType .rune) && g.tired u == some false)).length
  let won ← fire tired [.scored s.me bf true]
  let end_ ← fire won [.phaseStarted s.me .ending]
  let none_ ← fire tired [.phaseStarted s.me .ending]
  let theirs ← fire tired [.scored s.you bf true]
  let theirsEnd ← fire theirs [.phaseStarted s.me .ending]
  -- only one exhausted rune: it is readied; a hold, or a note of an earlier turn, does nothing
  let one := (runes.take 1).foldl (fun g u => g.tire u) s1
  let held ← fire tired [.scored s.me bf false]
  let heldEnd ← fire held [.phaseStarted s.me .ending]
  let oldNote := { won with turn := won.turn + 1 }
  let old ← fire oldNote [.phaseStarted s.me .ending]
  let onlyOne ← fire (← fire one [.scored s.me bf true]) [.phaseStarted s.me .ending]
  return ready heldEnd == 0 && ready old == 0 && ready onlyOne == ready one + 1 &&
    runes.length == 3 && ready tired == 0 && ready won == 0 && ready end_ == 2 &&
    ready none_ == 0 && ready theirsEnd == 0

-- Back-Alley Bar (OGN-277): when a unit moves from here, it gets +1 Might this turn
#guard t fun s => do
  let bf1 ← s.battlefields[1]?
  let (s1, bar) ← putBf s s.me "OGN-277"
  let (s2, here) ← putAt s1 s.me "OGN-136" bar
  let (s3, there) ← putAt s2 s.me "OGN-136" s.bf0
  let (s4, foe) ← putAt s3 s.you "OGN-136" bar
  let (a, ev) ← moveTo s4 s.me here (.battlefield bf1)
  let (b, ev2) ← moveTo s4 s.me there (.battlefield bf1)
  let (c, ev3) ← moveTo s4 s.me here .base
  let (d, ev4) ← moveTo s4 s.you foe (.battlefield bf1)
  -- (a move to the bar, not from it)
  let (e, ev5) ← moveTo s4 s.me there (.battlefield bar)
  let a' ← fire a ev
  let b' ← fire b ev2
  let c' ← fire c ev3
  let d' ← fire d ev4
  let e' ← fire e ev5
  -- an effect moves a unit from the bar; a second move of the same unit is not from here
  let (f, ev6) := sendToBf s.bf0 s4 here
  let f' ← fire f ev6
  let (g, ev7) ← moveTo a s.me here (.battlefield s.bf0)
  let g' ← fire g ev7
  let stale := { a' with turn := a'.turn + 1 }
  return f'.mightNow here == some 3 && g'.mightNow here == some 2 &&
    (Filter.movedFromHere.holds stale bar {} here) == some false &&
    a'.mightNow here == some 3 && b'.mightNow there == some 2 && c'.mightNow here == some 3 &&
    d'.mightNow foe == some 3 && e'.mightNow there == some 2

-- Stealthy Pursuer (OGN-177): when a friendly unit moves from my location, I may be moved with it
#guard t fun s => do
  let bf1 ← s.battlefields[1]?
  let (s1, p) ← putAt s s.me "OGN-177" s.bf0
  let (s2, x) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, y) ← putAt s2 s.me "OGN-136" bf1
  let (s4, foe) ← putAt s3 s.you "OGN-136" s.bf0
  let (a, ev) ← moveTo s4 s.me x (.battlefield bf1)
  let (b, ev2) ← moveTo s4 s.me x .base
  let (c, ev3) ← moveTo s4 s.me y .base
  let (d, ev4) ← moveTo s4 s.you foe (.battlefield bf1)
  let yes ← fire a ev { yes := true }
  let no ← fire a ev { yes := false }
  let home ← fire b ev2 { yes := true }
  let other ← fire c ev3 { yes := true }
  let foeMoves ← fire d ev4 { yes := true }
  let loc (g : GameState) := (g.obj? p).map (·.loc)
  -- from the Base: a unit that leaves my Base takes me with it
  let (t1, q) ← put s s.me "OGN-177" .base
  let (t2, z) ← put t1 s.me "OGN-136" .base
  let (e, ev5) ← moveTo t2 s.me z (.battlefield s.bf0)
  let fromBase ← fire e ev5 { yes := true }
  -- the unit dies before the ability resolves: nothing happens
  let queued := { a with pending := insertTriggers (a.detect ev) a.pending }
  let gone ← match advance 100 (killObj queued x).1 [] with
    | .ok (g, _) => some (settleChain { yes := true } 12 g)
    | .error _ => none
  return loc gone == some (some s.bf0) && loc yes == some (some bf1) &&
    loc no == some (some s.bf0) && loc home == some none &&
    loc other == some (some s.bf0) && loc foeMoves == some (some s.bf0) &&
    (fromBase.obj? q).map (·.loc) == some (some s.bf0)

-- How a unit was when it died. Vanguard Helm (OGN-228): when a buffed friendly unit dies, buff
-- another friendly unit
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-228" .base
  let (s2, a) ← put s1 s.me "OGN-136" .base
  let (s3, b) ← put s2 s.me "OGN-136" .base
  let (s4, foe) ← put s3 s.you "OGN-136" .base
  let bufA := s4.buff a
  let (k, ev) := killObj bufA a
  let (k2, ev2) := killObj s4 a
  let (k3, ev3) := killObj (s4.buff foe) foe
  let yes ← fire k ev
  let plain ← fire k2 ev2
  let theirs ← fire k3 ev3
  let (st, evst) := killObj (s4.modObj a (fun o => { o with stunned := true })) a
  let stunnedOnly ← fire st evst
  let (j, evj) := killObj (s2.buff a) a
  let lone ← fire j evj
  return (yes.obj? b).map (·.buffed) == some true &&
    (plain.obj? b).map (·.buffed) == some false &&
    (theirs.obj? b).map (·.buffed) == some false &&
    (lone.zone (.player s.me .base)).all (fun u => (lone.obj? u).all (fun o => !o.buffed)) &&
    (stunnedOnly.obj? b).map (·.buffed) == some false

-- Solari Shrine (OGN-072): when I kill a stunned enemy unit, I may exhaust it to draw 1
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-072" .base
  let (s2, foe) ← put s1 s.you "OGN-136" .base
  let (s3, mine) ← put s2 s.me "OGN-136" .base
  let stun (g : GameState) (u : ObjId) := g.modObj u (fun o => { o with stunned := true })
  let (a, ev) := killObj (stun s3 foe) foe
  let (b, ev2) := killObj s3 foe
  let (c, ev3) := killObj (stun s3 mine) mine
  let (d, ev4) := killObj (stun (s3.tire g) foe) foe
  let (e, ev5) := killObj (s3.buff foe) foe
  let buffedOnly ← fire e ev5
  let yes ← fire a ev { yes := true }
  let no ← fire a ev { yes := false }
  let plain ← fire b ev2
  let own ← fire c ev3
  let tired ← fire d ev4
  return yes.handN s.me == a.handN s.me + 1 && yes.tired g == some true &&
    no.handN s.me == a.handN s.me && plain.handN s.me == b.handN s.me &&
    own.handN s.me == c.handN s.me && tired.handN s.me == d.handN s.me &&
    buffedOnly.handN s.me == e.handN s.me

-- Gemcraft Seer (OGN-100): [Vision]; my other units have Vision: when I play one, I may recycle the
-- top card of my Main Deck (a unit that has Vision itself is not doubled)
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-100" .base
  let (s2, plain) ← put s1 s.me "OGN-136" .hand
  let (s3, vis) ← put s2 s.me "OGN-171" .hand
  let deck (x : GameState) (p : PlayerId) := x.zone (.player p .mainDeck)
  let top ← (deck s3 s.me).head?
  let a ← play s3 s.me plain
  let no ← play s3 s.me plain [] { yes := false }
  let v ← play s3 s.me vis
  let (t1, seer) ← put s s.me "OGN-100" .hand
  let own ← play t1 s.me seer
  let (u1, plain2) ← put s s.me "OGN-136" .hand
  let without ← play u1 s.me plain2
  return (deck a s.me).getLast? == some top && (deck no s.me).head? == some top &&
    (deck v s.me).getLast? == some top && (deck v s.me).length == (deck s3 s.me).length &&
    (deck without s.me).head? == (deck u1 s.me).head? &&
    (deck own s.me).getLast? == (deck t1 s.me).head?

-- Mistfall (OGN-152): when I buff a friendly unit, I may pay Body and exhaust it to ready that unit
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-152" .base
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, foe) ← put s2 s.you "OGN-136" .base
  let funded := (s3.tire u).fund s.me 0 (body := 1)
  let (a, ev) := buffObj funded u
  let yes ← fire a ev { yes := true }
  let no ← fire a ev { yes := false }
  let (b, ev2) := buffObj (funded.buff u) u
  let again ← fire b ev2 { yes := true }
  let (c, ev3) := buffObj ((s3.tire foe).fund s.me 0 (body := 1)) foe
  let theirs ← fire c ev3 { yes := true }
  let (d, ev4) := buffObj ((s3.tire u).fund s.me 0) u
  let broke ← fire d ev4 { yes := true }
  let (e, ev5) := buffObj ((funded.tire g)) u
  let spent ← fire e ev5 { yes := true }
  return yes.tired u == some false && yes.tired g == some true && (yes.poolOf s.me).body == 0 &&
    no.tired u == some true && again.tired u == some true && theirs.tired foe == some true &&
    broke.tired u == some true && spent.tired u == some true

-- Ember Monk (OGN-167): when I play a card from Hidden (a unit or a spell), it gets +2 Might this
-- turn; playing from the hand does not
#guard t fun s => do
  let (s1, monk) ← put s s.me "OGN-167" .base
  let (s2, c) ← put s1 s.me "OGN-135" .hand
  let mine := s2.control s.me s.bf0
  let hide ← activate mine s.me c 0 [s.bf0] ⟨0, [.fury]⟩
  let h ← (hide.zone (.player s.me .hidden)).head?
  let next := { hide with turn := hide.turn + 1 }
  let unitIn ← activate next s.me h 1 [] ⟨0, []⟩
  let (t1, m2) ← put s s.me "OGN-167" .base
  let (t2, sp) ← put t1 s.me "OGN-057" .hand
  let (t3, u) ← put t2 s.me "OGN-136" .base
  let mine2 := t3.control s.me s.bf0
  let hide2 ← activate mine2 s.me sp 0 [s.bf0] ⟨0, [.fury]⟩
  let h2 ← (hide2.zone (.player s.me .hidden)).head?
  let next2 := { hide2 with turn := hide2.turn + 1 }
  let spellIn ← activate next2 s.me h2 1 [u] ⟨0, []⟩
  let (v1, m3) ← put s s.me "OGN-167" .base
  let (v2, d) ← put v1 s.me "OGN-088" .hand
  let handIn ← play v2 s.me d
  -- two Monks each get it; a Hidden card played from the hand does not count
  let (w1, wa) ← put s s.me "OGN-167" .base
  let (w2, wb) ← put w1 s.me "OGN-167" .base
  let (w3, wc) ← put w2 s.me "OGN-135" .hand
  let wmine := w3.control s.me s.bf0
  let whide ← activate wmine s.me wc 0 [s.bf0] ⟨0, [.fury]⟩
  let wh ← (whide.zone (.player s.me .hidden)).head?
  let wnext := { whide with turn := whide.turn + 1 }
  let twice ← activate wnext s.me wh 1 [] ⟨0, []⟩
  let (x1, xm) ← put s s.me "OGN-167" .base
  let (x2, xc) ← put x1 s.me "OGN-135" .hand
  let fromHand ← play x2 s.me xc
  return unitIn.mightNow monk == (next.mightNow monk).map (· + 2) &&
    spellIn.mightNow m2 == (next2.mightNow m2).map (· + 2) &&
    handIn.mightNow m3 == v2.mightNow m3 && next.mightNow monk == mine.mightNow monk &&
    twice.mightNow wa == (wnext.mightNow wa).map (· + 2) &&
    twice.mightNow wb == (wnext.mightNow wb).map (· + 2) &&
    fromHand.mightNow xm == x2.mightNow xm

-- Reckoner's Arena (OGN-286): when I hold here, the conquer effects of my units here are activated
-- (Kai'Sa, Survivor, OGN-039: draw 1 when she conquers); the text says units here, so an enemy
-- unit's effect is activated for its controller too; not units elsewhere, and not when I conquer
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-286"
  let (s2, _) ← putAt s1 s.me "OGN-039" bf
  let (s3, _) ← putAt s2 s.me "OGN-039" bf
  let (s4, _) ← put s3 s.me "OGN-039" .base
  let (s5, _) ← putAt s4 s.you "OGN-039" bf
  let a ← fire s5 [.scored s.me bf false]
  let b ← fire s5 [.scored s.me bf true]
  let (t1, tb) ← putBf s s.me "OGN-286"
  let (t2, _) ← put t1 s.me "OGN-039" .base
  let c ← fire t2 [.scored s.me tb false]
  return a.handN s.me == s5.handN s.me + 2 && a.handN s.you == s5.handN s.you + 1 &&
    b.handN s.me == s5.handN s.me + 2 && c.handN s.me == t2.handN s.me

-- Hallowed Tomb (OGN-281): when I hold here, I may return my Chosen Champion (a Unit of my Legend's
-- Champion) from my Trash to my Champion Zone, if it is empty
#guard t fun s => do
  let empty := s.setZone (.player s.me .championZone) []
  let (s1, bf) ← putBf empty s.me "OGN-281"
  let (s2, _) ← put s1 s.me "OGN-247" .legendZone
  let (s3, _) ← put s2 s.me "OGN-039" .trash
  let (s4, _) ← put s3 s.me "OGN-136" .trash
  let zone (g : GameState) (p : PlayerId) := g.zone (.player p .championZone)
  let a ← fire s4 [.scored s.me bf false] { yes := true }
  let no ← fire s4 [.scored s.me bf false] { yes := false }
  let c ← fire s4 [.scored s.me bf true] { yes := true }
  let (t1, _) ← put s4 s.me "OGN-039" .championZone
  let full ← fire t1 [.scored s.me bf false] { yes := true }
  let (u1, _) ← put s1 s.me "OGN-247" .legendZone
  let (u2, _) ← put u1 s.me "OGN-136" .trash
  let wrong ← fire u2 [.scored s.me bf false] { yes := true }
  let (v1, _) ← put s1 s.me "OGN-039" .trash
  let nolegend ← fire v1 [.scored s.me bf false] { yes := true }
  let (w1, _) ← put s4 s.you "OGN-039" .trash
  let theirs ← fire w1 [.scored s.you bf false] { yes := true }
  let back ← (zone a s.me).head?
  return (zone a s.me).length == 1 && (a.obj? back).map (·.owner) == some s.me &&
    (a.cardDef? back).map (·.id) == some ⟨"OGN-039"⟩ &&
    (a.zone (.player s.me .trash)).length == 1 && (zone no s.me).isEmpty &&
    (no.zone (.player s.me .trash)).length == 2 && (zone c s.me).isEmpty &&
    (zone full s.me).length == 1 && (full.zone (.player s.me .trash)).length == 2 &&
    (zone wrong s.me).isEmpty && (zone nolegend s.me).isEmpty &&
    (zone theirs s.you).length == (zone w1 s.you).length

-- The Chosen Champion is played from the Champion Zone: a Unit there is played by paying its cost
-- (the printed one), and goes to my Base; not for less, not from the hand's ability, not twice
#guard t fun s => do
  let empty := s.setZone (.player s.me .championZone) []
  let (s1, c) ← put empty s.me "OGN-088" .championZone
  let a ← activate s1 s.me c 0 [] ⟨7, []⟩
  let short := activate s1 s.me c 0 [] ⟨6, []⟩
  let (t1, h) ← put empty s.me "OGN-088" .hand
  let fromHand := activate t1 s.me h 0 [] ⟨7, []⟩
  let (u1, b) ← put empty s.me "OGN-088" .base
  let inBase := activate u1 s.me b 0 [] ⟨7, []⟩
  let theirs := activate s1 s.you c 0 [] ⟨7, []⟩
  let twice := activate a s.me c 0 [] ⟨7, []⟩
  -- the opponent's "can't play cards" holds for this play too
  let blocked := activate (s1.addTurnFx s.you .opponentsCantPlay) s.me c 0 [] ⟨7, []⟩
  let freed := activate (s1.addTurnFx s.me .opponentsCantPlay) s.me c 0 [] ⟨7, []⟩
  return a.countIn s.me .base "OGN-088" == 1 && (a.zone (.player s.me .championZone)).isEmpty &&
    short.isNone && fromHand.isNone && inBase.isNone && theirs.isNone && twice.isNone &&
    blocked.isNone && freed.isSome &&
    (s1.zone (.player s.me .championZone)).length == 1

-- Symbol of the Solari (OGN-227): a combat I attack in that ends in a tie (Units of both sides are
-- left) recalls all the Units, not only mine; it is for the attacker's Symbol only
#guard t fun s => do
  let bf := s.bf0
  let (s1, mine) ← putAt s s.me "OGN-136" bf
  let (s2, foe) ← putAt s1 s.you "OGN-136" bf
  let (s3, _) ← put s2 s.me "OGN-227" .base
  let (s4, _) ← put s2 s.you "OGN-227" .base
  let here (g : GameState) (u : ObjId) : Bool := (g.obj? u).any (fun o => o.loc == some bf)
  let withSym := (combatResolve s3 bf s.me).1
  let without := (combatResolve s2 bf s.me).1
  let theirs := (combatResolve s4 bf s.me).1
  let (u1, f2) ← putAt s s.you "OGN-136" bf
  let (u2, _) ← put u1 s.me "OGN-227" .base
  let wiped := (combatResolve u2 bf s.me).1
  let (h1, _) ← put s2 s.me "OGN-227" .hand
  let inHand := (combatResolve h1 bf s.me).1
  let (k1, k) ← putAt s s.me "OGN-136" bf
  let (k2, _) ← put k1 s.me "OGN-227" .base
  let alone := (combatResolve k2 bf s.me).1
  return !here withSym mine && !here withSym foe &&
    (withSym.zone (.player s.you .base)).length == (s3.zone (.player s.you .base)).length + 1 &&
    !here without mine && here without foe && !here theirs mine && here theirs foe &&
    here wiped f2 && !here inHand mine && here inHand foe && here alone k

-- Mageseeker Warden (OGN-070): while it is at a battlefield, its opponents play Units only to their
-- base (Sneaky Deckhand cannot go to a battlefield), and spells and abilities cannot ready their
-- Units and Gear (First Mate cannot ready my Unit); its own side is not stopped, and a Warden at a
-- base does nothing
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-176" .hand
  let (w1, _) ← putAt s1 s.you "OGN-070" s.bf0
  let (b1, _) ← put s1 s.you "OGN-070" .base
  let (m1, d) ← put s s.me "OGN-132" .hand
  let (m2, v) ← put m1 s.me "OGN-001" .base
  let (m3, e) ← put m2 s.you "OGN-001" .base
  let (m4, _) ← putAt m3 s.you "OGN-070" s.bf0
  let m5 := (m4.tire v).tire e
  let ready := ({ pick := fun ts => ts.contains v } : Says)
  let readyFoe := ({ pick := fun ts => ts.contains e } : Says)
  let blocked ← play m5 s.me d [] ready
  let foeReady ← play m5 s.me d [] readyFoe
  let (n1, d2) ← put m2 s.me "OGN-132" .hand
  let free ← play (n1.tire v) s.me d2 [] ready
  let (o1, _) ← put (m3.tire v) s.you "OGN-070" .base
  let atBase ← play o1 s.me d [] ready
  return (activate w1 s.me c 0 [s.bf0] (payOf w1 c)).isNone &&
    (activate b1 s.me c 0 [s.bf0] (payOf b1 c)).isSome &&
    (activate s1 s.me c 0 [s.bf0] (payOf s1 c)).isSome &&
    (blocked.obj? v).map (·.exhausted) == some true &&
    (foeReady.obj? e).map (·.exhausted) == some false &&
    (free.obj? v).map (·.exhausted) == some false &&
    (atBase.obj? v).map (·.exhausted) == some false

-- Mageseeker Warden (OGN-070), more: its owner is not stopped; an effect that plays a card to a
-- battlefield (Ava Achiever, OGN-107) plays it to the base instead
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-298"
  let (s2, c) ← put s1 s.me "OGN-176" .hand
  let (s3, _) ← putAt s2 s.me "OGN-070" bf
  let (t1, _) ← putAt s1 s.me "OGN-107" bf
  let (t2, _) ← put t1 s.me "OGN-135" .hand
  let (t3, _) ← putAt t2 s.you "OGN-070" bf
  let free := t2.fund s.me 0 (mind := 1)
  let held := t3.fund s.me 0 (mind := 1)
  let a ← fire free [.combatStarted bf s.me] { yes := true }
  let b ← fire held [.combatStarted bf s.me] { yes := true }
  let there (x : GameState) :=
    ((x.zone .battlefieldZone).filter (fun u => (x.cardDef? u).any (·.id == cid "OGN-135") &&
      (x.obj? u).any (·.loc == some bf))).length
  return (activate s3 s.me c 0 [bf] (payOf s3 c)).isSome &&
    there a == 1 && there b == 0 && b.countIn s.me .base "OGN-135" == 1

-- Karma (OGN-235): when I recycle one or more cards, I buff a friendly unit (Mystic Poro's Vision
-- recycles; declining, an empty deck, and the opponent's recycling do not)
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-235" .base
  let (s2, _) ← put s1 s.me "OGN-136" .base
  let (s3, c) ← put s2 s.me "OGN-171" .hand
  let buffs (x : GameState) :=
    ((x.zone (.player s.me .base)).filter (fun v => (x.obj? v).any (·.buffed))).length
  let a ← play s3 s.me c
  let no ← play s3 s.me c [] { yes := false }
  let bare ← play (s3.setZone (.player s.me .mainDeck) []) s.me c
  let mine ← fire s3 [.recycled s.me]
  let theirs ← fire s3 [.recycled s.you]
  return buffs a == 1 && buffs no == 0 && buffs bare == 0 && buffs mine == 1 && buffs theirs == 0

-- Karma (OGN-235), more: recycling cards of the deck (Stacked Deck, OGN-183) counts; recycling a
-- rune (Sigil of the Storm, OGN-287) does not, as runes are not cards
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-235" .base
  let (s2, _) ← put s1 s.me "OGN-136" .base
  let (s3, c) ← put s2 s.me "OGN-183" .hand
  let (t1, bf) ← putBf s2 s.me "OGN-287"
  let buffs (x : GameState) :=
    ((x.zone (.player s.me .base)).filter (fun v => (x.obj? v).any (·.buffed))).length
  let a ← play s3 s.me c
  let rune ← fire t1 [.scored s.me bf true]
  return 0 < buffs a && buffs rune == 0

-- Hide (CR 811): one hidden card per battlefield; Bandle Tree (OGN-278): one additional card there
#guard t fun s => do
  let hideFor (g : GameState) (who : PlayerId) (bf : ObjId) : Option GameState := do
    let (g1, h) ← put g who "OGN-135" .hidden
    some (g1.modObj h (fun o => { o with hiddenAt := some bf, hiddenTurn := some 0 }))
  let hideAt (g : GameState) (bf : ObjId) : Option GameState := hideFor g s.me bf
  let tryHide (g : GameState) (bf : ObjId) : Bool :=
    match put g s.me "OGN-135" .hand with
    | some (g1, c) => (activate (g1.control s.me bf) s.me c 0 [bf] ⟨0, [.fury]⟩).isSome
    | none => false
  let (t1, tree) ← putBf s s.me "OGN-278"
  let plain := s.bf0
  let p1 ← hideAt s plain
  let t3 ← hideAt t1 tree
  let t2 ← hideAt t3 tree
  -- a card hidden at another battlefield, or one of the opponent's at this one
  let other ← hideAt t1 plain
  let theirs ← hideFor s s.you plain
  return tryHide s plain && !tryHide p1 plain && tryHide t3 tree && !tryHide t2 tree &&
    tryHide t1 tree && tryHide other tree && !tryHide theirs plain

-- King's Edict (OGN-237): each opponent chooses one of their own units, and it is killed; mine stay
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-237" .hand
  let (s2, _) ← put s1 s.me "OGN-017" .base
  let (s3, g) ← put s2 s.you "OGN-017" .base
  let (s4, h) ← put s3 s.you "OGN-001" .base
  let a ← play s4 s.me c [] { obj := fun o => o == h }
  let b ← play (s4.setZone (.player s.you .base) []) s.me c
  return a.countIn s.you .trash "OGN-001" == 1 && a.countIn s.you .base "OGN-017" == 1 &&
    (a.obj? g).isSome && a.countIn s.me .base "OGN-017" == 1 &&
    a.countIn s.me .trash "OGN-017" == 0 &&
    b.countIn s.me .base "OGN-017" == 1

-- Super Mega Death Rocket! (OGN-252): deal 5 to a unit; when I conquer, from my Trash, I may
-- discard 1 to return it to my hand (not when I hold, not for the opponent's conquer, not
-- without a card to discard, and only from the Trash)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-252" .hand
  let (s2, u) ← put s1 s.you "OGN-088" .base
  let hit ← play s2 s.me c [u]
  let (t1, bf) ← putBf s s.me "OGN-294"
  let (t2, _) ← put t1 s.me "OGN-252" .trash
  let (t3, _) ← put t2 s.me "OGN-136" .hand
  let handOf (x : GameState) := (x.zone (.player s.me .hand)).length
  let yes ← fire t3 [.scored s.me bf true] { yes := true }
  let no ← fire t3 [.scored s.me bf true] { yes := false }
  let hold ← fire t3 [.scored s.me bf false] { yes := true }
  let foe ← fire t3 [.scored s.you bf true] { yes := true }
  let (u1, _) ← put t1 s.me "OGN-252" .trash
  let empty ← fire (u1.setZone (.player s.me .hand) []) [.scored s.me bf true] { yes := true }
  let (v1, _) ← put (t3.setZone (.player s.me .trash) []) s.me "OGN-252" .hand
  let inHand ← fire v1 [.scored s.me bf true] { yes := true }
  let (v2, _) ← put (t3.setZone (.player s.me .trash) []) s.me "OGN-252" .base
  let inBase ← fire v2 [.scored s.me bf true] { yes := true }
  let (w1, _) ← put t3 s.you "OGN-252" .trash
  let theirs ← fire w1 [.scored s.me bf true] { yes := true }
  return (hit.obj? u).map (·.damage) == some 5 &&
    yes.countIn s.me .hand "OGN-252" == 1 && yes.countIn s.me .trash "OGN-252" == 0 &&
    handOf yes == handOf t3 && yes.countIn s.me .trash "OGN-136" == 1 &&
    no.countIn s.me .trash "OGN-252" == 1 && hold.countIn s.me .trash "OGN-252" == 1 &&
    foe.countIn s.me .trash "OGN-252" == 1 && empty.countIn s.me .trash "OGN-252" == 1 &&
    inHand.countIn s.me .trash "OGN-136" == 0 && inBase.countIn s.me .trash "OGN-136" == 0 &&
    theirs.countIn s.you .trash "OGN-252" == 1

-- Immortal Phoenix (OGN-037): when I kill a unit with a spell, I may pay 1 Energy and Fury to play
-- it from my Trash (not when I decline, not for the opponent's Trash, not from the hand)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-229" .hand
  let (s2, u) ← put s1 s.you "OGN-088" .base
  let (s3, _) ← put s2 s.me "OGN-037" .trash
  let (s4, _) ← put s2 s.you "OGN-037" .trash
  let (s5, _) ← put s2 s.me "OGN-037" .hand
  let a ← play s3 s.me c [u]
  let no ← play s3 s.me c [u] { yes := false }
  let foe ← play s4 s.me c [u]
  let hand ← play s5 s.me c [u]
  return a.countIn s.me .base "OGN-037" == 1 && a.countIn s.me .trash "OGN-037" == 0 &&
    a.countIn s.you .trash "OGN-088" == 1 && no.countIn s.me .trash "OGN-037" == 1 &&
    foe.countIn s.you .trash "OGN-037" == 1 && hand.countIn s.me .hand "OGN-037" == 1

-- Tideturner (OGN-199): when I play it, I may choose a friendly unit: it goes to that unit's
-- location, and that unit comes to my base (not for an enemy unit, not when I decline)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-199" .hand
  let (s2, u) ← putAt s1 s.me "OGN-136" s.bf0
  let (s3, foe) ← putAt s2 s.you "OGN-136" s.bf0
  let pick : Says := { yes := true, pick := fun ts => ts.contains u }
  let a ← play s3 s.me c [] pick
  let no ← play s3 s.me c [] { pick with yes := false }
  let t ← a.firstOf s.me .base "OGN-199" <|> (a.zone .battlefieldZone).find? (fun x =>
    (a.cardDef? x).any (·.id == cid "OGN-199"))
  let tn ← no.firstOf s.me .base "OGN-199"
  let (b1, v) ← put s1 s.me "OGN-136" .base
  let same ← play b1 s.me c [] { yes := true, pick := fun ts => ts.contains v }
  let ts ← same.firstOf s.me .base "OGN-199"
  -- no friendly unit to choose: nothing happens; a Vilemaw's Lair (OGN-295) stops the swap
  let (z1, z) ← putAt (s.setZone (.player s.me .base) []) s.me "OGN-199" s.bf0
  let alone ← fire z1 [.played s.me z] { yes := true }
  let (v1, lair) ← putBf s s.me "OGN-295"
  let (v2, held) ← putAt v1 s.me "OGN-136" lair
  let (v3, home) ← put v2 s.me "OGN-199" .base
  let stuck ← fire v3 [.played s.me home] { yes := true, pick := fun ts => ts.contains held }
  -- played to a battlefield (by an effect): its place is that battlefield, so the unit at the base
  -- comes there, and it goes to the base
  let (w1, w) ← putAt s s.me "OGN-199" s.bf0
  let (w2, base) ← put w1 s.me "OGN-136" .base
  let there ← fire w2 [.played s.me w] { yes := true, pick := fun ts => ts.contains base }
  return (a.obj? t).bind (·.loc) == some s.bf0 && (a.obj? u).bind (·.loc) == none &&
    (a.zone (.player s.me .base)).contains u && (a.obj? foe).bind (·.loc) == some s.bf0 &&
    (no.obj? tn).bind (·.loc) == none && (no.obj? u).bind (·.loc) == some s.bf0 &&
    (same.obj? ts).bind (·.loc) == none && (same.obj? v).bind (·.loc) == none &&
    (there.obj? base).bind (·.loc) == some s.bf0 && (alone.obj? z).bind (·.loc) == some s.bf0 &&
    (stuck.obj? held).bind (·.loc) == some lair && (stuck.obj? home).bind (·.loc) == none &&
    ((there.zone (.player s.me .base)).filter (fun z =>
      (there.cardDef? z).any (·.id == cid "OGN-199"))).length == 1

-- Teemo, Strategist (OGN-121): when I defend, or when I am played from Hidden, deal 1 to an enemy
-- unit here for each card with Hidden among the top 5 cards of my Main Deck, then recycle them
#guard t fun s => do
  let bf := s.bf0
  let empty := s.setZone (.player s.me .mainDeck) []
  let (d1, _) ← put empty s.me "OGN-135" .mainDeck
  let (d2, _) ← put d1 s.me "OGN-135" .mainDeck
  let (d3, _) ← put d2 s.me "OGN-136" .mainDeck
  let (d4, _) ← put d3 s.me "OGN-136" .mainDeck
  let (d5, _) ← put d4 s.me "OGN-135" .mainDeck
  let (d6, _) ← put d5 s.me "OGN-135" .mainDeck
  let (d7, _) ← put d6 s.me "OGN-135" .mainDeck
  let (e1, _) ← putAt d7 s.me "OGN-121" bf
  let (e2, foe) ← putAt e1 s.you "OGN-088" bf
  let a ← fire e2 [.combatStarted bf s.you]
  let mine ← fire e2 [.combatStarted bf s.me]
  let deck (x : GameState) := (x.zone (.player s.me .mainDeck)).length
  -- played from Hidden: the card was hidden (fromHidden); a card played from the hand does not
  let (g1, t) ← putAt e2 s.me "OGN-121" bf
  let hid := g1.modObj t (fun o => { o with fromHidden := true })
  let h ← fire hid [.played s.me t]
  let hand ← fire g1 [.played s.me t]
  return (a.obj? foe).map (·.damage) == some 3 && deck a == deck e2 &&
    (a.zone (.player s.me .mainDeck)).head? != (e2.zone (.player s.me .mainDeck)).head? &&
    (mine.obj? foe).map (·.damage) == some 0 && (h.obj? foe).map (·.damage) == some 3 &&
    (hand.obj? foe).map (·.damage) == some 0

-- Teemo, Strategist (OGN-121), more: really played from Hidden (hide, then play from the next turn)
-- the card remembers it; played from the hand it does not; with fewer than 5 cards in the deck only
-- those are recycled; the opponent's Teemo defending hits my unit
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-121" .hand
  let mine := s1.control s.me s.bf0
  let hide ← activate mine s.me c 2 [s.bf0] ⟨0, [.fury]⟩
  let h ← (hide.zone (.player s.me .hidden)).head?
  let next := { hide with turn := hide.turn + 1 }
  let played ← activate next s.me h 3 [] ⟨0, []⟩
  let teemo ← played.firstOf s.me .base "OGN-121"
  let (t1, d) ← put s s.me "OGN-121" .hand
  let handed ← play t1 s.me d
  let hteemo ← handed.firstOf s.me .base "OGN-121"
  let few := s.setZone (.player s.me .mainDeck) []
  let (f1, _) ← put few s.me "OGN-135" .mainDeck
  let (f2, _) ← put f1 s.me "OGN-136" .mainDeck
  let (f3, _) ← putAt f2 s.me "OGN-121" s.bf0
  let (f4, foe) ← putAt f3 s.you "OGN-088" s.bf0
  let fewer ← fire f4 [.combatStarted s.bf0 s.you]
  let (g1, _) ← putAt (s.setZone (.player s.you .mainDeck) []) s.you "OGN-121" s.bf0
  let (g2, v) ← putAt g1 s.me "OGN-088" s.bf0
  let (g3, _) ← put g2 s.you "OGN-135" .mainDeck
  let theirs ← fire g3 [.combatStarted s.bf0 s.me]
  return (played.obj? teemo).map (·.fromHidden) == some true &&
    (handed.obj? hteemo).map (·.fromHidden) == some false &&
    (fewer.obj? foe).map (·.damage) == some 1 &&
    (fewer.zone (.player s.me .mainDeck)).length == 2 &&
    (theirs.obj? v).map (·.damage) == some 1

-- Miss Fortune, Buccaneer (OGN-193): I may play her to an open battlefield; while she is in play,
-- friendly units may be played to open battlefields (not the opponent's, not without her, not to
-- an occupied battlefield)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-193" .hand
  let a ← play s1 s.me c [s.bf0]
  let (t1, _) ← put s s.me "OGN-193" .base
  let (t2, u) ← put t1 s.me "OGN-136" .hand
  let viaMf ← play t2 s.me u [s.bf0]
  let (v1, w) ← put s s.me "OGN-136" .hand
  let without := play v1 s.me w [s.bf0]
  let (x1, y) ← put t1 s.you "OGN-136" .hand
  let theirs := play x1 s.you y [s.bf0]
  let b1 := t2.control s.you s.bf0
  let busy := play b1 s.me u [s.bf0]
  -- the opponent's "can't play cards" and a Mageseeker Warden both stop it
  let (w1, _) ← putAt t2 s.you "OGN-070" s.bf0
  let warded := play w1 s.me u [s.bf0]
  let noPlay := play (t2.addTurnFx s.you .opponentsCantPlay) s.me u [s.bf0]
  let noPlayMf := play (s1.addTurnFx s.you .opponentsCantPlay) s.me c [s.bf0]
  -- a Miss Fortune in the hand does not let other units go
  let (h1, _) ← put s s.me "OGN-193" .hand
  let (h2, hu) ← put h1 s.me "OGN-136" .hand
  let inHand := play h2 s.me hu [s.bf0]
  return (a.zone .battlefieldZone).any (fun x => (a.cardDef? x).any (·.id == cid "OGN-193")) &&
    (viaMf.zone .battlefieldZone).any (fun x => (viaMf.cardDef? x).any (·.id == cid "OGN-136") &&
      (viaMf.obj? x).any (·.loc == some s.bf0)) &&
    without.isNone && theirs.isNone && busy.isNone && warded.isNone && noPlay.isNone &&
    noPlayMf.isNone && inHand.isNone

-- Udyr, Wildman (OGN-157): spend my buff, then choose a mode he has not chosen this turn: 2 damage
-- to a unit at a battlefield, stun one, ready him, or Ganking this turn
#guard t fun s => do
  let (s1, udyr) ← put s s.me "OGN-157" .base
  let (s2, foe) ← putAt s1 s.you "OGN-088" s.bf0
  let b := s2.buff udyr
  let deal ← activate b s.me udyr 0 [] ⟨0, []⟩ ({ yes := true } : Says)
  let gank ← activate b s.me udyr 0 [] ⟨0, []⟩ ({ yes := false } : Says)
  let noted := b.addTurnFxOn s.me udyr (.modeUsed 1)
  let again := activate noted s.me udyr 0 [] ⟨0, []⟩ ({ yes := true } : Says)
  let unbuffed := activate s2 s.me udyr 0 [] ⟨0, []⟩
  -- the other modes: stun (second from the start: 2 from the end), ready (1), Ganking (0)
  let stun ← activate b s.me udyr 0 [] ⟨0, []⟩ ({ fromEnd := some 2 } : Says)
  let tired := b.tire udyr
  let ready ← activate tired s.me udyr 0 [] ⟨0, []⟩ ({ fromEnd := some 1 } : Says)
  let first ← activate b s.me udyr 0 [] ⟨0, []⟩ ({ fromEnd := some 3 } : Says)
  -- a mode chosen in an earlier use of the ability this turn is noted by the use
  let used := deal.turnFx.any (fun f => f.kind == .modeUsed 1)
  let again2 ← again
  return (deal.obj? foe).map (·.damage) == some 2 &&
    (deal.obj? udyr).map (·.buffed) == some false &&
    (gank.obj? foe).map (·.damage) == some 0 && gank.hasKw udyr .ganking &&
    (gank.obj? udyr).map (·.buffed) == some false && !deal.hasKw udyr .ganking &&
    (again2.obj? foe).map (·.damage) == some 0 &&
    (again2.obj? udyr).map (·.buffed) == some false &&
    unbuffed.isNone && (stun.obj? foe).map (·.stunned) == some true &&
    (stun.obj? foe).map (·.damage) == some 0 && ready.tired udyr == some false &&
    (first.obj? foe).map (·.damage) == some 2 && used

-- Lee Sin, Ascetic (OGN-078): exhaust: buff him; he can have any number of buffs, each +1 Might
#guard t fun s => do
  let (s1, lee) ← put s s.me "OGN-078" .base
  let (s2, other) ← put s1 s.me "OGN-136" .base
  let base := s2.mightNow lee
  let one ← activate s2 s.me lee 1
  let two ← activate (one.modObj lee (fun o => { o with exhausted := false })) s.me lee 1
  let three ← activate (two.modObj lee (fun o => { o with exhausted := false })) s.me lee 1
  let plain := (buffObj (buffObj s2 other).1 other).1
  let spent := (unbuffObj three lee).1
  return one.mightNow lee == base.map (· + 1) && two.mightNow lee == base.map (· + 2) &&
    three.mightNow lee == base.map (· + 3) && spent.mightNow lee == base.map (· + 2) &&
    plain.mightNow other == (s2.mightNow other).map (· + 1) &&
    (one.obj? lee).map (·.buffed) == some true && (activate one s.me lee 1).isNone &&
    -- the turn bonus for each buff (3 buffs: 3 * 2), the event for each extra buff, a cleared card
    (three.addTurnFx s.me .buffsExtraMight).mightNow lee == base.map (· + 6) &&
    (buffObj one lee).2 == [Event.buffed lee] && (buffObj s2 other).2 == [Event.buffed other] &&
    (three.obj? lee).map (fun o => (Object.cleared o).extraBuffs) == some 0

-- Caitlyn, Patrolling (OGN-068): she must be assigned combat damage last; exhaust: deal damage
-- equal to her Might to a unit at a battlefield, only while she is at a battlefield
#guard t fun s => do
  let bf := s.bf0
  let (s1, cait) ← putAt s s.me "OGN-068" bf
  let (s2, other) ← putAt s1 s.me "OGN-136" bf
  let (s3, foe) ← putAt s2 s.you "OGN-088" bf
  let picks (acc : List ObjId) : List ObjId :=
    (legalAssigns s3 bf s.you acc).filterMap (fun a => match a.kind with
      | .assignPick u => some u | _ => none)
  let (t1, c2) ← putAt s2 s.me "OGN-068" bf
  let two (acc : List ObjId) := (legalAssigns t1 bf s.you acc).filterMap (fun a =>
    match a.kind with | .assignPick u => some u | _ => none)
  let hit ← activate s3 s.me cait 1 [foe] ⟨0, []⟩
  let (h1, home) ← put s s.me "OGN-068" .base
  let (h2, _) ← putAt h1 s.you "OGN-088" bf
  let away := activate h2 s.me home 1 [] ⟨0, []⟩
  -- a Tank (Blitzcrank, OGN-067) is first, then the others, Caitlyn last; she can be the only one
  let (k1, tank) ← putAt s2 s.me "OGN-067" bf
  let order (acc : List ObjId) := (legalAssigns k1 bf s.you acc).filterMap (fun a =>
    match a.kind with | .assignPick u => some u | _ => none)
  let (o1, only) ← putAt (s.setZone .battlefieldZone []) s.me "OGN-068" bf
  let (o2, _) ← putAt o1 s.you "OGN-088" bf
  let lone := (legalAssigns o2 bf s.you []).map (·.kind)
  let buffedHit ← activate (s3.buff cait) s.me cait 1 [foe] ⟨0, []⟩
  let dmgBuffed := (buffedHit.obj? foe).map (·.damage)
  let mightBuffed := ((s3.buff cait).mightNow cait).map Int.toNat
  let dmg := (hit.obj? foe).map (·.damage)
  let might := (s3.mightNow cait).map Int.toNat
  return picks [] == [other] && picks [other] == [cait] && two [] == [other] &&
    (two [other]).length == 2 && (two [other]).contains c2 &&
    dmg == might && away.isNone && dmgBuffed == mightBuffed && mightBuffed != might &&
    order [] == [tank] && (order [tank]).contains other && !(order [tank]).contains cait &&
    lone == [.assignPick only] && hit.tired cait == some true &&
    (away.map (·.tired home)) != some (some true)

-- Tryndamere, Barbarian (OGN-034): when he conquers, if I assigned 5 or more excess damage to
-- enemy units, I score 1 point (the damage beyond what is lethal, counted for the enemy units of
-- the Combat only; the note of the last Combat of the turn stands)
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-294"
  let (s2, _) ← putAt s1 s.me "OGN-034" bf
  let (s3, foe) ← putAt s2 s.you "OGN-088" s.bf0
  let (s4, mine) ← put s3 s.me "OGN-136" .base
  let need := s4.need foe
  let ex := excessOf s4 s.me [(foe, need + 5), (mine, 99)]
  let few := excessOf s4 s.me [(foe, need + 4)]
  let under := excessOf s4 s.me [(foe, need - 1)]
  let hit ← fire (noteExcess s4 s.me 5) [.scored s.me bf true]
  let miss ← fire (noteExcess s4 s.me 4) [.scored s.me bf true]
  let old ← fire (noteExcess (noteExcess s4 s.me 5) s.me 1) [.scored s.me bf true]
  let theirs ← fire (noteExcess s4 s.you 5) [.scored s.me bf true]
  let hold ← fire (noteExcess s4 s.me 5) [.scored s.me bf false]
  -- a damaged enemy needs less (more is excess); with two enemies only the last has an excess
  let (s5, foe2) ← putAt s4 s.you "OGN-136" s.bf0
  let hurt := s5.modObj foe (fun o => { o with damage := 3 })
  let damaged := excessOf hurt s.me [(foe, need - 3 + 2)]
  let two := excessOf s5 s.me [(foe2, s5.need foe2), (foe, need + 1)]
  let pts (x : GameState) := x.pointsOf s.me
  return ex == 5 && few == 4 && under == 0 && damaged == 2 && two == 1 &&
    pts hit == pts s4 + 1 && pts miss == pts s4 &&
    pts old == pts s4 && pts theirs == pts s4 && pts hold == pts s4

-- Volibear, Furious (OGN-041): when he attacks, deal 5 damage split among any number of enemy units
-- here (five single damages, each to a unit I choose)
#guard t fun s => do
  let bf := s.bf0
  let (s1, _) ← putAt s s.me "OGN-041" bf
  let (s2, a) ← putAt s1 s.you "OGN-088" bf
  let (s3, b) ← putAt s2 s.you "OGN-088" bf
  let other := (s.battlefields.filter (· != bf)).head?.getD ⟨0⟩
  let (s4, away) ← putAt s3 s.you "OGN-088" other
  let one ← fire s2 [.combatStarted bf s.me]
  let allA ← fire s4 [.combatStarted bf s.me] { obj := fun o => o == a }
  let allB ← fire s4 [.combatStarted bf s.me] { obj := fun o => o == b }
  let defend ← fire s4 [.combatStarted bf s.you]
  -- the choices that would go wrong with another place or side: another battlefield's unit, and
  -- Volibear himself, are offered first and are not hit
  let toAway ← fire s4 [.combatStarted bf s.me] { obj := fun o => o == away }
  let (m1, vol) ← putAt s s.me "OGN-041" bf
  let (m2, _) ← putAt m1 s.you "OGN-088" bf
  let toSelf ← fire m2 [.combatStarted bf s.me] { obj := fun o => o == vol }
  let (n1, _) ← putAt s s.me "OGN-041" bf
  let nobody ← fire n1 [.combatStarted bf s.me]
  let dmg (x : GameState) (u : ObjId) := (x.obj? u).map (·.damage)
  return dmg one a == some 5 && dmg allA a == some 5 && dmg allA b == some 0 &&
    dmg allB b == some 5 && dmg allA away == some 0 && dmg defend a == some 0 &&
    dmg toAway away == some 0 && dmg toSelf vol == some 0 &&
    nobody.countIn s.me .base "OGN-041" == 0

-- Bullet Time (OGN-268): pay any amount of Power to deal that much damage to all enemy units at a
-- battlefield (the Power in the pool is paid, one unit at a time; the units elsewhere and mine are
-- not hit; paying nothing deals nothing)
#guard t fun s => do
  let bf := s.bf0
  let other := (s.battlefields.filter (· != bf)).head?.getD ⟨0⟩
  let (s1, c) ← put s s.me "OGN-268" .hand
  let (s2, a) ← putAt s1 s.you "OGN-088" bf
  let (s3, b) ← putAt s2 s.you "OGN-088" bf
  let (s4, away) ← putAt s3 s.you "OGN-088" other
  let (s5, mine) ← putAt s4 s.me "OGN-088" bf
  let funded := s5.fund s.me 1 (fury := 3)
  let rich ← cast (s5.fund s.me 4 (fury := 3)) s.me c ⟨1, []⟩ [bf]
  -- an empty battlefield: the payment is made all the same
  let emptyBf ← cast (s1.fund s.me 1 (fury := 2)) s.me c ⟨1, []⟩ [bf]
  let three ← cast funded s.me c ⟨1, []⟩ [bf]
  let zero ← cast funded s.me c ⟨1, []⟩ [bf] { yes := false }
  let dmg (x : GameState) (u : ObjId) := (x.obj? u).map (·.damage)
  let left := (three.poolOf s.me).fury
  return dmg three a == some 3 && dmg three b == some 3 && dmg three away == some 0 &&
    dmg three mine == some 0 && dmg zero a == some 0 && left == 0 && (zero.poolOf s.me).fury == 3 &&
    (rich.poolOf s.me).energy == 3 && (emptyBf.poolOf s.me).fury == 0

-- Fox-Fire (OGN-256): kill any number of units at a battlefield with total Might 4 or less (the
-- player says yes to each step): two Might-1 units and a Might-2 unit are 4; the Might-3 and
-- Might-4 units stay; with 3 and 4 only, the unit of 3 goes; declining kills nothing
#guard t fun s => do
  let bf := s.bf0
  let (s1, c) ← put s s.me "OGN-256" .hand
  let (s2, r1) ← putAt s1 s.you "OGN-271" bf
  let (s3, r2) ← putAt s2 s.me "OGN-271" bf
  let (s4, two) ← putAt s3 s.you "OGN-136" bf
  let (s5, three) ← putAt s4 s.you "OGN-037" bf
  let (s6, four) ← putAt s5 s.you "OGN-167" bf
  let other := (s.battlefields.filter (· != bf)).head?.getD ⟨0⟩
  let (s7, away) ← putAt s6 s.you "OGN-271" other
  let a ← play s7 s.me c [bf]
  let no ← play s7 s.me c [bf] { yes := false }
  let (t2, c2) ← put s s.me "OGN-256" .hand
  let (t3, th) ← putAt t2 s.you "OGN-037" bf
  let (t4, fo) ← putAt t3 s.you "OGN-167" bf
  let b ← play t4 s.me c2 [bf]
  -- 3 and 1: the Might-1 unit goes first, the Might-3 unit after it (4 in all); a unit in the base
  -- is not at the battlefield
  let (u1, c3) ← put s s.me "OGN-256" .hand
  let (u2, one) ← putAt u1 s.you "OGN-271" bf
  let (u3, tre) ← putAt u2 s.you "OGN-037" bf
  let (u4, home) ← put u3 s.you "OGN-271" .base
  let both ← play u4 s.me c3 [bf]
  let alive (x : GameState) (u : ObjId) := (x.obj? u).isSome && (x.obj? u).any (·.loc == some bf)
  return !alive a r1 && !alive a r2 && !alive a two && alive a three && alive a four &&
    (a.obj? away).bind (·.loc) == some other && alive no r1 && alive no two &&
    !alive b th && alive b fo &&
    !alive both one && !alive both tre && (both.obj? home).isSome

-- Guerilla Warfare (OGN-264): return up to two cards with Hidden from my Trash to my hand, and
-- hiding costs nothing this turn (the Power paid for Hide comes back)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-264" .hand
  let (s2, _) ← put s1 s.me "OGN-135" .trash
  let (s3, _) ← put s2 s.me "OGN-135" .trash
  let (s4, _) ← put s3 s.me "OGN-135" .trash
  let (s5, _) ← put s4 s.me "OGN-136" .trash
  let a ← play s5 s.me c
  let no ← play s5 s.me c [] { yes := false }
  let inHand (x : GameState) := x.countIn s.me .hand "OGN-135"
  let noted := a.turnFx.any (fun f => f.kind == .hideFree)
  -- hiding: with the note the Power comes back
  let (h1, hc) ← put s s.me "OGN-135" .hand
  let mine := h1.control s.me s.bf0
  let normal ← activate mine s.me hc 0 [s.bf0] ⟨0, [.fury]⟩
  let free ← activate (mine.addTurnFx s.me .hideFree) s.me hc 0 [s.bf0] ⟨0, [.fury]⟩
  let hidden (x : GameState) := (x.zone (.player s.me .hidden)).length
  -- the next turn, and the opponent's note, give nothing back
  let later ← activate ({ mine.addTurnFx s.me .hideFree with turn := mine.turn + 1 }) s.me hc 0
    [s.bf0] ⟨0, [.fury]⟩
  let theirs ← activate (mine.addTurnFx s.you .hideFree) s.me hc 0 [s.bf0] ⟨0, [.fury]⟩
  return hidden free == 1 && hidden normal == 1 && (later.poolOf s.me).any == 0 &&
    (theirs.poolOf s.me).any == 0 &&
    inHand a == inHand s5 + 2 && a.countIn s.me .trash "OGN-135" == 1 &&
    a.countIn s.me .trash "OGN-136" == 1 && inHand no == inHand s5 && noted &&
    (free.poolOf s.me).any == (normal.poolOf s.me).any + 1

-- Daughter of the Void (OGN-247): exhaust, Reaction: add one Power of any domain; used only to play
-- spells (approximation: only while I hold a spell)
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-247" .legendZone
  let (s2, _) ← put s1 s.me "OGN-229" .hand
  let (s3, _) ← put s1 s.me "OGN-136" .hand
  let use (x : GameState) : Option GameState :=
    match step 100 x ⟨.player s.me, .manaAbility g 0 ⟨0, []⟩⟩ with
    | .ok (y, _) => some y
    | .error _ => none
  let on ← use s2
  let (s4, _) ← put s2 s.me "OGN-136" .hand
  let more ← use s4
  -- the opponent's Legend is not mine; a spell in the opponent's hand is not a spell of mine
  let (o1, og) ← put s s.you "OGN-247" .legendZone
  let (o2, _) ← put o1 s.you "OGN-229" .hand
  let (o3, _) ← put (s.setZone (.player s.me .hand) []) s.me "OGN-247" .legendZone
  let (o4, _) ← put o3 s.you "OGN-229" .hand
  let (_, pg) ← put (s.setZone (.player s.me .hand) []) s.me "OGN-247" .legendZone
  let theirsOnly := (legalActions o4).contains ⟨.player s.me, .manaAbility pg 0 ⟨0, []⟩⟩
  let useOf (x : GameState) (g : ObjId) : Bool :=
    (legalActions x).contains ⟨.player s.me, .manaAbility g 0 ⟨0, []⟩⟩
  return (on.poolOf s.me).any == (s2.poolOf s.me).any + 1 && on.tired g == some true &&
    (use s3).isNone && (use (s2.tire g)).isNone && (use on).isNone && more.tired g == some true &&
    !(useOf o2 og) && useOf s2 g && !useOf s3 g && !theirsOnly

-- Malzahar, Fanatic (OGN-113): kill a friendly unit or gear, exhaust: add two Power of any domain
-- (an Action; the kill is part of the effect here)
#guard t fun s => do
  let (s1, m) ← put s s.me "OGN-113" .base
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, g) ← put s2 s.me "OGN-124" .base
  let (s4, foe) ← put s3 s.you "OGN-136" .base
  let unit ← activate s4 s.me m 0 [] ⟨0, []⟩ { obj := fun o => o == u }
  let gear ← activate s4 s.me m 0 [] ⟨0, []⟩ { obj := fun o => o == g }
  let anyOf ← activate s4 s.me m 0 [] ⟨0, []⟩
  let tired := activate (s4.tire m) s.me m 0 [] ⟨0, []⟩
  -- the opponent's unit is not offered; Malzahar alone kills himself; a unit at a battlefield is
  -- offered
  let wanted ← activate s4 s.me m 0 [] ⟨0, []⟩ { obj := fun o => o == foe }
  let (l1, lone) ← put s s.me "OGN-113" .base
  let alone ← activate l1 s.me lone 0 [] ⟨0, []⟩
  let (f1, field) ← putAt s s.me "OGN-136" s.bf0
  let (f2, m2) ← put f1 s.me "OGN-113" .base
  let onField ← activate f2 s.me m2 0 [] ⟨0, []⟩ { obj := fun o => o == field }
  return unit.countIn s.me .trash "OGN-136" == 1 && (unit.poolOf s.me).any == 2 &&
    unit.tired m == some true && gear.countIn s.me .trash "OGN-124" == 1 &&
    (gear.poolOf s.me).any == 2 && (anyOf.poolOf s.me).any == 2 &&
    unit.countIn s.you .base "OGN-136" == 1 && tired.isNone &&
    wanted.countIn s.you .base "OGN-136" == 1 && alone.countIn s.me .trash "OGN-113" == 1 &&
    (alone.poolOf s.me).any == 2 && onField.countIn s.me .trash "OGN-136" == 1

-- The Boss (OGN-269): when a buffed unit I control dies, I may pay one Power and exhaust him to
-- bring it back to my base exhausted (approximation: it dies, then returns); when I conquer,
-- ready him
#guard t fun s => do
  let (s1, boss) ← put s s.me "OGN-269" .legendZone
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, foe) ← put s2 s.you "OGN-136" .base
  let funded := (s3.fund s.me 0 (fury := 1))
  let die (x : GameState) (id : ObjId) : Option GameState :=
    let (k, ev) := killObj x id
    fire k ev
  let back ← die (funded.buff u) u
  let plain ← die funded u
  let theirs ← die (funded.buff foe) foe
  let broke ← die ((s3.noRunes s.me).buff u) u
  let spent ← die ((funded.buff u).tire boss) u
  let no ← (let (k, ev) := killObj (funded.buff u) u; fire k ev { yes := false })
  let ready ← fire (s3.tire boss) [.scored s.me s.bf0 true]
  -- two buffed units die at once: the Boss saves one (he is exhausted for the second)
  let (s6, v) ← put funded s.me "OGN-136" .base
  let both := (s6.buff u).buff v
  let (k1, ev1) := killObj both u
  let (k2, ev2) := killObj k1 v
  let two ← fire k2 (ev1 ++ ev2)
  -- the opponent's conquer does not ready him
  let theirsReady ← fire (s3.tire boss) [.scored s.you s.bf0 true]
  let unitBack := (back.zone (.player s.me .base)).filter (fun x =>
    (back.cardDef? x).any (·.id == cid "OGN-136"))
  return back.countIn s.me .base "OGN-136" == 1 && back.countIn s.me .trash "OGN-136" == 0 &&
    unitBack.all (fun x => back.tired x == some true) && back.tired boss == some true &&
    (back.poolOf s.me).fury == 0 && plain.countIn s.me .trash "OGN-136" == 1 &&
    theirs.countIn s.you .trash "OGN-136" == 1 && broke.countIn s.me .trash "OGN-136" == 1 &&
    spent.countIn s.me .trash "OGN-136" == 1 && no.countIn s.me .trash "OGN-136" == 1 &&
    ready.tired boss == some false && two.countIn s.me .base "OGN-136" == 1 &&
    two.countIn s.me .trash "OGN-136" == 1 && theirsReady.tired boss == some true

-- Zhonya's Hourglass (OGN-077): the next time a friendly unit dies, the gear is killed and the
-- unit comes back exhausted (approximation: it dies, then returns); once, and not for an enemy unit
#guard t fun s => do
  let (s1, _) ← put s s.me "OGN-077" .base
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let (s4, foe) ← put s3 s.you "OGN-136" .base
  let die (x : GameState) (id : ObjId) : Option GameState :=
    let (k, ev) := killObj x id
    fire k ev
  let a ← die s4 u
  let theirs ← die s4 foe
  let (k1, ev1) := killObj s4 u
  let (k2, ev2) := killObj k1 v
  let twice ← fire k2 (ev1 ++ ev2)
  let back := (a.zone (.player s.me .base)).filter (fun x =>
    (a.cardDef? x).any (·.id == cid "OGN-136"))
  return a.countIn s.me .base "OGN-136" == 2 && a.countIn s.me .trash "OGN-136" == 0 &&
    a.countIn s.me .trash "OGN-077" == 1 && a.countIn s.me .base "OGN-077" == 0 &&
    back.all (fun x => (a.obj? x).any (fun o => o.exhausted || x == v)) &&
    theirs.countIn s.you .trash "OGN-136" == 1 && theirs.countIn s.me .base "OGN-077" == 1 &&
    twice.countIn s.me .trash "OGN-136" == 1 && twice.countIn s.me .base "OGN-136" == 1

-- Unlicensed Armory (OGN-023): discard 1, exhaust: choose a friendly unit; the next time it dies
-- this turn, I may pay Fury to bring it back exhausted (approximation: it dies, then returns)
#guard t fun s => do
  let (s1, g) ← put s s.me "OGN-023" .base
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, v) ← put s2 s.me "OGN-136" .base
  let (s4, _) ← put s3 s.me "OGN-136" .hand
  let funded := s4.fund s.me 0 (fury := 1)
  let marked ← activate funded s.me g 0 [u] ⟨0, []⟩
  let die (x : GameState) (id : ObjId) : Option GameState :=
    let (k, ev) := killObj x id
    fire k ev
  let back ← die marked u
  let other ← die marked v
  let unmarked ← die funded u
  let no ← (let (k, ev) := killObj marked u; fire k ev { yes := false })
  let (p1, _) ← put marked s.me "OGN-136" .base
  let broke ← die (p1.setPool s.me {}) u
  let noHand := activate (s4.setZone (.player s.me .hand) []) s.me g 0 [u] ⟨0, []⟩
  let backed := (back.zone (.player s.me .base)).filter (fun x => x != v &&
    (back.cardDef? x).any (·.id == cid "OGN-136"))
  -- the unit that came back is a new one: it can die again for good
  let again ← (match backed.head? with
    | some b => (let (k, ev) := killObj back b; fire k ev)
    | none => none)
  -- an enemy unit cannot be chosen
  let (e1, foe) ← put s4 s.you "OGN-136" .base
  let enemy := activate e1 s.me g 0 [foe] ⟨0, []⟩
  return marked.tired g == some true && marked.handN s.me + 1 == funded.handN s.me &&
    back.countIn s.me .base "OGN-136" == 2 && back.countIn s.me .trash "OGN-136" == 1 &&
    (back.poolOf s.me).fury + 1 == (marked.poolOf s.me).fury &&
    other.countIn s.me .trash "OGN-136" == 2 &&
    unmarked.countIn s.me .trash "OGN-136" == 1 && no.countIn s.me .trash "OGN-136" == 2 &&
    broke.countIn s.me .trash "OGN-136" == 2 && noHand.isNone &&
    backed.all (fun x => back.tired x == some true) && backed.length == 1 &&
    again.countIn s.me .trash "OGN-136" == 2 && enemy.isNone

-- Baited Hook (OGN-242): 1 Energy and Order, exhaust: kill a friendly unit; among the top 5 cards
-- of my Main Deck, a unit with Might up to 1 more than the killed one may be played for free; the
-- rest are recycled
#guard t fun s => do
  let (s1, hook) ← put s s.me "OGN-242" .base
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let empty := s2.setZone (.player s.me .mainDeck) []
  let (d1, _) ← put empty s.me "OGN-088" .mainDeck
  let (d2, _) ← put d1 s.me "OGN-124" .mainDeck
  let (d3, _) ← put d2 s.me "OGN-167" .mainDeck
  let (d4, fit) ← put d3 s.me "OGN-037" .mainDeck
  let (d5, _) ← put d4 s.me "OGN-136" .mainDeck
  let (d6, _) ← put d5 s.me "OGN-136" .mainDeck
  let deck (x : GameState) := x.zone (.player s.me .mainDeck)
  let ids (x : GameState) := (deck x).map (fun c => ((x.cardDef? c).map (·.id.code)).getD "?")
  let yes ← activate d6 s.me hook 0 [u] ⟨1, [.order]⟩ { obj := fun o => o == fit }
  let no ← activate d6 s.me hook 0 [u] ⟨1, [.order]⟩ { yes := false }
  -- only the Might-4 unit in the top 5: nothing can be played, all five are recycled
  let (m1, _) ← put empty s.me "OGN-088" .mainDeck
  let (m2, _) ← put m1 s.me "OGN-167" .mainDeck
  let (m3, _) ← put m2 s.me "OGN-124" .mainDeck
  let none5 ← activate m3 s.me hook 0 [u] ⟨1, [.order]⟩
  -- fewer than five cards: three, one of them playable: two are recycled; none playable: all three
  let (f1, _) ← put empty s.me "OGN-124" .mainDeck
  let (f2, _) ← put f1 s.me "OGN-167" .mainDeck
  let (f3, _) ← put f2 s.me "OGN-037" .mainDeck
  let three ← activate f3 s.me hook 0 [u] ⟨1, [.order]⟩
  let threeNo ← activate f3 s.me hook 0 [u] ⟨1, [.order]⟩ { yes := false }
  -- a buffed unit counts with its buff: Might 3 (2 + 1) lets a Might-4 unit be played
  let (b1, _) ← put empty s.me "OGN-167" .mainDeck
  let buffedHit ← activate (b1.buff u) s.me hook 0 [u] ⟨1, [.order]⟩
  return yes.countIn s.me .trash "OGN-136" == 1 && yes.countIn s.me .base "OGN-037" == 1 &&
    (deck yes).length == 5 && (ids yes).head? == some "OGN-088" &&
    yes.tired hook == some true && no.countIn s.me .base "OGN-037" == 0 &&
    (deck no).length == 6 && (ids no).head? == some "OGN-088" &&
    none5.countIn s.me .base "OGN-167" == 0 && (deck none5).length == 3 &&
    (deck three).length == 2 && three.countIn s.me .base "OGN-037" == 1 &&
    (deck threeNo).length == 3 && buffedHit.countIn s.me .base "OGN-167" == 1

-- Mystic Reversal (OGN-080): gain control of a spell on the Chain (Confront's note is then the
-- opponent's, not mine; the spell still goes to its owner's Trash); the original choices stay
#guard t fun s => do
  let (s1, conf) ← put s s.me "OGN-129" .hand
  let (s2, rev) ← put s1 s.you "OGN-080" .hand
  let on ← passBy (← castStop s2 s.me conf) s.me
  let tgt ← (on.zone .chain).head?
  let after ← play on s.you rev [tgt]
  let plain ← play s2 s.me conf
  -- the Chain is empty: it cannot be played; a Reversal does not take an ability
  let empty := play s2 s.you rev []
  let handDiff := after.handN s.you == on.handN s.you - 1 + 1 && after.handN s.me == on.handN s.me
  return after.countIn s.me .trash "OGN-129" == 1 && after.countIn s.you .trash "OGN-080" == 1 &&
    after.turnFx.any (fun f => f.who == s.you) && !after.turnFx.any (fun f => f.who == s.me) &&
    plain.turnFx.any (fun f => f.who == s.me) && empty.isNone && handDiff

-- The Dreaming Tree (OGN-292): when a player chooses a friendly unit here with a spell, for the
-- first time each turn, they draw 1 (not an enemy unit, not a unit elsewhere, not a second time)
#guard t fun s => do
  let (s1, tree) ← putBf s s.me "OGN-292"
  let (s2, c) ← put s1 s.me "OGN-004" .hand
  let (s3, mine) ← putAt s2 s.me "OGN-136" tree
  let (s4, foe) ← putAt s3 s.you "OGN-136" tree
  let other := (s.battlefields.filter (· != tree)).head?.getD ⟨0⟩
  let (s5, away) ← putAt s4 s.me "OGN-136" other
  let hit ← play s5 s.me c [mine]
  let enemy ← play s5 s.me c [foe]
  let elsewhere ← play s5 s.me c [away]
  let twice ← fire s5 [.chosenBySpell s.me mine, .chosenBySpell s.me mine]
  let theirs ← fire s5 [.chosenBySpell s.you foe]
  return hit.handN s.me == s5.handN s.me && enemy.handN s.me + 1 == s5.handN s.me &&
    elsewhere.handN s.me + 1 == s5.handN s.me && twice.handN s.me == s5.handN s.me + 1 &&
    theirs.handN s.you == s5.handN s.you + 1

-- Swift Scout (OGN-263): I may hide a card with Hidden for one Energy instead of one Power; one
-- Energy, exhaust: put a Teemo unit I own into my hand from the Champion Zone or the board
#guard t fun s => do
  let (s1, sc) ← put s s.me "OGN-263" .legendZone
  let (s2, c) ← put s1 s.me "OGN-135" .hand
  let (n1, nc) ← put s s.me "OGN-135" .hand
  let hid (x : GameState) := (x.zone (.player s.me .hidden)).length
  let hides ← activate (s2.control s.me s.bf0) s.me c 2 [s.bf0] ⟨1, []⟩
  let without := activate (n1.control s.me s.bf0) s.me nc 2 [s.bf0] ⟨1, []⟩
  let normal ← activate (s2.control s.me s.bf0) s.me c 0 [s.bf0] ⟨0, [.fury]⟩
  -- with hiding free (Guerilla Warfare) the Energy comes back, not a Power
  let free := (s2.control s.me s.bf0).addTurnFx s.me .hideFree
  let paid ← activate free s.me c 2 [s.bf0] ⟨1, []⟩
  let baseline ← activate (s2.control s.me s.bf0) s.me c 2 [s.bf0] ⟨1, []⟩
  -- the opponent's Legend gives me nothing
  let (e1, _) ← put n1 s.you "OGN-263" .legendZone
  let theirs := activate (e1.control s.me s.bf0) s.me nc 2 [s.bf0] ⟨1, []⟩
  -- the Teemo unit on the board goes to the hand; or the one in the Champion Zone
  let (b1, _) ← put s2 s.me "OGN-121" .base
  let (b2, _) ← put b1 s.me "OGN-136" .base
  let board ← activate b2 s.me sc 1 [] ⟨1, []⟩
  let emptyZone := b2.setZone (.player s.me .championZone) []
  let (z1, _) ← put emptyZone s.me "OGN-121" .championZone
  let fromZone ← activate z1 s.me sc 1 [] ⟨1, []⟩ { yes := false }
  return (paid.poolOf s.me).energy == (baseline.poolOf s.me).energy + 1 &&
    (paid.poolOf s.me).any == (baseline.poolOf s.me).any && theirs.isNone &&
    hid hides == 1 && hid normal == 1 && without.isNone &&
    board.countIn s.me .hand "OGN-121" == 1 && board.countIn s.me .base "OGN-121" == 0 &&
    board.countIn s.me .base "OGN-136" == 1 && board.tired sc == some true &&
    fromZone.countIn s.me .hand "OGN-121" == 1 &&
    (fromZone.zone (.player s.me .championZone)).isEmpty

-- Nocturne, Horrifying (OGN-194): when I look at the top card of my deck (and do not draw it) and
-- see him, I may pay one Power to play him (Vision looks; the card must be one I see)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-171" .hand
  let (s2, n) ← put s1 s.me "OGN-194" .mainDeck
  let deck (x : GameState) := (x.zone (.player s.me .mainDeck)).length
  let seen ← play s2 s.me c
  let declined ← play s2 s.me c [] { yes := false }
  -- the Vision recycle is accepted and he is declined: he stays in the deck
  let keep ← fire (s2.fund s.me 0 (fury := 1)) [.lookedAt s.me n] { yes := false }
  -- he is second from the top: not seen by a Vision look
  let (u2, _) ← put (s1.setZone (.player s.me .mainDeck) []) s.me "OGN-194" .mainDeck
  let (u3, _) ← put u2 s.me "OGN-136" .mainDeck
  let second ← play u3 s.me c
  -- the event itself: with Power he comes, without he stays; the opponent's look is not mine
  let funded := s2.fund s.me 0 (fury := 1)
  let paid ← fire funded [.lookedAt s.me n]
  let broke ← fire (s2.fund s.me 0) [.lookedAt s.me n]
  let theirs ← fire funded [.lookedAt s.you n]
  -- the card is no longer in the deck (it is in the hand): it is not played from there
  let (h1, h) ← put s1 s.me "OGN-194" .hand
  let inHand ← fire (h1.fund s.me 0 (fury := 1)) [.lookedAt s.me h]
  return seen.countIn s.me .base "OGN-194" == 1 && deck seen + 1 == deck s2 &&
    declined.countIn s.me .base "OGN-194" == 0 && keep.countIn s.me .base "OGN-194" == 0 &&
    second.countIn s.me .base "OGN-194" == 0 &&
    paid.countIn s.me .base "OGN-194" == 1 && (paid.poolOf s.me).fury == 0 &&
    broke.countIn s.me .base "OGN-194" == 0 && theirs.countIn s.me .base "OGN-194" == 0 &&
    inHand.countIn s.me .base "OGN-194" == 0 && inHand.countIn s.me .hand "OGN-194" == 1

-- Time Warp (OGN-122): take a turn after this one, and banish it (not the Trash): the turn after is
-- mine, the one after that the opponent's, as if the extra turn had not been
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-122" .hand
  let a ← play s1 s.me c
  let t1 := beginTurnStep a []
  let t2 := beginTurnStep t1 []
  let t3 := beginTurnStep t2 []
  let plain := beginTurnStep s1 []
  -- two Time Warps: two extra turns of mine, then the opponent's
  let two := { a with extraTurns := a.extraTurns ++ [s.me] }
  let w1 := beginTurnStep two []
  let w2 := beginTurnStep w1 []
  let w3 := beginTurnStep w2 []
  -- cast in the opponent's turn: the next turn is mine, then the one after the opponent's
  let theirs := { s1 with active := some s.you, extraTurns := [s.me] }
  let o1 := beginTurnStep theirs []
  let o2 := beginTurnStep o1 []
  -- the extra turn does not use up the second player's first-turn Rune (3 Runes at regular turn 2)
  let early := { s1 with turn := 1, extraTurns := [s.me] }
  let e1 := beginTurnStep early []
  let e2 := beginTurnStep e1 []
  return a.extraTurns == [s.me] && a.countIn s.me .trash "OGN-122" == 0 &&
    a.countIn s.me .banishment "OGN-122" == 1 && t1.active == some s.me && t1.extraTurns == [] &&
    t2.active == some s.you && t3.active == some s.me && t1.turn == a.turn + 1 &&
    plain.active == some s.you && s1.extraTurns == [] &&
    w1.active == some s.me && w2.active == some s.me && w3.active == some s.you &&
    w3.turnShift == 2 && o1.active == some s.me && o2.active == some s.you &&
    o1.turnFx.isEmpty && e1.channelCount == 2 && e2.channelCount == 3 && e1.turnShift == 1 &&
    plain.turnShift == 0

-- Blind Fury (OGN-025): the top card of the opponent's Main Deck: a unit or gear is played, free,
-- by me (it stays the opponent's card: it goes to their Trash when it dies); a spell is banished
-- (approximation: a spell is not played)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-025" .hand
  let (u1, _) ← put s1 s.you "OGN-136" .mainDeck
  let (g1, _) ← put s1 s.you "OGN-124" .mainDeck
  let (p1, _) ← put s1 s.you "OGN-229" .mainDeck
  let unit ← play u1 s.me c
  let gear ← play g1 s.me c
  let spell ← play p1 s.me c
  let deck (x : GameState) := (x.zone (.player s.you .mainDeck)).length
  -- the opponent's deck is empty: nothing happens; mine is not touched; the unit comes in exhausted
  let bare ← play (s1.setZone (.player s.you .mainDeck) []) s.me c
  let mineDeck (x : GameState) := (x.zone (.player s.me .mainDeck)).length
  let mine := (unit.zone (.player s.me .base)).filter (fun x =>
    (unit.cardDef? x).any (·.id == cid "OGN-136"))
  let dies ← (mine.head?).map (fun x => (killObj unit x).1)
  return mine.length == 1 && mine.all (fun x => (unit.obj? x).any (fun o =>
      o.controller == s.me && o.owner == s.you)) && deck unit + 1 == deck u1 &&
    gear.countIn s.me .base "OGN-124" == 1 && deck gear + 1 == deck g1 &&
    spell.countIn s.you .banishment "OGN-229" == 1 && spell.countIn s.me .base "OGN-229" == 0 &&
    dies.countIn s.you .trash "OGN-136" == 1 && dies.countIn s.me .trash "OGN-136" == 0 &&
    bare.countIn s.me .base "OGN-136" == 0 && mineDeck unit == mineDeck u1 &&
    mine.all (fun x => unit.tired x == some true)

-- Divine Judgment (OGN-244): each player keeps 2 units, 2 gear, 2 runes and 2 cards of the hand,
-- and recycles the rest (the players choose what goes)
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-244" .hand
  let (a1, _) ← put s1 s.me "OGN-136" .base
  let (a2, _) ← put a1 s.me "OGN-136" .base
  let (a3, _) ← put a2 s.me "OGN-136" .base
  let (a4, _) ← put a3 s.me "OGN-124" .base
  let (a5, _) ← put a4 s.me "OGN-124" .base
  let (a6, _) ← put a5 s.me "OGN-124" .base
  let (b1, _) ← put a6 s.you "OGN-136" .base
  let (b2, _) ← put b1 s.you "OGN-136" .base
  let (b3, _) ← put b2 s.you "OGN-136" .base
  let (b4, _) ← put b3 s.you "OGN-124" .base
  let (b5, _) ← put b4 s.you "OGN-124" .base
  let (b6, _) ← put b5 s.you "OGN-124" .base
  let a ← play b6 s.me c
  let units (x : GameState) (p : PlayerId) :=
    ((x.zone (.player p .base)).filter (fun u => (x.cardDef? u).any (·.hasType .unit))).length
  let gear (x : GameState) (p : PlayerId) :=
    ((x.zone (.player p .base)).filter (fun u => (x.cardDef? u).any (·.hasType .gear))).length
  let runes (x : GameState) (p : PlayerId) :=
    ((x.zone (.player p .base)).filter (fun u => (x.cardDef? u).any (·.hasType .rune))).length
  let hand (x : GameState) (p : PlayerId) := (x.zone (.player p .hand)).length
  return units a s.me == 2 && units a s.you == 2 && gear a s.me == 2 && gear a s.you == 2 &&
    runes a s.me == min 2 (runes b6 s.me) && runes a s.you == min 2 (runes b6 s.you) &&
    hand a s.me == min 2 (hand b6 s.me - 1) && hand a s.you == min 2 (hand b6 s.you) &&
    (a.zone (.player s.me .mainDeck)).length > (b6.zone (.player s.me .mainDeck)).length

-- Divine Judgment, the runes: four runes each are recycled down to two (to the Rune Deck); a kind
-- with fewer than two is left alone
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-244" .hand
  let (r1, _) ← put s1 s.me "OGN-007" .base
  let (r2, _) ← put r1 s.me "OGN-007" .base
  let (r3, _) ← put r2 s.you "OGN-007" .base
  let (r4, _) ← put r3 s.you "OGN-007" .base
  let (r5, _) ← put r4 s.you "OGN-007" .base
  let rich := r5.rich s.me
  let a ← match step 100 rich ⟨.player s.me, .playCard c (payOf rich c) []⟩ with
    | .ok (x, _) => some (settleChain {} 80 x)
    | .error _ => none
  let runes (x : GameState) (p : PlayerId) :=
    ((x.zone (.player p .base)).filter (fun u => (x.cardDef? u).any (·.hasType .rune))).length
  let deck (x : GameState) (p : PlayerId) := (x.zone (.player p .runeDeck)).length
  return runes a s.me == 2 && runes a s.you == 2 && runes rich s.me > 2 && runes rich s.you > 2 &&
    deck a s.me > deck rich s.me && deck a s.you > deck rich s.you

-- Promising Future (OGN-115): each player looks at the top 5 cards of their deck, chooses a unit
-- or gear and plays it ignoring its Energy cost (the Power is paid), and recycles the rest; a
-- spell cannot be played here
#guard t fun s => do
  let (s1, c) ← put s s.me "OGN-115" .hand
  let mkDeck (x : GameState) (p : PlayerId) : Option GameState := do
    let (d0, _) ← put (x.setZone (.player p .mainDeck) []) p "OGN-088" .mainDeck
    let (d1, _) ← put d0 p "OGN-136" .mainDeck
    let (d2, _) ← put d1 p "OGN-124" .mainDeck
    let (d3, _) ← put d2 p "OGN-229" .mainDeck
    let (d4, _) ← put d3 p "OGN-037" .mainDeck
    let (d5, _) ← put d4 p "OGN-136" .mainDeck
    some d5
  let a1 ← mkDeck s1 s.me
  let a2 ← mkDeck a1 s.you
  let phoenix ← (a2.zone (.player s.me .mainDeck)).find? (fun x =>
    (a2.cardDef? x).any (·.id == cid "OGN-037"))
  let done ← play a2 s.me c [] { obj := fun o => o == phoenix }
  let deck (x : GameState) (p : PlayerId) := (x.zone (.player p .mainDeck)).length
  -- the Phoenix cannot be paid for (no Power): it is not played, and nothing is paid
  let poor := (a2.rich s.me).setPool s.me { energy := 12, mind := 3, calm := 3 }
  let broke ← match step 100 poor ⟨.player s.me, .playCard c (payOf poor c) []⟩ with
    | .ok (x, _) => some (settleChain { obj := fun o => o == phoenix } 40 x)
    | .error _ => none
  let ids (x : GameState) (p : PlayerId) := (x.zone (.player p .mainDeck)).map (fun u =>
    ((x.cardDef? u).map (·.id.code)).getD "?")
  return done.countIn s.me .base "OGN-037" == 1 && (deck done s.me) + 1 == deck a2 s.me &&
    (ids done s.me).head? == some "OGN-088" && (deck done s.you) + 1 == deck a2 s.you &&
    (done.zone (.player s.you .base)).any (fun u =>
      (done.cardDef? u).any (·.id == cid "OGN-136")) &&
    (done.poolOf s.me).fury + 1 == ((a2.rich s.me).poolOf s.me).fury &&
    broke.countIn s.me .base "OGN-037" == 0

-- Kai'Sa, Evolutionary (OGN-112): when she conquers, I may play a spell from my Trash with an
-- Energy cost less than my points, without its Energy (its Power is paid), then recycle it; only a
-- spell with no choice of objects to make (Confront) is played here
#guard t fun s => do
  let (s1, bf) ← putBf s s.me "OGN-294"
  let (s2, _) ← putAt s1 s.me "OGN-112" bf
  let (s3, _) ← put s2 s.me "OGN-129" .trash
  let (s4, _) ← put s3 s.me "OGN-229" .trash
  let points := s4.gainPoints s.me 5
  let rich := points.rich s.me
  let a ← fire rich [.scored s.me bf true]
  let no ← fire rich [.scored s.me bf true] { yes := false }
  let few ← fire (s4.rich s.me) [.scored s.me bf true]
  -- only a spell with a choice in the Trash: it stays; points equal to the cost: not enough
  let (v1, _) ← put s2 s.me "OGN-229" .trash
  let only := fire ((v1.gainPoints s.me 5).rich s.me) [.scored s.me bf true]
  let onlyV ← only
  let edge ← fire (((s3.gainPoints s.me 2)).rich s.me) [.scored s.me bf true]
  -- a spell with a Power cost: the Power is paid from the pool (and not when it is not there)
  let (p1, _) ← put s2 s.me "OGN-145" .trash
  let withPow := (p1.gainPoints s.me 5).rich s.me
  let paid ← fire withPow [.scored s.me bf true]
  let poor ← fire (withPow.setPool s.me { energy := 12 }) [.scored s.me bf true]
  return a.turnFx.length == rich.turnFx.length + 1 && a.countIn s.me .trash "OGN-129" == 0 &&
    a.countIn s.me .mainDeck "OGN-129" == 1 && a.countIn s.me .trash "OGN-229" == 1 &&
    no.countIn s.me .trash "OGN-129" == 1 && no.turnFx.length == rich.turnFx.length &&
    few.countIn s.me .trash "OGN-129" == 1 && few.turnFx.length == rich.turnFx.length &&
    onlyV.countIn s.me .trash "OGN-229" == 1 && edge.countIn s.me .trash "OGN-129" == 1 &&
    paid.countIn s.me .trash "OGN-145" == 0 && poor.countIn s.me .trash "OGN-145" == 1 &&
    (paid.poolOf s.me).body < (withPow.poolOf s.me).body

-- Heimerdinger, Inventor (OGN-111): he has the exhaust abilities of my legends, units and gear:
-- with Lee Sin (exhaust: buff me) in play, he can exhaust to buff himself; without Lee Sin he
-- cannot; not with the opponent's Lee Sin
#guard t fun s => do
  let (s1, hd) ← put s s.me "OGN-111" .base
  let (s2, lee) ← put s1 s.me "OGN-078" .base
  let leeIdx ← (RiftboundCards.Origins.OGN_111.fullAbilities.findIdx? (fun a => match a with
    | .activated _ _ b _ => b.body ==
        .ifThen (.hasFriendlyCard ⟨"OGN-078"⟩) (.prim (.buff .self)) .nop
    | _ => false))
  let used ← activate s2 s.me hd leeIdx [] ⟨0, []⟩
  let (n1, nhd) ← put s s.me "OGN-111" .base
  let without := activate n1 s.me nhd leeIdx [] ⟨0, []⟩
  let (t1, thd) ← put s s.me "OGN-111" .base
  let (t2, _) ← put t1 s.you "OGN-078" .base
  let theirs := activate t2 s.me thd leeIdx [] ⟨0, []⟩
  let again := activate used s.me hd leeIdx [] ⟨0, []⟩
  return (used.obj? hd).map (·.buffed) == some true && used.tired hd == some true &&
    (used.obj? lee).map (·.buffed) == some false && without.isNone && theirs.isNone &&
    again.isNone

-- Heimerdinger, Inventor (OGN-111), more: an ability with a guard that waits for a chosen
-- object (Baited Hook) is still not there without the Hook; a Legend's mana ability is his while
-- the Legend is there (Daughter of the Void, with a spell in hand)
#guard t fun s => do
  let abilities := RiftboundCards.Origins.OGN_111.fullAbilities
  let idxOf (c : String) : Option Nat := abilities.findIdx? (fun a => match a with
    | .activated _ _ b _ => (match b.body with
        | .ifThen (.and (.hasFriendlyCard id) _) _ _ => id == ⟨c⟩
        | .ifThen (.hasFriendlyCard id) _ _ => id == ⟨c⟩
        | _ => false)
    | _ => false)
  let hookIdx ← idxOf "OGN-242"
  let (s1, hd) ← put s s.me "OGN-111" .base
  let (s2, u) ← put s1 s.me "OGN-136" .base
  let (s3, _) ← put s2 s.me "OGN-242" .base
  let withHook := activate s3 s.me hd hookIdx [u] ⟨1, [.order]⟩
  let withoutHook := activate s2 s.me hd hookIdx [u] ⟨1, [.order]⟩
  let daughterIdx ← idxOf "OGN-247"
  let (l1, _) ← put s1 s.me "OGN-247" .legendZone
  let (l2, _) ← put l1 s.me "OGN-229" .hand
  let (n1, _) ← put s1 s.me "OGN-229" .hand
  let manaOk (x : GameState) :=
    (legalActions x).contains ⟨.player s.me, .manaAbility hd daughterIdx ⟨0, []⟩⟩
  return withHook.isSome && withoutHook.isNone && manaOk l2 && !manaOk n1

-- Playing a spell for free (the effect `play`): a spell with no choice goes on the Chain as a new
-- object, does its effect, and goes to the Trash; it is a play (Legion); a spell with a choice is
-- not played; a unit is still played to the Base
#guard t fun s => do
  let (s1, conf) ← put s s.me "OGN-129" .hand
  let (s2, veng) ← put s1 s.me "OGN-229" .hand
  let (s3, unit) ← put s2 s.me "OGN-136" .hand
  let (s4, src) ← put s3 s.me "OGN-129" .trash
  let playIt (x : GameState) (c : ObjId) : Option GameState :=
    let x2 := { x with pending := [.run x.me src { slots := [.obj c] } (.cons (.prim
      (.play (Selector.one .friendly .inHand [.sameAs (.slot 0)]))) .nil)] }
    match advance 100 x2 [] with
    | .ok (y, _) => some (settleChain {} 12 y)
    | .error _ => none
  let (s5, stu) ← put s4 s.me "OGN-103" .base
  let a0 ← playIt s5 conf
  let a ← playIt s4 conf
  let b ← playIt s4 veng
  let c ← playIt s4 unit
  return a.countIn s.me .hand "OGN-129" == 0 && a.countIn s.me .trash "OGN-129" == 2 &&
    a.handN s.me == s4.handN s.me - 1 + 1 && a.zone .chain == [] &&
    a.playedBefore s.me &&
    b.countIn s.me .hand "OGN-229" == 1 && b.countIn s.me .trash "OGN-229" == 0 &&
    !(s4.playedBefore s.me) &&
    -- the play is seen by what waits for a spell to be played (Ravenbloom Student: +1 Might)
    (a0.mightOf stu).getD 0 == ((s5.mightOf stu).getD 0) + 1 &&
    c.countIn s.me .hand "OGN-136" == 0 && c.countIn s.me .base "OGN-136" == 1

-- Playing a spell for free, more: inside an item that is being resolved the Chain is not opened
-- again (the outer item is not resolved twice); a free play pays nothing, so it is not "paid"; a
-- spell of the opponent goes to its owner's Trash
#guard t fun s => do
  let (s0, o0) ← put (s.rich s.me) s.me "OGN-129" .hand
  let s1 ← match step 100 s0 ⟨.player s.me, .playCard o0 (payOf s0 o0) []⟩ with
    | .ok (y, _) => some y
    | .error _ => none
  let outer ← (s1.zone .chain).head?
  let (s2, inner) ← put s1 s.me "OGN-129" .hand
  let (s3, other) ← put s2 s.you "OGN-129" .hand
  let play (x : GameState) (c : ObjId) (rest : List Frame) : Option GameState :=
    let x2 := { x with pending := [.run x.me outer { slots := [.obj c] } (.cons (.prim
      (.play (Selector.one .any .inHand [.sameAs (.slot 0)]))) .nil)] ++ rest }
    match advance 100 x2 [] with
    | .ok (y, _) => some (settleChain {} 12 y)
    | .error _ => none
  let nested ← play s3 inner [.finishSpell outer]
  let theirs ← play s3 other []
  return nested.zone .chain == [] && nested.pending.isEmpty &&
    nested.countIn s.me .trash "OGN-129" == 2 && nested.handN s.me == s3.handN s.me - 1 + 1 &&
    (nested.zone (.player s.me .trash)).all (fun i => (nested.obj? i).all (!·.paid)) &&
    theirs.countIn s.you .trash "OGN-129" == 1 && theirs.countIn s.me .trash "OGN-129" == 0

end RiftboundTest
