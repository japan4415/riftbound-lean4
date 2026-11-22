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

end RiftboundTest
