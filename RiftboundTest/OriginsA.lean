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

end RiftboundTest
