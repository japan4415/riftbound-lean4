module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests: Spiritforged (scenario tests of single cards)

Each test puts the cards it needs in the lab (the Main Phase of the first turn), plays the card
for exactly its cost, lets the Chain resolve, and reads what happened (as `OriginsA.lean` does).
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- The card of the player in their Base that has the identifier. -/
meta def _root_.Riftbound.GameState.inBase (s : GameState) (p : PlayerId) (code : String) :
    Option ObjId :=
  (s.zone (.player p .base)).find? (fun o => (s.cardDef? o).any (·.id.code == code))

/-- Run a scenario in the lab; it must say `true`. -/
meta def tsf (f : GameState → Option Bool) : Bool :=
  match lab with
  | some s => (f s).getD false
  | none => false

-- Quick-Draw (Sterak's Gage, SFD-056): played, it attaches itself to a unit its player controls
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-056" .hand
  let (s2, u) ← put s1 s.me "OGN-001" .base
  let s3 ← play s2 s.me g
  let gear := s3.inBase s.me "SFD-056"
  return gear.any (fun o => (s3.obj? o).any (·.attached == some u))
-- ... and not to a unit of the opponent
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-056" .hand
  let (s2, _) ← put s1 s.you "OGN-001" .base
  let s3 ← play s2 s.me g
  let gear := s3.inBase s.me "SFD-056"
  return gear.any (fun o => (s3.obj? o).any (·.attached == none))

-- Weaponmaster (Combat Chef, SFD-092): when played, the player may Equip one of their Equipment to
-- it for one Power less: Brutalizer (Equip: one Power) is free
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-042" .base
  let s3 ← play s2 s.me chef
  let chef' := s3.inBase s.me "SFD-092"
  return chef'.any (fun c => (s3.obj? gear).any (·.attached == some c)) &&
    (s3.poolOf s.me).calm == 12 && (s3.poolOf s.me).energy == 7
-- Skyfall of Areion (Equip: 1 Energy and 1 Fury): one Power less leaves 1 Energy to pay
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-030" .base
  let s3 ← play s2 s.me chef
  let chef' := s3.inBase s.me "SFD-092"
  return chef'.any (fun c => (s3.obj? gear).any (·.attached == some c)) &&
    (s3.poolOf s.me).fury == 12 && (s3.poolOf s.me).energy == 6
-- ... and if the Energy is not there, the Equipment stays where it is
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-030" .base
  let s3 ← cast (s2.fund s.me 5) s.me chef (payOf s2 chef)
  return (s3.obj? gear).any (·.attached == none)
-- "even if it's already attached": the Equipment of another unit moves to the new one
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-042" .base
  let (s3, other) ← put s2 s.me "OGN-001" .base
  let s4 := s3.modObj gear (fun o => { o with attached := some other })
  let s5 ← play s4 s.me chef
  let chef' := s5.inBase s.me "SFD-092"
  return chef'.any (fun c => (s5.obj? gear).any (·.attached == some c))
-- the Equipment of the opponent is not one of "your Equipment"
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.you "SFD-042" .base
  let s3 ← play s2 s.me chef
  return (s3.obj? gear).any (·.attached == none)
-- no Equipment: the unit is simply played
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let s2 ← play s1 s.me chef
  return s2.countIn s.me .base "SFD-092" == 1

-- Quick-Draw with several friendly units: the player picks the unit
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-056" .hand
  let (s2, u) ← put s1 s.me "OGN-001" .base
  let (s3, v) ← put s2 s.me "OGN-051" .base
  let s4 ← play s3 s.me g [] { pick := fun ts => ts == [v] }
  let s5 ← play s3 s.me g [] { pick := fun ts => ts == [u] }
  let gear4 := s4.inBase s.me "SFD-056"
  let gear5 := s5.inBase s.me "SFD-056"
  return gear4.any (fun o => (s4.obj? o).any (·.attached == some v)) &&
    gear5.any (fun o => (s5.obj? o).any (·.attached == some u))
-- Weaponmaster: "may", so the player can decline
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-042" .base
  let s3 ← play s2 s.me chef [] { yes := false }
  return (s3.obj? gear).any (·.attached == none) && (s3.poolOf s.me).calm == 12
-- ... one of several Equipment, as the player picks
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, g1) ← put s1 s.me "SFD-042" .base
  let (s3, g2) ← put s2 s.me "SFD-051" .base
  let s4 ← play s3 s.me chef [] { pick := fun ts => ts == [g2] }
  return (s4.obj? g1).any (·.attached == none) && (s4.obj? g2).any (·.attached.isSome)
-- an Equip cost of one Power of any domain (Forgefire Cape) is paid in full by the discount
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .hand
  let (s2, gear) ← put s1 s.me "SFD-190" .base
  let s3 ← play s2 s.me chef
  return (s3.obj? gear).any (·.attached.isSome) && (s3.poolOf s.me).energy == 7
-- the unit may have left play before the ability resolves: nothing is attached, nothing is paid
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .trash
  let (s2, gear) ← put s1 s.me "SFD-030" .base
  let r ← applyAttachPaying (s2.rich s.me) s.me chef { slots := [.obj gear] } (.slot 0) .self 1
  return (r.1.obj? gear).any (·.attached == none) &&
    (r.1.poolOf s.me).energy == ((s2.rich s.me).poolOf s.me).energy
-- (the same with the unit in play: it is attached, and the Energy is paid)
#guard tsf fun s => do
  let (s1, chef) ← put s s.me "SFD-092" .base
  let (s2, gear) ← put s1 s.me "SFD-030" .base
  let r ← applyAttachPaying (s2.rich s.me) s.me chef { slots := [.obj gear] } (.slot 0) .self 1
  return (r.1.obj? gear).any (·.attached == some chef) &&
    (r.1.poolOf s.me).energy + 1 == ((s2.rich s.me).poolOf s.me).energy

/-- The Energy cost the card is played for now. -/
meta def _root_.Riftbound.GameState.energyCost? (s : GameState) (p : PlayerId) (c : ObjId) :
    Option Nat :=
  (s.cardDef? c).bind (fun d => (s.effCost p c d).map (·.energy))

/-- The damage on the object. -/
meta def _root_.Riftbound.GameState.dmg (s : GameState) (u : ObjId) : Option Nat :=
  (s.obj? u).map (·.damage)

-- Against the Odds (SFD-001): +2 Might for each enemy unit at the battlefield
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-001" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, _) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, _) ← putAt s3 s.you "OGN-001" s.bf0
  let s5 ← play s4 s.me c [u]
  return s5.mightNow u == (s4.mightNow u).map (· + 4)
-- no enemy there: no bonus; and an enemy unit is not a friendly target
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-001" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, e) ← put s2 s.you "OGN-001" .base
  let s4 ← play s3 s.me c [u]
  return s4.mightNow u == s3.mightNow u && (play s3 s.me c [e]).isNone

-- Blood Rush (SFD-003): a unit has Assault 2 this turn, only that unit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-003" .hand
  let (s2, v) ← put s1 s.me "OGN-136" .base
  let (s3, w) ← put s2 s.me "OGN-136" .base
  let s4 ← play s3 s.me c [v]
  return s4.kwAmount v .assault == 2 && s4.kwAmount w .assault == 0

-- Bushwhack (SFD-004): a Gold token, and the units played this turn enter ready
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-004" .hand
  let (s2, v) ← put s1 s.me "OGN-051" .hand
  let (s2b, w) ← put s2 s.me "OGN-136" .hand
  let s3 ← play s2b s.me c
  let s4 ← play s3 s.me v
  let s5 ← play s4 s.me w
  let (t1, v2) ← put s s.me "OGN-051" .hand
  let t3 ← play t1 s.me v2
  return s3.countIn s.me .base "SFD-T03" == 1 &&
    (s5.firstOf s.me .base "OGN-051").bind s5.tired == some false &&
    (s5.firstOf s.me .base "OGN-136").bind s5.tired == some false &&
    (t3.firstOf s.me .base "OGN-051").bind t3.tired == some true

-- Detonate (SFD-005): kill a gear; its controller draws 2
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-005" .hand
  let (s2, g) ← put s1 s.me "SFD-030" .base
  let s3 ← play s2 s.me c [g]
  return s3.countIn s.me .trash "SFD-030" == 1 && s3.handN s.me == s2.handN s.me + 1 &&
    s3.handN s.you == s2.handN s.you
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-005" .hand
  let (s2, g) ← put s1 s.you "SFD-030" .base
  let s3 ← play s2 s.me c [g]
  return s3.countIn s.you .trash "SFD-030" == 1 && s3.handN s.you == s2.handN s.you + 2 &&
    s3.handN s.me == s2.handN s.me - 1

-- Gem Jammer (SFD-007): the unit the player picks has Ganking this turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-007" .hand
  let (s2, v) ← put s1 s.you "OGN-051" .base
  let (s3, w) ← put s2 s.me "OGN-051" .base
  let s4 ← play s3 s.me c [] { pick := fun ts => ts == [v] }
  return s4.hasKw v .ganking && !s4.hasKw w .ganking

-- Battering Ram (SFD-012): 1 less for each card played this turn, never below 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-012" .hand
  let (s2, a) ← put s1 s.me "OGN-051" .hand
  let (s3, b) ← put s2 s.me "OGN-051" .hand
  let s4 ← play s3 s.me a
  let s5 ← play s4 s.me b
  let (s6, d) ← put s5 s.me "OGN-051" .hand
  let (s7, e) ← put s6 s.me "OGN-051" .hand
  let (s8, f) ← put s7 s.me "OGN-051" .hand
  let (s9, g) ← put s8 s.me "OGN-051" .hand
  let t1 ← play s9 s.me d
  let t2 ← play t1 s.me e
  let t3 ← play t2 s.me f
  let t4 ← play t3 s.me g
  return s1.energyCost? s.me c == some 5 && s4.energyCost? s.me c == some 4 &&
    s5.energyCost? s.me c == some 3 && t3.energyCost? s.me c == some 1 &&
    t4.energyCost? s.me c == some 1

-- Sudden Storm (SFD-017): 2 damage to a unit at a battlefield, 4 if it is attacking
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-017" .hand
  let (s2, u) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, _) ← putAt s2 s.you "OGN-051" s.bf0
  let a ← play s3 s.me c [u]
  let b ← play (s3.inShowdownAt s.bf0 s.me) s.me c [u]
  return a.dmg u == some 2 && b.dmg u == some 4
-- not a unit at a base
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-017" .hand
  let (s2, u) ← put s1 s.you "OGN-001" .base
  return (play s2 s.me c [u]).isNone

-- Piercing Light (SFD-023): 2 to a unit at a battlefield, then 2 to up to one other unit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-023" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, v) ← put s2 s.you "OGN-001" .base
  let s4 ← play s3 s.me c [u]
  return s4.dmg u == some 2 && s4.dmg v == some 2
-- ... with no other unit, only the first is hit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-023" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let s3 ← play s2 s.me c [u]
  return s3.dmg u == some 2

/-- The player keeps the card `c` and the first `n` other cards of their hand. -/
meta def _root_.Riftbound.GameState.keepHand (s : GameState) (p : PlayerId) (c : ObjId) (n : Nat) :
    GameState :=
  let l := s.zone (.player p .hand)
  s.setZone (.player p .hand) (l.filter (· == c) ++ (l.filter (· != c)).take n)

-- Dunebreaker (SFD-027): enters ready with two or fewer cards in hand
#guard tsf fun s => do
  let (s1, d) ← put s s.me "SFD-027" .hand
  let a ← play (s1.keepHand s.me d 1) s.me d
  let a2 ← play (s1.keepHand s.me d 2) s.me d
  let b ← play (s1.keepHand s.me d 3) s.me d
  return (a.firstOf s.me .base "SFD-027").bind a.tired == some false &&
    (a2.firstOf s.me .base "SFD-027").bind a2.tired == some false &&
    (b.firstOf s.me .base "SFD-027").bind b.tired == some true
-- ... and draws 2 when it holds
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, _) ← putAt s1 s.me "SFD-027" bf
  let r ← fire s2 [.scored s.me bf false]
  return r.handN s.me == s2.handN s.me + 2

-- Disarming Rake (SFD-032): when played, the player may kill a gear
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-032" .hand
  let (s2, g) ← put s1 s.you "SFD-030" .base
  let a ← play s2 s.me c
  let b ← play s2 s.me c [] { yes := false }
  return a.countIn s.you .trash "SFD-030" == 1 && b.countIn s.you .base "SFD-030" == 1 &&
    (a.obj? g).isNone
-- (with no gear, the unit is simply played)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-032" .hand
  let a ← play s1 s.me c
  return a.countIn s.me .base "SFD-032" == 1

-- Guardian of the Passage (SFD-035): when it holds, a unit or gear (not a spell) from the Trash
-- may return to the hand
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "OGN-280"
  let (s2, _) ← putAt s1 s.me "SFD-035" bf
  let (s3, _) ← put s2 s.me "OGN-004" .trash
  let (s4, _) ← put s3 s.me "OGN-051" .trash
  let a ← fire s4 [.scored s.me bf false]
  let b ← fire s4 [.scored s.me bf false] { yes := false }
  return a.countIn s.me .hand "OGN-051" == 1 && a.countIn s.me .hand "OGN-004" == 0 &&
    b.countIn s.me .hand "OGN-051" == 0

-- Ribbon Dancer (SFD-038): when it moves to a battlefield, another friendly unit has +1 Might
#guard tsf fun s => do
  let (s1, d) ← putAt s s.me "SFD-038" s.bf0
  let (s2, v) ← put s1 s.me "OGN-051" .base
  let (s3, e) ← put s2 s.me "SFD-038" .base
  let picks ← firePicks s2 [.standardMoved d (some s.bf0)]
  let a ← fire s2 [.standardMoved d (some s.bf0)] { pick := fun ts => ts == [v] }
  let b ← fire s3 [.standardMoved e none] { pick := fun ts => ts == [v] }
  return picks.contains v && !picks.contains d && a.mightNow v == (s2.mightNow v).map (· + 1) &&
    b.mightNow v == s3.mightNow v

-- Thwonk! (SFD-040): stun an attacking unit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-040" .hand
  let (s2, u) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, _) ← putAt s2 s.you "OGN-051" s.bf0
  let r ← play (s3.inShowdownAt s.bf0 s.me) s.me c [u]
  return (r.obj? u).map (·.stunned) == some true && (play s3 s.me c [u]).isNone

-- Emperor's Divide (SFD-043): friendly units at a battlefield may move to their base
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-043" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-051" s.bf0
  let a ← play s3 s.me c [s.bf0]
  let b ← play s3 s.me c [s.bf0] { yes := false }
  return (a.obj? u).any (·.loc.isNone) && (a.obj? e).any (·.loc == some s.bf0) &&
    (b.obj? u).any (·.loc == some s.bf0)

-- Simian Ancestor (SFD-047): when buffed, it readies
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-047" .base
  let s2 := s1.tire u
  let r ← fire s2 [.buffed u]
  return s2.tired u == some true && r.tired u == some false

-- Janna, Savior (SFD-053), at a battlefield when played: heal my units here, and move an enemy
-- unit from here to its base
#guard tsf fun s => do
  let (s1, j) ← putAt s s.me "SFD-053" s.bf0
  let (s2, a) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let s4 := s3.modObj a (fun o => { o with damage := 3 })
  let r ← fire s4 [.played s.me j]
  return r.dmg a == some 0 && (r.obj? e).any (·.loc.isNone) &&
    (r.obj? j).any (·.loc == some s.bf0)

-- Bubble Bot (SFD-062): when played, ready another friendly Mech (not itself, not a non-Mech)
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-062" .hand
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, o) ← put s2 s.me "OGN-051" .base
  let s4 := (s3.tire m).tire o
  let r ← play s4 s.me b [] { pick := fun ts => ts == [m] }
  let picks ← firePicks (s4.rich s.me) [.played s.me b]
  return r.tired m == some false && r.tired o == some true && !picks.contains o

-- Breakneck Mech (SFD-071): friendly Mechs have Deflect and Ganking; it enters ready if there is
-- another Mech
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-071" .base
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, o) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "SFD-062" .base
  return s4.hasKw m .deflect && s4.hasKw m .ganking && !s4.hasKw o .deflect &&
    !s4.hasKw e .ganking && b != m
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-071" .hand
  let (s2, _) ← put s1 s.me "SFD-062" .base
  let (t1, c) ← put s s.me "SFD-071" .hand
  let a ← play s2 s.me b
  let r ← play t1 s.me c
  return (a.firstOf s.me .base "SFD-071").bind a.tired == some false &&
    (r.firstOf s.me .base "SFD-071").bind r.tired == some true

-- Dropboarder (SFD-072): when played with two or more gear, it readies itself
#guard tsf fun s => do
  let (s1, d) ← put s s.me "SFD-072" .hand
  let (s2, _) ← put s1 s.me "SFD-030" .base
  let (s3, _) ← put s2 s.me "SFD-030" .base
  let a ← play s3 s.me d
  let (t1, c) ← put s s.me "SFD-072" .hand
  let (t2, _) ← put t1 s.me "SFD-030" .base
  let r ← play t2 s.me c
  return (a.firstOf s.me .base "SFD-072").bind a.tired == some false &&
    (r.firstOf s.me .base "SFD-072").bind r.tired == some true

-- Production Surge (SFD-076): costs 2 less with a Mech; a Mech token, and draw 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-076" .hand
  let (s2, _) ← put s1 s.me "SFD-062" .base
  let r ← play s2 s.me c
  return s1.energyCost? s.me c == some 4 && s2.energyCost? s.me c == some 2 &&
    r.countNamed s.me .base "Mech" == 1 && r.handN s.me == s2.handN s.me

-- Rumble, Scrapper (SFD-089): friendly Mechs have +1 Might; a Mech token when it holds
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, e) ← put s2 s.you "SFD-062" .base
  let (s4, _) ← putAt s3 s.me "SFD-089" bf
  let r ← fire s4 [.scored s.me bf false]
  return s4.mightNow m == (s3.mightNow m).map (· + 1) && s4.mightNow e == s3.mightNow e &&
    r.countNamed s.me .base "Mech" == 1

-- Buhru Captain (SFD-091): when played, the player may draw 1 or buff it
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-091" .hand
  let d ← play s1 s.me c [] { fromEnd := some 1 }
  let b ← play s1 s.me c [] { fromEnd := some 2 }
  let n ← play s1 s.me c [] { yes := false }
  let buffed (x : GameState) :=
    (x.firstOf s.me .base "SFD-091").bind (fun o => (x.obj? o).map (·.buffed))
  return buffed d == some false && buffed b == some true && buffed n == some false &&
    d.handN s.me == b.handN s.me + 1 && d.handN s.me == n.handN s.me + 1

-- Direwing (SFD-094): enters ready if the player controls another Dragon
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-094" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let a ← play s2 s.me c
  let (t1, c2) ← put s s.me "SFD-094" .hand
  let r ← play t1 s.me c2
  return (a.firstOf s.me .base "SFD-094").bind a.tired == some false &&
    (r.firstOf s.me .base "SFD-094").bind r.tired == some true

-- Laurent Bladekeeper (SFD-096) has Ganking
#guard match RiftboundCards.db.find? ⟨"SFD-096"⟩ with
  | some c => c.hasKeyword .ganking && c.runs
  | none => false

-- Yordle Explorer (SFD-100): draw 1 when the player plays a card with two or more Power
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-100" .base
  let (s2, hi) ← put s1 s.me "OGN-029" .trash
  let (s3, lo) ← put s2 s.me "OGN-051" .trash
  let a ← fire s3 [.played s.me hi]
  let b ← fire s3 [.played s.me lo]
  let c ← fire s3 [.played s.you hi]
  return a.handN s.me == s3.handN s.me + 1 && b.handN s.me == s3.handN s.me &&
    c.handN s.me == s3.handN s.me

-- Petricite Monument (SFD-104): friendly units have Deflect
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-104" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, e) ← put s2 s.you "OGN-051" .base
  return s3.hasKw u .deflect && !s3.hasKw e .deflect

-- Show of Strength (SFD-106): draw 1 for each friendly Mighty unit
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-106" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let (s3, _) ← put s2 s.me "OGN-001" .base
  let (s4, _) ← put s3 s.me "OGN-051" .base
  let (s5, _) ← put s4 s.you "OGN-001" .base
  let r ← play s5 s.me c
  return r.handN s.me == s5.handN s.me - 1 + 2

-- Marching Orders (SFD-114): a friendly unit and an enemy unit at a battlefield deal damage
-- equal to their Might to each other
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-114" .hand
  let (s2, f) ← put s1 s.me "OGN-001" .base
  let (s3, e) ← putAt s2 s.you "OGN-051" s.bf0
  let r ← play s3 s.me c [f, e]
  return r.dmg f == some 2 && (r.obj? e).isNone && (play s3 s.me c [e, f]).isNone

-- Danger Zone (SFD-182): friendly Mechs have +1 Might this turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-182" .hand
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, o) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "SFD-062" .base
  let r ← play s4 s.me c
  return r.mightNow m == (s4.mightNow m).map (· + 1) && r.mightNow o == s4.mightNow o &&
    r.mightNow e == s4.mightNow e

-- (review) Detonate: if the gear is gone when the spell resolves, nobody draws
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-005" .hand
  let (s2, g) ← put s1 s.me "SFD-030" .base
  let s3 ← match step 100 (s2.rich s.me) ⟨.player s.me, .playCard c (payOf s2 c) [g]⟩ with
    | .ok (x, _) => some x
    | .error _ => none
  let s4 := (killObj s3 g).1
  let s5 := settleChain {} 12 s4
  return s5.handN s.me == s3.handN s.me && s5.handN s.you == s3.handN s.you
-- (review) Against the Odds and Emperor's Divide look at the one battlefield only
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-001" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, b2) ← putBf s2 s.you "SFD-216"
  let (s4, _) ← putAt s3 s.you "OGN-001" b2
  let (s5, _) ← put s4 s.you "OGN-001" .base
  let r ← play s5 s.me c [u]
  return r.mightNow u == s5.mightNow u
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-043" .hand
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, b2) ← putBf s2 s.me "SFD-216"
  let (s4, w) ← putAt s3 s.me "OGN-051" b2
  let r ← play s4 s.me c [s.bf0]
  return (r.obj? u).any (·.loc.isNone) && (r.obj? w).any (·.loc == some b2)
-- (review) Yordle Explorer: a card with exactly one Power does not draw
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-100" .base
  let (s2, one) ← put s1 s.me "SFD-004" .trash
  let a ← fire s2 [.played s.me one]
  return a.handN s.me == s2.handN s.me
-- (review) Production Surge: an enemy Mech does not lower the cost
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-076" .hand
  let (s2, _) ← put s1 s.you "SFD-062" .base
  return s2.energyCost? s.me c == some 4
-- (review) Bushwhack: the Gold token is exhausted, and a Mech token enters ready
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-004" .hand
  let (s2, p) ← put s1 s.me "SFD-076" .hand
  let s3 ← play s2 s.me c
  let s4 ← play s3 s.me p
  let gold := s4.firstOf s.me .base "SFD-T03"
  let mech := (s4.zone (.player s.me .base)).find? (fun o =>
    (s4.cardDef? o).any (·.name == "Mech"))
  return gold.bind s4.tired == some true && mech.bind s4.tired == some false
-- (review) Piercing Light with Repeat paid: the effect is done twice
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-023" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let pay := payOf s2 c
  let r ← cast (s2.rich s.me) s.me c ⟨pay.energy + 2, pay.power ++ [.fury]⟩ [u]
  return r.dmg u == some 4
-- (review) Blood Rush with Repeat paid: Assault 2 is given twice
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-003" .hand
  let (s2, v) ← put s1 s.me "OGN-136" .base
  let pay := payOf s2 c
  let a ← cast (s2.rich s.me) s.me c ⟨pay.energy + 1, pay.power⟩ [v]
  let b ← cast (s2.rich s.me) s.me c pay [v]
  return a.kwAmount v .assault == 4 && b.kwAmount v .assault == 2
-- (review) Marching Orders: each unit takes damage equal to the Might of the other
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-114" .hand
  let (s2, f) ← put s1 s.me "OGN-051" .base
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let r ← play s3 s.me c [f, e]
  return r.dmg e == some 2 && (r.obj? f).isNone
-- (review) Simian Ancestor: buffing another unit does not ready it
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-047" .base
  let (s2, o) ← put s1 s.me "OGN-051" .base
  let s3 := s2.tire u
  let r ← fire s3 [.buffed o]
  return r.tired u == some true
-- (review) Piercing Light: with no other unit, the first unit is not hit twice
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-023" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let r ← play s2 s.me c [u]
  return r.dmg u == some 2
-- Trinity Force (SFD-115): the unit it is attached to scores 1 point when it holds
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, u) ← putAt s1 s.me "OGN-051" bf
  let (s3, g) ← put s2 s.me "SFD-115" .base
  let s4 := s3.modObj g (fun o => { o with attached := some u })
  let a ← fire s4 [.scored s.me bf false]
  let b ← fire s3 [.scored s.me bf false]
  return a.pointsOf s.me == s4.pointsOf s.me + 1 && b.pointsOf s.me == s3.pointsOf s.me

-- Forgefire Cape (SFD-190): when its unit attacks or defends, 2 damage to all enemy units here
#guard tsf fun s => do
  let (s1, u) ← putAt s s.me "OGN-001" s.bf0
  let (s2, g) ← put s1 s.me "SFD-190" .base
  let (s3, e) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, f) ← put s3 s.you "OGN-001" .base
  let s5 := s4.modObj g (fun o => { o with attached := some u })
  let a ← fire s5 [.combatStarted s.bf0 s.me]
  let b ← fire s5 [.combatStarted s.bf0 s.you]
  return a.dmg e == some 2 && a.dmg f == some 0 && a.dmg u == some 0 && b.dmg e == some 2

-- Emperor's Dais (SFD-207): conquer here, pay 1 and return a unit here to its hand: a Sand Soldier
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-207"
  let (s2, u) ← putAt s1 s.me "OGN-051" bf
  let a ← fire (s2.rich s.me) [.scored s.me bf true]
  let b ← fire (s2.rich s.me) [.scored s.me bf true] { yes := false }
  let c ← fire (s2.rich s.me) [.scored s.me bf false]
  return a.countIn s.me .hand "OGN-051" == s2.countIn s.me .hand "OGN-051" + 1 &&
    (a.zone .battlefieldZone).any (fun o => (a.cardDef? o).any (·.name == "Sand Soldier")) &&
    (b.obj? u).isSome && c.countIn s.me .hand "OGN-051" == s2.countIn s.me .hand "OGN-051"

-- Minefield (SFD-212): when its player conquers here, the top 2 cards of their Main Deck go to
-- the Trash
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-212"
  let a ← fire s1 [.scored s.me bf true]
  let b ← fire s1 [.scored s.me bf false]
  let trash (x : GameState) := (x.zone (.player s.me .trash)).length
  let deck (x : GameState) := (x.zone (.player s.me .mainDeck)).length
  return trash a == trash s1 + 2 && deck a + 2 == deck s1 && trash b == trash s1

-- Power Nexus (SFD-214): when its player holds here, they may pay 4 Power to score 1 point
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-214"
  let rich := s1.rich s.me
  let a ← fire rich [.scored s.me bf false]
  let b ← fire rich [.scored s.me bf false] { yes := false }
  let c ← fire (s1.fund s.me 0 3) [.scored s.me bf false]
  let d ← fire rich [.scored s.me bf true]
  return a.pointsOf s.me == rich.pointsOf s.me + 1 && b.pointsOf s.me == rich.pointsOf s.me &&
    c.pointsOf s.me == s1.pointsOf s.me && d.pointsOf s.me == rich.pointsOf s.me

-- Seat of Power (SFD-217): when its player conquers here, they draw 1 for each other battlefield
-- they control
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-217"
  let (s2, b2) ← putBf s1 s.me "SFD-216"
  let (s3, b3) ← putBf s2 s.you "SFD-216"
  let s4 := ((s3.control s.me bf).control s.me b2).control s.you b3
  let a ← fire s4 [.scored s.me bf true]
  return a.handN s.me == s4.handN s.me + 1
-- (not for one the opponent controls, not when the player holds)
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-217"
  let (s2, b2) ← putBf s1 s.you "SFD-216"
  let s3 := (s2.control s.me bf).control s.you b2
  let a ← fire s3 [.scored s.me bf true]
  return a.handN s.me == s3.handN s.me

-- Sunken Temple (SFD-218): conquer here with a Mighty unit, pay 1: draw 1
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-218"
  let (s2, _) ← putAt s1 s.me "OGN-001" bf
  let (t2, _) ← putAt s1 s.me "OGN-051" bf
  let a ← fire (s2.rich s.me) [.scored s.me bf true]
  let b ← fire (t2.rich s.me) [.scored s.me bf true]
  let c ← fire (s2.fund s.me 0) [.scored s.me bf true]
  return a.handN s.me == s2.handN s.me + 1 && (a.poolOf s.me).energy + 1 == 12 &&
    b.handN s.me == t2.handN s.me && c.handN s.me == s2.handN s.me

-- The Papertree (SFD-219): when its player holds here, each player channels 1 rune exhausted
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-219"
  let a ← fire s1 [.scored s.me bf false]
  let b ← fire s1 [.scored s.me bf true]
  let runes (x : GameState) (p : PlayerId) := (x.zone (.player p .runeDeck)).length
  return runes a s.me + 1 == runes s1 s.me && runes a s.you + 1 == runes s1 s.you &&
    runes b s.me == runes s1 s.me

-- Treasure Hoard (SFD-220): conquer here, pay 1: a Gold token
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-220"
  let a ← fire (s1.rich s.me) [.scored s.me bf true]
  let b ← fire (s1.rich s.me) [.scored s.me bf true] { yes := false }
  let c ← fire (s1.fund s.me 0) [.scored s.me bf true]
  return a.countIn s.me .base "SFD-T03" == 1 && b.countIn s.me .base "SFD-T03" == 0 &&
    c.countIn s.me .base "SFD-T03" == 0

-- Gold (SFD-T03): kill it, exhaust it: 1 Power of any domain
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-T03" .base
  let runs := (RiftboundCards.db.find? ⟨"SFD-T03"⟩).any (·.runs)
  return runs && manaReady s1 s.me g 0

-- the end of a Combat: the player whose units are the only ones left at the battlefield wins it
-- (the attacker's units are recalled when a defender is left: the defender wins)
#guard tsf fun s => do
  let (s1, a) ← putAt s s.me "OGN-001" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-051" s.bf0
  let evs (x : GameState) : List Event := (combatResolve x s.bf0 s.me).2.2
  let lost := s2.modObj e (fun o => { o with loc := none })
  let neither := lost.modObj a (fun o => { o with loc := none })
  return (evs s2).contains (.combatWon s.bf0 s.you) && !(evs s2).contains (.combatWon s.bf0 s.me) &&
    (evs lost).contains (.combatWon s.bf0 s.me) && !(evs lost).contains (.combatWon s.bf0 s.you) &&
    (evs neither).all (fun ev => match ev with | .combatWon .. => false | _ => true)

-- Draven, Vanquisher (SFD-020): when it wins a combat, a Gold token; when it attacks or defends,
-- the player may pay 1 Fury for +2 Might
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-020" s.bf0
  let a ← fire s1 [.combatWon s.bf0 s.me]
  let b ← fire s1 [.combatWon s.bf0 s.you]
  let gold := a.firstOf s.me .base "SFD-T03"
  return a.countIn s.me .base "SFD-T03" == 1 && b.countIn s.me .base "SFD-T03" == 0 &&
    gold.bind a.tired == some true
#guard tsf fun s => do
  let (s1, d) ← putAt s s.me "SFD-020" s.bf0
  let (s2, _) ← putAt s1 s.you "OGN-051" s.bf0
  let a ← fire (s2.rich s.me) [.combatStarted s.bf0 s.me]
  let b ← fire (s2.rich s.me) [.combatStarted s.bf0 s.you]
  let c ← fire (s2.rich s.me) [.combatStarted s.bf0 s.me] { yes := false }
  let e ← fire (s2.fund s.me 5) [.combatStarted s.bf0 s.me]
  return a.mightNow d == (s2.mightNow d).map (· + 2) && (a.poolOf s.me).fury == 11 &&
    b.mightNow d == (s2.mightNow d).map (· + 2) && c.mightNow d == s2.mightNow d &&
    e.mightNow d == s2.mightNow d

-- Corrupt Enforcer (SFD-123): discard 1 when it moves to a battlefield; draw 1 when it wins
#guard tsf fun s => do
  let (s1, u) ← putAt s s.me "SFD-123" s.bf0
  let (s2, v) ← put s1 s.me "SFD-123" .base
  let a ← fire s2 [.standardMoved u (some s.bf0)]
  let b ← fire s2 [.standardMoved v none]
  let c ← fire s2 [.combatWon s.bf0 s.me]
  return a.handN s.me + 1 == s2.handN s.me && b.handN s.me == s2.handN s.me &&
    c.handN s.me == s2.handN s.me + 1

-- Glorious Executioner (SFD-185), a Legend: draw 1 when its player wins a combat
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-185" .legendZone
  let a ← fire s1 [.combatWon s.bf0 s.me]
  let b ← fire s1 [.combatWon s.bf0 s.you]
  return a.handN s.me == s1.handN s.me + 1 && b.handN s.me == s1.handN s.me

-- Mechanized Menace (SFD-181), a Legend: the Mechs of its player have Shield
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-181" .legendZone
  let (s2, m) ← put s1 s.me "SFD-062" .base
  let (s3, o) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "SFD-062" .base
  return s4.hasKw m .shield && !s4.hasKw o .shield && !s4.hasKw e .shield

-- (review) Mechanized Menace: Shield is +1 Might in the damage of a defending Mech
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-181" .legendZone
  let (s2, m) ← putAt s1 s.me "SFD-062" s.bf0
  let (s3, o) ← putAt s2 s.me "OGN-051" s.bf0
  return s3.combatMight m false == s3.combatMight m true + 1 &&
    s3.combatMight o false == s3.combatMight o true

-- (review) the events of the end of a real Combat set off the trigger: the attacker whose
-- opponent has no unit left wins, and Draven gets a Gold token; the defender who is left wins when
-- the attacker is recalled (and the attacker's Draven is recalled, so nothing for it)
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-020" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-051" s.bf0
  let dead := s2.modObj e (fun o => { o with loc := none })
  let (t1, _, evs) := combatResolve dead s.bf0 s.me
  let won ← fire t1 evs
  let (u1, _, evs2) := combatResolve s2 s.bf0 s.me
  let lost ← fire u1 evs2
  return won.countIn s.me .base "SFD-T03" == 1 && lost.countIn s.me .base "SFD-T03" == 0

-- (review) The Papertree: the runes channelled are exhausted
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-219"
  let a ← fire s1 [.scored s.me bf false]
  let fresh (x : GameState) (p : PlayerId) :=
    (x.zone (.player p .base)).filter (fun r => (x.cardDef? r).any (·.hasType .rune) &&
      (s1.zone (.player p .base)).all (· != r))
  return (fresh a s.me).length == 1 && (fresh a s.me).all (fun r => a.tired r == some true) &&
    (fresh a s.you).all (fun r => a.tired r == some true)

-- (review) Treasure Hoard and Draven's Gold token are exhausted; the cost is exactly 1
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-220"
  let a ← fire (s1.fund s.me 1) [.scored s.me bf true]
  let g := a.firstOf s.me .base "SFD-T03"
  return g.bind a.tired == some true && (a.poolOf s.me).energy == 0

-- (review) Power Nexus: exactly 4 Power pays; the Power is gone afterwards
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-214"
  let a ← fire (s1.fund s.me 0 4) [.scored s.me bf false]
  return a.pointsOf s.me == s1.pointsOf s.me + 1 && (a.poolOf s.me).fury == 0

-- (review) Emperor's Dais: no Energy, no return and no token; with 1 Energy, one cost
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-207"
  let (s2, _) ← putAt s1 s.me "OGN-051" bf
  let a ← fire (s2.fund s.me 0) [.scored s.me bf true]
  let b ← fire (s2.fund s.me 1) [.scored s.me bf true]
  return a.countIn s.me .hand "OGN-051" == s2.countIn s.me .hand "OGN-051" &&
    b.countIn s.me .hand "OGN-051" == s2.countIn s.me .hand "OGN-051" + 1 &&
    (b.poolOf s.me).energy == 0

-- (review) Sunken Temple: no draw when the player declines, or when they hold
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-218"
  let (s2, _) ← putAt s1 s.me "OGN-001" bf
  let a ← fire (s2.rich s.me) [.scored s.me bf true] { yes := false }
  let b ← fire (s2.rich s.me) [.scored s.me bf false]
  return a.handN s.me == s2.handN s.me && b.handN s.me == s2.handN s.me

-- (review) Corrupt Enforcer: the opponent's win does not draw for the player
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-123" s.bf0
  let a ← fire s1 [.combatWon s.bf0 s.you]
  return a.handN s.me == s1.handN s.me

-- Chemtech Cask (SFD-063): when its player plays a spell on an opponent's turn, they may exhaust it
-- to play a Gold token (exhausted)
#guard tsf fun s => do
  let (s1, k) ← put s s.me "SFD-063" .base
  let (s2, sp) ← put s1 s.me "OGN-004" .trash
  let theirs := { s2 with active := some s.you }
  let a ← fire theirs [.played s.me sp]
  let b ← fire s2 [.played s.me sp]
  let c ← fire theirs [.played s.me sp] { yes := false }
  let d ← fire (theirs.tire k) [.played s.me sp]
  let e ← fire theirs [.played s.you sp]
  let gold (x : GameState) := x.countIn s.me .base "SFD-T03"
  return gold a == 1 && a.tired k == some true &&
    (a.firstOf s.me .base "SFD-T03").bind a.tired == some true &&
    gold b == 0 && gold c == 0 && gold d == 0 && gold e == 0

-- Pickpocket (SFD-074): kill a gear with Energy cost 1 or less, then a Gold token
#guard tsf fun s => do
  let (s1, p) ← put s s.me "SFD-074" .hand
  let (s2, g) ← put s1 s.you "SFD-009" .base
  let (s3, big) ← put s2 s.you "SFD-042" .base
  let a ← play s3 s.me p [] { pick := fun ts => ts == [g] }
  let b ← play s3 s.me p [] { yes := false }
  let st ← castStop s3 s.me p
  return (a.obj? g).isNone && a.countIn s.me .base "SFD-T03" == 1 && (a.obj? big).isSome &&
    (b.obj? g).isSome && b.countIn s.me .base "SFD-T03" == 0 &&
    st.trigPicks.contains g && !st.trigPicks.contains big

-- Beast Below (SFD-132): when played, return another friendly unit and an enemy unit to hands
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-132" .hand
  let (s2, f) ← put s1 s.me "OGN-051" .base
  let (s3, e) ← put s2 s.you "OGN-001" .base
  let r ← play s3 s.me b [] { pick := fun ts => ts == [f, e] }
  let st ← castStop s3 s.me b
  let beast := st.firstOf s.me .base "SFD-132"
  return r.countIn s.me .hand "OGN-051" == 1 && r.countIn s.you .hand "OGN-001" == 1 &&
    r.countIn s.me .base "SFD-132" == 1 && beast.any (fun x => !st.trigPicks.contains x)
-- (an enemy unit is needed, and a friendly unit other than itself)
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-132" .hand
  let (s2, _) ← put s1 s.me "OGN-051" .base
  let r ← play s2 s.me b
  return r.countIn s.me .hand "OGN-051" == 0 && r.countIn s.me .base "SFD-132" == 1

-- Factory Recall (SFD-135): return a gear to its owner's hand (not a unit)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-135" .hand
  let (s2, g) ← put s1 s.you "SFD-030" .base
  let (s3, u) ← put s2 s.you "OGN-051" .base
  let r ← play s3 s.me c [g]
  return r.countIn s.you .hand "SFD-030" == 1 && (play s3 s.me c [u]).isNone

-- Windsinger (SFD-138): Hidden; when played, may return another unit at a battlefield with 3 Might
-- or less
#guard match RiftboundCards.db.find? ⟨"SFD-138"⟩ with
  | some c => c.hasKeyword .hidden && c.runs
  | none => false
#guard tsf fun s => do
  let (s1, w) ← put s s.me "SFD-138" .hand
  let (s2, small) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, big) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, base) ← put s3 s.you "OGN-051" .base
  let r ← play s4 s.me w
  let r2 ← play s4 s.me w [] { yes := false }
  let st ← castStop s4 s.me w
  return r.countIn s.you .hand "OGN-051" == 1 && (r.obj? small).isNone &&
    (r.obj? big).isSome && (r.obj? base).isSome && r2.countIn s.you .hand "OGN-051" == 0 &&
    st.trigPicks == [small]

-- Downwell (SFD-147): return all units and gear to their owners' hands
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-147" .hand
  let (s2, _) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, _) ← put s3 s.you "SFD-030" .base
  let r ← play s4 s.me c
  return r.countIn s.me .hand "OGN-051" == 1 && r.countIn s.you .hand "OGN-001" == 1 &&
    r.countIn s.you .hand "SFD-030" == 1 && (r.zone .battlefieldZone).length ==
      (s4.zone .battlefieldZone).length - 1 && (r.zone (.player s.me .base)).all (fun o =>
        (r.cardDef? o).any (fun d => d.hasType .rune))

-- Bonds of Strength (SFD-151): two different friendly units each have +1 Might
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-151" .hand
  let (s2, a) ← put s1 s.me "OGN-051" .base
  let (s3, b) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-051" .base
  let r ← play s4 s.me c [a, b]
  let same ← play s4 s.me c [a, a]
  return r.mightNow a == (s4.mightNow a).map (· + 1) &&
    r.mightNow b == (s4.mightNow b).map (· + 1) &&
    same.mightNow a == s4.mightNow a && (play s4 s.me c [a, e]).isNone

-- Guards! (SFD-154): a Sand Soldier token; the player may pay 1 Order Power to ready it
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-154" .hand
  let (s2, _) ← putAt s1 s.me "OGN-001" s.bf0
  let soldier (x : GameState) :=
    (x.zone (.player s.me .base)).find? (fun o => (x.cardDef? o).any (·.name == "Sand Soldier"))
  let a ← cast (s2.fund s.me 5 0 0 0 0 0 1) s.me c (payOf s2 c) [] { fromEnd := some 1 }
  let b ← cast (s2.fund s.me 5 0 0 0 0 0 1) s.me c (payOf s2 c) [] { fromEnd := some 2 }
  let n ← cast (s2.fund s.me 5) s.me c (payOf s2 c)
  return (soldier a).bind a.tired == some false && (a.poolOf s.me).order == 0 &&
    (soldier b).bind b.tired == some true && (b.poolOf s.me).order == 1 &&
    (soldier n).bind n.tired == some true

-- Sandshifter (SFD-158): when played, kill an enemy unit with 3 Might or less
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-158" .hand
  let (s2, small) ← put s1 s.you "OGN-051" .base
  let (s3, big) ← put s2 s.you "OGN-001" .base
  let (s4, mine) ← put s3 s.me "OGN-051" .base
  let r ← play s4 s.me c
  return (r.obj? small).isNone && (r.obj? big).isSome && (r.obj? mine).isSome
-- (nothing to kill: the unit is simply played)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-158" .hand
  let (s2, big) ← put s1 s.you "OGN-001" .base
  let r ← play s2 s.me c
  return (r.obj? big).isSome && r.countIn s.me .base "SFD-158" == 1

-- Trusty Ramhound (SFD-159): +1 Might while another friendly unit is at the same place
#guard tsf fun s => do
  let (s1, r) ← put s s.me "SFD-159" .base
  let (s2, _) ← put s1 s.you "OGN-051" .base
  let (s3, _) ← put s2 s.me "OGN-051" .base
  let (t1, q) ← putAt s s.me "SFD-159" s.bf0
  let (t2, _) ← putAt t1 s.me "OGN-051" s.bf0
  let (t3, _) ← put t2 s.me "OGN-051" .base
  return s2.mightNow r == s1.mightNow r && s3.mightNow r == (s1.mightNow r).map (· + 1) &&
    t2.mightNow q == (t1.mightNow q).map (· + 1) && t1.mightNow q == s1.mightNow r &&
    t3.mightNow q == t2.mightNow q

-- Blood Money (SFD-162): kill a unit at a battlefield with 2 Might or less; 1 Gold if it was an
-- enemy's, 2 if it was a friendly one
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-162" .hand
  let (s2, e) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, f) ← putAt s2 s.me "OGN-051" s.bf0
  let (s4, big) ← putAt s3 s.you "OGN-001" s.bf0
  let a ← play s4 s.me c [e]
  let b ← play s4 s.me c [f]
  return (a.obj? e).isNone && a.countIn s.me .base "SFD-T03" == 1 &&
    (b.obj? f).isNone && b.countIn s.me .base "SFD-T03" == 2 && (play s4 s.me c [big]).isNone
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-162" .hand
  let (s2, e) ← put s1 s.you "OGN-051" .base
  return (play s2 s.me c [e]).isNone

-- Deathgrip (SFD-163): kill a friendly unit to give another friendly unit +Might equal to its
-- Might this turn, and draw 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-163" .hand
  let (s2, a) ← put s1 s.me "OGN-001" .base
  let (s3, b) ← put s2 s.me "OGN-051" .base
  let r ← play s3 s.me c [a, b]
  let same ← play s3 s.me c [a, a]
  return (r.obj? a).isNone && r.mightNow b == (s3.mightNow b).map (· + 5) &&
    r.handN s.me == s3.handN s.me && (same.obj? a).isSome && same.handN s.me == s3.handN s.me - 1

-- Janna, Savior (SFD-053) at a base: heals the friendly units there
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-053" .base
  let (s2, a) ← put s1 s.me "OGN-001" .base
  let (s3, b) ← putAt s2 s.me "OGN-001" s.bf0
  let hurt (x : GameState) (u : ObjId) := x.modObj u (fun o => { o with damage := 3 })
  let s4 := hurt (hurt s3 a) b
  let r ← fire s4 [.played s.me j]
  return r.dmg a == some 0 && r.dmg b == some 3

-- (review) Chemtech Cask: a spell played from Hidden is played too; a unit played is not a spell
#guard tsf fun s => do
  let (s1, k) ← put s s.me "SFD-063" .base
  let (s2, h) ← put s1 s.me "SFD-017" .hidden
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let theirs := { s3 with active := some s.you }
  let a ← fire theirs [.played s.me h]
  let b ← fire theirs [.played s.me u]
  return a.countIn s.me .base "SFD-T03" == 1 && b.countIn s.me .base "SFD-T03" == 0 && k != u
-- (review) the effect of playing a Hidden spell announces that it was played
#guard tsf fun s => do
  let (s1, h) ← put s s.me "SFD-017" .hidden
  let r := applyPrim s1 s.me h {} (.turnEffect .hiddenPlayed)
  return r.any (fun (_, es) => es.contains (.played s.me h))
-- (review) Bonds of Strength: if the second unit is gone when the spell resolves, the first still
-- gets +1 (and the other way round)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-151" .hand
  let (s2, a) ← put s1 s.me "OGN-051" .base
  let (s3, b) ← put s2 s.me "OGN-051" .base
  let s4 ← match step 100 (s3.rich s.me) ⟨.player s.me, .playCard c (payOf s3 c) [a, b]⟩ with
    | .ok (x, _) => some x
    | .error _ => none
  let r1 := settleChain {} 12 (killObj s4 b).1
  let r2 := settleChain {} 12 (killObj s4 a).1
  return r1.mightNow a == (s3.mightNow a).map (· + 1) &&
    r2.mightNow b == (s3.mightNow b).map (· + 1)
-- (review) Windsinger: a unit of its own player is a legal choice too
#guard tsf fun s => do
  let (s1, w) ← put s s.me "SFD-138" .hand
  let (s2, mine) ← putAt s1 s.me "OGN-051" s.bf0
  let r ← play s2 s.me w
  return r.countIn s.me .hand "OGN-051" == 1 && (r.obj? mine).isNone
-- (review) Ramhound: an enemy at the same battlefield does not count
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-159" s.bf0
  let (s2, _) ← putAt s1 s.you "OGN-051" s.bf0
  return s2.mightNow r == s1.mightNow r
-- (review) Pickpocket: if the gear is gone when the ability resolves, no Gold
#guard tsf fun s => do
  let (s1, p) ← put s s.me "SFD-074" .hand
  let (s2, g) ← put s1 s.you "SFD-009" .base
  let s3 ← match step 100 (s2.rich s.me) ⟨.player s.me, .playCard p (payOf s2 p) []⟩ with
    | .ok (x, _) => some x
    | .error _ => none
  let s4 := settleChain { pick := fun ts => ts == [g] } 1 s3
  let s5 := (killObj s4 g).1
  let r := settleChain {} 12 s5
  return r.countIn s.me .base "SFD-T03" == 0
/-- How many Sand Soldier tokens the player has at their Base, and how many are ready. -/
meta def _root_.Riftbound.GameState.soldiers (s : GameState) (p : PlayerId) : Nat × Nat :=
  let l := (s.zone (.player p .base)).filter (fun o =>
    (s.cardDef? o).any (·.name == "Sand Soldier"))
  (l.length, (l.filter (fun o => s.tired o == some false)).length)

-- Rocket Barrage (SFD-077): choose one: 4 damage to a unit in a base, or kill a gear
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-077" .hand
  let (s2, u) ← put s1 s.you "OGN-001" .base
  let (s3, g) ← put s2 s.you "SFD-030" .base
  let (s4, w) ← putAt s3 s.you "OGN-001" s.bf0
  let a ← play s4 s.me c [] { fromEnd := some 1 }
  let b ← play s4 s.me c [] { fromEnd := some 2 }
  return a.dmg u == some 4 && (a.obj? g).isSome && a.dmg w == some 0 &&
    (b.obj? g).isNone && b.dmg u == some 0

-- Jayce (SFD-084): when played, may kill a friendly gear; if so, may play a gear (cost 7 or less)
-- from the hand for nothing
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-084" .hand
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-115" .hand
  let a ← play s3 s.me c [] { pick := fun ts => ts == [g] }
  let b ← play s3 s.me c [] { yes := false }
  return (a.obj? g).isNone && a.countIn s.me .base "SFD-115" == 1 &&
    a.countIn s.me .hand "SFD-115" == 0 && (a.poolOf s.me).energy == 12 - 4 &&
    b.countIn s.me .base "SFD-115" == 0 && (b.obj? g).isSome

-- Ornn, Forge God (SFD-085): +1 Might for each friendly gear
#guard tsf fun s => do
  let (s1, o) ← put s s.me "SFD-085" .base
  let (s2, _) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-030" .base
  let (s4, _) ← put s3 s.you "SFD-030" .base
  return s3.mightNow o == (s1.mightNow o).map (· + 2) && s4.mightNow o == s3.mightNow o

-- Fae Porter (SFD-125): when it moves to a battlefield, pay 1 Chaos to move another unit there
#guard tsf fun s => do
  let (s1, p) ← putAt s s.me "SFD-125" s.bf0
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let a ← fire (s2.fund s.me 0 0 0 0 0 1) [.standardMoved p (some s.bf0)]
  let b ← fire (s2.fund s.me 0) [.standardMoved p (some s.bf0)]
  let c ← fire (s2.fund s.me 0 0 0 0 0 1) [.standardMoved p (some s.bf0)] { yes := false }
  return (a.obj? u).any (·.loc == some s.bf0) && (a.poolOf s.me).chaos == 0 &&
    (b.obj? u).any (·.loc.isNone) && (c.obj? u).any (·.loc.isNone) && p != u

-- Overzealous Fan (SFD-128): when it defends, may kill itself to move an attacker to its base
#guard tsf fun s => do
  let (s1, f) ← putAt s s.me "SFD-128" s.bf0
  let (s2, a) ← putAt s1 s.you "OGN-001" s.bf0
  let s3 := s2.modObj s.bf0 (fun o => { o with contested := some s.you })
  let fight := s3.inShowdownAt s.bf0 s.you
  let r ← fire fight [.combatStarted s.bf0 s.you]
  let n ← fire fight [.combatStarted s.bf0 s.you] { yes := false }
  let o ← fire fight [.combatStarted s.bf0 s.me]
  return (r.obj? f).isNone && (r.obj? a).any (·.loc.isNone) && (n.obj? f).isSome &&
    (n.obj? a).any (·.loc == some s.bf0) && (o.obj? a).any (·.loc == some s.bf0)

-- Temptation (SFD-129): move an enemy unit to where another enemy unit is
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-129" .hand
  let (s2, a) ← put s1 s.you "OGN-051" .base
  let (s3, b) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, m) ← put s3 s.me "OGN-051" .base
  let r ← play s4 s.me c [a, b]
  let same ← play s4 s.me c [a, a]
  return (r.obj? a).any (·.loc == some s.bf0) && (same.obj? a).any (·.loc.isNone) &&
    (play s4 s.me c [m, b]).isNone

-- Switcheroo (SFD-145): swap the Mights of two units at the same battlefield this turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-145" .hand
  let (s2, a) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, b) ← putAt s2 s.you "OGN-051" s.bf0
  let r ← play s3 s.me c [a, b]
  return r.mightNow a == s3.mightNow b && r.mightNow b == s3.mightNow a &&
    s3.mightNow a == some 5 && s3.mightNow b == some 2
-- (not two units at different battlefields; not a unit at a base)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-145" .hand
  let (s2, a) ← putAt s1 s.me "OGN-001" s.bf0
  let (s3, other) ← putBf s2 s.you "SFD-216"
  let (s4, b) ← putAt s3 s.you "OGN-051" other
  let (s5, base) ← put s4 s.you "OGN-051" .base
  let r ← play s4 s.me c [a, b]
  return r.mightNow a == s4.mightNow a && r.mightNow b == s4.mightNow b &&
    (play s5 s.me c [a, base]).isNone

-- Glasc Mixologist (SFD-165): when it dies, may play a unit (cost 3 or less, at most 1 Power) from
-- the Trash for nothing
#guard tsf fun s => do
  let (s1, m) ← put s s.me "SFD-165" .trash
  let (s2, _) ← put s1 s.me "OGN-051" .trash
  let (s3, big) ← put s2 s.me "OGN-001" .trash
  let a ← fire s3 [.died m s.me]
  let b ← fire s3 [.died m s.me] { yes := false }
  return a.countIn s.me .base "OGN-051" == 1 && a.countIn s.me .base "OGN-001" == 0 &&
    b.countIn s.me .base "OGN-051" == 0 && (a.obj? big).isSome

-- Xin Zhao, Vigilant (SFD-176): enters ready if two or more other units of the player are at base
#guard tsf fun s => do
  let (s1, x) ← put s s.me "SFD-176" .hand
  let (s2, _) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← put s2 s.me "OGN-051" .base
  let (s4, _) ← putAt s2 s.me "OGN-051" s.bf0
  let (s5, _) ← put s2 s.you "OGN-051" .base
  let a ← play s3 s.me x
  let b ← play s2 s.me x
  let c ← play s4 s.me x
  let d ← play s5 s.me x
  let ready (r : GameState) := (r.firstOf s.me .base "SFD-176").bind r.tired
  return ready a == some false && ready b == some true && ready c == some true &&
    ready d == some true

-- Corina Veraza (SFD-179): when it moves to a battlefield, three Recruit tokens there
#guard tsf fun s => do
  let (s1, c) ← putAt s s.me "SFD-179" s.bf0
  let (s2, d) ← put s1 s.me "SFD-179" .base
  let a ← fire s2 [.standardMoved c (some s.bf0)]
  let b ← fire s2 [.standardMoved d none]
  let recruits (x : GameState) := ((x.zone .battlefieldZone).filter (fun o =>
    (x.cardDef? o).any (·.name == "Recruit") && (x.obj? o).any (·.loc == some s.bf0))).length
  return recruits a == 3 && recruits b == 0

-- Defiant Dance (SFD-196): one unit +2 Might, another -2 Might this turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-196" .hand
  let (s2, a) ← put s1 s.me "OGN-001" .base
  let (s3, b) ← put s2 s.you "OGN-001" .base
  let r ← play s3 s.me c [a, b]
  let same ← play s3 s.me c [a, a]
  return r.mightNow a == (s3.mightNow a).map (· + 2) &&
    r.mightNow b == (s3.mightNow b).map (· - 2) && same.mightNow a == s3.mightNow a

-- Arise! (SFD-198): a Sand Soldier for each Equipment the player controls, and two of them ready
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-198" .hand
  let (s2, _) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-042" .base
  let (s4, _) ← put s3 s.me "SFD-042" .base
  let (s5, _) ← put s3 s.you "SFD-042" .base
  let a ← play s4 s.me c
  let b ← play s3 s.me c
  let n ← play s1 s.me c
  let e ← play s5 s.me c
  return a.soldiers s.me == (3, 2) && b.soldiers s.me == (2, 2) && n.soldiers s.me == (0, 0) &&
    e.soldiers s.me == (2, 2)

-- On the Hunt (SFD-204): ready the units of the player
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-204" .hand
  let (s2, a) ← put s1 s.me "OGN-051" .base
  let (s3, b) ← put s2 s.you "OGN-051" .base
  let s4 := (s3.tire a).tire b
  let r ← play s4 s.me c
  return r.tired a == some false && r.tired b == some true

-- (review) Jayce: the gear is played ignoring its Energy cost, but its Power cost is paid
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-084" .hand
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-022" .hand
  let a ← play s3 s.me c [] { pick := fun ts => ts == [g] }
  let n ← play (s3.fund s.me 4) s.me c [] { pick := fun ts => ts == [g] }
  return a.countIn s.me .base "SFD-022" == 1 && (a.poolOf s.me).fury == 11 &&
    (a.poolOf s.me).energy == 8 && n.countIn s.me .base "SFD-022" == 1
-- (a hand with no Fury: the gear is not played, but the other gear was killed)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-084" .hand
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, _) ← put s2 s.me "SFD-022" .hand
  let poor := s3.fund s.me 4
  let r ← cast poor s.me c (payOf s3 c) [] { pick := fun ts => ts == [g] }
  return (r.obj? g).isNone && r.countIn s.me .base "SFD-022" == 0
-- (review) Switcheroo with the first unit weaker, and with equal Might
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-145" .hand
  let (s2, a) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, b) ← putAt s2 s.you "OGN-001" s.bf0
  let (s4, e) ← putAt s3 s.you "OGN-051" s.bf0
  let r ← play s4 s.me c [a, b]
  let q ← play s4 s.me c [a, e]
  return r.mightNow a == some 5 && r.mightNow b == some 2 &&
    q.mightNow a == some 2 && q.mightNow e == some 2
-- (review) Temptation: to the place of a unit at a base, the unit goes to its base
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-129" .hand
  let (s2, a) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, b) ← put s2 s.you "OGN-051" .base
  let r ← play s3 s.me c [a, b]
  return (r.obj? a).any (·.loc.isNone) && (r.zone (.player s.you .base)).contains a
-- (review) Arise!: no Equipment, nothing happens; one Equipment, one new soldier ready, and
-- another soldier was already there, exhausted
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-198" .hand
  let (s2, old) ← put s1 s.me "TKN-Sand Soldier" .base
  let s2t := s2.tire old
  let (s3, _) ← put s2t s.me "SFD-042" .base
  let r ← play s3 s.me c
  let n ← play s2t s.me c
  return r.soldiers s.me == (2, 1) && n.soldiers s.me == (1, 0)
-- (review) Fae Porter at a base does not set the ability off; the move away from a battlefield
-- to a base does not either
#guard tsf fun s => do
  let (s1, p) ← put s s.me "SFD-125" .base
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let a ← fire (s2.fund s.me 0 0 0 0 0 1) [.standardMoved p none]
  return (a.obj? u).any (·.loc.isNone) && (a.poolOf s.me).chaos == 1
-- (review) Defiant Dance: the changes end with the turn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-196" .hand
  let (s2, a) ← put s1 s.me "OGN-001" .base
  let (s3, b) ← put s2 s.you "OGN-001" .base
  let r ← play s3 s.me c [a, b]
  let t := r.mapObjects endTurnObj
  return t.mightNow a == s3.mightNow a && t.mightNow b == s3.mightNow b

-- Angle Shot (SFD-011): attach an Equipment to a unit, or detach it (same controller), then draw 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-011" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let a ← play s3 s.me c [u, g] { fromEnd := some 1 }
  let hooked := s3.modObj g (fun o => { o with attached := some u })
  let d ← play hooked s.me c [u, g] { fromEnd := some 2 }
  return (a.obj? g).any (·.attached == some u) && a.handN s.me == s3.handN s.me &&
    (d.obj? g).any (·.attached == none) && d.handN s.me == s3.handN s.me
-- (a unit of the player and an Equipment of the opponent: nothing happens, nothing is drawn)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-011" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.you "SFD-042" .base
  let a ← play s3 s.me c [u, g]
  return (a.obj? g).any (·.attached == none) && a.handN s.me + 1 == s3.handN s.me
-- (the enemy's own: the Equipment may be attached to the enemy's unit)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-011" .hand
  let (s2, u) ← put s1 s.you "OGN-051" .base
  let (s3, g) ← put s2 s.you "SFD-042" .base
  let a ← play s3 s.me c [u, g]
  return (a.obj? g).any (·.attached == some u)

-- Strike Down (SFD-107): an equipped friendly unit deals damage equal to its Might to an enemy
-- unit, then an Equipment is detached from it
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-107" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let (s4, e) ← put s3 s.you "OGN-001" .base
  let (s5, free) ← put s4 s.me "OGN-051" .base
  let s6 := s5.modObj g (fun o => { o with attached := some u })
  let r ← play s6 s.me c [u, e]
  return r.dmg e == (s6.mightNow u).map Int.toNat && (r.obj? g).any (·.attached == none) &&
    (play s6 s.me c [free, e]).isNone && (play s6 s.me c [u, free]).isNone

-- (the Equipment of another unit stays attached, whichever of the two was put first)
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-107" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, v) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-001" .base
  let (a1, g) ← put s4 s.me "SFD-042" .base
  let (a2, g2) ← put a1 s.me "SFD-051" .base
  let (b1, h2) ← put s4 s.me "SFD-051" .base
  let (b2, h) ← put b1 s.me "SFD-042" .base
  let sa := (a2.modObj g (fun o => { o with attached := some u })).modObj g2
    (fun o => { o with attached := some v })
  let sb := (b2.modObj h (fun o => { o with attached := some u })).modObj h2
    (fun o => { o with attached := some v })
  let ra ← play sa s.me c [u, e]
  let rb ← play sb s.me c [u, e]
  return (ra.obj? g).any (·.attached == none) && (ra.obj? g2).any (·.attached == some v) &&
    (rb.obj? h).any (·.attached == none) && (rb.obj? h2).any (·.attached == some v)

-- Veiled Temple (SFD-221): conquer here, ready a friendly gear; an Equipment may be detached
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-221"
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let s4 := (s3.modObj g (fun o => { o with attached := some u })).tire g
  let a ← fire s4 [.scored s.me bf true] { pick := fun ts => ts == [g] }
  let b ← fire s4 [.scored s.me bf true] { pick := fun ts => ts == [g], yes := false }
  let c ← fire s4 [.scored s.me bf false] { pick := fun ts => ts == [g] }
  return a.tired g == some false && (a.obj? g).any (·.attached == none) &&
    b.tired g == some true && (b.obj? g).any (·.attached == some u) &&
    c.tired g == some true

-- Jae Medarda (SFD-142): draw 1 when its player chooses it with a spell
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, jae) ← put s1 s.me "SFD-142" .base
  let (s3, other) ← put s2 s.me "OGN-051" .base
  let a ← play s3 s.me c [jae]
  let b ← play s3 s.me c [other]
  let e ← fire s3 [.chosenBySpell s.you jae]
  return a.handN s.me == s3.handN s.me && b.handN s.me + 1 == s3.handN s.me &&
    e.handN s.me == s3.handN s.me

-- Irelia, Fervent (SFD-057): +1 Might this turn when she is chosen or readied
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, i) ← put s1 s.me "SFD-057" .base
  let a ← play s2 s.me c [i]
  let b ← fire s2 [.readied i]
  let n ← fire s2 [.chosenBySpell s.you i]
  return a.mightNow i == (s2.mightNow i).map (· + 1) &&
    b.mightNow i == (s2.mightNow i).map (· + 1) && n.mightNow i == s2.mightNow i

-- Spirit Wheel (SFD-144): when its player chooses a friendly unit, pay 1 and exhaust it to draw 1
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, w) ← put s1 s.me "SFD-144" .base
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-051" .base
  let a ← play s4 s.me c [u]
  let b ← play s4 s.me c [e]
  let n ← play s4 s.me c [u] { yes := false }
  let t ← play (s4.tire w) s.me c [u]
  let p ← cast (s4.fund s.me 1) s.me c (payOf s4 c) [u]
  return a.handN s.me == s4.handN s.me && a.tired w == some true &&
    b.handN s.me + 1 == s4.handN s.me && n.handN s.me + 1 == s4.handN s.me &&
    t.handN s.me + 1 == s4.handN s.me && p.tired w == some false

-- Blade Dancer (SFD-195), a Legend: when its player chooses a friendly unit, exhaust it and pay 1
-- Power to ready the unit; when they conquer, pay 1 Energy to ready it
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, l) ← put s1 s.me "SFD-195" .legendZone
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let tired := s3.tire u
  let a ← play tired s.me c [u]
  let b ← play (s3.tire l) s.me c [u]
  let (s4, bf) ← putBf s3 s.me "SFD-216"
  let k ← fire ((s4.tire l).rich s.me) [.scored s.me bf true]
  let m ← fire ((s4.tire l).fund s.me 0) [.scored s.me bf true]
  return a.tired u == some false && a.tired l == some true && b.tired u == some false &&
    k.tired l == some false && m.tired l == some true

-- Azir, Sovereign (SFD-177): when it attacks, the player may move their token units there
#guard tsf fun s => do
  let (s1, a) ← putAt s s.me "SFD-177" s.bf0
  let (s2, _) ← applyCreate s1 s.me a {} "Sand Soldier" (.const 1) .atBase false
  let (s3, plain) ← put s2 s.me "OGN-051" .base
  let tok := (s3.zone (.player s.me .base)).find? (fun o =>
    (s3.cardDef? o).any (·.name == "Sand Soldier"))
  let t ← tok
  let r ← fire s3 [.combatStarted s.bf0 s.me]
  let n ← fire s3 [.combatStarted s.bf0 s.me] { yes := false }
  let d ← fire s3 [.combatStarted s.bf0 s.you]
  return (r.obj? t).any (·.loc == some s.bf0) && (r.obj? plain).any (·.loc.isNone) &&
    (n.obj? t).any (·.loc.isNone) && (d.obj? t).any (·.loc.isNone)

-- Renata Glasc, Industrialist (SFD-171): the player's tokens enter ready
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-076" .hand
  let (s2, _) ← put s1 s.me "SFD-171" .base
  let (s3, c2) ← put s1 s.me "SFD-076" .hand
  let a ← play s2 s.me c
  let b ← play s3 s.me c2
  let mech (x : GameState) :=
    (x.zone (.player s.me .base)).find? (fun o => (x.cardDef? o).any (·.name == "Mech"))
  return (mech a).bind a.tired == some false && (mech b).bind b.tired == some true

-- (review) Angle Shot: "detach from that unit": an Equipment attached to another unit stays
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-011" .hand
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, v) ← put s2 s.me "OGN-051" .base
  let (s4, g) ← put s3 s.me "SFD-042" .base
  let hooked := s4.modObj g (fun o => { o with attached := some v })
  let d ← play hooked s.me c [u, g] { fromEnd := some 2 }
  return (d.obj? g).any (·.attached == some v) && d.handN s.me == hooked.handN s.me

-- (review) Blade Dancer: an enemy unit, a refusal, and no Power change nothing
#guard tsf fun s => do
  let (s1, c) ← put s s.me "OGN-004" .hand
  let (s2, l) ← put s1 s.me "SFD-195" .legendZone
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let (s4, e) ← put s3 s.you "OGN-051" .base
  let t := (s4.tire u).tire e
  let a ← play t s.me c [e]
  let n ← play t s.me c [u] { yes := false }
  let p ← cast (t.fund s.me 1) s.me c (payOf t c) [u]
  let ok ← play t s.me c [u]
  return a.tired e == some true && a.tired l == some false && n.tired u == some true &&
    n.tired l == some false && p.tired u == some true && p.tired l == some false &&
    ok.tired u == some false && ok.tired l == some true && (ok.poolOf s.me).fury == 11

-- (review) Renata: the opponent's Renata does not help; Gold stays exhausted; a unit card is played
-- exhausted as usual
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-076" .hand
  let (s2, _) ← put s1 s.you "SFD-171" .base
  let (t1, _) ← put s s.me "SFD-171" .base
  let (t2, bw) ← put t1 s.me "SFD-004" .hand
  let (t3, v) ← put t2 s.me "OGN-051" .hand
  let a ← play s2 s.me c
  let b ← play t3 s.me bw
  let u ← play t3 s.me v
  let mech (x : GameState) :=
    (x.zone (.player s.me .base)).find? (fun o => (x.cardDef? o).any (·.name == "Mech"))
  return (mech a).bind a.tired == some true &&
    (b.firstOf s.me .base "SFD-T03").bind b.tired == some true &&
    (u.firstOf s.me .base "OGN-051").bind u.tired == some true

-- (review) Veiled Temple: a gear that is not an Equipment is only readied; an enemy gear is no
-- choice
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-221"
  let (s2, g) ← put s1 s.me "OGN-098" .base
  let (s3, e) ← put s2 s.you "OGN-098" .base
  let t := (s3.tire g).tire e
  let a ← fire t [.scored s.me bf true] { pick := fun ts => ts == [g] }
  let picks ← firePicks t [.scored s.me bf true]
  return a.tired g == some false && picks.contains g && !picks.contains e
-- (ready it, but do not detach)
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-221"
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let t := (s3.modObj g (fun o => { o with attached := some u })).tire g
  let a ← fire t [.scored s.me bf true] { pick := fun ts => ts == [g], fromEnd := some 1 }
  return a.tired g == some false

-- (review) Azir: tokens at another battlefield come too; the opponent's tokens do not
#guard tsf fun s => do
  let (s1, a) ← putAt s s.me "SFD-177" s.bf0
  let (s2, _) ← applyCreate s1 s.me a {} "Sand Soldier" (.const 2) .atBase false
  let (s3, _) ← applyCreate s2 s.you a {} "Sand Soldier" (.const 1) .atBase false
  let mine (x : GameState) := (x.zone .battlefieldZone).filter (fun o =>
    (x.cardDef? o).any (·.name == "Sand Soldier") &&
      (x.obj? o).any (fun ob => ob.loc == some s.bf0 && ob.controller == s.me))
  let r ← fire s3 [.combatStarted s.bf0 s.me]
  return (mine r).length == 2 && (r.zone (.player s.you .base)).length ==
    (s3.zone (.player s.you .base)).length
/-- Put the cards on top of the player's Main Deck, the first of the list on top; their ids. -/
meta def _root_.Riftbound.GameState.stackTop (s : GameState) (p : PlayerId) (cards : List String) :
    Option (GameState × List ObjId) :=
  let r := cards.foldlM (fun (acc : GameState × List ObjId) c => do
    let (s1, o) ← put acc.1 p c .mainDeck
    pure (s1, acc.2 ++ [o])) (s, [])
  r.map (fun (s1, ids) =>
    (s1.setZone (.player p .mainDeck)
      (ids ++ (s1.zone (.player p .mainDeck)).filter (fun o => !ids.contains o)), ids))

/-- The top card of the player's Main Deck. -/
meta def _root_.Riftbound.GameState.topCard (s : GameState) (p : PlayerId) : Option ObjId :=
  (s.zone (.player p .mainDeck)).head?

/-- The last card of the player's Main Deck, the bottom one. -/
meta def _root_.Riftbound.GameState.bottomCards (s : GameState) (p : PlayerId) (n : Nat) :
    List ObjId :=
  ((s.zone (.player p .mainDeck)).reverse.take n).reverse

/-- The cards of the bottom `n` places of the Main Deck of the player are the card. -/
meta def _root_.Riftbound.GameState.bottomIs (s : GameState) (p : PlayerId) (n : Nat)
    (code : String) : Bool :=
  (s.bottomCards p n).length == n &&
    (s.bottomCards p n).all (fun o => (s.cardDef? o).any (·.id.code == code))

/-- The number of cards in the Main Deck of the player. -/
meta def _root_.Riftbound.GameState.deckN (s : GameState) (p : PlayerId) : Nat :=
  (s.zone (.player p .mainDeck)).length

/-- The object is a card with the identifier. -/
meta def _root_.Riftbound.GameState.isCard (s : GameState) (code : String) (o : ObjId) : Bool :=
  (s.cardDef? o).any (·.id.code == code)

-- Apprentice Smith (SFD-041): when it moves, reveal the top card: a gear is drawn, else recycled
#guard tsf fun s => do
  let (s1, a) ← put s s.me "SFD-041" .base
  let (g, _) ← s1.stackTop s.me ["SFD-042"]
  let (u, _) ← s1.stackTop s.me ["OGN-051"]
  let r ← fire g [.standardMoved a none]
  let q ← fire u [.standardMoved a none]
  return r.countIn s.me .hand "SFD-042" == g.countIn s.me .hand "SFD-042" + 1 &&
    r.deckN s.me + 1 == g.deckN s.me &&
    q.countIn s.me .hand "OGN-051" == u.countIn s.me .hand "OGN-051" &&
    q.deckN s.me == u.deckN s.me && q.bottomIs s.me 1 "OGN-051"

-- Ornn, Blacksmith (SFD-058): when played or when it holds, look at the top 4 cards: a gear among
-- them may be drawn, the rest are recycled
#guard tsf fun s => do
  let (s1, o) ← put s s.me "SFD-058" .base
  let (d, _) ← s1.stackTop s.me ["OGN-051", "SFD-042", "OGN-051", "OGN-051"]
  let a ← fire d [.played s.me o]
  let b ← fire d [.played s.me o] { yes := false }
  let (h1, bf) ← putBf s1 s.me "SFD-216"
  let (h2, _) ← putAt h1 s.me "SFD-058" bf
  let (h3, _) ← h2.stackTop s.me ["OGN-051", "SFD-042", "OGN-051", "OGN-051"]
  let c ← fire h3 [.scored s.me bf false]
  let e ← fire h3 [.scored s.me bf true]
  return a.countIn s.me .hand "SFD-042" == d.countIn s.me .hand "SFD-042" + 1 &&
    a.deckN s.me + 1 == d.deckN s.me && a.bottomIs s.me 3 "OGN-051" &&
    b.countIn s.me .hand "SFD-042" == d.countIn s.me .hand "SFD-042" &&
    b.deckN s.me == d.deckN s.me && b.bottomIs s.me 1 "OGN-051" &&
    c.countIn s.me .hand "SFD-042" == h3.countIn s.me .hand "SFD-042" + 1 &&
    e.deckN s.me == h3.deckN s.me

-- Called Shot (SFD-122): look at the top 2 cards, draw one and recycle the other
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-122" .hand
  let (d, _) ← s1.stackTop s.me ["OGN-051", "SFD-042"]
  let r ← play d s.me c
  return r.deckN s.me + 1 == d.deckN s.me && r.handN s.me == d.handN s.me &&
    (r.countIn s.me .hand "OGN-051" + r.countIn s.me .hand "SFD-042" ==
      d.countIn s.me .hand "OGN-051" + d.countIn s.me .hand "SFD-042" + 1)

-- Ravenbloom Conservatory (SFD-215): when its player defends here, reveal the top card: a spell is
-- put in the hand, anything else is recycled
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-215"
  let (s2, _) ← putAt s1 s.me "OGN-051" bf
  let (s3, _) ← putAt s2 s.you "OGN-051" bf
  let (sp, _) ← s3.stackTop s.me ["OGN-004"]
  let (un, _) ← s3.stackTop s.me ["OGN-051"]
  let a ← fire sp [.combatStarted bf s.you]
  let b ← fire un [.combatStarted bf s.you]
  let c ← fire sp [.combatStarted bf s.me]
  return a.countIn s.me .hand "OGN-004" == sp.countIn s.me .hand "OGN-004" + 1 &&
    b.countIn s.me .hand "OGN-051" == un.countIn s.me .hand "OGN-051" &&
    b.deckN s.me == un.deckN s.me && b.bottomIs s.me 1 "OGN-051" &&
    c.countIn s.me .hand "OGN-004" == sp.countIn s.me .hand "OGN-004"

-- Void Rush (SFD-188): reveal the top 2 cards, play one for 2 less, draw the ones not played
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-188" .hand
  let (d, _) ← s1.stackTop s.me ["OGN-001", "SFD-042"]
  let r ← play d s.me c [] { obj := d.isCard "OGN-001" }
  let n ← play d s.me c [] { yes := false }
  return r.countIn s.me .base "OGN-001" == 1 && r.countIn s.me .hand "SFD-042" ==
      d.countIn s.me .hand "SFD-042" + 1 && (r.poolOf s.me).energy == 12 - 2 - 3 &&
    n.countIn s.me .base "OGN-001" == 0 && n.countIn s.me .hand "OGN-001" ==
      d.countIn s.me .hand "OGN-001" + 1 && n.countIn s.me .hand "SFD-042" ==
      d.countIn s.me .hand "SFD-042" + 1

-- Rek'Sai, Swarm Queen (SFD-170): when it attacks, may reveal the top 2, play one, recycle the rest
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-170" s.bf0
  let (d, _) ← s1.stackTop s.me ["OGN-051", "SFD-042"]
  let a ← fire (d.rich s.me) [.combatStarted s.bf0 s.me] { obj := d.isCard "OGN-051" }
  let n ← fire (d.rich s.me) [.combatStarted s.bf0 s.me] { yes := false }
  return a.countIn s.me .base "OGN-051" == 1 && a.deckN s.me + 1 == d.deckN s.me &&
    a.bottomIs s.me 1 "SFD-042" && n.countIn s.me .base "OGN-051" == 0 &&
    n.deckN s.me == d.deckN s.me && r != s.bf0

-- Void Burrower (SFD-187), a Legend: when its player conquers, it may be exhausted to reveal the
-- top 2 cards, play one and recycle the rest
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-187" .legendZone
  let (bfs, bf) ← putBf s1 s.me "SFD-216"
  let (d, _) ← bfs.stackTop s.me ["OGN-051", "SFD-042"]
  let a ← fire (d.rich s.me) [.scored s.me bf true] { obj := d.isCard "OGN-051" }
  let t ← fire ((d.tire l).rich s.me) [.scored s.me bf true]
  return a.countIn s.me .base "OGN-051" == 1 && a.tired l == some true &&
    t.countIn s.me .base "OGN-051" == 0 && t.deckN s.me == d.deckN s.me

-- Here to Help (SFD-111): play a unit from the hand to a battlefield the player controls, for 3
-- less
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-111" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .hand
  let s3 := s2.control s.me s.bf0
  let r ← play s3 s.me c [s.bf0]
  let n ← play s3 s.me c [s.bf0] { yes := false }
  let there := (r.zone .battlefieldZone).any (fun o => r.isCard "OGN-001" o &&
    (r.obj? o).any (·.loc == some s.bf0))
  return there && (r.poolOf s.me).energy == 12 - 2 - 2 && n.countIn s.me .hand "OGN-001" == 1 &&
    (play s2 s.me c [s.bf0]).isNone

-- Rumble, Hotheaded (SFD-026): when it conquers, may recycle another friendly unit to play a Mech
-- from the Trash, its Energy cost reduced by the Might of the recycled unit; Mechs have Assault
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-026" s.bf0
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← put s2 s.me "SFD-062" .trash
  let (s4, m) ← put s3 s.me "SFD-062" .base
  let a ← fire (s4.rich s.me) [.conquerActivated r] { pick := fun ts => ts == [u] }
  let n ← fire (s4.rich s.me) [.conquerActivated r] { pick := fun ts => ts == [u], yes := false }
  return a.countIn s.me .base "SFD-062" == 2 && (a.obj? u).isNone &&
    (a.poolOf s.me).energy == 12 - 1 && n.countIn s.me .base "SFD-062" == 1 &&
    (n.obj? u).isSome && s4.kwAmount m .assault == 1 && s4.kwAmount u .assault == 0

-- (Fizz: a spell with Energy cost 4 is not a legal choice)
#guard tsf fun s => do
  let (s1, f) ← put s s.me "SFD-140" .hand
  let (s2, sp) ← put s1 s.me "SFD-076" .trash
  let r ← play s2 s.me f
  return r.countIn s.me .trash "SFD-076" == 1 && (r.obj? sp).isSome &&
    r.countNamed s.me .base "Mech" == 0

-- Fizz, Trickster (SFD-140): when played, may play a spell from the Trash (Energy cost 3 or less),
-- ignoring its Energy cost; it is recycled after
#guard tsf fun s => do
  let (s1, f) ← put s s.me "SFD-140" .hand
  let (s2, sp) ← put s1 s.me "SFD-204" .trash
  let (s3, u) ← put s2 s.me "OGN-051" .base
  let (s4, big) ← put s3 s.me "SFD-147" .trash
  let a ← play (s4.tire u) s.me f
  let n ← play (s4.tire u) s.me f [] { yes := false }
  return a.tired u == some false && (a.obj? sp).isNone && a.countIn s.me .trash "SFD-204" == 0 &&
    n.tired u == some true && n.countIn s.me .trash "SFD-204" == 1 &&
    a.countIn s.me .trash "SFD-147" == 1 && (a.poolOf s.me).energy == 12 - 3 - 0 - 0 &&
    (a.obj? big).isSome

-- (review) playing for a reduced cost: the Energy goes down to the floor of 0 and the Power is paid
-- in full; with no Power in the Pool, nothing is paid and the card is not played
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-002" .hand
  let rich := s1.fund s.me 3 1
  let ok := playReducedOne s.me 3 none rich u
  let poor := playReducedOne s.me 3 none (s1.fund s.me 3) u
  let (s2, v) ← put s s.me "OGN-051" .hand
  let floor := playReducedOne s.me 10 none (s2.fund s.me 0) v
  return ok.1.countIn s.me .base "SFD-002" == 1 && (ok.1.poolOf s.me).energy == 0 &&
    (ok.1.poolOf s.me).fury == 0 && poor.1.countIn s.me .base "SFD-002" == 0 &&
    (poor.1.poolOf s.me).energy == 3 && floor.1.countIn s.me .base "OGN-051" == 1

-- (review) Rek'Sai and Void Burrower pay the whole cost of the unit they play
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-170" s.bf0
  let (d, ids) ← s1.stackTop s.me ["OGN-051", "SFD-042"]
  let cost := (d.energyCost? s.me (ids.head?.getD ⟨0⟩)).getD 0
  let a ← fire (d.rich s.me) [.combatStarted s.bf0 s.me] { obj := d.isCard "OGN-051" }
  return a.countIn s.me .base "OGN-051" == 1 && (a.poolOf s.me).energy + cost == 12 && cost > 0

-- (review) Called Shot: the card not drawn goes to the bottom of the deck
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-122" .hand
  let (d, _) ← s1.stackTop s.me ["OGN-051", "SFD-042"]
  let r ← play d s.me c
  let gainedA := r.countIn s.me .hand "OGN-051" == d.countIn s.me .hand "OGN-051" + 1
  let gainedB := r.countIn s.me .hand "SFD-042" == d.countIn s.me .hand "SFD-042" + 1
  return (gainedA && r.bottomIs s.me 1 "SFD-042") || (gainedB && r.bottomIs s.me 1 "OGN-051")

-- (review) Void Rush: a spell among the cards cannot be played this way: both are drawn
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-188" .hand
  let (d, _) ← s1.stackTop s.me ["OGN-004", "OGN-051"]
  let r ← play d s.me c [] { obj := d.isCard "OGN-004" }
  return r.countIn s.me .hand "OGN-004" == d.countIn s.me .hand "OGN-004" + 1 &&
    r.countIn s.me .hand "OGN-051" == d.countIn s.me .hand "OGN-051" + 1 &&
    r.countIn s.me .base "OGN-051" == 0

-- (review) Rumble: if the unit chosen is gone when the ability resolves, no Mech is played
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-026" s.bf0
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, _) ← put s2 s.me "SFD-062" .trash
  let s4 := s3.rich s.me
  let s5 := { s4 with pending := insertTriggers (s4.detect [.conquerActivated r]) s4.pending }
  let r1 ← match advance 100 s5 [] with
    | .ok (x, _) => some x
    | .error _ => none
  let r2 := settleChain { pick := fun ts => ts == [u] } 1 r1
  let r3 := (killObj r2 u).1
  let r4 := settleChain {} 12 r3
  return r4.countIn s.me .base "SFD-062" == 0 && r4.countIn s.me .trash "SFD-062" == 1
-- Assembly Rig (SFD-019): pay 1 Fury, exhaust, recycle a unit from the Trash: a 3 Might Mech token
#guard tsf fun s => do
  let (s1, rig) ← put s s.me "SFD-019" .base
  let (s2, _) ← put s1 s.me "OGN-051" .trash
  let (s3, _) ← put s2 s.me "OGN-004" .trash
  let a ← activate s3 s.me rig 0 [] ⟨1, [.fury]⟩
  let n ← activate s3 s.me rig 0 [] ⟨1, [.fury]⟩
  let tr (x : GameState) := (x.zone (.player s.me .trash)).length
  return a.countNamed s.me .base "Mech" == 1 && a.countIn s.me .trash "OGN-051" == 0 &&
    a.countIn s.me .trash "OGN-004" == 1 && a.tired rig == some true && tr a + 1 == tr s3 &&
    a.deckN s.me == s3.deckN s.me + 1 && n.countNamed s.me .base "Mech" == 1 &&
    (activate (s3.tire rig) s.me rig 0 [] ⟨1, [.fury]⟩).isNone &&
    (activate (s1.fund s.me 5 5) s.me rig 0 [] ⟨1, [.fury]⟩).isNone && s2.deckN s.me > 0

-- Poro Snax (SFD-046): draw 1 when played; pay 1 Calm, exhaust, kill it: draw 1
#guard tsf fun s => do
  let (s1, g) ← put s s.me "SFD-046" .base
  let a ← fire s1 [.played s.me g]
  let b ← activate s1 s.me g 1 [] ⟨1, [.calm]⟩
  return a.handN s.me == s1.handN s.me + 1 && b.handN s.me == s1.handN s.me + 1 &&
    (b.obj? g).isNone && b.countIn s.me .trash "SFD-046" == 1 &&
    (activate s1 s.me g 1 [] ⟨1, []⟩).isNone

-- Renata Glasc, Mastermind (SFD-088): at a battlefield only: pay 1 Mind to draw 1; pay 4 Mind and
-- exhaust to score 1 point (an ability with a guard cannot be used while the guard is false)
#guard tsf fun s => do
  let (s1, r) ← putAt s s.me "SFD-088" s.bf0
  let (s2, q) ← put s s.me "SFD-088" .base
  let a ← activate s1 s.me r 0 [] ⟨1, [.mind]⟩
  let b ← activate s1 s.me r 1 [] ⟨4, [.mind, .mind, .mind, .mind]⟩
  return a.handN s.me == s1.handN s.me + 1 && b.pointsOf s.me == s1.pointsOf s.me + 1 &&
    b.tired r == some true && (activate s2 s.me q 0 [] ⟨1, [.mind]⟩).isNone &&
    (activate s2 s.me q 1 [] ⟨4, [.mind, .mind, .mind, .mind]⟩).isNone

-- Azir, Ascendant (SFD-050): pay 1 Calm: swap places with a friendly unit; may take its Equipment;
-- once per turn
#guard tsf fun s => do
  let (s1, az) ← put s s.me "SFD-050" .base
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let (s3, g) ← put s2 s.me "SFD-042" .base
  let hooked := s3.modObj g (fun o => { o with attached := some u })
  let r ← activate hooked s.me az 0 [u] ⟨0, [.calm]⟩
  let n ← activate hooked s.me az 0 [u] ⟨0, [.calm]⟩ { yes := false }
  return (r.obj? az).any (·.loc == some s.bf0) && (r.obj? u).any (·.loc.isNone) &&
    (r.obj? g).any (·.attached == some az) && (n.obj? g).any (·.attached == some u) &&
    (n.obj? az).any (·.loc == some s.bf0) && (activate r s.me az 0 [u] ⟨0, [.calm]⟩).isNone &&
    (r.obj? az).any (·.used.length == 1)

-- Grandmaster at Arms (SFD-193), a Legend: attach a detached Equipment to a unit (pay 1, exhaust);
-- move an attached Equipment to another unit (exhaust)
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-193" .legendZone
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, v) ← put s2 s.me "OGN-051" .base
  let (s4, g) ← put s3 s.me "SFD-042" .base
  let a ← activate s4 s.me l 0 [g, u] ⟨1, []⟩
  let hooked := s4.modObj g (fun o => { o with attached := some u })
  let b ← activate hooked s.me l 1 [g, v]
  return (a.obj? g).any (·.attached == some u) && a.tired l == some true &&
    (b.obj? g).any (·.attached == some v) && b.tired l == some true &&
    (activate hooked s.me l 0 [g, v] ⟨1, []⟩).isNone && (activate s4 s.me l 1 [g, v]).isNone

-- Purifier (SFD-183), a Legend: the units with an Equipment have Assault
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-183" .legendZone
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, w) ← put s2 s.me "OGN-051" .base
  let (s4, g) ← put s3 s.me "SFD-042" .base
  let (s5, e) ← put s4 s.you "OGN-051" .base
  let (s6, h) ← put s5 s.you "SFD-042" .base
  let s7 := (s6.modObj g (fun o => { o with attached := some u })).modObj h
    (fun o => { o with attached := some e })
  return s7.kwAmount u .assault == 1 && s7.kwAmount w .assault == 0 && s7.kwAmount e .assault == 0

-- Lonely Poro (SFD-036): when it dies alone, draw 1 (a real death by `killObj`)
#guard tsf fun s => do
  let (s1, x) ← putAt s s.me "SFD-036" s.bf0
  let (b1, y) ← put s s.me "SFD-036" .base
  let (s2, _) ← put b1 s.me "OGN-051" .base
  let (s3, _) ← putAt s1 s.me "OGN-051" s.bf0
  let (s4, _) ← putAt s1 s.me "OGN-051" s.bf0
  let (s5, _) ← putAt s1 s.you "OGN-051" s.bf0
  let (s6, _) ← put s1 s.me "OGN-051" .base
  let die (st : GameState) (u : ObjId) : Option GameState :=
    let (st1, evs) := killObj st u
    fire st1 evs
  let _ := s4
  let alone ← die s1 x
  let company ← die s3 x
  let elsewhere ← die s6 x
  let enemy ← die s5 x
  let atBase ← die b1 y
  let baseCompany ← die s2 y
  return alone.handN s.me == s1.handN s.me + 1 && company.handN s.me == s3.handN s.me &&
    elsewhere.handN s.me == s6.handN s.me + 1 && enemy.handN s.me == s5.handN s.me + 1 &&
    atBase.handN s.me == b1.handN s.me + 1 && baseCompany.handN s.me == s2.handN s.me

-- Unsung Hero (SFD-167): when it dies and was Mighty (a real death), draw 2
#guard tsf fun s => do
  let (s1, x) ← put s s.me "SFD-167" .base
  let big := s1.modObj x (fun o => { o with mightMods := [{ amount := 3, ends := .never }] })
  let die (st : GameState) : Option GameState :=
    let (st1, evs) := killObj st x
    fire st1 evs
  let a ← die big
  let b ← die s1
  return a.handN s.me == big.handN s.me + 2 && b.handN s.me == s1.handN s.me

-- Zaun Punk (SFD-160): when played, may kill a friendly gear; if so, kill a gear
#guard tsf fun s => do
  let (s1, z) ← put s s.me "SFD-160" .hand
  let (s2, mine) ← put s1 s.me "SFD-042" .base
  let (s3, theirs) ← put s2 s.you "SFD-042" .base
  let a ← play s3 s.me z [] { obj := fun o => o == mine || o == theirs }
  let n ← play s3 s.me z [] { yes := false }
  let none_ ← play s1 s.me z
  return (a.obj? mine).isNone && (a.obj? theirs).isNone && (n.obj? mine).isSome &&
    (n.obj? theirs).isSome && none_.countIn s.me .base "SFD-160" == 1

-- Card Sharp (SFD-081): the player and each opponent may play a Gold; for each opponent who did,
-- the player plays another
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-081" .hand
  let a ← play s1 s.me c
  let n ← play s1 s.me c [] { yes := false }
  return a.countIn s.me .base "SFD-T03" == 2 && a.countIn s.you .base "SFD-T03" == 1 &&
    n.countIn s.me .base "SFD-T03" == 0 && n.countIn s.you .base "SFD-T03" == 0

-- (review) Assembly Rig: with no unit in the Trash the ability cannot be used at all (a guard)
#guard tsf fun s => do
  let (s1, rig) ← put s s.me "SFD-019" .base
  let (s2, _) ← put s1 s.me "OGN-004" .trash
  return (activate s1 s.me rig 0 [] ⟨1, [.fury]⟩).isNone &&
    (activate s2 s.me rig 0 [] ⟨1, [.fury]⟩).isNone

-- (review) Zaun Punk: with only an enemy gear, nothing is killed (the cost is a friendly gear)
#guard tsf fun s => do
  let (s1, z) ← put s s.me "SFD-160" .hand
  let (s2, theirs) ← put s1 s.you "SFD-042" .base
  let r ← play s2 s.me z
  return (r.obj? theirs).isSome && r.countIn s.me .base "SFD-160" == 1

-- (review) Azir, Ascendant cannot choose itself; Grandmaster at Arms moves only its player's
-- Equipment; Lonely Poro's enemies at the same place do not count (above)
#guard tsf fun s => do
  let (s1, az) ← put s s.me "SFD-050" .base
  return (activate s1 s.me az 0 [az] ⟨0, [.calm]⟩).isNone
#guard tsf fun s => do
  let (s1, l) ← put s s.me "SFD-193" .legendZone
  let (s2, u) ← put s1 s.me "OGN-051" .base
  let (s3, g) ← put s2 s.you "SFD-042" .base
  return (activate s3 s.me l 0 [g, u] ⟨1, []⟩).isNone

-- (review) Azir, Ascendant: if it left play before the ability resolves, nothing is swapped
#guard tsf fun s => do
  let (s1, az) ← put s s.me "SFD-050" .base
  let (s2, u) ← putAt s1 s.me "OGN-051" s.bf0
  let act : Action := ⟨.player s.me, .activate az 0 ⟨0, [.calm]⟩ [u]⟩
  let s3 ← match step 100 (s2.rich s.me) act with
    | .ok (x, _) => some x
    | .error _ => none
  let s4 := (killObj s3 az).1
  let r := settleChain {} 12 s4
  return (r.obj? u).any (·.loc == some s.bf0)

/-- Run the effect of the object `src` of the player, with the objects chosen in `slots`, and let
the questions it asks be answered. -/
meta def runBody (s : GameState) (p : PlayerId) (src : ObjId) (slots : List ObjId) (body : Effect)
    (says : Says := {}) : Option GameState :=
  let env : Env := { slots := slots.map Value.obj }
  let s0 := { s with pending := Frame.run p src env (EffectList.cons body EffectList.nil) ::
    s.pending }
  match advance 100 s0 [] with
  | .ok (s1, _) => some (settleChain says 12 s1)
  | .error _ => none

/-- The effect of the card. -/
meta def effectOf (code : String) : Option EffectDef :=
  (RiftboundCards.db.find? ⟨code⟩).bind (·.spellEffect)

/-- Put a spell of the player on the Chain: the object it is there. -/
meta def onChain (s : GameState) (p : PlayerId) (code : String) : Option (GameState × ObjId) := do
  let (s1, c) ← put s p code .hand
  let (s2, c') ← moveObj s1 c .chain
  pure (s2, c')

-- Jaull-Fish (SFD-103): costs 2 Energy less for each of its player's Mighty units
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-103" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let (s3, _) ← put s2 s.me "OGN-001" .base
  let (s4, _) ← put s3 s.you "OGN-001" .base
  let (s5, _) ← put s4 s.me "OGN-051" .base
  return s1.energyCost? s.me j == some 7 && s2.energyCost? s.me j == some 5 &&
    s5.energyCost? s.me j == some 3

-- Hard Bargain (SFD-136): counter a spell unless its controller pays 2 Energy
#guard tsf fun s => do
  let (s1, sp) ← onChain s s.you "OGN-004"
  let (s2, hb) ← put s1 s.me "SFD-136" .hand
  let body := ((effectOf "SFD-136").map (·.body)).getD .nop
  let poor ← runBody (s2.fund s.you 1) s.me hb [sp] body
  let rich ← runBody (s2.fund s.you 2) s.me hb [sp] body
  let refuse ← runBody (s2.fund s.you 2) s.me hb [sp] body { fromEnd := some 2 }
  return (poor.zone .chain).isEmpty && (poor.poolOf s.you).energy == 1 &&
    (rich.zone .chain).length == 1 && (rich.poolOf s.you).energy == 0 &&
    (refuse.zone .chain).isEmpty && (refuse.poolOf s.you).energy == 2 &&
    (s2.zone .chain).length == 1

-- Not So Fast (SFD-045): counter an enemy spell that chooses a unit or gear of its player
#guard tsf fun s => do
  let (s1, mine) ← put s s.me "OGN-051" .base
  let (s2, sp) ← onChain s1 s.you "OGN-004"
  let (s3, nsf) ← put s2 s.me "SFD-045" .hand
  let (s4, other) ← put s3 s.you "OGN-051" .base
  let on (st : GameState) (sp' : ObjId) (t : ObjId) :=
    let st' := st.modObj sp' (fun o => { o with targets := [t] })
    match effectOf "SFD-045" with
    | some e => targetsOk st' s.me nsf e.choices [sp']
    | none => false
  return on s4 sp mine && !on s4 sp other

-- Riposte (SFD-206): counter a spell and give a friendly unit +Might equal to its Energy cost
#guard tsf fun s => do
  let (s1, u) ← put s s.me "OGN-051" .base
  let (s2, sp) ← onChain s1 s.you "OGN-004"
  let (s3, rip) ← put s2 s.me "SFD-206" .hand
  let body := ((effectOf "SFD-206").map (·.body)).getD .nop
  let r ← runBody s3 s.me rip [u, sp] body
  return (r.zone .chain).isEmpty && r.mightNow u == (s3.mightNow u).map (· + 1)

-- Dauntless Vanguard (SFD-093): may be played to a battlefield where an enemy unit is
#guard tsf fun s => do
  let (s1, v) ← put s s.me "SFD-093" .hand
  let (s2, _) ← putAt s1 s.you "OGN-051" s.bf0
  let (s3, bf2) ← putBf s2 s.me "SFD-216"
  let r ← activate s3 s.me v 0 [s.bf0] ⟨4, [.body]⟩
  return (r.zone .battlefieldZone).any (fun o => r.isCard "SFD-093" o &&
      (r.obj? o).any (·.loc == some s.bf0)) &&
    (activate s3 s.me v 0 [bf2] ⟨4, [.body]⟩).isNone

-- Lucian, Gunslinger (SFD-028): when it attacks, damage equal to its Assault to an enemy unit here
#guard tsf fun s => do
  let (s1, l) ← putAt s s.me "SFD-028" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-001" s.bf0
  let boosted := s2.modObj l (fun o => { o with tempKws := [(⟨.assault, .amount 2⟩, .turn)] })
  let a ← fire s2 [.combatStarted s.bf0 s.me]
  let b ← fire boosted [.combatStarted s.bf0 s.me]
  let d ← fire s2 [.combatStarted s.bf0 s.you]
  return a.dmg e == some 1 && b.dmg e == some 3 && d.dmg e == some 0

-- Drag Under (SFD-164): kill a unit at a battlefield
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-164" .hand
  let (s2, u) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, v) ← put s2 s.you "OGN-001" .base
  let r ← play s3 s.me c [u]
  return (r.obj? u).isNone && (play s3 s.me c [v]).isNone

-- (review) Hard Bargain: the opponent's spell only (not one's own); a Repeat does not ask again
-- once the spell is gone; a spell that left the Chain is not asked about
#guard tsf fun s => do
  let (s1, sp) ← onChain s s.you "OGN-004"
  let (s2, mine) ← onChain s1 s.me "OGN-004"
  let (s3, hb) ← put s2 s.me "SFD-136" .hand
  let e ← effectOf "SFD-136"
  let body := e.body
  let twice : Effect := .seq (.cons body (.cons body .nil))
  let r ← runBody (s3.fund s.you 5) s.me hb [sp] twice { fromEnd := some 2 }
  let after : Effect := .seq (.cons (.prim (.counter (.slot 0))) (.cons body .nil))
  let gone ← runBody (s3.fund s.you 5) s.me hb [sp] after
  return (r.poolOf s.you).energy == 5 && (r.zone .chain).length == 1 &&
    (gone.poolOf s.you).energy == 5 && targetsOk s3 s.me hb e.choices [sp] &&
    !targetsOk s3 s.me hb e.choices [mine]

-- (review) Not So Fast counters the spell; one that chooses nothing of the player is left alone
#guard tsf fun s => do
  let (s1, mine) ← put s s.me "OGN-051" .base
  let (s2, sp) ← onChain s1 s.you "OGN-004"
  let (s3, nsf) ← put s2 s.me "SFD-045" .hand
  let (s4, gear) ← put s3 s.me "SFD-042" .base
  let e ← effectOf "SFD-045"
  let aimed := s4.modObj sp (fun o => { o with targets := [mine] })
  let aimedAtGear := s4.modObj sp (fun o => { o with targets := [gear] })
  let r ← runBody aimed s.me nsf [sp] e.body
  return (r.zone .chain).isEmpty && targetsOk aimedAtGear s.me nsf e.choices [sp] &&
    !targetsOk s4 s.me nsf e.choices [sp]

-- (review) Jaull-Fish: never below 0; Drag Under can kill a friendly unit; Lucian hits one enemy
-- unit here, and nothing at a base or at another battlefield
#guard tsf fun s => do
  let (s1, j) ← put s s.me "SFD-103" .hand
  let (s2, _) ← put s1 s.me "OGN-001" .base
  let (s3, _) ← put s2 s.me "OGN-001" .base
  let (s4, _) ← put s3 s.me "OGN-001" .base
  let (s5, _) ← put s4 s.me "OGN-001" .base
  return s5.energyCost? s.me j == some 0
#guard tsf fun s => do
  let (s1, c) ← put s s.me "SFD-164" .hand
  let (s2, u) ← putAt s1 s.me "OGN-001" s.bf0
  let r ← play s2 s.me c [u]
  return (r.obj? u).isNone
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-028" s.bf0
  let (s2, near) ← putAt s1 s.you "OGN-001" s.bf0
  let (s3, base) ← put s2 s.you "OGN-001" .base
  let (s4, mine) ← putAt s3 s.me "OGN-001" s.bf0
  let r ← fire s4 [.combatStarted s.bf0 s.me]
  return r.dmg near == some 1 && r.dmg base == some 0 && r.dmg mine == some 0
-- Lucian, Merciless (SFD-113): the first time it conquers each turn, ready it
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-216"
  let (s2, l) ← putAt s1 s.me "SFD-113" bf
  let t := s2.tire l
  let a ← fire t [.scored s.me bf true]
  let b ← fire (a.tire l) [.scored s.me bf true]
  let c ← fire t [.scored s.me bf false]
  return a.tired l == some false && b.tired l == some true && c.tired l == some true

-- Draven, Audacious (SFD-148): the first time it wins a combat each turn, score 1 point; when it
-- dies in a combat, the opponent scores 1 point
#guard tsf fun s => do
  let (s1, _) ← putAt s s.me "SFD-148" s.bf0
  let a ← fire s1 [.combatWon s.bf0 s.me]
  let b ← fire a [.combatWon s.bf0 s.me]
  let (s2, x) ← put s s.me "SFD-148" .trash
  let (s3, _) ← putAt s2 s.me "OGN-051" s.bf0
  let (s4, _) ← putAt s3 s.you "OGN-051" s.bf0
  let fight := s4.inShowdownAt s.bf0 s.me
  let c ← fire fight [.died x s.me]
  let e ← fire s4 [.died x s.me]
  return a.pointsOf s.me == s1.pointsOf s.me + 1 && b.pointsOf s.me == a.pointsOf s.me &&
    c.pointsOf s.you == fight.pointsOf s.you + 1 && e.pointsOf s.you == s4.pointsOf s.you &&
    s1.pointsOf s.you == a.pointsOf s.you

-- Black Market Broker (SFD-121): when its player plays a card from face down, a Gold token
#guard tsf fun s => do
  let (s1, _) ← put s s.me "SFD-121" .base
  let a ← fire s1 [.hiddenPlayed s.me]
  let b ← fire s1 [.hiddenPlayed s.you]
  return a.countIn s.me .base "SFD-T03" == 1 && b.countIn s.me .base "SFD-T03" == 0

-- Harpoon Squad (SFD-137): when it moves from a battlefield, +2 Might this turn
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-137" .base
  let left := s1.modObj u (fun o => { o with prevLoc := some s.bf0 })
  let a ← fire left [.standardMoved u none]
  let b ← fire s1 [.standardMoved u none]
  return a.mightNow u == (left.mightNow u).map (· + 2) && b.mightNow u == s1.mightNow u

-- Prize of Progress (SFD-075): when its player uses an activated ability of a gear, +1 Might
#guard tsf fun s => do
  let (s1, u) ← put s s.me "SFD-075" .base
  let (s2, g) ← put s1 s.me "SFD-046" .base
  let (s3, h) ← put s2 s.you "SFD-046" .base
  let a ← fire s3 [.activated s.me g 1]
  let b ← fire s3 [.activated s.me u 0]
  let c ← fire s3 [.activated s.you h 1]
  return a.mightNow u == (s3.mightNow u).map (· + 1) && b.mightNow u == s3.mightNow u &&
    c.mightNow u == s3.mightNow u

-- Legion Quartermaster (SFD-044): a friendly gear returns to its owner's hand when it is played
#guard tsf fun s => do
  let (s1, q) ← put s s.me "SFD-044" .hand
  let (s2, g) ← put s1 s.me "SFD-042" .base
  let (s3, h) ← put s2 s.you "SFD-042" .base
  let a ← play s3 s.me q
  let n ← play s1 s.me q
  return a.countIn s.me .hand "SFD-042" == 1 && (a.obj? h).isSome && (a.obj? g).isNone &&
    n.countIn s.me .base "SFD-044" == 1

/-- The first Legend of the player (the lab has one for each player). -/
meta def _root_.Riftbound.GameState.legendOf (s : GameState) (p : PlayerId) : Option ObjId :=
  (s.zone (.player p .legendZone)).head?

-- Royal Entourage (SFD-039): ready or exhaust a legend
#guard tsf fun s => do
  let (s1, e) ← put s s.me "SFD-039" .hand
  let l ← s1.legendOf s.me
  let tired := s1.tire l
  let a ← play tired s.me e [] { fromEnd := some 1 }
  let b ← play s1 s.me e [] { fromEnd := some 2 }
  return a.tired l == some false && b.tired l == some true
-- (a legend of the opponent too)
#guard tsf fun s => do
  let (s1, e) ← put s s.me "SFD-039" .hand
  let l ← s1.legendOf s.you
  let mine ← s1.legendOf s.me
  let b ← play (s1.tire mine) s.me e [] { fromEnd := some 2 }
  let c ← play (s1.tire mine) s.me e [] { fromEnd := some 2, obj := fun o => o == l }
  return b.tired l == some false && c.tired l == some true

-- Hall of Legends (SFD-210): when its player conquers here, pay 1 Energy to ready their legend
#guard tsf fun s => do
  let (s1, bf) ← putBf s s.me "SFD-210"
  let l ← s1.legendOf s.me
  let other ← s1.legendOf s.you
  let t := (s1.tire l).tire other
  let a ← fire (t.rich s.me) [.scored s.me bf true]
  let b ← fire (t.rich s.me) [.scored s.me bf true] { yes := false }
  let c ← fire (t.fund s.me 0) [.scored s.me bf true]
  let d ← fire (t.rich s.me) [.scored s.me bf false]
  return a.tired l == some false && a.tired other == some true && (a.poolOf s.me).energy == 11 &&
    b.tired l == some true && c.tired l == some true && d.tired l == some true

-- Bard, Mercurial (SFD-079): when played, the player may exhaust their legend to move any number
-- of their units to an open battlefield
#guard tsf fun s => do
  let (s1, b) ← put s s.me "SFD-079" .hand
  let l ← s1.legendOf s.me
  let (s3, u) ← put s1 s.me "OGN-051" .base
  let a ← play s3 s.me b
  let n ← play s3 s.me b [] { yes := false }
  let t ← play (s3.tire l) s.me b
  return a.tired l == some true && (a.obj? u).any (·.loc == some s.bf0) &&
    (n.obj? u).any (·.loc.isNone) && n.tired l == some false && (t.obj? u).any (·.loc.isNone)

end RiftboundTest
