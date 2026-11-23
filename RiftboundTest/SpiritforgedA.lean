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
  return s1.energyCost? s.me c == some 5 && s4.energyCost? s.me c == some 4 &&
    s5.energyCost? s.me c == some 3

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
  let b ← play (s1.keepHand s.me d 3) s.me d
  return (a.firstOf s.me .base "SFD-027").bind a.tired == some false &&
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
  return r.dmg a == some 0 && (r.obj? e).any (·.loc.isNone) && (r.obj? j).any (·.loc == some s.bf0)

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

end RiftboundTest
