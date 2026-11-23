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

end RiftboundTest
