module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Firelights' Hideout -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Only Conquer grants the option. Declining it still spends it on the first Unit played.
#guard radianceCase fun s => do
  let p := s.me
  let (s, hideout) ← putBf s p "RAD-162"
  let (s, first) ← put s p "RAD-011" .hand
  let (s, second) ← put s p "RAD-011" .hand
  let (s, gear) ← put s p "RAD-024" .hand
  let s := s.control p hideout
  let conquered ← fire s [.scored p hideout true]
  let held ← fire s [.scored p hideout false]
  let reset (g : GameState) := { g with pending := [.priority p] }
  let pay := ⟨5, [.fury]⟩
  let before := (reset conquered).rich p
  let readied ← cast before p first pay
  let ordinary ← cast before p first ⟨4, []⟩
  let afterGear ← play before p gear [hideout]
  let accelerated ← cast ((reset afterGear).rich p) p first pay
  let readyUnit ← readied.firstOf p .base "RAD-011"
  let ordinaryUnit ← ordinary.firstOf p .base "RAD-011"
  let afterGearUnit ← accelerated.firstOf p .base "RAD-011"
  return (cast ((reset held).rich p) p first pay).isNone &&
    (cast before p first ⟨5, [.calm]⟩).isNone &&
    (cast ((reset ordinary).rich p) p second pay).isNone &&
    readied.tired readyUnit == some false && ordinary.tired ordinaryUnit == some true &&
    accelerated.tired afterGearUnit == some false

-- Hidden ignores the base cost while still offering the granted additional cost of Accelerate.
#guard radianceCase fun s => do
  let p := s.me
  let (s, hideout) ← putBf s p "RAD-162"
  let (s, companion) ← put s p "RAD-095" .hidden
  let s := (s.control p hideout).modObj companion
    (fun o => { o with hiddenAt := some hideout, hiddenTurn := some (s.turn - 1) })
  let s ← fire s [.scored p hideout true]
  let ready := ({ s with pending := [.priority p] } : GameState).rich p
  let (queued, _) ← (step 100 ready ⟨.player p, .activate companion 2 ⟨0, [], none⟩ []⟩).toOption
  let paid := settleChain { fromEnd := some 0 } 16 queued
  let skipped := settleChain { fromEnd := some 1 } 16 queued
  let entered (g : GameState) := (g.unitsAtOf hideout p).find? (fun id =>
    (g.obj? id).any (·.fromHidden))
  let paidUnit ← entered paid
  let ordinaryUnit ← entered skipped
  return paid.tired paidUnit == some false && skipped.tired ordinaryUnit == some true &&
    (paid.poolOf p).energy + 1 == (skipped.poolOf p).energy

end RiftboundTest
