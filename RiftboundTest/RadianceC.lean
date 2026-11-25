module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance card scenarios for costs, characteristics and linked instructions -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Improvised Projectile takes damage from a friendly Gear and selects a Unit at a Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, spell) ← put s p "RAD-056" .hand
  let (s, gear) ← put s p "RAD-039" .base
  let (s, enemyGear) ← put s q "RAD-039" .base
  let (s, target) ← putAt s q "RAD-060" field
  let (s, distant) ← put s q "RAD-060" .base
  let s := (s.control q field).fund p 3 (mind := 1)
  let paid := ⟨3, [.mind]⟩
  let done ← cast s p spell paid [gear, target]
  return (done.obj? target).any (·.damage == 4) && done.inPlay.contains gear &&
    (cast s p spell paid [enemyGear, target]).isNone &&
    (cast s p spell paid [gear, distant]).isNone

-- The erratum permits Elnuk Herd to choose itself. Only the facedown play Recycles it.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, card) ← put s p "RAD-081" .hand
  let (s, hidden) ← put s p "RAD-081" .hidden
  let (s, nearby) ← putAt s p "RAD-011" field
  let s := (s.control p field).modObj hidden
    (fun o => { o with hiddenAt := some field, hiddenTurn := some (s.turn - 1) })
  let waiting ← castStop s p card
  let unit ← waiting.firstOf p .base "RAD-081"
  let ordinary := settleChain { pick := (· == [unit]) } 10 waiting
  let flipped ← activate s p hidden 2 [] ⟨0, []⟩ { pick := (· == [nearby]) }
  return waiting.trigPicks.contains unit && ordinary.mightNow unit == some 8 &&
    flipped.mightNow nearby == some 7 &&
    flipped.countIn p .mainDeck "RAD-081" == s.countIn p .mainDeck "RAD-081" + 1 &&
    !(flipped.unitsAtOf field p).any (fun id => (flipped.cardDef? id).any (·.id == cid "RAD-081"))

-- Negotiator locks an opponent as its player target before either side draws.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, card) ← put s p "RAD-099" .hand
  let waiting ← castStop s p card
  let choose (target : PlayerId) : Action := ⟨.player p, .putTrigger 0 [] (.pay [] none (some target))⟩
  let (queued, _) ← (step 100 waiting (choose q)).toOption
  let done := settleChain {} 8 queued
  return !(legalFrameActions waiting).contains (choose p) &&
    done.handN p == s.handN p && done.handN q == s.handN q + 1

-- Party Crasher's Energy discount counts only its player's exhausted Units.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, card) ← put s p "RAD-122" .hand
  let (s, a) ← put s p "RAD-011" .base
  let (s, b) ← putAt s p "RAD-011" s.bf0
  let (s, ready) ← put s p "RAD-011" .base
  let (s, gear) ← put s p "SFD-117" .base
  let (s, enemy) ← put s q "RAD-011" .base
  let s := ((((s.control p s.bf0).tire a).tire b).tire gear).tire enemy
  let funded := s.fund p 7 (order := 1)
  let done ← cast funded p card ⟨7, [.order]⟩
  let unit ← done.firstOf p .base "RAD-122"
  return (s.energyCost? p card) == some 7 && done.hasKw unit .tank &&
    (s.tire ready).energyCost? p card == some 6 &&
    (cast funded p card ⟨6, [.order]⟩).isNone

-- Devourer pays less only if its proposed sacrifice is friendly.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, card) ← put s p "RAD-125" .hand
  let (s, fodder) ← put s p "RAD-011" .base
  let (s, enemy) ← put s q "RAD-011" .base
  let cheap := s.fund p 5 (order := 1)
  let ordinary ← cast (s.fund p 7 (order := 1)) p card ⟨7, [.order]⟩
  let sacrificed ← cast cheap p card ⟨5, [.order]⟩ [fodder]
  let unit ← sacrificed.firstOf p .base "RAD-125"
  return (cast cheap p card ⟨5, [.order]⟩).isNone &&
    (cast cheap p card ⟨5, [.order]⟩ [enemy]).isNone &&
    ordinary.inPlay.contains fodder && sacrificed.countIn p .trash "RAD-011" == 1 &&
    sacrificed.deflectOf unit == 1

-- Realm of Death changes both Mights before calculating their simultaneous damage.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "RAD-144" .hand
  let (s, own) ← put s p "RAD-060" .base
  let (s, enemy) ← put s q "RAD-060" .base
  let funded := s.fund p 2 (fury := 1) (calm := 1) (order := 1)
  let first ← cast funded p spell ⟨2, [.fury]⟩ [enemy, own]
  let second ← cast funded p spell ⟨2, [.order]⟩ [enemy, own]
  return [first, second].all (fun t =>
    (t.obj? own).any (·.damage == 6) && t.mightNow own == some 10 &&
      t.countIn q .trash "RAD-060" == 1) &&
    (cast funded p spell ⟨2, [.calm]⟩ [enemy, own]).isNone

-- Ntofo Strikes deals damage equal to all the Shield on the friendly target after granting two.
#guard radianceCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "RAD-148" .hand
  let (s, ally) ← put s p "RAD-031" .base
  let (s, enemy) ← put s s.you "RAD-060" .base
  let funded := s.fund p 2 (fury := 1) (calm := 1) (body := 1)
  let first ← cast funded p spell ⟨2, [.calm]⟩ [ally, enemy]
  let second ← cast funded p spell ⟨2, [.body]⟩ [ally, enemy]
  return [first, second].all (fun t => t.kwAmount ally .shield == 5 && (t.obj? enemy).any (·.damage == 5)) &&
    (cast funded p spell ⟨2, [.fury]⟩ [ally, enemy]).isNone

-- Packed Amphitheater affects both players' Champion Units at the location.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s p "RAD-164"
  let (s, own) ← putAt s p "RAD-086" field
  let (s, enemy) ← putAt s q "RAD-110" field
  let (s, civilian) ← putAt s p "RAD-011" field
  let (s, distant) ← put s p "RAD-086" .base
  return [s, s.control p field, s.control q field].all (fun t =>
    t.mightNow own == some 5 && t.mightNow enemy == some 4 &&
      t.mightNow civilian == some 4 && t.mightNow distant == some 4)

end RiftboundTest
