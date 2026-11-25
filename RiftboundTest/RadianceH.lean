module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance play and movement triggers -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Hunting Blind can pull an enemy in and grants Shield only to friendly Units at its Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, gear) ← put s p "RAD-044" .hand
  let (s, ally) ← putAt s p "RAD-011" field
  let (s, outside) ← put s p "RAD-011" .base
  let (s, enemy) ← put s q "RAD-060" .base
  let s := s.control p field
  let pulled ← play s p gear [field] { pick := (· == [enemy]) }
  let declined ← play s p gear [field] { yes := false }
  return (pulled.obj? enemy).any (·.loc == some field) && (declined.obj? enemy).any (·.loc.isNone) &&
    pulled.kwAmount ally .shield == 2 && pulled.kwAmount outside .shield == 0 &&
    pulled.kwAmount enemy .shield == 0

-- The Guidebot sets base Might to the Energy cost of the played card, preserving its buff.
#guard radianceCase fun s => do
  let p := s.me
  let (s, guidebot) ← put s p "RAD-057" .base
  let (s, card) ← put s p "RAD-085" .hand
  let s := s.buff guidebot
  let changed ← play s p card
  let declined ← play s p card [] { yes := false }
  let (expired, _) ← (advance 100 { changed with pending := [.expireTurn] } []).toOption
  return changed.mightNow guidebot == some 6 &&
    declined.mightNow guidebot == s.mightNow guidebot && expired.mightNow guidebot == s.mightNow guidebot

-- Raving Witness draws at the Mighty boundary and recycles a unit below it.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, witness) ← put (s.control p field) p "RAD-074" .base
  let (large, _) ← put s p "VEN-071" .mainDeck
  let (small, _) ← put s p "RAD-011" .mainDeck
  let go (g : GameState) := do
    let (queued, _) ← (step 100 g ⟨.player p, .standardMove witness (.battlefield field)⟩).toOption
    return settleChain {} 8 queued
  let drawn ← go large
  let recycled ← go small
  let last ← (recycled.zone (.player p .mainDeck)).getLast?
  return drawn.countIn p .hand "VEN-071" == 1 && recycled.handN p == small.handN p &&
    (recycled.cardDef? last).any (·.id == cid "RAD-011")

-- Skystrike Squadron gets its discount only when a friendly Gear returns to its owner's hand.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, card) ← put s p "RAD-075" .hand
  let (s, returning) ← put s p "SFD-117" .base
  let (s, theirGear) ← put s q "SFD-117" .base
  let (s, unit) ← put s p "RAD-011" .base
  let cheap := s.fund p 3
  let ordinary ← cast (s.fund p 5) p card ⟨5, []⟩
  let discounted ← cast cheap p card ⟨3, []⟩ [returning]
  let squadron ← discounted.firstOf p .base "RAD-075"
  return (cast cheap p card ⟨3, []⟩).isNone &&
    (cast cheap p card ⟨3, []⟩ [theirGear]).isNone && (cast cheap p card ⟨3, []⟩ [unit]).isNone &&
    ordinary.inPlay.contains returning && discounted.countIn p .hand "SFD-117" == 1 &&
    discounted.deflectOf squadron == 1

-- The Tusker adds all instances of Shield and may pick a Unit at another Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field ← s.battlefields[0]?
  let distant ← s.battlefields[1]?
  let (s, tusker) ← put (s.control p field) p "RAD-078" .base
  let (s, other) ← putAt s q "RAD-060" distant
  let (s, home) ← put s q "RAD-060" .base
  let s := (addTempKw ⟨.shield, .amount 2⟩ .turn s tusker).1
  let (waiting, _) ← (step 100 s ⟨.player p, .standardMove tusker (.battlefield field)⟩).toOption
  let hit := settleChain { pick := (· == [other]) } 8 waiting
  let declined := settleChain { yes := false } 8 waiting
  return waiting.trigPicks.contains other && !waiting.trigPicks.contains home &&
    (hit.obj? other).any (·.damage == 5) && (declined.obj? other).any (·.damage == 0)

end RiftboundTest
