module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # The alternative Equip costs of Blade of the Exile -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- The card's play cost uses one Power of its Domain. Equip can instead use one Power
-- of any Domain or exhaust a friendly Unit independently of the Equip target.
#guard radianceCase fun s => do
  let p := s.me
  let (s, blade) ← put s p "RAD-150" .base
  let (s, payer) ← put s p "RAD-011" .base
  let (s, target) ← put s p "RAD-011" .base
  let (s, enemy) ← put s s.you "RAD-011" .base
  let s := s.fund p 0 (fury := 1)
  let d ← s.cardDef? blade
  let resources := ActionKind.activate blade 0 ⟨0, [.fury]⟩ [target]
  let exhaust (id : ObjId) := ActionKind.activate blade 1 ⟨0, []⟩ [target] [] none none (some id)
  let (resourceChain, _) ← (step 100 s ⟨.player p, resources⟩).toOption
  let (exhaustChain, _) ← (step 100 s ⟨.player p, exhaust payer⟩).toOption
  let triedEnemy := step 100 s ⟨.player p, exhaust enemy⟩
  let tired := s.modObj payer (fun obj => { obj with exhausted := true })
  let triedTired := step 100 tired ⟨.player p, exhaust payer⟩
  let byResources := settleChain {} 15 resourceChain
  let byExhaust := settleChain {} 15 exhaustChain
  return d.cost == some ⟨3, [.own]⟩ && d.supertypes.contains .signature &&
    triedEnemy.toOption.isNone && triedTired.toOption.isNone &&
    (byResources.poolOf p).total == 0 && (byExhaust.poolOf p).fury == 1 &&
    (exhaustChain.obj? payer).any (·.exhausted) && (byExhaust.obj? target).any (fun obj => !obj.exhausted) &&
    !(byResources.obj? payer).any (·.exhausted) &&
    (byResources.obj? blade).any (·.attached == some target) &&
    (byExhaust.obj? blade).any (·.attached == some target) && byExhaust.hasKw target .ganking

-- Weaponmaster discounts the resource alternative to zero and still offers the Exhaust alternative.
#guard radianceCase fun s => do
  let p := s.me
  let (s, blade) ← put s p "RAD-150" .base
  let (s, payer) ← put s p "RAD-011" .base
  let (s, chef) ← put s p "SFD-092" .hand
  let (queued, _) ← (step 100 (s.fund p 5) ⟨.player p, .playCard chef ⟨5, []⟩ []⟩).toOption
  let byResources := settleChain {} 20 queued
  let byExhaust := settleChain { fromEnd := some 0 } 20 queued
  let chef' ← (byExhaust.zone (.player p .base)).find? (fun id =>
    (byExhaust.cardDef? id).any (fun d => d.id.code == "SFD-092"))
  return (byResources.obj? blade).any (·.attached == some chef') &&
    (byExhaust.obj? blade).any (·.attached == some chef') &&
    !(byResources.obj? payer).any (·.exhausted) && (byExhaust.obj? payer).any (·.exhausted) &&
    byExhaust.hasKw chef' .ganking && (byResources.poolOf p).total == 0 && (byExhaust.poolOf p).total == 0

end RiftboundTest
