module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Starry-Eyed Songstress -/

namespace RiftboundTest

open Riftbound

-- The Legend and three different ready friendly Units pay one joint additional cost.
-- Neither a repeated Unit nor an opposing Unit is a legal payer.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let (s, legend) ← put s p "RAD-151" .legendZone
  let (s, a) ← put s p "V0" .base
  let (s, b) ← put s p "V1" .base
  let (s, c) ← put s p "V2" .base
  let (s, foe) ← put s q "V0" .base
  let (s, card) ← put s p "RAD-047" .hand
  let s := s.fund p 3
  let choice (units : List ObjId) := SpellPick.withSpellExhausts .plain [(legend, units)]
  let select (units : List ObjId) : Action :=
    ⟨.player p, .playCard card ⟨1, []⟩ [] none none (choice units)⟩
  -- Cost choices use the Base zone order, with the newest Unit first.
  let act := select [c, b, a]
  let (paid, _) ← (step 100 s act).toOption
  let ordinary ← cast s p card ⟨3, []⟩
  let together := (s.actionTransitionEvents paid act).any (fun event =>
    match event with
    | .exhaustBatch (some who) ids false =>
      who == p && ids.length == 4 && [legend, a, b, c].all ids.contains
    | _ => false)
  return together && [legend, a, b, c].all (fun id => paid.tired id == some true) &&
    [legend, a, b, c].all (fun id => ordinary.tired id == some false) &&
    (paid.poolOf p).energy == 2 &&
    (step 100 s (select [a, a, b])).toOption.isNone &&
    (step 100 s (select [a, b, foe])).toOption.isNone).getD false

-- A limited play makes the same election as part of finalization, even after its base price is reduced.
#guard (lab.bind fun s => do
  let p := s.me
  let (s, legend) ← put s p "RAD-151" .legendZone
  let (s, a) ← put s p "V0" .base
  let (s, b) ← put s p "V1" .base
  let (s, c) ← put s p "V2" .base
  let (s, card) ← put s p "RAD-047" .banishment
  let s := s.fund p 0
  let price := EffectPlayPrice.reduceEnergy 1
  let (queued, pending) ← queueLimitedSpell s p card price .normal
  let plan ← (limitedSpellOptions queued p pending price).find? (fun plan =>
    plan.cost == Cost.zero && plan.pick.spellExhausts == [(legend, [c, b, a])])
  let (paid, _) ← commitLimitedSpell queued p pending plan [] effectAddPolicy
  return [legend, a, b, c].all (fun id => paid.tired id == some true) &&
    (paid.pendingSpell pending).isNone).getD false

end RiftboundTest
