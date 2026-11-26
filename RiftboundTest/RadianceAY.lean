module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Orianna, Mechanical Marvel -/

namespace RiftboundTest

open Riftbound

-- Paying the ordinary price leaves Orianna's discount available. Electing it pays
-- one less Energy and one less Power and uses only the chosen copy's allowance.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, first) ← putAt s p "RAD-068" field
  let (s, second) ← putAt s p "RAD-068" field
  let (s, opponent) ← putAt s q "RAD-068" field
  let (s, home) ← put s p "RAD-068" .base
  let (s, gear) ← put s p "RAD-062" .hand
  let (s, following) ← put s p "RAD-062" .hand
  let s := (s.control p field).fund p 9 0 0 0 1
  let reduced := SpellPick.withGearDiscounts .plain [first]
  let ordinary ← cast s p gear ⟨5, [.mind]⟩ [field]
  let spent ← cast s p gear ⟨4, []⟩ [field] {} reduced
  return ordinary.gearDiscountAt p first == (1, 1) &&
    spent.gearDiscountAt p first == (0, 0) &&
    spent.gearDiscountAt p second == (1, 1) &&
    ({ spent with turn := spent.turn + 1 } : GameState).gearDiscountAt p first == (1, 1) &&
    (spent.poolOf p).energy == 5 && (spent.poolOf p).mind == 1 &&
    !(playable spent p following ⟨4, []⟩ (some field) [field] reduced) &&
    playable spent p following ⟨4, []⟩ (some field) [field] (.withGearDiscounts .plain [second]) &&
    !(playable s p gear ⟨4, []⟩ (some field) [field] (.withGearDiscounts .plain [home])) &&
    !(playable s p gear ⟨4, []⟩ (some field) [field] (.withGearDiscounts .plain [opponent]))).getD false

-- Effect plays offer the same elected discount and consume it only on completion.
#guard (lab.bind fun s => do
  let p := s.me
  let field := s.bf0
  let (s, source) ← putAt s p "RAD-068" field
  let (s, gear) ← put s p "RAD-062" .banishment
  let s := (s.control p field).fund p 2
  let terms : EffectPlayTerms := { price := .reduceEnergy 2 }
  let choices := permanentPlayPlans s p gear terms
  let chosen ← choices.find? (fun plan => plan.gearDiscounts == [source] &&
    plan.battlefield == some field && plan.cost == ⟨2, []⟩)
  let (played, entered, _) ← applyReducedPermanent s p gear chosen
  return choices.all (fun choice => choice.gearDiscounts == [source]) &&
    played.gearDiscountAt p source == (0, 0) &&
    (played.obj? entered).any (fun object => object.loc == some field) &&
    (played.poolOf p).energy == 0).getD false

end RiftboundTest
