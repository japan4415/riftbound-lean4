module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance Exhaust costs and attack movement -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Bloom can use the Might it granted on play to pay its draw cost.
#guard radianceCase fun s => do
  let p := s.me
  let (s, bloom) ← put s p "RAD-035" .hand
  let (s, grown) ← put s p "RAD-011" .base
  let (s, small) ← put s p "RAD-011" .base
  let entered ← play s p bloom [] { pick := (· == [grown]) }
  let gear ← entered.firstOf p .base "RAD-035"
  let act (cost : Option ObjId) := Action.mk (.player p)
    (.activate gear 1 ⟨0, []⟩ [] [] none none cost)
  let (paid, events) ← (step 100 entered (act (some grown))).toOption
  let drawn := settleChain {} 12 paid
  return (step 100 entered (act none)).toOption.isNone &&
    (step 100 entered (act (some small))).toOption.isNone &&
    (step 100 (entered.tire grown) (act (some grown))).toOption.isNone &&
    (legalFrameActions entered).contains (act (some grown)) &&
    paid.tired gear == some true && paid.tired grown == some true &&
    !events.contains (.chosenByAbility p grown) && drawn.handN p == entered.handN p + 1

-- Riven distinguishes the payment from the target, even when both are the same Unit.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, riven) ← put s p "RAD-114" .base
  let (s, ally) ← put s p "RAD-011" .base
  let (s, foe) ← put s q "RAD-011" .base
  let s := s.tire foe
  let act (paying target : ObjId) := Action.mk (.player p)
    (.activate riven 1 ⟨0, []⟩ [target] [] none none (some paying))
  let (paid, events) ← (step 100 s (act ally foe)).toOption
  let resolved := settleChain {} 16 paid
  let (selfPaid, _) ← (step 100 s (act riven riven)).toOption
  let selfReady := settleChain {} 12 selfPaid
  return (step 100 s (act foe ally)).toOption.isNone &&
    (legalFrameActions s).contains (act ally foe) &&
    paid.tired ally == some true && events.contains (.chosenByAbility p foe) &&
    !events.contains (.chosenByAbility p ally) &&
    resolved.tired foe == some false && resolved.mightEff riven == 6 &&
    selfPaid.tired riven == some true && selfReady.tired riven == some false &&
    selfReady.mightEff riven == 5 && (step 100 selfReady (act ally foe)).toOption.isNone

-- Jarvan offers the move on attack. The original Battlefield is still used if he is recalled.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, heir) ← putAt s p "RAD-133" field
  let (s, ally) ← put s p "RAD-011" .base
  let (s, enemy) ← putAt s q "RAD-011" field
  let triggers := s.detect [.combatStarted field p]
  let (waiting, _) ← (advance 100 { s with pending := .triggers triggers :: s.pending } []).toOption
  let (paid, _) ← (step 100 waiting ⟨.player p, .putTrigger 0 [ally] (.pay [])⟩).toOption
  let (declined, _) ← (step 100 waiting ⟨.player p, .putTrigger 0 [] .skip⟩).toOption
  let resolved := settleChain {} 12 (recallFx true paid heir).1
  return (s.detect [.combatStarted field q]).isEmpty &&
    (step 100 waiting ⟨.player p, .putTrigger 0 [enemy] (.pay [])⟩).toOption.isNone &&
    (declined.obj? ally).any (·.loc.isNone) &&
    (resolved.obj? heir).any (·.loc.isNone) && (resolved.obj? ally).any (·.loc == some field)

end RiftboundTest
