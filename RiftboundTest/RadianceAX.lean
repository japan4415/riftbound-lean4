module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Lady of Clockwork -/

namespace RiftboundTest

open Riftbound

private meta def chooseAnimation (s : GameState) (p : PlayerId) (gear : ObjId) : Option GameState := do
  let pending := insertTriggers (s.detect [.phaseStarted p .main]) [.priority p]
  let (choosing, _) ← (advance 100 { s with pending } []).toOption
  let action := Action.mk (.player p) (.putTrigger 0 [gear] (.pay []))
  (step 100 choosing action).toOption.map Prod.fst

-- The Legend's choice and payment are finalized before the selected Gear becomes a Unit.
-- Animating Equipment detaches it in the recipient's Battlefield, without a Move action.
#guard (lab.bind fun s => do
  let p := s.me
  let (s, _) ← put s p "RAD-145" .legendZone
  let (s, target) ← putAt s p "V0" s.bf0
  let (s, blade) ← put s p "RAD-150" .base
  let s := (attachTo target (s.fund p 2) blade).1
  let chain ← chooseAnimation s p blade
  let resolved := settleChain {} 16 chain
  let attempted := attachTo target resolved blade
  return !(chain.isUnit blade) && (chain.obj? blade).any (·.attached == some target) &&
    (chain.poolOf p).energy == 1 && resolved.isUnit blade && resolved.hasType blade .gear &&
    resolved.mightOf blade == some 3 && (resolved.unitsAt s.bf0).contains blade &&
    (resolved.obj? blade).any (·.attached.isNone) && attempted.2.isEmpty).getD false

-- Choosing the next Gear immediately ends the previous animation. Other Equipment attached
-- to the old animation stays on the old Gear, including through Cleanup.
#guard (lab.bind fun s => do
  let p := s.me
  let (s, _) ← put s p "RAD-145" .legendZone
  let (s, first) ← putAt s p "RAD-024" s.bf0
  let (s, second) ← putAt s p "RAD-146" s.bf0
  let (s, blade) ← put s p "RAD-150" .base
  let s := (s.control p s.bf0).fund p 2
  let chain ← chooseAnimation s p first
  let previous := settleChain {} 16 chain
  let previous := (attachTo first previous blade).1
  let choosing ← chooseAnimation previous p second
  let resolved := settleChain {} 16 choosing
  return previous.isUnit first && !choosing.isUnit first && !choosing.isUnit second &&
    resolved.isUnit second && resolved.mightOf second == some 5 && !resolved.isUnit first &&
    resolved.mightOf first == none && (resolved.obj? blade).any (·.attached == some first)).getD false

end RiftboundTest
