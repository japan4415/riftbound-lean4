module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance a Deploy Gear's linked Banishment -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Dockside Lock-Up targets a Unit at its Battlefield. On Hold, the Gear is killed
-- at finalization, and the same physical card is played by the holder without paying its cost.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, lock) ← put s p "RAD-136" .hand
  let (s, target) ← putAt (s.control p field) q "RAD-088" field
  let (s, _) ← putAt s p "RAD-088" field
  let (s, outside) ← put s q "RAD-088" .base
  let (s, unrelated) ← put s q "RAD-088" .banishment
  let physical ← (s.obj? target).bind (·.kind.phys?)
  let (placing, _) ← (step 100 (s.fund p 6 (order := 2))
    ⟨.player p, .playCard lock ⟨6, [.order, .order]⟩ [field]⟩).toOption
  let linkedChoices := legalFrameActions placing
  let banished := settleChain { pick := (· == [target]) } 20 placing
  let gear ← banished.inPlay.find? (fun id => (banished.cardDef? id).any (·.id == ⟨"RAD-136"⟩))
  let prisoner ← (banished.zone (.player q .banishment)).find? (fun id =>
    (banished.obj? id).any (fun o => o.kind.phys? == some physical && o.banishedWith == some gear))
  let (holding, _) ← (advance 100 (banished.withTriggers [.scored p field false]) []).toOption
  let pay ← (legalFrameActions holding).find? (fun a =>
    match a.kind with | .putTrigger _ _ (.pay [id] ..) => id == gear | _ => false)
  let (paid, _) ← (step 100 holding pay).toOption
  let released := settleChain {} 30 paid
  let unit ← released.inPlay.find? (fun id =>
    (released.obj? id).any (·.kind.phys? == some physical))
  return !(linkedChoices.any (fun a =>
      match a.kind with | .putTrigger _ ts _ => ts.contains outside | _ => false)) &&
    paid.countIn p .trash "RAD-136" == 1 && (paid.zone (.player q .banishment)).contains prisoner &&
    (released.zone (.player q .banishment)).contains unrelated && !(released.zone (.player q .banishment)).contains prisoner &&
    (released.obj? unit).any (fun o => o.owner == q && o.controller == p) &&
    (released.zone (.player p .base)).contains unit && (released.poolOf p).total == 0

end RiftboundTest
