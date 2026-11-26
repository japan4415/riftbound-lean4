module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance triggered plays from the Trash -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- The ability is optional at finalization. With no Energy left, the alternate Order cost
-- buys the original Unit, and another player's copy does not trigger.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, wyvern) ← put s p "RAD-092" .hand
  let (s, restorationist) ← put s p "RAD-120" .trash
  let (s, opponentCopy) ← put s q "RAD-120" .trash
  let act (state : GameState) := step 100 state ⟨.player p, .playCard wyvern ⟨7, []⟩ []⟩
  let (offered, _) ← (act (s.fund p 7 (order := 1))).toOption
  let (unfunded, _) ← (act (s.fund p 7 (body := 1))).toOption
  let declined := settleChain { yes := false } 30 offered
  let played := settleChain {} 30 offered
  let noPower := settleChain {} 30 unfunded
  let physical ← (s.obj? restorationist).bind (·.kind.phys?)
  let arrived ← played.inPlay.find? (fun id => (played.obj? id).any (·.kind.phys? == some physical))
  return (legalFrameActions offered).any (fun a =>
        match a.kind with | .putTrigger _ _ .skip => true | _ => false) &&
    (played.locate arrived == some (.player p .base)) && played.countIn p .trash "RAD-120" == 0 &&
    (played.zone (.player q .trash)).contains opponentCopy && (played.poolOf p).order == 0 &&
    (declined.zone (.player p .trash)).contains restorationist &&
    (noPower.zone (.player p .trash)).contains restorationist

-- A hand cast goes to the Trash. A later Spell has to finish resolving before it enables
-- Forbidden Technique. The play from the Trash pays Energy and Fury, and leaves for Banishment.
#guard radianceCase fun s => do
  let p := s.me
  let (s, tech) ← put s p "RAD-010" .hand
  let (s, unit) ← put s p "RAD-088" .base
  let (s, spell) ← put s p "RAD-135" .hand
  let exhausted (g : GameState) := g.modObj unit (fun o => { o with exhausted := true })
  let fromHand ← cast (exhausted (s.fund p 2)) p tech ⟨2, []⟩ [unit]
  let trash := Zone.player p .trash
  let original ← (fromHand.zone trash).find? (fun id =>
    (fromHand.cardDef? id).any (·.id == ⟨"RAD-010"⟩))
  let rich := exhausted (fromHand.fund p 9 (fury := 2) (order := 2))
  let (onStack, _) ← (step 100 rich
    ⟨.player p, .playCard spell ⟨8, [.order, .order]⟩ []⟩).toOption
  let expensive ← (onStack.zone .chain).head?
  let countered := counterObj onStack expensive
  let rec waitForReplay (g : GameState) : Nat → Option (GameState × ObjId)
    | 0 => none
    | n + 1 => do
      let isReplay (item : ObjId) :=
        (g.cardDef? item).any (·.id == ⟨"RAD-010"⟩) && (g.pendingSpell item).isNone
      match g.pending, (g.zone .chain).head? with
      | .chainPass .. :: _, some item =>
        if isReplay item then some (g, item) else waitForReplay (settleChain {} 1 g) n
      | _, _ => waitForReplay (settleChain {} 1 g) n
  let (replay, item) ← waitForReplay onStack 35
  let counteredReplay := counterObj replay item
  let result := settleChain {} 45 onStack
  let declined := settleChain { yes := false } 45 onStack
  return (fromHand.obj? unit).any (!·.exhausted) &&
    (onStack.zone trash).contains original && !(onStack.pending.any (fun | .triggerOrder .. => true | _ => false)) &&
    (countered.1.detect countered.2).isEmpty &&
    counteredReplay.1.countIn p .banishment "RAD-010" == 1 &&
    (counteredReplay.1.obj? unit).any (·.exhausted) &&
    result.countIn p .banishment "RAD-010" == 1 && result.countIn p .trash "RAD-010" == 0 &&
    (result.poolOf p).fury == 0 && (result.poolOf p).energy == 0 &&
    (result.obj? unit).any (!·.exhausted) && (declined.zone trash).contains original

end RiftboundTest
