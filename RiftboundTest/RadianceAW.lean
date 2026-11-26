module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Chronobreak -/

namespace RiftboundTest

open Riftbound

-- The payment declares how many Units are targeted on the Chain. The game checks the count
-- and the player can declare zero.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let (s, card) ← put s p "RAD-140" .hand
  let (s, a) ← put s p "V0" .base
  let (s, b) ← put s p "V1" .base
  let (s, enemy) ← put s q "V2" .base
  let s := s.fund p 2 1 0 0 1
  let pay : RunePool.Payment := ⟨2, [.fury, .mind]⟩
  let two := SpellPick.withVariablePower .plain 2
  let zero := SpellPick.withVariablePower .plain 0
  let (casted, events) ← (step 100 s ⟨.player p, .playCard card pay [a, b] none none two⟩).toOption
  let done ← cast s p card ⟨2, []⟩ [] {} zero
  return casted.zone .chain != [] &&
    (events.contains (.chosenBySpell p a)) && (events.contains (.chosenBySpell p b)) &&
    !(castable s p card pay [a] none two) && !(castable s p card pay [a, enemy] none two) &&
    !(castable s p card pay [a, b]) && done.inPlay.contains a && done.inPlay.contains b &&
    done.countIn p .trash "RAD-140" == 1).getD false

-- The active player's card finalizes first. The other owner picks their own second Unit to
-- replay before their first, after all three original objects have been Banished.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, card) ← put s p "RAD-140" .hand
  let (s, mine) ← put s p "V0" .base
  let (s, first) ← putAt s q "V1" field
  let (s, second) ← putAt s q "V2" field
  let s := (s.modObj first (fun o => { o with controller := p })).modObj second
    (fun o => { o with controller := p })
  let s := s.fund p 2 3
  let pick := SpellPick.withVariablePower .plain 3
  let (started, _) ← (step 100 s ⟨.player p, .playCard card ⟨2, [.fury, .fury, .fury]⟩
    [mine, first, second] none none pick⟩).toOption
  let .chainPass player _ :: _ := started.pending | none
  let (continued, _) ← (step 100 started ⟨.player player, .pass⟩).toOption
  let .chainPass player _ :: _ := continued.pending | none
  let (ordering, _) ← (step 100 continued ⟨.player player, .pass⟩).toOption
  let .pickDo owner _ _ _ _ (.recordBanishReplay ..) _ :: _ := ordering.pending | none
  let chosen ← ordering.firstOf q .banishment "V2"
  let (plans, _) ← (step 100 ordering ⟨.player q, .choose chosen⟩).toOption
  let queuedCards := (plans.zone .chain).filterMap (fun id => (plans.cardDef? id).map (·.id.code))
  let resolved := settleChain { yes := false } 16 plans
  let ours ← resolved.firstOf p .base "V0"
  let returning := resolved.inPlay.filter (fun id => (resolved.obj? id).any (fun o =>
    o.loc == some field && o.controller == q))
  let theirSecond ← returning.find? (fun id => (resolved.cardDef? id).any (fun d => d.id.code == "V2"))
  let theirFirst ← returning.find? (fun id => (resolved.cardDef? id).any (fun d => d.id.code == "V1"))
  let relevant := (resolved.playLog.filter (fun play =>
    play.moment == .resolved && [ours, theirSecond, theirFirst].contains play.object)).map (·.object)
  return owner == q && ordering.countIn p .banishment "V0" == 1 &&
    ordering.countIn q .banishment "V1" == 1 && ordering.countIn q .banishment "V2" == 1 &&
    queuedCards.take 2 == ["V1", "V2"] && relevant.reverse == [ours, theirSecond, theirFirst]).getD false

end RiftboundTest
