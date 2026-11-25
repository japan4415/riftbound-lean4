module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance Spell costs paid with permanents -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Ki Burst exhausts the selected payer before anyone can respond. Only its target is chosen.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put (s.rich p) p "RAD-028" .hand
  let (s, payer) ← put s p "RAD-061" .base
  let (s, target) ← put s q "RAD-061" .base
  let action (pick : SpellPick) : Action := ⟨.player p, .playCard spell ⟨1, []⟩ [target] none none pick⟩
  let paid := action (.withExtraObject .plain payer)
  let (waiting, events) ← (step 100 s paid).toOption
  let item ← (waiting.zone .chain).head?
  let resolved := settleChain {} 12 waiting
  let self ← cast s p spell ⟨1, []⟩ [payer] {} (.withExtraObject .plain payer)
  return (legalActions s).contains paid && !(legalActions s).contains (action .plain) &&
    !(legalActions s).contains (action (.withExtraObject .plain target)) &&
    !(legalActions (s.tire payer)).contains paid && waiting.tired payer == some true &&
    (waiting.obj? item).any (fun o => o.paid && o.targets == [target]) &&
    events.contains (.chosenBySpell p target) && !(events.contains (.chosenBySpell p payer)) &&
    (resolved.obj? target).any (·.stunned) && (self.obj? payer).any (·.stunned)

-- Repeat chooses twice and pays the printed non-resource cost once for the single play.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put ((s.rich p).addTurnFx p .nextSpellRepeat) p "RAD-028" .hand
  let (s, payer) ← put s p "RAD-061" .base
  let (s, first) ← put s q "RAD-061" .base
  let (s, second) ← put s q "RAD-061" .base
  let executions : SpellPick := .withCosts (.thenRepeat .plain 1 .plain) false 1
  let action : Action := ⟨.player p, .playCard spell ⟨2, []⟩ [first, second]
    none none (.withExtraObject executions payer)⟩
  let (waiting, events) ← (step 100 s action).toOption
  let item ← (waiting.zone .chain).head?
  let resolved := settleChain {} 12 waiting
  return (legalActions s).contains action && (events.countP (· == .exhausted payer)) == 1 &&
    (waiting.obj? item).any (fun o => o.extraPaid == 1 && o.targets == [first, second]) &&
    (resolved.obj? first).any (·.stunned) && (resolved.obj? second).any (·.stunned)

-- Life from Stone has no target. Its Ready Unit is still required to cast it as a Reaction.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put (s.rich p) p "RAD-029" .hand
  let (s, payer) ← put s p "RAD-061" .base
  let (s, _) ← onChain s q "RAD-100"
  let s := { s with pending := [.chainPass p 0, .priority p] }
  let gone := s.zone (.player p .runeDeck)
  let done ← cast s p spell ⟨1, []⟩ [] {} (.withExtraObject .plain payer)
  let channeled ← (done.zone (.player p .base)).find? (fun id =>
    (done.obj? id).any (fun o => o.formerId.any gone.contains && o.runeDomain.isSome))
  return done.tired payer == some true && done.tired channeled == some true &&
    done.handN p == s.handN p && (done.zone (.player p .runeDeck)).length + 1 == gone.length &&
    (cast s p spell ⟨1, []⟩).isNone

-- An effect that ignores the base price still needs an available cost and queues that choice.
#guard radianceCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "RAD-029" .hand
  let env := Env.empty.bind pickVar (.obj spell)
  let offer (g : GameState) := playSpellStep g p g.bf0 env (.var pickVar) .nil effectAddPolicy
  let (unpaid, _, _) ← offer s
  let (s, payer) ← put s p "RAD-061" .base
  let (queued, _, _) ← offer s
  let item ← (queued.zone .chain).head?
  let plans := limitedSpellOptions queued p item .ignoreBase
  let plan ← plans.find? (fun plan => plan.pick.extraObject == some payer)
  let (committed, _) ← commitLimitedSpell queued p item plan [] effectAddPolicy
  return unpaid.countIn p .hand "RAD-029" == 1 && unpaid.zone .chain == [] &&
    plans.length == 1 && plan.cost == Cost.zero && committed.tired payer == some true &&
    (committed.obj? item).any (fun o => o.paid && o.targets.isEmpty)

-- Parallel Convergence cannot return its own target. A reduced play still pays the same cost.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, spell) ← put (s.rich p) p "RAD-051" .hand
  let (s, payer) ← putAt (s.control p field) p "RAD-061" field
  let (s, target) ← putAt s q "RAD-067" field
  let pick := SpellPick.withExtraObject .plain payer
  let action : Action := ⟨.player p, .playCard spell ⟨2, [.mind]⟩ [target] none none pick⟩
  let (waiting, _) ← (step 100 s action).toOption
  let resolved := settleChain {} 12 waiting
  let price : EffectPlayPrice := .reduceEnergy 1
  let (queued, item) ← queueLimitedSpell s p spell price .normal
  let plan ← (limitedSpellOptions queued p item price).find? (fun plan =>
    plan.targets == [target] && plan.pick == pick)
  let (paid, events) ← commitLimitedSpell queued p item plan [] effectAddPolicy
  return (legalActions s).contains action &&
    (cast s p spell ⟨2, [.mind]⟩ [payer] {} pick).isNone &&
    waiting.countIn p .hand "RAD-061" == 1 &&
    (resolved.obj? target).any (fun o => o.damage == 5) &&
    paid.countIn p .hand "RAD-061" == 1 &&
    (paid.obj? item).any (fun o => o.paid && o.targets == [target]) &&
    events.contains (.chosenBySpell p target) && !(events.contains (.chosenBySpell p payer))

end RiftboundTest
