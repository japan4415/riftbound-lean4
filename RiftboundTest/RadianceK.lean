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

-- A teammate's ready Unit can be exhausted for either spell. Only Ki Burst has a target.
#guard radianceCase fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (RiftboundDriver.runUntilTurn 100 1 2000 (RiftboundDriver.Rng.ofSeed 1) initial).toOption
  let p := s.me
  let mate ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← s.players.find? (fun q => !config.mode.sameSide p q)
  let (s, ki) ← put (s.rich p) p "RAD-028" .hand
  let (s, life) ← put s p "RAD-029" .hand
  let (s, payer) ← put s mate "RAD-061" .base
  let (s, target) ← put s enemy "RAD-061" .base
  let action (spell : ObjId) (targets : List ObjId) (cost : ObjId) : Action :=
    ⟨.player p, .playCard spell ⟨1, []⟩ targets none none (.withExtraObject .plain cost)⟩
  let kiPlay := action ki [target] payer
  let lifePlay := action life [] payer
  let (kiPaid, kiEvents) ← (step 100 s kiPlay).toOption
  let (lifePaid, lifeEvents) ← (step 100 s lifePlay).toOption
  let finished := settleChain {} 20 kiPaid
  return (legalActions s).contains kiPlay && (legalActions s).contains lifePlay &&
    !(step 100 s (action life [] target)).isOk && !(step 100 (s.tire payer) lifePlay).isOk &&
    kiPaid.tired payer == some true && lifePaid.tired payer == some true &&
    kiEvents.contains (.chosenBySpell p target) && !(kiEvents.contains (.chosenBySpell p payer)) &&
    !lifeEvents.any (fun | .chosenBySpell .. | .chosenByAbility .. => true | _ => false) &&
    (finished.obj? target).any (·.stunned)

-- Ekko and Parallel Convergence return the chosen friendly Unit to its owner.
#guard radianceCase fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (RiftboundDriver.runUntilTurn 100 1 2000 (RiftboundDriver.Rng.ofSeed 1) initial).toOption
  let p := s.me
  let mate ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← s.players.find? (fun q => !config.mode.sameSide p q)
  let field := s.bf0
  let (s, spell) ← put (s.rich p) p "RAD-051" .hand
  let (s, ekko) ← put s p "RAD-061" .hand
  let (s, borrowed) ← put s enemy "RAD-011" .base
  let (s, target) ← putAt (s.control enemy field) enemy "RAD-067" field
  let s := (setController mate s borrowed).1
  let spellPay (cost : ObjId) : Action :=
    ⟨.player p, .playCard spell ⟨2, [.mind]⟩ [target] none none (.withExtraObject .plain cost)⟩
  let unitPay (cost : ObjId) : Action := ⟨.player p, .playCard ekko ⟨3, []⟩ [cost] none none .plain⟩
  let (casting, events) ← (step 100 s (spellPay borrowed)).toOption
  let (played, _) ← (step 100 s (unitPay borrowed)).toOption
  let finished := settleChain {} 20 casting
  let returned (state : GameState) :=
    state.countIn enemy .hand "RAD-011" == 1 && state.countIn mate .hand "RAD-011" == 0
  return (legalActions s).contains (spellPay borrowed) && (legalActions s).contains (unitPay borrowed) &&
    !(step 100 s (spellPay target)).isOk && !(step 100 s (unitPay target)).isOk &&
    returned casting && returned played && played.countIn p .base "RAD-061" == 1 &&
    events.contains (.chosenBySpell p target) && !(events.contains (.chosenBySpell p borrowed)) &&
    (finished.obj? target).any (fun unit => unit.damage == 5)

-- Starry-Eyed Songstress can share its three-Unit discount with the caster's teammate.
#guard radianceCase fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (RiftboundDriver.runUntilTurn 100 1 2000 (RiftboundDriver.Rng.ofSeed 1) initial).toOption
  let p := s.me
  let mate ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let enemy ← s.players.find? (fun q => !config.mode.sameSide p q)
  let (s, legend) ← put s p "RAD-151" .legendZone
  let (s, own) ← put s p "RAD-061" .base
  let (s, first) ← put s mate "RAD-061" .base
  let (s, second) ← put s mate "RAD-061" .base
  let (s, foe) ← put s enemy "RAD-061" .base
  let (s, spell) ← put (s.fund p 1) p "RAD-047" .hand
  let action ← (legalActions s).find? (fun a => match a.kind with
    | .playCard id pay _ _ _ pick => id == spell && pay == ⟨1, []⟩ &&
      (pick.spellExhausts.any (fun (source, units) => source == legend && units.length == 3 &&
        [own, first, second].all units.contains))
    | _ => false)
  let (paid, _) ← (step 100 s action).toOption
  return (paid.poolOf p).energy == 0 && [legend, own, first, second].all (fun id => paid.tired id == some true) &&
    paid.tired foe == some false

end RiftboundTest
