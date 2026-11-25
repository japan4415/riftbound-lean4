module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Vendetta scenarios

These checks exercise the added cards through the game interpreter and the Chain.
-/

namespace RiftboundTest

open Riftbound

/-- Run a Vendetta scenario in the card lab. -/
meta def vendettaCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Butcher pays two Power and Exhausts immediately. Its Energy pays for a
-- Unit or its activation, and stays separate from other payments (CR 166, 430, 445).
#guard vendettaCase fun s => do
  let p := s.me
  let (s, legend) ← put s p "VEN-141" .legendZone
  let (s, unit) ← put s p "VEN-074" .hand
  let (s, mage) ← put s p "VEN-047" .base
  let (s, spell) ← put s p "VEN-066" .hand
  let (s, gear) ← put s p "SFD-117" .hand
  let (s, henge) ← put s p "SFD-117" .base
  let (s, unforgiven) ← put s p "OGN-259" .legendZone
  let s := s.fund p 0 (fury := 1) (calm := 1) (body := 1) (mind := 1)
  let good : Action := ⟨.player p, .manaAbility legend 0 ⟨0, [.fury, .calm]⟩⟩
  let one : Action := ⟨.player p, .manaAbility legend 0 ⟨0, [.fury]⟩⟩
  let unavailable : Action := ⟨.player p, .manaAbility legend 0 ⟨0, [.chaos, .order]⟩⟩
  let (funded, events) ← (step 100 s good).toOption
  let unitAct : Action := ⟨.player p, .playCard unit ⟨2, []⟩ []⟩
  let empowerment : Action := ⟨.player p, .activate mage 0 ⟨2, []⟩ []⟩
  let rejects : List Action := [⟨.player p, .playCard spell ⟨2, [.mind]⟩ [mage]⟩,
    ⟨.player p, .playCard gear ⟨2, [.body]⟩ []⟩,
    ⟨.player p, .activate unforgiven 0 ⟨2, []⟩ [mage]⟩,
    ⟨.player p, .manaAbility henge 0 ⟨1, []⟩⟩,
    ⟨.player p, .manaAbility legend 0 ⟨0, [.body, .mind]⟩⟩]
  let (unitPlayed, _) ← (step 100 funded unitAct).toOption
  let (activating, _) ← (step 100 funded empowerment).toOption
  let (endTurn, _) ← microStep0 { funded with pending := [.expireTurn] }
  let (startMain, _) ← microStep0 { funded with pending := [.phase .main] }
  let empowered := settleChain {} 12 activating
  let pool := funded.poolOf p
  return (legalActions s).contains good &&
    [one, unavailable].all (fun a => !(legalActions s).contains a && ((step 100 s a).toOption).isNone) &&
    funded.tired legend == some true && funded.zone .chain == s.zone .chain &&
    funded.pending == s.pending && events.contains (.activated p legend 0 (some 0)) &&
    pool.energy == 0 && pool.unitEnergy == 2 && pool.fury == 0 && pool.calm == 0 &&
    pool.body == 1 && pool.mind == 1 &&
    rejects.all (fun a => !(legalActions funded).contains a && ((step 100 funded a).toOption).isNone) &&
    unitPlayed.countIn p .base "VEN-074" == 1 && (unitPlayed.poolOf p).unitEnergy == 0 &&
    (activating.poolOf p).unitEnergy == 0 && (empowered.obj? mage).any (·.empowerCount == 1) &&
    (endTurn.poolOf p).unitEnergy == 0 && (startMain.poolOf p).unitEnergy == 0 &&
    (payByRunes funded p mage ⟨1, []⟩).isNone

-- Unit-only Energy pays the Unit played during an effect's resolution.
#guard vendettaCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, _) ← putAt s p "VEN-074" field
  let (s, legend) ← put s p "VEN-141" .legendZone
  let (s, help) ← put s p "SFD-111" .hand
  let (s, drake) ← put s p "OGN-131" .hand
  let s := (s.control p field).fund p 3 (fury := 2) (body := 1)
  let (funded, _) ← (step 100 s ⟨.player p, .manaAbility legend 0 ⟨0, [.fury, .fury]⟩⟩).toOption
  let final ← cast funded p help ⟨2, [.body]⟩ [] { obj := (· == drake) }
  return (final.unitsAtOf field p).any (fun id => (final.cardDef? id).any (·.id.code == "OGN-131")) &&
    (final.poolOf p).energy == 1 && (final.poolOf p).unitEnergy == 0

-- Swift Scout's Energy payment to Hide a Unit is a discretionary action.
#guard vendettaCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, _) ← putAt s p "VEN-074" field
  let (s, _) ← put s p "OGN-263" .legendZone
  let (s, legend) ← put s p "VEN-141" .legendZone
  let (s, disciple) ← put s p "VEN-117" .hand
  let s := (s.control p field).fund p 0 (calm := 2)
  let (funded, _) ← (step 100 s ⟨.player p, .manaAbility legend 0 ⟨0, [.calm, .calm]⟩⟩).toOption
  let hide : Action := ⟨.player p, .activate disciple 3 ⟨1, []⟩ [field]⟩
  let parts := funded.setPool p ((funded.poolOf p).addEnergy 1)
  let (castHide, _) ← (step 100 parts hide).toOption
  let hiddenState := settleChain {} 10 castHide
  return !(legalActions funded).contains hide && ((step 100 funded hide).toOption).isNone &&
    (hiddenState.countIn p .hidden "VEN-117" == 1) && (hiddenState.poolOf p).energy == 0 &&
    (hiddenState.poolOf p).unitEnergy == 2

-- Reaction Add remains immediate when a Chain is open in the Ending Step.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, legend) ← put s q "VEN-141" .legendZone
  let (s, spell) ← put s p "VEN-066" .hand
  let (s, unit) ← put s p "VEN-074" .base
  let s := (s.fund p 2 (mind := 1)).fund q 0 (fury := 2)
  let (casting, _) ← (step 100 s ⟨.player p, .playCard spell ⟨2, [.mind]⟩ [unit]⟩).toOption
  let (passed, _) ← (step 100 casting ⟨.player p, .pass⟩).toOption
  let ending := { passed with phase := .ending }
  let action : Action := ⟨.player q, .manaAbility legend 0 ⟨0, [.fury, .fury]⟩⟩
  let (paid, _) ← (step 100 ending action).toOption
  return (legalActions ending).contains action && paid.phase == .ending &&
    paid.pending == ending.pending && paid.zone .chain == ending.zone .chain &&
    paid.tired legend == some true && (paid.poolOf q).unitEnergy == 2

-- Any player may pay for Dragon Roost, even when the opponent controls it (CR 355.17).
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s q "VEN-157"
  let (s, dragon) ← put s p "OGN-131" .hand
  let (s, other) ← put s p "VEN-014" .hand
  let s := (s.control q field).fund p 5 1 0 0 1
  let pay : RunePool.Payment := ⟨5, [.fury, .mind]⟩
  let elect (card : ObjId) (pay : RunePool.Payment) (ts : List ObjId) : Action :=
    ⟨.player p, .playCard card pay ts none none (.payForBattlefield [field])⟩
  let legal := elect dragon pay [field]
  let rejected := [elect other pay [field], elect dragon ⟨5, [.fury]⟩ [field],
    elect dragon pay [], ⟨.player p, .playCard dragon ⟨5, []⟩ [field]⟩]
  let (played, events) ← (step 100 s legal).toOption
  let unit ← (played.unitsAtOf field p).find? (fun id => (played.cardDef? id).any (·.id == cid "OGN-131"))
  return (legalActions s).contains legal && rejected.all (fun a =>
      !(legalActions s).contains a && ((step 100 s a).toOption).isNone) &&
    (played.poolOf p).energy == 0 && (played.poolOf p).fury == 0 &&
    (played.poolOf p).mind == 0 && played.tired unit == some true &&
    events.contains (.played p unit) && !(events.any (fun
      | .standardMoved id _ => id == unit
      | _ => false))

-- Electing the location fee is independent of Accelerate, even when discounts remove Power.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, field) ← putBf s p "VEN-157"
  let (s, dragon) ← put s p "VEN-016" .hand
  let s := ((s.control p field).fund p 9).addTurnFx p (.nextCardCostMinus 0 3)
  let ordinary : Action := ⟨.player p, .playCard dragon ⟨8, []⟩ [field]⟩
  let fee : Action := ⟨.player p, .playCard dragon ⟨8, []⟩ [field] none none (.payForBattlefield [field])⟩
  let ready : Action := ⟨.player p, .playCard dragon ⟨9, []⟩ [field] none none (.payForBattlefield [field] [0])⟩
  let (normal, _) ← (step 100 s fee).toOption
  let (accelerated, _) ← (step 100 s ready).toOption
  let a ← (normal.unitsAtOf field p).find? (fun id => (normal.cardDef? id).any (·.id == cid "VEN-016"))
  let b ← (accelerated.unitsAtOf field p).find? (fun id => (accelerated.cardDef? id).any (·.id == cid "VEN-016"))
  return [ordinary, fee, ready].all ((legalActions s).contains ·) &&
    normal.tired a == some true && accelerated.tired b == some false &&
    (normal.obj? a).any (fun o => o.spellPick == .payForBattlefield [field] && !o.paid) &&
    (accelerated.obj? b).any (fun o => o.spellPick == .payForBattlefield [field] [0] && o.paid)

-- A paid destination remains subject to a Unit's own restriction and opponents' restrictions.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let other := s.bf0
  let (s, field) ← putBf s q "VEN-157"
  let (s, grimwyrm) ← put s p "SFD-015" .hand
  let s := s.fund p 4 2
  let elsewhere := s.modObj other (fun o => { o with scored := [p] })
  let permitted := elsewhere.modObj field (fun o => { o with scored := [p] })
  let (warden, _) ← putAt permitted q "OGN-070" other
  let action : Action :=
    ⟨.player p, .playCard grimwyrm ⟨4, [.fury, .fury]⟩ [field] none none (.payForBattlefield [field])⟩
  return !(legalActions s).contains action && !(legalActions elsewhere).contains action &&
    (legalActions permitted).contains action && !(legalActions warden).contains action

-- Two independent fees impose conflicting locations. The player can choose either (CR 355.17.a).
#guard vendettaCase fun s => do
  let p := s.me
  let other := s.bf0
  let (s, left) ← putBf s p "VEN-157"
  let (s, right) ← putBf s s.you "VEN-157"
  let (s, dragon) ← put s p "OGN-131" .hand
  let s := s.fund p 5 4
  let sources := s.battlefields.filter (fun id => id == left || id == right)
  let pay : RunePool.Payment := ⟨5, List.replicate 4 .fury⟩
  let choose (bf : ObjId) (sources : List ObjId) : Action :=
    ⟨.player p, .playCard dragon pay [bf] none none (.payForBattlefield sources)⟩
  let (first, _) ← (step 100 s (choose left sources)).toOption
  let (second, _) ← (step 100 s (choose right sources)).toOption
  return (first.unitsAtOf left p).any (fun id => (first.cardDef? id).any (·.id == cid "OGN-131")) &&
    (second.unitsAtOf right p).any (fun id => (second.cardDef? id).any (·.id == cid "OGN-131")) &&
    !(legalActions s).contains (choose other sources) &&
    !(legalActions s).contains (choose left [left, left])

-- Cataclysmic Duel asks each player for their own non-targeted choice in turn
-- order, skips a player with no Units, and kills only after the choices finish.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let mode := { s.config.mode with players := 3 }
  let s := { s with config := { s.config with mode := mode }, turnOrder := [q, third, p] }
  let (s, spell) ← put s p "VEN-090" .hand
  let (s, mine) ← put s p "VEN-014" .base
  let (s, mineOther) ← put s p "VEN-014" .base
  let (s, theirs) ← put s q "VEN-014" .base
  let (s, theirsOther) ← put s q "VEN-014" .base
  let s := s.rich p
  let (casting, _) ← (step 100 s ⟨.player p, .playCard spell ⟨8, [.body, .body, .body]⟩ []⟩).toOption
  let pass (t : GameState) : Option GameState := do
    let .chainPass actor _ :: _ := t.pending | none
    (step 100 t ⟨.player actor, .pass⟩).toOption.map Prod.fst
  let first ← pass casting >>= pass >>= pass
  let (second, firstEvents) ← (step 100 first ⟨.player p, .choose mine⟩).toOption
  let (resolved, secondEvents) ← (step 100 second ⟨.player q, .choose theirs⟩).toOption
  return !(legalActions first).contains ⟨.player q, .choose theirs⟩ &&
    !(legalActions second).contains ⟨.player q, .choose mineOther⟩ &&
    (second.obj? mineOther).isSome && (second.obj? theirsOther).isSome &&
    (resolved.obj? mine).isSome && (resolved.obj? theirs).isSome &&
    resolved.countIn p .trash "VEN-014" == 1 && resolved.countIn q .trash "VEN-014" == 1 &&
    !((firstEvents ++ secondEvents).any (fun
      | .chosenByAbility _ _ | .chosenBySpell _ _ => true
      | _ => false))

-- Jagged Cutlass applies once Equip resolves. The opponent can target the
-- equipped Unit with Fight or Flight but cannot move it. Friendly moves and Recall still work.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, unit) ← putAt s q "VEN-014" field
  let (s, gear) ← put s q "VEN-073" .base
  let (s, enemyMove) ← put s p "OGN-168" .hand
  let (s, ownMove) ← put s q "OGN-168" .hand
  let (s, other) ← put s p "VEN-014" .base
  let own := { s.control q field with active := some q, pending := [.priority q] }
  let equipped ← activate own q gear 0 [unit] ⟨0, [.body]⟩
  let opposing := { equipped with active := some p, pending := [.priority p] }
  let blocked ← play opposing p enemyMove [unit]
  let allowed ← play equipped q ownMove [unit]
  let plain ← play (detachObj opposing gear).1 p enemyMove [unit]
  let (standard, _) ← (step 100 equipped ⟨.player q, .standardMove unit .base⟩).toOption
  let (swapped, _) ← applyPrim opposing p enemyMove { slots := [.obj unit, .obj other] }
    (.swapPlaces (.slot 0) (.slot 1))
  let recalled := (recallFx false equipped unit).1
  return (equipped.obj? gear).any (·.attached == some unit) && equipped.mightNow unit == some 4 &&
    (blocked.obj? unit).any (·.loc == some field) &&
    (swapped.obj? unit).any (·.loc == some field) && (swapped.obj? other).any (·.loc.isNone) &&
    allowed.locate unit == some (.player q .base) && plain.locate unit == some (.player q .base) &&
    standard.locate unit == some (.player q .base) && recalled.locate unit == some (.player q .base)

-- Decree of Focus can answer an enemy Fury spell choosing a friendly Unit.
-- It rechecks the relation if that spell is countered while the Decree is on the Chain.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, unit) ← putAt s q "VEN-014" s.bf0
  let (s, spare) ← put s q "VEN-014" .base
  let (s, ray) ← put s p "OGN-009" .hand
  let (s, decree) ← put s q "VEN-040" .hand
  let s := (s.control q s.bf0 |>.rich p).rich q
  let (casting, _) ← (step 100 s ⟨.player p, .playCard ray ⟨1, [.fury]⟩ [unit]⟩).toOption
  let item ← (casting.zone .chain).head?
  let (priority, _) ← (step 100 casting ⟨.player p, .pass⟩).toOption
  let action (target : ObjId) : Action := ⟨.player q, .playCard decree ⟨1, []⟩ [target]⟩
  let (reply, _) ← (step 100 priority (action unit)).toOption
  let boosted := settleChain {} 12 reply
  let mistargeted := settleChain {} 12 (counterObj reply item).1
  return !(legalActions priority).contains (action spare) &&
    boosted.mightNow unit == some 6 && (boosted.obj? unit).any (·.damage == 3) &&
    mistargeted.mightNow unit == some 2

-- Combat with a Fury defender qualifies before either player casts a spell.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, unit) ← putAt s p "VEN-033" s.bf0
  let (s, enemy) ← putAt s q "VEN-014" s.bf0
  let (s, decree) ← put s p "VEN-040" .hand
  let rich := s.rich p
  let showdown := { rich with pending := [.showdown s.bf0 p 0] }
  let action : Action := ⟨.player p, .playCard decree ⟨1, []⟩ [unit]⟩
  let (casting, _) ← (step 100 showdown action).toOption
  let boosted := settleChain {} 8 casting
  return !(legalActions rich).contains action &&
    !(legalActions (moveHome showdown enemy).1).contains action &&
    boosted.mightNow unit == (s.mightNow unit).map (· + 4)

-- Decree of Discord can choose zero or more Order units. A Reaction raises one unit
-- from 1 Might to 4, so the caster must keep it alone or keep the two 2-Might units.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, decree) ← put s p "VEN-107" .hand
  let (s, answer) ← put s q "OGN-207" .hand
  let (s, first) ← put s q "VEN-117" .base
  let (s, second) ← put s q "VEN-128" .base
  let (s, third) ← put s q "VEN-128" .base
  let (s, large) ← put s q "VEN-118" .base
  let (s, wrongDomain) ← put s q "VEN-014" .base
  let s := (s.rich p).rich q
  let cast (ts : List ObjId) : Action := ⟨.player p, .playCard decree ⟨1, [.chaos]⟩ ts⟩
  let pass (t : GameState) : Option GameState := do
    let .chainPass actor _ :: _ := t.pending | none
    (step 100 t ⟨.player actor, .pass⟩).toOption.map Prod.fst
  let (casting, _) ← (step 100 s (cast [first, second, third])).toOption
  let priority ← pass casting
  let (reacting, _) ←
    (step 100 priority ⟨.player q, .playCard answer ⟨3, []⟩ [first]⟩).toOption
  let stronger ← pass reacting >>= pass
  let deciding ← pass stronger >>= pass
  let (one, oneEvents) ← (step 100 deciding ⟨.player p, .choose first⟩).toOption
  let (pair, _) ← (step 100 deciding ⟨.player p, .choose second⟩).toOption
  let returned (t : GameState) (old : ObjId) :=
    (t.zone (.player q .hand)).any (fun id => (t.obj? id).any (·.formerId == some old))
  return (legalActions s).contains (cast []) && !(legalActions s).contains (cast [first, first]) &&
    !(legalActions s).contains (cast [large]) && !(legalActions s).contains (cast [wrongDomain]) &&
    stronger.mightNow first == some 4 && returned one first &&
    !returned one second && !returned one third &&
    !returned pair first && returned pair second && returned pair third &&
    !(oneEvents.any (fun
      | .chosenBySpell _ _ | .chosenByAbility _ _ => true
      | _ => false))

/-- Pass only Chain priority, stopping at the next question. -/
meta def passToChoice : Nat → GameState → Option GameState
  | 0, _ => none
  | fuel + 1, s =>
    match s.pending with
    | .chainPass p _ :: _ =>
      (step 100 s ⟨.player p, .pass⟩).toOption.bind (passToChoice fuel ∘ Prod.fst)
    | _ => some s

/-- Choose the first matching finalization, including one on a later page of the decision. -/
meta def choosePermanentPlan (p : PlayerId) (accept : ReducedPermanentPlay → Bool) :
    Nat → GameState → Option (GameState × List Event)
  | 0, _ => none
  | fuel + 1, s =>
    let answer (yes : Bool) := (step 100 s ⟨.player p, .decide yes⟩).toOption
    match s.pending with
    | .eitherDo player _ _ (.finishReducedPermanent _ _ plan) other _ :: _ =>
      if p != player then none
      else if accept plan then answer true
      else match other with
        | .finishReducedPermanent _ _ alternative => if accept alternative then answer false else none
        | .eitherOf _ => (answer false).bind (choosePermanentPlan p accept fuel ∘ Prod.fst)
        | _ => none
    | _ => none

-- Temporal Breach: its owner can decline the fee, pay and return to Base,
-- or pay and go to the Roost (Vendetta FAQ, CR 355.17.a).
#guard vendettaCase fun s => do
  let p := s.me
  let (s, roost) ← putBf s s.you "VEN-157"
  let (s, breach) ← put s p "VEN-066" .hand
  let (s, elder) ← put s p "UNL-118" .base
  let s := s.fund p 2 (mind := 1) (fury := 2)
  let (casting, _) ← (step 100 s ⟨.player p, .playCard breach ⟨2, [.mind]⟩ [elder]⟩).toOption
  let waiting ← passToChoice 8 casting
  let accepts (dest : Option ObjId) (fees : List ObjId) (plan : ReducedPermanentPlay) :=
    plan.battlefield == dest && plan.battlefieldFees == fees
  let (plain, plainEvents) ← choosePermanentPlan p (accepts none []) 32 waiting
  let (same, sameEvents) ← choosePermanentPlan p (accepts none [roost]) 32 waiting
  let (there, thereEvents) ← choosePermanentPlan p (accepts (some roost) [roost]) 32 waiting
  let plainCard ← plain.firstOf p .base "UNL-118"
  let sameCard ← same.firstOf p .base "UNL-118"
  let roostCard ← (there.unitsAtOf roost p).find? (fun id => (there.cardDef? id).any (·.id.code == "UNL-118"))
  return waiting.countIn p .banishment "UNL-118" == 1 &&
    plainCard != elder && sameCard != elder && roostCard != elder &&
    (plain.poolOf p).fury == 2 && (same.poolOf p).total == 0 && (there.poolOf p).total == 0 &&
    plainEvents.contains (.played p plainCard) && sameEvents.contains (.played p sameCard) &&
    thereEvents.contains (.played p roostCard) &&
    !(thereEvents.any (fun | .standardMoved id _ => id == roostCard | _ => false))

-- Temporal Breach offers the fee and destination to the Unit's owner when cast by an opponent.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, roost) ← putBf s p "VEN-157"
  let (s, breach) ← put s p "VEN-066" .hand
  let (s, elder) ← put s q "UNL-118" .base
  let s := (s.fund p 2 (mind := 1)).fund q 0 (body := 2)
  let (casting, _) ← (step 100 s ⟨.player p, .playCard breach ⟨2, [.mind]⟩ [elder]⟩).toOption
  let waiting ← passToChoice 8 casting
  let .eitherDo player _ _ _ _ _ :: _ := waiting.pending | none
  let (there, events) ← choosePermanentPlan q (fun plan =>
    plan.battlefield == some roost && plan.battlefieldFees == [roost]) 32 waiting
  let dragon ← (there.unitsAtOf roost q).find? (fun id => (there.cardDef? id).any (·.id.code == "UNL-118"))
  return player == q && ((step 100 waiting ⟨.player p, .decide true⟩).toOption).isNone &&
    (there.poolOf q).total == 0 && events.contains (.played q dragon)

-- Here to Help has no Battlefield target. After choosing the Dragon, paying for
-- a controlled Roost meets both requirements and makes that location mandatory.
#guard vendettaCase fun s => do
  let p := s.me
  let site := s.bf0
  let (s, roost) ← putBf s s.you "VEN-157"
  let (s, _) ← putAt s p "VEN-014" site
  let (s, _) ← putAt s p "VEN-014" roost
  let (s, spell) ← put s p "SFD-111" .hand
  let (s, drake) ← put s p "OGN-131" .hand
  let (s, grimwyrm) ← put s p "SFD-015" .hand
  let s := ((s.control p site).control p roost).fund p 4 (body := 3)
  let act (state : GameState) (kind : ActionKind) := (step 100 state ⟨.player p, kind⟩).toOption.map Prod.fst
  let casting ← act s (.playCard spell ⟨2, [.body]⟩ [])
  let incoming ← passToChoice 8 casting
  let taking ← act incoming (.decide true)
  let paying ← match taking.pending with
    | .pickDo .. :: _ => act taking (.choose drake)
    | _ => some taking
  let forSite (plan : ReducedPermanentPlay) := plan.battlefield == some site
  let (plain, _) ← choosePermanentPlan p (fun plan => forSite plan && plan.battlefieldFees.isEmpty) 32 paying
  let (there, _) ← choosePermanentPlan p (fun plan =>
    plan.battlefield == some roost && plan.battlefieldFees == [roost]) 32 paying
  return (plain.unitsAtOf site p).any (fun id => (plain.cardDef? id).any (·.id.code == "OGN-131")) &&
    (there.unitsAtOf roost p).any (fun id => (there.cardDef? id).any (·.id.code == "OGN-131")) &&
    !(legalActions taking).contains ⟨.player p, .choose grimwyrm⟩ &&
    (plain.poolOf p).body == 2 && (there.poolOf p).total == 0 &&
    (choosePermanentPlan p (fun plan => forSite plan && plan.battlefieldFees == [roost]) 32 paying).isNone &&
    ((step 100 s ⟨.player p, .playCard spell ⟨2, [.body]⟩ [site]⟩).toOption).isNone

-- When Here to Help is played from Hidden, the Hidden Battlefield and another
-- controlled Roost compete. Either can be chosen after paying (CR 355.17.a, 811.1.d.5).
#guard vendettaCase fun s => do
  let p := s.me
  let site := s.bf0
  let (s, roost) ← putBf s s.you "VEN-157"
  let (s, _) ← putAt s p "VEN-014" site
  let (s, _) ← putAt s p "VEN-014" roost
  let (s, spell) ← put s p "SFD-111" .hidden
  let (s, drake) ← put s p "OGN-131" .hand
  let s := (((s.control p site).control p roost).fund p 2 (body := 2)).modObj spell (fun o =>
    { o with hiddenAt := some site, hiddenTurn := some (s.turn - 1) })
  let act (state : GameState) (kind : ActionKind) := (step 100 state ⟨.player p, kind⟩).toOption.map Prod.fst
  let cast ← act s (.activate spell 1 ⟨0, []⟩ [])
  let incoming ← passToChoice 8 cast
  let taking ← act incoming (.decide true)
  let paying ← match taking.pending with
    | .pickDo .. :: _ => act taking (.choose drake)
    | _ => some taking
  let choose (bf : ObjId) (fees : List ObjId) := choosePermanentPlan p
    (fun plan => plan.battlefield == some bf && plan.battlefieldFees == fees) 32 paying
  let (hidden, _) ← choose site [roost]
  let (there, _) ← choose roost [roost]
  return (hidden.unitsAtOf site p).any (fun id => (hidden.cardDef? id).any (·.id.code == "OGN-131")) &&
    (there.unitsAtOf roost p).any (fun id => (there.cardDef? id).any (·.id.code == "OGN-131")) &&
    (choose roost []).isNone && (hidden.poolOf p).total == 0 && (there.poolOf p).total == 0

-- Location restrictions use the player playing a Dragon from an opponent's zone.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, roost) ← putBf s q "VEN-157"
  let (s, grimwyrm) ← put s q "SFD-015" .trash
  let s := s.fund p 0 (fury := 2)
  let earned := s.modObj roost (fun o => { o with scored := [p] })
  let other := s.modObj roost (fun o => { o with scored := [q] })
  let terms : EffectPlayTerms := { price := .ignoreBase }
  let chosen ← (permanentPlayPlans earned p grimwyrm terms).find? (fun plan =>
    plan.battlefield == some roost && plan.battlefieldFees == [roost])
  let (done, unit, _) ← applyReducedPermanent earned p grimwyrm chosen
  return (permanentPlayPlans other p grimwyrm terms).isEmpty && (done.poolOf p).total == 0 &&
    (done.obj? unit).any (fun o => o.loc == some roost && o.controller == p && o.owner == q)

-- Mel draws on play and empowers for 3 Energy. Moonfall chooses the Unit
-- before responses and pays Deflect. Only that Unit loses the extra Might.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, melCard) ← put s p "VEN-069" .hand
  let (s, moonfall) ← put s p "UNL-198" .hand
  let deckSize := (s.zone (.player p .mainDeck)).length
  let entered ← play s p melCard
  let mel ← entered.firstOf p .base "VEN-069"
  let empowered ← activate entered p mel 2 [] ⟨3, []⟩
  let (s, _) ← putAt empowered p "VEN-070" field
  let (s, bystander) ← putAt s q "VEN-086" field
  let (s, target) ← put s q "VEN-064" .base
  let s := (empowerObj q (s.control p field |>.fund p 3 0 0 0 2) bystander).1
  let poor := s.fund p 3 0 0 0 1
  let action : Action := ⟨.player p, .playCard moonfall ⟨3, [.mind]⟩ [field, target]⟩
  let (waiting, _) ← (step 100 s action).toOption
  let item ← (waiting.zone .chain).head?
  let moved := settleChain {} 8 waiting
  let stayed := settleChain { yes := false } 8 waiting
  let noTarget ← cast s p moonfall ⟨3, [.mind]⟩ [field]
  return (entered.zone (.player p .mainDeck)).length + 1 == deckSize &&
    (empowered.obj? mel).any (·.empowerCount == 1) &&
    !(legalActions poor).contains action && (waiting.poolOf p).total == 0 &&
    (waiting.obj? item).any (·.targets == [field, target]) &&
    (moved.obj? target).any (·.loc == some field) && moved.mightNow target == some 5 &&
    moved.mightNow bystander == some 4 && stayed.locate target == some (.player q .base) &&
    stayed.mightNow target == some 8 && stayed.mightNow bystander == some 4 &&
    noTarget.mightNow bystander == some 4

-- Not So Fast can legally target either protected Chain item, but cannot
-- counter it. Stupefy still observes its minimum of 1 Might.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, mel) ← put s p "VEN-069" .base
  let (s, stupefy) ← put s p "OGN-095" .hand
  let (s, shieldbearer) ← put s p "OGN-051" .hand
  let (s, answer) ← put s q "SFD-045" .hand
  let (s, target) ← put s q "VEN-070" .base
  let (s, small) ← put s q "VEN-014" .base
  let s := (s.rich p).rich q
  let empowered := (empowerObj p s mel).1
  let reply (t : GameState) : Option GameState := do
    let item ← (t.zone .chain).head?
    let (priority, _) ← (step 100 t ⟨.player p, .pass⟩).toOption
    cast priority q answer ⟨2, [.calm]⟩ [item]
  let castStupefy (t : GameState) : Option GameState :=
    (step 100 t ⟨.player p, .playCard stupefy ⟨1, []⟩ [target]⟩).toOption.map Prod.fst
  let stronger ← castStupefy empowered >>= reply
  let countered ← castStupefy s >>= reply
  let floor ← cast empowered p stupefy ⟨1, []⟩ [small]
  let (trigger, _) ←
    (step 100 empowered ⟨.player p, .playCard shieldbearer ⟨3, []⟩ []⟩).toOption
  let putOnChain ← (legalActions trigger).find? (fun a => match a.kind with
    | .putTrigger _ ts _ => ts == [target]
    | _ => false)
  let (ability, _) ← (step 100 trigger putOnChain).toOption
  let stunned ← reply ability
  return stronger.mightNow target == some 2 && floor.mightNow small == some 1 &&
    countered.mightNow target == some 4 && (stunned.obj? target).any (·.stunned)

-- Gangplank replaces only his half of Switcheroo. He replaces targeted stuns
-- and returns as well, including when his own controller chooses him.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, gangplank) ← putAt s q "VEN-086" field
  let (s, switcheroo) ← put s p "SFD-145" .hand
  let (s, rebuke) ← put s p "OGN-172" .hand
  let (s, prison) ← put s q "OGN-050" .hand
  let s := (s.control q field |>.rich p).rich q
  let forPlayer (t : GameState) (actor : PlayerId) :=
    { t with active := some actor, pending := [.priority actor] }
  let empowered ← activate (forPlayer s q) q gangplank 1 [] ⟨0, [.body, .body]⟩
  let noStun ← play empowered q prison [gangplank]
  let (opposing, small) ← putAt (forPlayer empowered p) p "VEN-014" field
  let swapped ← play opposing p switcheroo [small, gangplank]
  let sameMight ← play (opposing.modObj small (fun o => { o with baseMightThisTurn := some 6 }))
    p switcheroo [small, gangplank]
  let stayed ← play opposing p rebuke [gangplank]
  let returned ← play (disempowerObj opposing gangplank).1 p rebuke [gangplank]
  return (empowered.obj? gangplank).any (·.empowerCount == 1) &&
    (noStun.obj? gangplank).any (! ·.stunned) && noStun.mightNow gangplank == some 9 &&
    swapped.mightNow gangplank == some 9 && swapped.mightNow small == some 6 &&
    sameMight.mightNow gangplank == some 6 &&
    (stayed.obj? gangplank).any (·.loc == some field) && stayed.mightNow gangplank == some 9 &&
    returned.countIn q .hand "VEN-086" == 1

-- Rampage makes both decisions available even when the total payments are equal.
-- The bonus follows the original decision, including if the Spell changes controllers.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, ally) ← put s p "VEN-014" .base
  let (s, enemy) ← put s q "VEN-014" .base
  let (s, card) ← put s p "VEN-083" .hand
  let s := s.rich p
  let cast (pay : RunePool.Payment) (paid : Bool) (repeats : Nat := 0) : Action :=
    ⟨.player p, .playCard card pay [ally, enemy] none none (.withCosts .plain paid repeats)⟩
  let s0 := ((s.fund p 1).addTurnFx p (.nextCardCostMinus 2 2)).addTurnFx q .preventEffectDamage
  let accept := cast ⟨1, []⟩ true
  let decline := cast ⟨1, []⟩ false
  let (accepted, _) ← (step 100 s0 accept).toOption
  let (declined, _) ← (step 100 s0 decline).toOption
  let paidItem ← (accepted.zone .chain).head?
  let declinedItem ← (declined.zone .chain).head?
  let paid ← passToChoice 8 accepted
  let unpaid ← passToChoice 8 declined
  let retargeted := accepted.modObj paidItem (fun o =>
    { o with controller := q, targets := [enemy, ally] })
  let taken ← passToChoice 8 retargeted
  let (repeating, _) ← (step 100 (s.addTurnFx p .nextSpellRepeat)
    (cast ⟨6, [.body]⟩ true 1)).toOption
  let rep ← (repeating.zone .chain).head?
  let defn ← s0.cardDef? card
  let effect ← defn.spellEffect
  let reducedIndex ← (reducedSpellChoices s0 p card defn effect 0).findIdx? (· ==
    ([ally, enemy], ⟨1, []⟩, .withCosts .plain true 0))
  let (reduced, _) := castPickedOne p 0 reducedIndex s0 card
  let reducedItem ← (reduced.zone .chain).head?
  return (legalFrameActions s).contains (cast ⟨3, [.body]⟩ true) &&
    (legalFrameActions s).contains (cast ⟨3, []⟩ false) &&
    !(legalFrameActions s).contains (cast ⟨3, []⟩ true) &&
    !(legalFrameActions s0).contains ⟨.player p, .playCard card ⟨1, []⟩ [ally, enemy]⟩ &&
    (accepted.obj? paidItem).any (fun o => o.paid && o.extraPaid == 0) &&
    (declined.obj? declinedItem).any (fun o => !o.paid && o.extraPaid == 0) &&
    (repeating.obj? rep).any (fun o => o.paid && o.extraPaid == 1) &&
    (reduced.obj? reducedItem).any (fun o => o.paid && o.extraPaid == 0) &&
    (paid.obj? ally).any (fun o => o.damage == 2) && paid.mightNow ally == some 4 &&
    (paid.obj? enemy).isNone && (unpaid.obj? ally).isNone && (unpaid.obj? enemy).isNone &&
    taken.mightNow enemy == some 4 && (taken.obj? ally).isNone

-- A Repeat reduced to zero is still a separate choice from casting the Spell once.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, target) ← putAt s p "VEN-064" s.bf0
  let (s, spell) ← put s p "OGN-009" .hand
  let s := ((s.fund p 0).addTurnFx p .nextSpellRepeat).addTurnFx p (.nextCardCostMinus 2 2)
  let cast (copies : Nat) : Action :=
    ⟨.player p, .playCard spell ⟨0, []⟩ [target] none none (.withCosts .plain false copies)⟩
  let (once, _) ← (step 100 s (cast 0)).toOption
  let (twice, _) ← (step 100 s (cast 1)).toOption
  let count (t : GameState) := (t.zone .chain).head?.bind (fun item =>
    (t.obj? item).map (·.extraPaid))
  return count once == some 0 && count twice == some 1 &&
    !(legalFrameActions s).contains ⟨.player p, .playCard spell ⟨0, []⟩ [target]⟩ &&
    !(legalFrameActions s).contains (cast 2)

-- Astral Heron waits for the first successful card resolution and must be at
-- a Battlefield when it happens. Its discount lasts through one finalized play.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let away ← s.battlefields.find? (· != bf)
  let (s, heron) ← putAt s p "VEN-044" bf
  let (s, enemy) ← putAt s q "VEN-064" away
  let (s, first) ← put s p "OGN-009" .hand
  let (s, second) ← put s p "OGN-009" .hand
  let (s, reaction) ← put s p "VEN-035" .hand
  let (s, unit) ← put s p "VEN-047" .hand
  let (s, free) ← put s p "VEN-014" .trash
  let d ← s.cardDef? unit
  let d := { d with cost := some ⟨5, [.domain .body, .domain .calm, .domain .fury]⟩ }
  let s := { s with cards := { s.cards with cards := d :: s.cards.cards } }
  let s := ((s.control p bf).control q away).rich p
  let cast (src : ObjId) (pay : RunePool.Payment) : Action :=
    ⟨.player p, .playCard src pay [enemy]⟩
  let playUnit (energy : Nat) (power : List Domain) : Action :=
    ⟨.player p, .playCard unit ⟨energy, power⟩ []⟩
  let (casting, _) ← (step 100 s (cast first ⟨1, [.fury]⟩)).toOption
  let firstItem ← (casting.zone .chain).head?
  let .chainPass a _ :: _ := casting.pending | none
  let (priority, _) ← (step 100 casting ⟨.player a, .pass⟩).toOption
  let .chainPass b _ :: _ := priority.pending | none
  let (triggered, events) ← (step 100 priority ⟨.player b, .pass⟩).toOption
  let triggerItem ← (triggered.zone .chain).head?
  let discounted ← passToChoice 8 triggered
  let (responded, _) ← (step 100 triggered
    ⟨.player p, .playCard reaction ⟨3, [.calm]⟩ [heron] none none (.mode 0)⟩).toOption
  let afterResponse ← passToChoice 8 responded
  let awayDuringResponse ← passToChoice 8 (moveHome casting heron).1
  let firstCountered ← passToChoice 8 (counterObj casting firstItem).1
  let (unitFirst, _) ← (step 100 firstCountered (playUnit 5 [.body, .calm, .fury])).toOption
  let unitAfterTrigger ← passToChoice 8 unitFirst
  let (played, _) ← (step 100 discounted (playUnit 3 [.body])).toOption
  let (nextOnChain, _) ← (step 100 (discounted.fund p 0) (cast second ⟨0, []⟩)).toOption
  let nextItem ← (nextOnChain.zone .chain).head?
  let nextCountered ← passToChoice 8 (counterObj nextOnChain nextItem).1
  let (freePlay, freeEvents) ← applyPrim discounted p heron { slots := [.obj free] } (.play (.slot 0))
  let (afterFree, _) ← (advance 100 (freePlay.withTriggers freeEvents) []).toOption
  let (expired, _) ← (advance 100 { discounted with pending := [.expireTurn] } []).toOption
  return (casting.zone .chain).length == 1 && casting.nextCardDiscount p == (0, 0) &&
    events.any (fun | .spellResolved who _ => who == p | _ => false) &&
    (triggered.obj? triggerItem).any (fun o => o.kind == .chainAbility (cid "VEN-044") 0 heron) &&
    triggered.nextCardDiscount p == (0, 0) && discounted.nextCardDiscount p == (2, 2) &&
    responded.nextCardDiscount p == (0, 0) && afterResponse.nextCardDiscount p == (2, 2) &&
    awayDuringResponse.nextCardDiscount p == (0, 0) && firstCountered.nextCardDiscount p == (0, 0) &&
    unitAfterTrigger.nextCardDiscount p == (2, 2) &&
    ([.body, .calm, .fury] : List Domain).all (fun d =>
      (legalActions discounted).contains (playUnit 3 [d])) &&
    !(legalActions discounted).contains (playUnit 3 []) &&
    !(legalActions discounted).contains (playUnit 5 [.body, .calm, .fury]) &&
    played.nextCardDiscount p == (0, 0) && nextCountered.nextCardDiscount p == (0, 0) &&
    afterFree.nextCardDiscount p == (0, 0) && expired.nextCardDiscount p == (0, 0)

-- Flow and Hidden are card plays for the discount even though neither starts in the Hand.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, ally) ← putAt s p "VEN-014" bf
  let (s, enemy) ← putAt s q "VEN-064" bf
  let (s, flow) ← put s p "VEN-105" .trash
  let (s, hidden) ← put s p "SFD-145" .hidden
  let s := ((s.control p bf).fund p 2).modObj hidden (fun o =>
    { o with hiddenAt := some bf, hiddenTurn := some (s.turn - 1) })
  let discounted := s.addTurnFx p (.nextCardCostMinus 2 2)
  let fromTrash : Action := ⟨.player p, .playCard flow ⟨2, []⟩ [ally] none none (.destination none)⟩
  let reveal : Action := ⟨.player p, .activate hidden 1 ⟨0, []⟩ [ally, enemy]⟩
  let (flowing, _) ← (step 100 discounted fromTrash).toOption
  let (revealing, _) ← (step 100 discounted reveal).toOption
  let revealed ← passToChoice 8 revealing
  return !(legalActions s).contains fromTrash && !(legalActions s).contains reveal &&
    (flowing.poolOf p).total == 0 && (revealing.poolOf p).total == 2 &&
    flowing.nextCardDiscount p == (0, 0) && revealing.nextCardDiscount p == (0, 0) &&
    revealed.finalizedCount p == s.finalizedCount p + 1

-- Blade Twirler can target any player, including its controller. Resolution
-- respects the recorded target, and a countered trigger still used the first move.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let mode := { s.config.mode with players := 3 }
  let s := { s with config := { s.config with mode := mode }, turnOrder := [p, q, third] }
  let bf := s.bf0
  let (s, blade) ← put s p "VEN-002" .base
  let (s, top) ← put s third "VEN-014" .mainDeck
  let s := s.control p bf
  let move : Action := ⟨.player p, .standardMove blade (.battlefield bf)⟩
  let pick (r : PlayerId) : Action := ⟨.player p, .putTrigger 0 [] (.pay [] none (some r))⟩
  let (choosing, _) ← (step 100 s move).toOption
  let (waiting, _) ← (step 100 choosing (pick third)).toOption
  let item ← (waiting.zone .chain).head?
  let resolved ← passToChoice 6 waiting
  let canceled ← passToChoice 6 (counterObj waiting item).1
  let (movedAgain, events) := moveHome canceled blade
  let next := { movedAgain with turn := movedAgain.turn + 1 }
  let (next, firstMove) := sendToBf bf next blade
  let (nextChoice, _) ← (advance 100 (next.withTriggers firstMove) []).toOption
  let deck (t : GameState) (r : PlayerId) := t.zone (.player r .mainDeck)
  let burned := (resolved.zone (.player third .trash)).any (fun id =>
    (resolved.obj? id).any (·.formerId == some top))
  return legalFrameActions choosing == s.players.map pick &&
    ((step 100 choosing (pick ⟨3⟩)).toOption).isNone &&
    ((step 100 choosing ⟨.player p, .putTrigger 0 []⟩).toOption).isNone &&
    (waiting.obj? item).any (fun o => o.targetPlayer == some third && o.targets.isEmpty) &&
    deck waiting third == [top] && (deck resolved third).isEmpty && burned &&
    deck resolved p == deck s p && deck resolved q == deck s q &&
    deck canceled third == [top] && (movedAgain.detect events).isEmpty &&
    legalFrameActions nextChoice == s.players.map pick

-- Kharox targets either opponent before Burn. The optional free play can use
-- a Unit burned by this effect, and keeps the original owner.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let mode := { s.config.mode with players := 3 }
  let s := { s with config := { s.config with mode := mode }, turnOrder := [p, q, third] }
  let (s, kharox) ← put s p "VEN-114" .base
  let (s, recruit) ← put s third "VEN-064" .mainDeck
  let (s, otherUnit) ← put s third "VEN-014" .mainDeck
  let (s, spell) ← put s third "OGN-095" .mainDeck
  let (s, distractor) ← put s q "VEN-070" .trash
  let s := s.fund p 6 0 0 0 0 2
  let (empowering, _) ←
    (step 100 s ⟨.player p, .activate kharox 1 ⟨6, [.chaos, .chaos]⟩ []⟩).toOption
  let choosing ← passToChoice 10 empowering
  let pick (target : PlayerId) : Action := ⟨.player p, .putTrigger 0 [] (.pay [] none (some target))⟩
  let (waiting, _) ← (step 100 choosing (pick third)).toOption
  let item ← (waiting.zone .chain).head?
  let deciding ← passToChoice 10 waiting
  let (selecting, _) ← (step 100 deciding ⟨.player p, .decide true⟩).toOption
  let chosen ← selecting.firstOf third .trash "VEN-064"
  let backup ← selecting.firstOf third .trash "VEN-014"
  let burnedSpell ← selecting.firstOf third .trash "OGN-095"
  let (finished, _) ← (step 100 selecting ⟨.player p, .choose chosen⟩).toOption
  let played ← finished.firstOf p .base "VEN-064"
  let (refused, _) ← (step 100 deciding ⟨.player p, .decide false⟩).toOption
  let canceled ← passToChoice 10 (counterObj waiting item).1
  let deck (t : GameState) := t.zone (.player third .mainDeck)
  return (legalActions choosing).contains (pick q) && !(legalActions choosing).contains (pick p) &&
    (waiting.obj? item).any (·.targetPlayer == some third) &&
    (deck waiting).length == 3 && deck canceled == deck waiting &&
    (deck selecting).isEmpty && selecting.zone (.player q .trash) == [distractor] &&
    (selecting.obj? chosen).any (·.formerId == some recruit) &&
    (selecting.obj? backup).any (·.formerId == some otherUnit) &&
    (selecting.obj? burnedSpell).any (·.formerId == some spell) &&
    (legalActions selecting).contains ⟨.player p, .choose backup⟩ &&
    !(legalActions selecting).contains ⟨.player p, .choose distractor⟩ &&
    !(legalActions selecting).contains ⟨.player p, .choose burnedSpell⟩ &&
    (finished.obj? played).any (fun o =>
      o.owner == third && o.controller == p && o.exhausted && o.formerId == some chosen) &&
    (finished.poolOf p).total == 0 && refused.countIn third .trash "VEN-064" == 1

-- Decree of Strength targets a player before replies. Its caster picks
-- from the Mind cards that the opponent actually reveals during resolution.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let mode := { s.config.mode with players := 3 }
  let s := { s with config := { s.config with mode := mode }, turnOrder := [p, q, third] }
  let (s, decree) ← put s p "VEN-085" .hand
  let (s, wrongHand) ← put s q "VEN-069" .hand
  let (s, mel) ← put s third "VEN-069" .hand
  let (s, nonMind) ← put s third "VEN-014" .hand
  let (s, draw) ← put s third "OGN-095" .hand
  let (s, _) ← put s third "VEN-064" .mainDeck
  let (s, unit) ← put s third "VEN-070" .base
  let s := (s.rich p).rich third
  let playAgainst (r : PlayerId) : Action :=
    ⟨.player p, .playCard decree ⟨1, []⟩ [] none none (.withPlayer .plain r)⟩
  let (waiting, _) ← (step 100 s (playAgainst third)).toOption
  let item ← (waiting.zone .chain).head?
  let pass (t : GameState) : Option (GameState × List Event) := do
    let .chainPass actor _ :: _ := t.pending | none
    (step 100 t ⟨.player actor, .pass⟩).toOption
  let rec settle (n : Nat) (t : GameState) (events : List Event) :
      Option (GameState × List Event) := do
    match n, t.pending with
    | n + 1, .chainPass .. :: _ =>
      let (next, es) ← pass t
      settle n next (events ++ es)
    | _, _ => some (t, events)
  let priority ← pass waiting >>= (fun (t, _) => (pass t).map Prod.fst)
  let (reply, _) ← (step 100 priority ⟨.player third, .playCard draw ⟨1, []⟩ [unit]⟩).toOption
  let (choosing, revealed) ← settle 12 reply []
  let fromDraw ← choosing.firstOf third .hand "VEN-064"
  let answer (a : PlayerId) (id : ObjId) : Action := ⟨.player a, .choose id⟩
  let (resolved, es) ← (step 100 choosing (answer p fromDraw)).toOption
  let recycled ← (resolved.zone (.player third .mainDeck)).getLast?
  let (countered, canceled) ← settle 12 (counterObj waiting item).1 []
  let (stolen, stolenEvents) ← settle 12 (setController third waiting item).1 []
  let definition ← s.cardDef? decree
  let effect ← definition.spellEffect
  let reduced := reducedSpellChoices s p decree definition effect 1
  let castByEffect := (castPickedOne p 1 1 s decree).1
  let reducedItem ← (castByEffect.zone .chain).head?
  let paid := (legalActions s).filter (fun a => match a.kind with
    | .playCard card _ _ _ _ _ => card == decree
    | _ => false)
  return paid.length == 2 && paid.contains (playAgainst q) && !(paid.contains (playAgainst p)) &&
    !(paid.contains (playAgainst ⟨3⟩)) &&
    (waiting.obj? item).any (fun o => o.targetPlayer == some third && o.targets.isEmpty) &&
    revealed.contains (.handRevealed third (choosing.zone (.player third .hand))) &&
    (legalActions choosing).contains (answer p mel) &&
    !(legalActions choosing).contains (answer p nonMind) &&
    !(legalActions choosing).contains (answer p wrongHand) &&
    !(legalActions choosing).contains (answer third fromDraw) &&
    (resolved.obj? recycled).any (fun o => o.formerId == some fromDraw && o.owner == third) &&
    es.contains (.recycled third) && !(es.any (fun
      | .chosenBySpell .. | .chosenByAbility .. => true
      | _ => false)) &&
    canceled.isEmpty && countered.zone (.player third .hand) == waiting.zone (.player third .hand) &&
    !(stolenEvents.any (fun | .handRevealed .. => true | _ => false)) &&
    stolen.countIn p .trash "VEN-085" == 1 &&
    reduced.map (fun (_, cost, pick) => (cost.energy, pick.playerTarget)) ==
      [(0, some q), (0, some third)] &&
    (castByEffect.obj? reducedItem).any (·.targetPlayer == some third)

-- Jayce's controller fixes which keyword he gets before players can respond to the ability.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, jayce) ← put s p "VEN-088" .base
  let (ready, events) := readyEffect (s.tire jayce) jayce
  let (choosing, _) ← (advance 100 (ready.withTriggers events) []).toOption
  let pick (i : Nat) : Action := ⟨.player p, .putTrigger 0 [] (.pay [] (some i))⟩
  let grants : List KeywordInst :=
    [⟨.assault, .amount 2⟩, ⟨.deflect, .amount 2⟩, ⟨.ganking, .none⟩]
  let results ← grants.zipIdx.mapM fun (kw, i) => do
    let (waiting, _) ← (step 100 choosing (pick i)).toOption
    let .chainPass .. :: _ := waiting.pending | none
    let item ← (waiting.zone .chain).head?
    let ability ← waiting.obj? item
    let resolved ← passToChoice 5 waiting
    let canceled ← passToChoice 5 (counterObj waiting item).1
    return ability.spellPick == .mode i && ability.kind == .chainAbility (cid "VEN-088") 0 jayce &&
      (waiting.keywordsNow jayce).isEmpty && (canceled.keywordsNow jayce).isEmpty &&
      resolved.keywordsNow jayce == [kw] && (readyEffect resolved jayce).2.isEmpty
  return events == [.readied jayce] &&
    legalFrameActions choosing == (List.range 3).map pick && results.all id &&
    ((step 100 choosing ⟨.player p, .putTrigger 0 []⟩).toOption).isNone &&
    ((step 100 choosing (pick 3)).toOption).isNone

-- The Disciple burns the top card before anyone can respond. Countering the
-- ability keeps the Burn paid. An empty deck only allows declining.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let deck := Zone.player p .mainDeck
  let (s, disciple) ← put s p "VEN-095" .base
  let (s, top) ← put s p "VEN-014" .mainDeck
  let s := (s.control p bf).reorder deck (top :: (s.zone deck).erase top)
  let move : Action := ⟨.player p, .standardMove disciple (.battlefield bf)⟩
  let accept : Action := ⟨.player p, .putTrigger 0 []⟩
  let decline : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (choosing, _) ← (step 100 s move).toOption
  let (paid, events) ← (step 100 choosing accept).toOption
  let (declined, _) ← (step 100 choosing decline).toOption
  let .chainPass .. :: _ := paid.pending | none
  let item ← (paid.zone .chain).head?
  let granted ← passToChoice 5 paid
  let canceled ← passToChoice 5 (counterObj paid item).1
  let (expired, _) ← (advance 100 { granted with pending := [.expireTurn] } []).toOption
  let (empty, _) := applyEach (sendObj .trash) s (s.zone deck)
  let (noPayment, _) ← (step 100 empty move).toOption
  let (passed, _) ← (step 100 noPayment decline).toOption
  let burned := events.any (fun
    | .moved id _ (.player who .trash) => id == top && who == p
    | _ => false)
  return legalFrameActions choosing == [accept, decline] &&
    legalFrameActions noPayment == [decline] && passed.pointsOf q == empty.pointsOf q &&
    burned && (paid.zone deck).length + 1 == (s.zone deck).length &&
    canceled.zone deck == paid.zone deck && declined.zone deck == s.zone deck &&
    paid.mightNow disciple == some 2 && granted.mightNow disciple == some 3 &&
    canceled.mightNow disciple == some 2 && expired.mightNow disciple == some 2

-- Minah's controller chooses the mode even on another player's turn. When the
-- ability resolves, the turn player draws or discards first.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let s := { s with active := some q, turnOrder := [p, q], pending := [.priority q] }
  let (s, minah) ← put s p "VEN-111" .base
  let (s, mine) ← put s p "VEN-014" .hand
  let (s, theirs) ← put s q "VEN-014" .hand
  let (moved, events) := sendToBf bf s minah
  let entering ← moved.zone .battlefieldZone |>.find? (fun u =>
    (moved.cardDef? u).any (·.id == cid "VEN-111"))
  let (choosing, _) ← (advance 100 (moved.withTriggers events) []).toOption
  let pick (i : Nat) : Action := ⟨.player p, .putTrigger 0 [] (.pay [] (some i))⟩
  let (discarding, _) ← (step 100 choosing (pick 0)).toOption
  let first ← passToChoice 5 discarding
  let .discard firstActor 1 :: _ := first.pending | none
  let (second, _) ← (step 100 first ⟨.player q, .discardPick theirs⟩).toOption
  let .discard secondActor 1 :: _ := second.pending | none
  let (discarded, _) ← (step 100 second ⟨.player p, .discardPick mine⟩).toOption
  let (drawing, _) ← (step 100 choosing (pick 1)).toOption
  let .chainPass a _ :: _ := drawing.pending | none
  let (priority, _) ← (step 100 drawing ⟨.player a, .pass⟩).toOption
  let .chainPass b _ :: _ := priority.pending | none
  let (drawn, draws) ← (step 100 priority ⟨.player b, .pass⟩).toOption
  let (home, returned) := moveHome moved entering
  let hand (t : GameState) (r : PlayerId) := (t.zone (.player r .hand)).length
  return events == [.standardMoved entering (some bf)] && (home.detect returned).isEmpty &&
    legalFrameActions choosing == [pick 0, pick 1] && firstActor == q && secondActor == p &&
    hand discarded p + 1 == hand s p && hand discarded q + 1 == hand s q &&
    hand drawn p == hand s p + 1 && hand drawn q == hand s q + 1 &&
    draws.filter (fun | .drew _ => true | _ => false) == [.drew q, .drew p]

-- Tornado Warrior chooses an object here while its optional play trigger is
-- finalized. That choice is rechecked at resolution and survives the source
-- leaving once the delayed Disempower has been created.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, hidden) ← put s p "VEN-099" .hidden
  let (s, ordinary) ← put s p "VEN-099" .hand
  let (s, target) ← putAt s p "VEN-014" field
  let (s, elsewhere) ← put s q "VEN-014" .base
  let s := ((s.control p field).rich p).modObj hidden (fun o =>
    { o with hiddenAt := some field, hiddenTurn := some (s.turn - 1) })
  let reveal : Action := ⟨.player p, .activate hidden 3 ⟨0, []⟩ []⟩
  let choose (id : ObjId) : Action := ⟨.player p, .putTrigger 0 [id]⟩
  let decline : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (revealing, _) ← (step 100 s reveal).toOption
  let selecting ← passToChoice 10 revealing
  let inPlay ← (selecting.zone .battlefieldZone).find? (fun id =>
    (selecting.cardDef? id).any (·.id == cid "VEN-099"))
  let (waiting, _) ← (step 100 selecting (choose target)).toOption
  let (place, _) ← (step 100 selecting (choose field)).toOption
  let (refused, _) ← (step 100 selecting decline).toOption
  let (plain, _) ← (step 100 s ⟨.player p, .playCard ordinary ⟨3, []⟩ []⟩).toOption
  let granted ← passToChoice 10 waiting
  let empoweredField ← passToChoice 10 place
  let invalid ← passToChoice 10 (moveHome waiting target).1
  let already ← passToChoice 10 (empowerObj p waiting target).1
  let ended ← fire (sendObj .trash granted inPlay).1 [.phaseStarted p .ending]
  let alreadyEnded ← fire already [.phaseStarted p .ending]
  let count (t : GameState) (id : ObjId) := (t.obj? id).map (·.empowerCount)
  let marked (t : GameState) := t.turnFx.any (fun f => f.kind == .endTrigger "VEN-099" 1)
  return (legalFrameActions selecting).contains (choose inPlay) &&
    !(legalFrameActions selecting).contains (choose elsewhere) &&
    (legalFrameActions plain).all (fun a => match a.kind with | .putTrigger .. => false | _ => true) &&
    count waiting target == some 0 && count refused target == some 0 && !marked refused &&
    count granted target == some 1 && count empoweredField field == some 1 &&
    count invalid target == some 0 && !marked invalid &&
    count ended target == some 0 && count already target == some 1 && count alreadyEnded target == some 0

-- Dune Surfer ignores an enemy's Tank only for its controller at that Battlefield.
-- It neither removes Tank from the card nor changes the other side's assignment.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, surfer) ← putAt s p "VEN-004" field
  let (s, theirTank) ← putAt s q "VEN-118" field
  let (s, theirOther) ← putAt s q "VEN-014" field
  let (s, ourTank) ← putAt s p "VEN-118" field
  let (s, ourOther) ← putAt s p "VEN-014" field
  let choices (t : GameState) (side : PlayerId) :=
    legalFrameActions { t with pending := [.assign field p side [] []] }
  let pick (side : PlayerId) (u : ObjId) : Action := ⟨.player side, .assignPick u⟩
  return (choices s p).contains (pick p theirOther) &&
    (choices s p).contains (pick p theirTank) && s.hasKw theirTank .tank && s.hasKw ourTank .tank &&
    (choices s q).contains (pick q ourTank) && !(choices s q).contains (pick q ourOther) &&
    !(choices (moveHome s surfer).1 p).contains (pick p theirOther)

-- Ki Barrier spends only the amount of damage prevented, follows a Unit that
-- stays on the Board, accumulates with another Barrier, and expires at turn end.
#guard vendettaCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, first) ← put s p "VEN-126" .hand
  let (s, second) ← put s p "VEN-126" .hand
  let (s, unit) ← putAt s p "VEN-091" field
  let s := s.control p field
  let shielded ← play s p first [unit]
  let (afterThree, events) := dealObj 3 shielded unit
  let moved := (moveHome afterThree unit).1
  let (hit, incoming) := dealObj 6 moved unit
  let stacked ← play shielded p second [unit]
  let (spent, _) := dealObj 9 stacked unit
  let (later, _) := dealObj 2 { shielded with turn := shielded.turn + 1 } unit
  return shielded.preventValue unit == 7 && afterThree.preventValue unit == 4 && events.isEmpty &&
    moved.preventValue unit == 4 && hit.preventValue unit == 0 && incoming == [.damaged unit 2] &&
    (hit.obj? unit).any (·.damage == 2) && stacked.preventValue unit == 14 &&
    spent.preventValue unit == 5 && (spent.obj? unit).any (fun o => o.damage == 0) &&
    later.preventValue unit == 0 && (later.obj? unit).any (·.damage == 2)

-- Assigning lethal damage to a shielded 3-Might Unit takes 10 of 12 raw damage.
-- The next Unit receives only the remaining 2 damage.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, spell) ← put s p "VEN-126" .hand
  let (s, attacker) ← putAt s p "VEN-091" field
  let (s, shield) ← putAt s q "VEN-004" field
  let (s, spare) ← putAt s q "VEN-004" field
  let s := (s.control q field).modObj attacker (fun o => { o with baseMightThisTurn := some 12 })
  let shielded ← play s p spell [shield]
  let (first, _) ← (advance 100 { shielded with pending := [.combatDamage field p] } []).toOption
  let (second, _) ← (step 100 first ⟨.player p, .assignPick shield⟩).toOption
  let (third, _) ← (step 100 second ⟨.player p, .assignPick spare⟩).toOption
  let (fourth, _) ← (step 100 third ⟨.player p, .assignDone⟩).toOption
  let (fifth, _) ← (step 100 fourth ⟨.player q, .assignPick attacker⟩).toOption
  let (_, events) ← (step 100 fifth ⟨.player q, .assignDone⟩).toOption
  return shielded.combatNeed shield == some 10 &&
    events.contains (.damaged shield 3) && events.contains (.damaged spare 2)

-- The Vendetta FAQ example with Ki Barrier and Lotus Trap. The affected
-- Unit's controller, rather than the assigning player, orders the replacements.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, barrier) ← put s p "VEN-126" .hand
  let (s, trap) ← put s p "UNL-013" .hand
  let (s, attacker) ← putAt s p "VEN-091" field
  let (s, defender) ← putAt s q "VEN-091" field
  let s := (s.control q field).modObj attacker (fun o => { o with baseMightThisTurn := some 4 })
  let s := s.modObj defender (fun o => { o with baseMightThisTurn := some 4 })
  let prepared ← play s p barrier [defender]
  let prepared ← play prepared p trap [defender]
  let (question, _) ← (advance 100 { prepared with pending := [.combatDamage field p] } []).toOption
  let order (before : Bool) : Action := ⟨.player q, .decide before⟩
  let (preventionFirst, _) ← (step 100 question (order true)).toOption
  let (doublingFirst, _) ← (step 100 question (order false)).toOption
  let finish (s : GameState) := do
    let (s, _) ← (step 100 s ⟨.player p, .assignPick defender⟩).toOption
    let (s, _) ← (step 100 s ⟨.player p, .assignDone⟩).toOption
    let (s, _) ← (step 100 s ⟨.player q, .assignPick attacker⟩).toOption
    (step 100 s ⟨.player q, .assignDone⟩).toOption
  let (held, firstEvents) ← finish preventionFirst
  let (spent, secondEvents) ← finish doublingFirst
  return !(legalActions question).contains ⟨.player p, .decide true⟩ &&
    preventionFirst.combatNeed defender == some 9 && doublingFirst.combatNeed defender == some 6 &&
    excessOf preventionFirst p [(defender, 8)] == 0 &&
    excessOf doublingFirst p [(defender, 8)] == 5 &&
    held.preventValue defender == 3 && spent.preventValue defender == 0 &&
    !held.preventFirst defender &&
    !(firstEvents.any (fun | .damaged u n => u == defender && n > 0 | _ => false)) &&
    secondEvents.contains (.damaged defender 1)

-- Mesmerize records the mode before responses and uses only that mode's target.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "VEN-052" .hand
  let (s, ally) ← put s p "VEN-014" .base
  let (s, enemy) ← put s q "VEN-091" .base
  let s := s.rich p
  let cast (mode : Nat) (u : ObjId) : Action :=
    ⟨.player p, .playCard spell ⟨1, [.mind]⟩ [u] none none (.mode mode)⟩
  let (bouncing, _) ← (step 100 s (cast 0 ally)).toOption
  let (weakening, _) ← (step 100 s (cast 1 enemy)).toOption
  let pending ← (weakening.zone .chain).head?
  let bounced := settleChain {} 8 bouncing
  let weakened := settleChain {} 8 weakening
  return (weakening.obj? pending).any (·.spellPick == .mode 1) &&
    (weakened.mightNow enemy == some 8) && (weakened.obj? ally).isSome &&
    bounced.countIn p .hand "VEN-014" == 1 && (bounced.obj? enemy).isSome &&
    !(legalActions s).contains (cast 0 enemy) && !(legalActions s).contains (cast 1 ally) &&
    !(legalActions s).contains (cast 2 ally)

-- Both modes of Sanction act now and follow the chosen Unit through the same turn.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "VEN-035" .hand
  let (s, unit) ← put s p "VEN-014" .base
  let s := s.rich p
  let cast (mode : Nat) : Action := ⟨.player p, .playCard spell ⟨3, [.calm]⟩ [unit] none none (.mode mode)⟩
  let (granting, _) ← (step 100 s (cast 0)).toOption
  let (removing, _) ← (step 100 (empowerObj p s unit).1 (cast 1)).toOption
  let gained := settleChain {} 8 granting
  let lost := settleChain {} 8 removing
  let expired ← fire gained [.phaseStarted p .ending]
  let regained ← fire lost [.phaseStarted p .ending]
  let invalid ← passToChoice 5 (disempowerObj removing unit).1
  let stillInvalid ← fire invalid [.phaseStarted p .ending]
  return !(legalActions s).contains (cast 1) &&
    (gained.obj? unit).any (·.empowerCount == 1) && (lost.obj? unit).any (·.empowerCount == 0) &&
    (expired.obj? unit).any (·.empowerCount == 0) && (regained.obj? unit).any (·.empowerCount == 1) &&
    (stillInvalid.obj? unit).any (·.empowerCount == 0)

-- Twilight Step records the Base or a different Battlefield at finalization,
-- including when playing it for Flow. Neither destination is a target.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let origin := s.bf0
  let away ← s.battlefields.find? (· != origin)
  let (s, spell) ← put s p "VEN-105" .hand
  let (s, flow) ← put s p "VEN-105" .trash
  let (s, unit) ← putAt s q "VEN-014" origin
  let (s, large) ← putAt s q "VEN-091" origin
  let s := (s.control q origin).rich p
  let cast (u : ObjId) (dest : Option ObjId) : Action :=
    ⟨.player p, .playCard spell ⟨2, [.chaos]⟩ [u] none none (.destination dest)⟩
  let (goingHome, _) ← (step 100 s (cast unit none)).toOption
  let (casting, events) ← (step 100 s (cast unit (some away))).toOption
  let item ← (casting.zone .chain).head?
  let home ← passToChoice 5 goingHome
  let moved ← passToChoice 5 casting
  let (replaying, _) ← (step 100 s
    ⟨.player p, .playCard flow ⟨4, [.chaos]⟩ [unit] none none (.destination (some away))⟩).toOption
  let replayed ← passToChoice 5 replaying
  let invalid ← passToChoice 5 (casting.modObj unit (fun o => { o with baseMightThisTurn := some 4 }))
  return (casting.obj? item).any (·.spellPick == .destination (some away)) &&
    !(legalActions s).contains (cast large (some away)) &&
    !(legalActions s).contains (cast unit (some origin)) &&
    home.countIn q .base "VEN-014" == 1 && (home.obj? large).any (·.loc == some origin) &&
    (moved.obj? unit).any (·.loc == some away) &&
    (replayed.obj? unit).any (·.loc == some away) && replayed.countIn p .banishment "VEN-105" == 1 &&
    (invalid.obj? unit).any (·.loc == some origin) &&
    (events.filter (fun | .chosenBySpell _ _ => true | _ => false)) == [.chosenBySpell p unit]

-- Shuriken Flip's friendly target is required. The separate damage target can be
-- omitted or lost in response, while the friendly target can still move.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, spell) ← put s p "VEN-140" .hand
  let (s, ally) ← put s p "VEN-014" .base
  let (s, enemy) ← putAt s q "VEN-091" field
  let (s, spare) ← put s q "VEN-014" .base
  let s := ((s.control q field).modObj ally (fun o => { o with exhausted := false })).rich p
  let cast (targets : List ObjId) : Action :=
    ⟨.player p, .playCard spell ⟨1, [.fury]⟩ targets none none (.destination (some field))⟩
  let (casting, _) ← (step 100 s (cast [ally, enemy])).toOption
  let (movingOnly, _) ← (step 100 s (cast [ally])).toOption
  let both := settleChain {} 12 casting
  let moved := settleChain {} 12 movingOnly
  let enemyGone := settleChain {} 12 (moveHome casting enemy).1
  let allyAt (t : GameState) := (t.unitsAtOf field p).any (fun id =>
    (t.cardDef? id).any (·.id == cid "VEN-014") && (t.obj? id).any (fun o => !o.exhausted))
  return [both, moved, enemyGone].all allyAt &&
    (both.obj? enemy).any (·.damage == 2) && (moved.obj? enemy).any (·.damage == 0) &&
    !(legalActions s).contains (cast []) && !(legalActions s).contains (cast [ally, spare])

-- Shadow Dash locks the destination in with the target. The Might bonus is
-- calculated after the move and cannot be redirected if the Battlefield stops qualifying.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let field := s.bf0
  let other ← s.battlefields.find? (· != field)
  let (s, empty) ← putBf s p "VEN-159"
  let (s, spell) ← put s p "VEN-148" .hand
  let (s, enemy) ← put s q "VEN-091" .base
  let (s, first) ← putAt s p "VEN-014" field
  let (s, second) ← putAt s p "VEN-014" field
  let (s, solo) ← putAt s p "VEN-014" other
  let s := ((s.control p field).control p other).rich p
  let cast (bf : ObjId) : Action :=
    ⟨.player p, .playCard spell ⟨2, [.fury]⟩ [enemy] none none (.destination (some bf))⟩
  let (casting, _) ← (step 100 s (cast field)).toOption
  let (elsewhere, _) ← (step 100 s (cast other)).toOption
  let double ← passToChoice 5 casting
  let single ← passToChoice 5 elsewhere
  let lost ← passToChoice 5 (moveHome (moveHome casting first).1 second).1
  let (s, _) ← putAt s third "VEN-014" field
  let trio := { s with
    config := { s.config with mode := { s.config.mode with players := 3 } }
    turnOrder := [p, q, third] }
  return !(legalActions s).contains (cast empty) &&
    !(double.unitsAtOf field q).isEmpty && !(single.unitsAtOf other q).isEmpty &&
    double.mightNow first == (s.mightNow first).map (· + 1) &&
    double.mightNow second == (s.mightNow second).map (· + 1) &&
    double.mightNow solo == s.mightNow solo && single.mightNow solo == s.mightNow solo &&
    (lost.obj? enemy).any (·.loc.isNone) &&
    !(legalActions trio).contains (cast field) && (legalActions trio).contains (cast other)

-- Bottled Constellation's three other friendly cards are paid before responses.
-- The payment does not target those cards, and survives countering the ability.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, bottle) ← put s p "VEN-067" .base
  let (s, first) ← put s p "VEN-014" .base
  let (s, second) ← put s p "VEN-014" .base
  let (s, enemy) ← put s q "VEN-014" .base
  let wait (t : GameState) (turnPlayer : PlayerId) := (advance 100
    (t.withTriggers [.phaseStarted turnPlayer .main]) []).toOption.map Prod.fst
  let short ← wait s p
  let (s, gear) ← put s p "VEN-058" .base
  let picking ← wait s p
  let opponent ← wait s q
  let skip : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let pay (ids : List ObjId) : Action := ⟨.player p, .putTrigger 0 [] (.pay ids)⟩
  let picks := legalFrameActions picking
  let payment ← picks.find? (fun a => match a.kind with | .putTrigger _ _ (.pay ..) => true | _ => false)
  let .putTrigger _ _ (.pay paidIds _ _) := payment.kind | none
  let (declined, _) ← (step 100 picking skip).toOption
  let (waiting, events) ← (step 100 picking payment).toOption
  let ability ← (waiting.zone .chain).head?
  let resolved := settleChain {} 8 waiting
  let countered := settleChain {} 8 (counterObj waiting ability).1
  return (legalFrameActions short) == [skip] && (opponent.zone .chain).isEmpty &&
    (legalFrameActions opponent).all (fun a => a.kind != .putTrigger 0 [] .skip) &&
    picks.length == 2 && paidIds.length == 3 && [first, second, gear].all paidIds.contains &&
    !(picks.contains (pay [bottle, first, second])) &&
    !(picks.contains (pay [enemy, first, second])) &&
    !(picks.contains (pay [gear, first, first])) &&
    declined.pointsOf p == s.pointsOf p && (declined.zone .chain).isEmpty &&
    paidIds.all (fun id => (declined.obj? id).isSome && (waiting.obj? id).isNone) &&
    (waiting.obj? bottle).isSome && (waiting.obj? enemy).isSome &&
    !(events.any (fun | .chosenByAbility _ _ => true | _ => false)) &&
    (events.filter (fun | .died _ _ => true | _ => false)).length == 3 &&
    waiting.pointsOf p == s.pointsOf p && resolved.pointsOf p == s.pointsOf p + 1 &&
    countered.pointsOf p == s.pointsOf p && countered.countIn p .trash "VEN-014" == 2 &&
    countered.countIn p .trash "VEN-058" == 1

-- Kennen pays at finalization both on play and on attack. The Stun and the
-- resulting Might bonus apply on resolution, and a payment can use ready Basic Runes.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, enemy) ← putAt s q "VEN-014" field
  let (s, homeTarget) ← put s q "VEN-014" .base
  let (s, kennen) ← putAt s p "VEN-135" field
  let (s, inHand) ← put s p "VEN-135" .hand
  let s := s.control q field
  let attack (t : GameState) := (advance 100
    (t.withTriggers [.combatStarted field p]) []).toOption.map Prod.fst
  let skip : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let target (u : ObjId) : Action := ⟨.player p, .putTrigger 0 [u]⟩
  let picking ← attack (s.fund p 2)
  let short ← attack (s.fund p 1)
  let (declined, _) ← (step 100 picking skip).toOption
  let (waiting, _) ← (step 100 picking (target enemy)).toOption
  let spell ← (waiting.zone .chain).head?
  let resolved := settleChain {} 8 waiting
  let countered := settleChain {} 8 (counterObj waiting spell).1
  let fromRunes ← attack (channel p 2 (s.setPool p {})).1
  let (runed, _) ← (step 100 fromRunes (target enemy)).toOption
  let tiredRunes (t : GameState) := (t.zone (.player p .base)).filter (fun id =>
    (t.obj? id).any (fun o => o.runeDomain.isSome && o.exhausted))
  let (played, _) ← (step 100 (s.fund p 5) ⟨.player p, .playCard inHand ⟨3, []⟩ []⟩).toOption
  let (stunning, _) ← (step 100 played (target homeTarget)).toOption
  let playedResolved := settleChain {} 8 stunning
  return (legalFrameActions short) == [skip] &&
    (legalActions picking).contains (target homeTarget) &&
    (declined.poolOf p).energy == 2 && (declined.zone .chain).isEmpty &&
    (waiting.poolOf p).energy == 0 && (countered.poolOf p).energy == 0 &&
    (waiting.obj? enemy).any (fun o => !o.stunned) && waiting.mightNow kennen == some 2 &&
    (countered.obj? enemy).any (fun o => !o.stunned) &&
    (resolved.obj? enemy).any (·.stunned) && resolved.mightNow kennen == some 4 &&
    (tiredRunes runed).length == (tiredRunes fromRunes).length + 2 &&
    (played.poolOf p).energy == 2 && (stunning.poolOf p).energy == 0 &&
    (playedResolved.obj? homeTarget).any (·.stunned)

-- Corrupted Dragon's attack selects a subset at its Battlefield. Each selected
-- Unit is rechecked after Reactions, and declining leaves all defenders in place.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, dragon) ← putAt s p "VEN-091" field
  let (s, first) ← putAt s q "VEN-014" field
  let (s, second) ← putAt s q "VEN-014" field
  let (s, large) ← putAt s q "VEN-091" field
  let (s, elsewhere) ← put s q "VEN-014" .base
  let s := (s.modObj first (fun o => { o with baseMightThisTurn := some 5 })).control q field
  let (picking, _) ← (advance 100 (s.withTriggers [.combatStarted field p]) []).toOption
  let target (ts : List ObjId) : Action := ⟨.player p, .putTrigger 0 ts⟩
  let (declined, _) ← (step 100 picking ⟨.player p, .putTrigger 0 [] .skip⟩).toOption
  let (empty, _) ← (step 100 picking (target [])).toOption
  let (chosen, _) ← (step 100 picking (target [first, second])).toOption
  let stronger := chosen.modObj first (fun o => { o with baseMightThisTurn := some 6 })
  let resolved := settleChain {} 8 stronger
  return (legalActions picking).contains (target [first]) &&
    !(legalActions picking).contains (target [large]) &&
    !(legalActions picking).contains (target [elsewhere]) &&
    (declined.obj? second).any (·.loc == some field) &&
    (declined.zone .chain).isEmpty && (empty.zone .chain).length == 1 &&
    (resolved.obj? dragon).isSome && (resolved.obj? first).any (·.loc == some field) &&
    resolved.locate second == some (.player q .base) &&
    (resolved.obj? large).any (·.loc == some field)

-- The Dragon enters ready with four points left and exhausted with three.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, card) ← put s p "VEN-091" .hand
  let far ← play (s.gainPoints p (s.victoryScore - 4)) p card
  let close ← play (s.gainPoints p (s.victoryScore - 3)) p card
  let ready ← far.firstOf p .base "VEN-091"
  let exhausted ← close.firstOf p .base "VEN-091"
  return far.tired ready == some false && close.tired exhausted == some true

-- The Legend watches its controller's action on their own card, even when that card
-- was controlled by someone else. The Action spends Empowered and exhausts it up front.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, zed) ← put s p "VEN-143" .legendZone
  let (s, enemyZed) ← put s q "VEN-143" .legendZone
  let (s, spell) ← put s p "VEN-106" .hand
  let (s, smite) ← put s p "UNL-007" .hand
  let (s, discard) ← put s p "VEN-014" .hand
  let (s, otherField) ← putBf s q "VEN-159"
  let (s, own) ← putAt s p "VEN-014" s.bf0
  let (s, enemy) ← putAt s q "VEN-014" otherField
  let s := (s.modObj own (fun o => { o with controller := q })).control q s.bf0
  let s := s.control q otherField
  let no ← play s p spell [enemy]
  let yes ← play s p spell [own]
  let smited ← play s p smite [own]
  let showdown := { yes with pending := [.showdown s.bf0 p 0] }
  let use : Action := ⟨.player p, .activate zed 1 ⟨0, []⟩ []⟩
  let (used, _) ← (step 100 showdown use).toOption
  let after := settleChain {} 12 used
  return (no.obj? zed).any (·.empowerCount == 0) && (no.obj? enemyZed).any (·.empowerCount == 0) &&
    (yes.obj? zed).any (·.empowerCount == 1) && yes.countIn p .banishment "VEN-014" == 1 &&
    (smited.obj? zed).any (·.empowerCount == 1) &&
    (used.obj? zed).any (fun o => o.exhausted && o.empowerCount == 0) &&
    (used.zone (.player p .hand)).contains discard &&
    !(after.zone (.player p .hand)).contains discard &&
    (after.zone (.player p .mainDeck)).length + 1 == (yes.zone (.player p .mainDeck)).length

-- A Flow card goes to Banishment even if countered. Credit goes to the player who
-- played it from Trash. A token moved to Banishment cannot trigger Master of Shadows.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, zed) ← put s p "VEN-143" .legendZone
  let (s, flow) ← put s p "VEN-003" .trash
  let (s, gear) ← put s p "VEN-054" .base
  let token := createOne (tokenId "Tentacle") p none true s
  let (tokenGone, tokenEvents) := banishObj p token ⟨s.nextId⟩
  let no ← fire tokenGone tokenEvents
  let action : Action := ⟨.player p, .playCard flow ⟨4, [.fury]⟩ [gear]⟩
  let (casting, _) ← (step 100 (s.rich p) action).toOption
  let item ← (casting.zone .chain).head?
  let delivered := settleChain {} 12 casting
  let (countered, events) := counterObjHand casting item
  let (queued, _) ← (advance 100 (countered.withTriggers events) []).toOption
  let fromCounter := settleChain {} 12 queued
  return (no.obj? zed).any (·.empowerCount == 0) &&
    (delivered.obj? zed).any (·.empowerCount == 1) &&
    (fromCounter.obj? zed).any (·.empowerCount == 1) &&
    fromCounter.countIn p .banishment "VEN-003" == 1

-- At seven runes, enemy effects cannot damage Esteemed Hierophant; its owner's
-- effects and Combat Damage still can. Spending a Rune disables the prevention.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, unit) ← putAt s q "VEN-025" s.bf0
  let (s, enemySpell) ← put s p "OGN-009" .hand
  let (s, ownSpell) ← put s q "OGN-009" .hand
  let s := s.control q s.bf0
  let six := (channel q (6 - (s.runesOf q).length) s).1
  let seven := (channel q 1 six).1
  let low ← play six p enemySpell [unit]
  let high ← play seven p enemySpell [unit]
  let rune ← (seven.runesOf q).head?
  let (spent, _) ← applyRune seven q rune .recycle
  let dropped ← play spent p enemySpell [unit]
  let own ← play { seven with active := some q, pending := [.priority q] } q ownSpell [unit]
  let (combat, _) := dealAll seven [(unit, 2)]
  let dmg (t : GameState) := (t.obj? unit).map (·.damage)
  return (six.runesOf q).length == 6 && (seven.runesOf q).length == 7 &&
    dmg low == some 3 && dmg high == some 0 && dmg dropped == some 3 &&
    dmg own == some 3 && dmg combat == some 2

-- Piltovan Forge discounts the first Gear ability even when it is countered. The
-- next activation costs full price, and a new turn resets the history.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, field) ← putBf s p "VEN-161"
  let (s, _) ← putAt s p "VEN-014" field
  let (s, first) ← put s p "UNL-136" .base
  let (s, second) ← put s p "UNL-136" .base
  let s := ((s.control p field).rich p).modObj first (fun o => { o with exhausted := false })
  let s := s.modObj second (fun o => { o with exhausted := false })
  let free : Action := ⟨.player p, .activate first 1 ⟨0, []⟩ []⟩
  let nextFree : Action := ⟨.player p, .activate second 1 ⟨0, []⟩ []⟩
  let nextPaid : Action := ⟨.player p, .activate second 1 ⟨1, []⟩ []⟩
  let (used, _) ← (step 100 s free).toOption
  let item ← (used.zone .chain).head?
  let countered := (counterObj used item).1
  let after := { countered with pending := [.priority p] }
  let nextTurn := { after with turn := after.turn + 1 }
  return !(legalActions s).contains nextPaid && (legalActions s).contains nextFree &&
    !(legalActions after).contains nextFree && (legalActions after).contains nextPaid &&
    (legalActions nextTurn).contains nextFree

-- Hiding a Gear is not a Gear activation. Gold's Add is one, even though its
-- source disappears and the player takes control of the Forge only later.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, field) ← putBf s p "VEN-161"
  let (s, otherField) ← putBf s p "VEN-163"
  let (s, _) ← putAt s p "VEN-014" otherField
  let (s, hourglass) ← put s p "OGN-077" .hand
  let (s, gear) ← put s p "UNL-136" .base
  let s := ((s.control p otherField).rich p).modObj gear (fun o => { o with exhausted := false })
  let hid ← activate s p hourglass 1 [otherField] ⟨0, [.calm]⟩
  let gold ← hid.tokenCard "Gold"
  let ready := createOne gold.id p none true hid
  let free : Action := ⟨.player p, .activate gear 1 ⟨0, []⟩ []⟩
  let paid : Action := ⟨.player p, .activate gear 1 ⟨1, []⟩ []⟩
  let id : ObjId := ⟨hid.nextId⟩
  let (spent, _) ← (step 100 ready ⟨.player p, .manaAbility id 0 ⟨0, []⟩⟩).toOption
  let claimed := spent.control p field
  return hid.countIn p .hidden "OGN-077" == 1 &&
    (legalActions (ready.control p field)).contains free && (spent.obj? id).isNone &&
    (legalActions claimed).contains paid && !(legalActions claimed).contains free

-- Risen Altar offers either resource reduction to the controller's Units at the
-- Battlefield. The same keyword still costs full price in Base or under enemy control.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, field) ← putBf s p "VEN-163"
  let (s, fiend) ← putAt s p "VEN-014" field
  let (s, base) ← put s p "VEN-014" .base
  let (s, renekton) ← putAt s p "VEN-092" field
  let s := s.fund p 3 1
  let controlled := s.control p field
  let reducedEnergy : Action := ⟨.player p, .activate fiend 1 ⟨1, [.fury]⟩ []⟩
  let reducedPower : Action := ⟨.player p, .activate fiend 1 ⟨2, []⟩ []⟩
  let full : Action := ⟨.player p, .activate fiend 1 ⟨2, [.fury]⟩ []⟩
  let (energy, _) ← (step 100 controlled reducedEnergy).toOption
  let (power, _) ← (step 100 controlled reducedPower).toOption
  let e := settleChain {} 3 energy
  let w := settleChain {} 3 power
  return (legalActions controlled).contains reducedEnergy &&
    (legalActions controlled).contains reducedPower && !(legalActions controlled).contains full &&
    (legalActions (s.control s.you field)).contains full && (legalActions s).contains full &&
    !(legalActions controlled).contains ⟨.player p, .activate base 1 ⟨2, []⟩ []⟩ &&
    !(legalActions controlled).contains ⟨.player p, .activate renekton 0 ⟨0, []⟩ []⟩ &&
    (e.obj? fiend).any (·.empowerCount == 1) && (w.obj? fiend).any (·.empowerCount == 1) &&
    (e.poolOf p).energy == 2 && (e.poolOf p).get .fury == 0 &&
    (w.poolOf p).energy == 1 && (w.poolOf p).get .fury == 1

-- The second opponent's Spell still counts for Crumbling Sands after Defy has
-- countered it. The same target remains on the Chain if it is the only enemy Spell.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let mode := { s.config.mode with players := 3 }
  let s := { s with
    config := { s.config with mode := mode }
    turnOrder := [q, third, p]
    active := some q
    pending := [.priority q] }
  let (s, unit) ← put s q "VEN-091" .base
  let (s, first) ← put s q "OGN-095" .hand
  let (s, second) ← put s third "OGN-095" .hand
  let (s, defy) ← put s p "OGN-045" .hand
  let (s, sands) ← put s p "VEN-039" .hand
  let s := ((s.rich p).rich q).rich third
  let (casting, _) ← (step 100 s ⟨.player q, .playCard first ⟨1, []⟩ [unit]⟩).toOption
  let original ← (casting.zone .chain).head?
  let (priThird, _) ← (step 100 casting ⟨.player q, .pass⟩).toOption
  let (onlyOne, _) ← (step 100 priThird ⟨.player third, .pass⟩).toOption
  let counter : Action := ⟨.player p, .playCard sands ⟨1, [.calm]⟩ [original]⟩
  let (attempt, _) ← (step 100 onlyOne counter).toOption
  let (two, _) ← (step 100 priThird ⟨.player third, .playCard second ⟨1, []⟩ [unit]⟩).toOption
  let later ← (two.zone .chain).head?
  let (west, _) ← (step 100 two ⟨.player third, .pass⟩).toOption
  let (defying, _) ← (step 100 west ⟨.player p, .playCard defy ⟨1, [.calm]⟩ [later]⟩).toOption
  let negated := settleChain {} 3 defying
  let (passQ, _) ← (step 100 negated ⟨.player q, .pass⟩).toOption
  let (available, _) ← (step 100 passQ ⟨.player third, .pass⟩).toOption
  let (answered, _) ← (step 100 available counter).toOption
  let noCounter := settleChain {} 3 attempt
  let done := settleChain {} 3 answered
  return (negated.zone .chain) == [original] && negated.countIn third .trash "OGN-095" == 1 &&
    (noCounter.zone .chain).contains original && done.zone .chain == [] &&
    done.countIn q .trash "OGN-095" == 1

-- Patched Porobot counts once as a Unit and once as a Gear, even after leaving the
-- Board. Swain also counts a countered Spell, but tokens and plays last turn are excluded.
#guard vendettaCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, swain) ← putAt s p "VEN-065" field
  let (s, porobot) ← put s p "VEN-058" .hand
  let (s, spell) ← put s p "OGN-095" .hand
  let s := s.rich p
  let (casting, _) ← (step 100 s ⟨.player p, .playCard spell ⟨1, []⟩ [swain]⟩).toOption
  let item ← (casting.zone .chain).head?
  let afterCounter := (counterObj casting item).1
  let afterCounter := { afterCounter with pending := [.priority p] }
  let gold ← s.tokenCard "Gold"
  let tentacles := createOne (tokenId "Tentacle") p none false afterCounter
  let tokens := createOne gold.id p none true tentacles
  let tokens := tokens.withTriggers [.tokenPlayed p ⟨afterCounter.nextId⟩,
    .tokenPlayed p ⟨tentacles.nextId⟩]
  let noBonus ← fire tokens [.scored p field true]
  let withBoth ← play afterCounter p porobot
  let robot ← withBoth.firstOf p .base "VEN-058"
  let (left, _) ← moveObj withBoth robot (.player p .trash)
  let scored ← fire left [.scored p field true]
  let later ← fire { left with turn := left.turn + 1 } [.scored p field true]
  return (left.playsOfType .finalized .unit).any (·.object == robot) &&
    (left.playsOfType .finalized .gear).any (·.object == robot) &&
    scored.pointsOf p == s.pointsOf p + 1 && later.pointsOf p == s.pointsOf p &&
    noBonus.pointsOf p == s.pointsOf p

-- Jayce's own play can ready a Legend. The first card Gear play counts even if its
-- trigger is declined. There is a new first Gear on the next turn.
#guard vendettaCase fun s => do
  let p := s.me
  let legend ← (s.zone (.player p .legendZone)).head?
  let (s, jayce) ← put s p "VEN-068" .hand
  let (s, first) ← put s p "VEN-058" .hand
  let (s, second) ← put s p "VEN-058" .hand
  let enter := s.tire legend
  let onPlay ← castStop enter p jayce
  let onBoard ← onPlay.firstOf p .base "VEN-068"
  let ready := settleChain { pick := (· == [legend]) } 12 onPlay
  let gold ← s.tokenCard "Gold"
  let ready := createOne gold.id p none true ready
  let waiting ← castStop (ready.tire legend) p first
  let viaGear := settleChain { pick := (· == [legend]) } 12 waiting
  let (declined, _) ← (step 100 waiting ⟨.player p, .putTrigger 0 []⟩).toOption
  let noSecond ← play declined p second [] { pick := (· == [legend]) }
  let turn := { declined with turn := declined.turn + 1 }
  let nextFirst ← play turn p second [] { pick := (· == [legend]) }
  return !(onPlay.trigPicks.contains onBoard) && ready.tired legend == some false &&
    waiting.trigPicks.contains legend && viaGear.tired legend == some false &&
    (declined.zone .chain).isEmpty && noSecond.tired legend == some true &&
    nextFirst.tired legend == some false

-- Hungry Wolf checks who controlled the Unit when it was chosen. A later move
-- does not forget the choice, and the ability can only be used once that turn.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, wolf) ← put s p "VEN-125" .base
  let (s, enemy) ← put s q "VEN-091" .base
  let (s, gear) ← put s q "VEN-011" .base
  let (s, spell) ← put s p "OGN-095" .hand
  let s := (s.tire wolf).rich p
  let action : Action := ⟨.player p, .activate wolf 0 ⟨0, [.order]⟩ []⟩
  let friendly ← cast s p spell ⟨1, []⟩ [wolf]
  let (casting, _) ← (step 100 s ⟨.player p, .playCard spell ⟨1, []⟩ [enemy]⟩).toOption
  let (left, _) ← moveObj casting enemy (.player q .hand)
  let done := settleChain {} 12 left
  let (used, _) ← (step 100 done action).toOption
  let used := settleChain {} 12 used
  let later := { done with turn := done.turn + 1 }
  let noted := s.withTriggers [.chosenByAbility p enemy]
  let pickedGear := s.withTriggers [.chosenByAbility p gear]
  return !(legalActions s).contains action && !(legalActions friendly).contains action &&
    !(legalActions pickedGear).contains action && (legalActions noted).contains action &&
    (legalActions done).contains action && !(legalActions used).contains action &&
    !(legalActions later).contains action && used.tired wolf == some false &&
    used.mightNow wolf == some 5

-- Ruthless Strike can discard a different hand card at Action speed. The discard
-- is paid before reactions and is neither a target nor a second play.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, target) ← putAt s q "VEN-091" field
  let (s, spell) ← put s p "VEN-008" .hand
  let (s, hand) ← put s p "VEN-047" .hand
  let (s, other) ← put s p "VEN-071" .hand
  let (s, enemy) ← put s q "VEN-047" .hand
  let (s, trash) ← put s p "VEN-047" .trash
  let s := s.rich p
  let action (d : Option ObjId) : Action := ⟨.player p, .playCard spell ⟨3, []⟩ [target] none d⟩
  let showdown := { s with pending := [.showdown field p 0] }
  let (casting, events) ← (step 100 showdown (action (some hand))).toOption
  let top ← (casting.zone .chain).head?
  let done := settleChain {} 12 casting
  let (unpaid, _) ← (step 100 s (action none)).toOption
  let unpaid := settleChain {} 12 unpaid
  let paidEvents := events.filter (fun e => match e with | .played .. => true | _ => false)
  let discarded := events.any (fun e =>
    match e with
    | .discarded who id true => who == p && (casting.obj? id).any (·.formerId == some hand)
    | _ => false)
  return (legalActions showdown).contains (action none) &&
    (legalActions showdown).contains (action (some other)) &&
    !([spell, enemy, trash].any (fun u => (legalActions showdown).contains (action (some u)))) &&
    (casting.obj? top).any (fun o => o.targets == [target] && o.discardPaid && o.extraPaid == 0) &&
    paidEvents == [.played p top] && discarded &&
    (done.obj? target).any (·.damage == 5) && (unpaid.obj? target).any (·.damage == 3)

-- A Repeat granted from outside the card repeats three damage if the discard was declined.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, target) ← putAt s s.you "VEN-091" s.bf0
  let (s, spell) ← put s p "VEN-008" .hand
  let (s, payment) ← put s p "VEN-047" .hand
  let s := (s.rich p).addTurnFx p .nextSpellRepeat
  let (casting, _) ← (step 100 s ⟨.player p, .playCard spell ⟨6, []⟩ [target]⟩).toOption
  let (withDiscard, _) ← (step 100 s
    ⟨.player p, .playCard spell ⟨6, []⟩ [target] none (some payment)⟩).toOption
  let top ← (casting.zone .chain).head?
  let paidTop ← (withDiscard.zone .chain).head?
  let done := settleChain {} 12 casting
  let paid := settleChain {} 12 withDiscard
  return (casting.obj? top).any (fun o => o.extraPaid == 1 && !o.discardPaid) &&
    (withDiscard.obj? paidTop).any (fun o => o.extraPaid == 1 && o.discardPaid) &&
    (done.obj? target).any (·.damage == 6) &&
    paid.countIn s.you .trash "VEN-091" == 1

-- A declined discard does not trigger Zed, while paying it plays a Shadow Clone.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, zed) ← put s p "VEN-023" .hand
  let (s, card) ← put s p "VEN-047" .hand
  let s := s.rich p
  let playZed (d : Option ObjId) : Action := ⟨.player p, .playCard zed ⟨4, [.fury]⟩ [] none d⟩
  let (paid, _) ← (step 100 s (playZed (some card))).toOption
  let (unpaid, _) ← (step 100 s (playZed none)).toOption
  let paid := settleChain {} 12 paid
  let unpaid := settleChain {} 12 unpaid
  return paid.countNamed p .base "Shadow Clone" == 1 && unpaid.countNamed p .base "Shadow Clone" == 0 &&
    paid.locate card == none && unpaid.locate card == some (.player p .hand)

-- The two Tentacles can be played at different locations. Playing the spell for Flow
-- still offers the location of each token and banishes the spell.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s p "VEN-158"
  let (s, enemyField) ← putBf s q "VEN-158"
  let (s, _) ← putAt s p "VEN-047" field
  let (s, _) ← putAt s q "VEN-047" enemyField
  let (s, spell) ← put s p "VEN-100" .trash
  let s := ((s.control p field).control q enemyField).rich p
  let tentacle ← s.tokenCard "Tentacle"
  let (waiting, _) ← (step 100 s ⟨.player p, .playCard spell ⟨3, []⟩ []⟩).toOption
  let waiting := settleChain {} 2 waiting
  let (placed, _) ← (step 100 waiting ⟨.player p, .decide false⟩).toOption
  let (done, _) ← (step 100 placed ⟨.player p, .decide true⟩).toOption
  let tokenAt (t : GameState) (bf : ObjId) :=
    (t.zone .battlefieldZone).filter (fun u => (t.cardDef? u).any (·.id == tentacle.id) &&
      (t.obj? u).any (fun o => o.loc == some bf && o.exhausted))
  return s.unitTokenDestinations p tentacle == [none, some field] &&
    tentacle.tags == [⟨"Bilgewater"⟩] &&
    (tokenAt placed field).length == 1 && placed.countNamed p .base "Tentacle" == 0 &&
    tokenAt done field == tokenAt placed field && done.countNamed p .base "Tentacle" == 1 &&
    done.countIn p .banishment "VEN-100" == 1

-- Illaoi makes a token on play and on each kind of score at her location. Skipping over an
-- enemy token or a friendly Gear token, her Might counts only the controller's Unit tokens.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let ordinaryField := s.bf0
  let (s, field) ← putBf s p "VEN-158"
  let (s, _) ← putAt s p "VEN-047" field
  let (s, hand) ← put s p "VEN-109" .hand
  let gold ← s.tokenCard "Gold"
  let s := createOne gold.id p none true (createOne (tokenId "Tentacle") q none false s)
  let s := s.control p field
  let after ← play s p hand
  let illaoi ← after.firstOf p .base "VEN-109"
  let r ← moveObj after illaoi .battlefieldZone
  let s := r.1.modObj r.2 (fun o => { o with loc := some field })
  let elsewhere ← fire s [.scored p ordinaryField true]
  let conquered ← fire s [.scored p field true]
  let held ← fire s [.scored p field false]
  return after.mightNow illaoi == some 5 && after.countNamed p .base "Tentacle" == 1 &&
    elsewhere.countNamed p .base "Tentacle" == 1 &&
    conquered.countNamed p .base "Tentacle" == 2 && held.countNamed p .base "Tentacle" == 2 &&
    held.mightNow r.2 == some 6

-- Profiteer targets the recipient when the ability is put on the Chain. It can pay with
-- an Empowered Legend, and leaves both objects alone when the cost is declined.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, legend) ← put s p "VEN-153" .legendZone
  let (s, target) ← put s p "VEN-155" .legendZone
  let (s, gear) ← put s p "VEN-147" .base
  let (s, card) ← put s p "VEN-082" .hand
  let marked (t : GameState) (id : ObjId) := (t.obj? id).map (·.empowerCount)
  let s := (s.modObj legend (fun o => { o with empowerCount := 1 })).modObj gear
    (fun o => { o with empowerCount := 1 })
  let targets ← castStop s p card
  let paid ← play s p card [] { pick := (· == [target]), obj := (· == legend) }
  let declined ← play s p card [] { pick := (· == [target]), yes := false }
  return targets.trigPicks.contains target && targets.trigPicks.contains gear &&
    marked paid target == some 1 && marked paid gear == some 1 && marked paid legend == some 1 &&
    marked declined target == some 0 && marked declined legend == some 1

-- Death Mark burns before playing a Shadow Clone. The 0 Might clone survives with zero
-- damage. On attack, it can banish a newly burned Unit, choose between Units, or decline.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, field) ← putBf s p "VEN-158"
  let (s, _) ← putAt s p "VEN-047" field
  let (s, spell) ← put s p "VEN-144" .hand
  let (s, unit) ← put s p "VEN-047" .mainDeck
  let (s, otherUnit) ← put s p "VEN-071" .mainDeck
  let (s, gear) ← put s p "VEN-147" .mainDeck
  let zone := Zone.player p .mainDeck
  let s := (s.control p field).reorder zone ([unit, otherUnit, gear] ++
    (s.zone zone).filter (fun u => !([unit, otherUnit, gear].contains u)))
  let made ← play s p spell [] { yes := false }
  let clone ← (made.zone .battlefieldZone).find? (fun o =>
    (made.cardDef? o).any (·.name == "Shadow Clone"))
  let fodder ← (made.zone (.player p .trash)).find? (fun o =>
    (made.obj? o).any (·.formerId == some unit))
  let paid ← fire made [.combatStarted field p] { obj := (· == fodder) }
  let declined ← fire made [.combatStarted field p] { yes := false }
  let (expired, _) ← (advance 100 { paid with pending := [.expireTurn] } []).toOption
  let assault (t : GameState) := (t.keywordsNow clone).contains ⟨.assault, .amount 4⟩
  return made.mightNow clone == some 0 && made.tired clone == some true &&
    made.countIn p .trash "VEN-147" == 1 && assault paid && !assault declined && !assault expired &&
    (paid.zone (.player p .banishment)).any (fun o => (paid.obj? o).any (·.formerId == some fodder)) &&
    declined.locate fodder == some (.player p .trash)

-- Zed's Conquer specifies the Base even when a Battlefield is available. His action
-- chooses a friendly Shadow Clone and swaps the two Units' locations.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s p "VEN-158"
  let (s, zed) ← putAt s p "VEN-112" field
  let s := s.control p field
  let scored ← fire s [.scored p field true] { yes := false }
  let clone ← scored.firstOf p .base "TKN-Shadow Clone"
  let withEnemy := createOne (tokenId "Shadow Clone") q none false scored
  let enemy ← withEnemy.firstOf q .base "TKN-Shadow Clone"
  let ready := { withEnemy.rich p with pending := [.priority p] }
  let action (target : ObjId) : Action := ⟨.player p, .activate zed 1 ⟨1, [.chaos]⟩ [target]⟩
  let (waiting, _) ← (step 100 ready (action clone)).toOption
  let swapped := settleChain {} 12 waiting
  return !(legalActions ready).contains (action enemy) &&
    swapped.locate zed == some (.player p .base) &&
    (swapped.obj? clone).bind (·.loc) == some field

-- Mystic Vortex adds one Power to Reaction, including Quick-Draw and destination-granted
-- Ambush, for both players. Action by itself costs the printed amount.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let ordinaryField := s.bf0
  let (s, vortex) ← putBf s p "VEN-160"
  let (s, spell) ← put s p "VEN-056" .hand
  let (s, other) ← put s q "VEN-056" .hand
  let (s, action) ← put s p "SFD-184" .hand
  let (s, inferna) ← put s p "UNL-002" .hand
  let (s, gear) ← put s p "SFD-022" .hand
  let (s, ally) ← putAt s p "VEN-047" vortex
  let s := (s.rich p).rich q
  let sd (bf : ObjId) (focus : PlayerId) := { s with pending := [.showdown bf focus 0, .priority p] }
  let nested : GameState := { s with pending := [.chainPass p 0, .showdown vortex p 0, .priority p] }
  let free : Action := ⟨.player p, .playCard spell ⟨7, []⟩ []⟩
  let pay : Action := ⟨.player p, .playCard spell ⟨7, [.body]⟩ []⟩
  let tax (st : GameState) (c : ObjId) :=
    ((st.cardDef? c).bind (st.effCost p c)).map (fun k => k.power.length)
  let ambush : Action := ⟨.player p, .playCard inferna ⟨2, [.mind]⟩ [vortex]⟩
  let (answered, _) ← (step 100 nested pay).toOption
  return (legalActions s).contains free && (legalActions (sd ordinaryField p)).contains free &&
    !(legalActions (sd vortex p)).contains free && (legalActions (sd vortex p)).contains pay &&
    (legalActions (sd vortex q)).contains ⟨.player q, .playCard other ⟨7, [.order]⟩ []⟩ &&
    (answered.poolOf p).body + 1 == (s.poolOf p).body &&
    (legalActions (sd vortex p)).contains ⟨.player p, .playCard action ⟨2, [.body]⟩ [ally]⟩ &&
    (legalActions (sd vortex p)).contains ambush &&
    !(legalActions (sd vortex p)).contains ⟨.player p, .playCard inferna ⟨2, []⟩ [vortex]⟩ &&
    (legalActions (sd vortex p)).contains ⟨.player p, .playCard gear ⟨2, [.fury, .calm]⟩ []⟩ &&
    tax (sd vortex p) gear == (tax s gear).map (· + 1)

-- A card being played from Hidden gains Reaction, even with no printed Reaction keyword.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, vortex) ← putBf s p "VEN-160"
  let (s, hidden) ← put s p "OGN-168" .hidden
  let (s, ally) ← putAt s p "VEN-047" vortex
  let s := (s.control p vortex).modObj hidden (fun o =>
    { o with hiddenAt := some vortex, hiddenTurn := some (s.turn - 1) })
  let s := s.rich p
  let showdown : GameState := { s with pending := [.showdown vortex p 0, .priority p] }
  let action (power : List Domain) : Action := ⟨.player p, .activate hidden 1 ⟨0, power⟩ [ally]⟩
  let (waiting, _) ← (step 100 showdown (action [.calm])).toOption
  let done := settleChain {} 12 waiting
  let finalized (t : GameState) := (t.playsOfType .finalized .spell).map (·.object)
  return (legalActions s).contains (action []) &&
    !(legalActions showdown).contains (action []) &&
    (legalActions showdown).contains (action [.calm]) &&
    (waiting.poolOf p).calm + 1 == (s.poolOf p).calm &&
    (finalized waiting).count hidden == 1 && finalized done == finalized waiting &&
    done.locate ally == some (.player p .base) && done.countIn p .trash "OGN-168" == 1

-- Sandswept Tomb removes one symbol of the caster's choice per qualifying Battlefield,
-- regardless of who controls it or how many friendly Units the Spell chooses there.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, first) ← putBf s q "VEN-164"
  let (s, second) ← putBf s p "VEN-164"
  let (s, a) ← putAt s p "VEN-047" first
  let (s, b) ← putAt s p "VEN-047" first
  let (s, c) ← putAt s p "VEN-047" second
  let (s, e) ← putAt s q "VEN-047" first
  let (s, f) ← put s q "VEN-047" .base
  let (s, spell) ← put s p "UNL-110" .hand
  let d ← s.cardDef? spell
  let d := { d with cost := some ⟨6, [.domain .mind, .domain .body]⟩ }
  let s := { s with cards := { s.cards with cards := d :: s.cards.cards } }
  let s := (s.control q first).rich p
  let act (power : List Domain) (ts : List ObjId) : Action :=
    ⟨.player p, .playCard spell ⟨6, power⟩ ts⟩
  let (casting, _) ← (step 100 s (act [.body] [a, b])).toOption
  let actions := legalActions s
  return actions.contains (act [.mind] [a, b]) && actions.contains (act [.body] [a, b]) &&
    !(actions.contains (act [] [a, b])) && !(actions.contains (act [.mind, .body] [a, b])) &&
    actions.contains (act [] [a, c]) && actions.contains (act [.body] [a, e]) &&
    actions.contains (act [.mind, .body] [e, f]) && !(actions.contains (act [.body] [e, f])) &&
    (casting.poolOf p).body + 1 == (s.poolOf p).body && (casting.poolOf p).mind == (s.poolOf p).mind

-- Deflect adds Power to the total, so Tomb can cover it both for a normal cast and from Hidden.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, tomb) ← putBf s p "VEN-164"
  let (s, ally) ← putAt s p "VEN-047" tomb
  let (s, enemy) ← putAt s q "VEN-064" tomb
  let (s, spell) ← put s p "UNL-110" .hand
  let (s, hidden) ← put s p "SFD-145" .hidden
  let d ← s.cardDef? spell
  let s := { s with cards := { s.cards with cards := { d with cost := some ⟨6, []⟩ } :: s.cards.cards } }
  let s := (s.control p tomb).modObj hidden (fun o =>
    { o with hiddenAt := some tomb, hiddenTurn := some (s.turn - 1) })
  let s := s.fund p 6
  let targets := [ally, enemy]
  let cast : Action := ⟨.player p, .playCard spell ⟨6, []⟩ targets⟩
  let reveal : Action := ⟨.player p, .activate hidden 1 ⟨0, []⟩ targets⟩
  let (ordinary, _) ← (step 100 s cast).toOption
  let (fromHidden, _) ← (step 100 s reveal).toOption
  return s.deflectCost p targets (some spell) == 1 &&
    (ordinary.poolOf p).total == 0 && (fromHidden.poolOf p).total == 6

-- Two Tomb discounts can cover the Power in both the base and the additional Repeat cost.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, first) ← putBf s p "VEN-164"
  let (s, second) ← putBf s p "VEN-164"
  let (s, a) ← putAt s p "VEN-047" first
  let (s, b) ← putAt s p "VEN-047" second
  let (s, spell) ← put s p "SFD-023" .hand
  let s := s.fund p 4
  let ordinary : Action := ⟨.player p, .playCard spell ⟨2, []⟩ [a, b]⟩
  let repeat_ : Action := ⟨.player p, .playCard spell ⟨4, []⟩ [a, b]⟩
  let (one, _) ← (step 100 s ordinary).toOption
  let (two, _) ← (step 100 s repeat_).toOption
  let paidRepeats (t : GameState) :=
    (t.zone .chain).head?.bind (fun id => (t.obj? id).map (·.extraPaid))
  return paidRepeats one == some 0 && paidRepeats two == some 1 &&
    (one.poolOf p).energy == 2 && (two.poolOf p).energy == 0

-- Temporal Portal uses the Spell's printed cost for Repeat. The Vortex raises the total once.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, vortex) ← putBf s p "VEN-160"
  let (s, spell) ← put s p "VEN-056" .hand
  let s := (s.fund p 14 (body := 2)).addTurnFx p .nextSpellRepeat
  let s := { s with pending := [.showdown vortex p 0, .priority p] }
  let pay (power : List Domain) : Action := ⟨.player p, .playCard spell ⟨14, power⟩ []⟩
  let (casting, _) ← (step 100 s (pay [.body])).toOption
  let entry ← (casting.zone .chain).head?
  return (casting.obj? entry).any (·.extraPaid == 1) &&
    (casting.poolOf p).body == 1 && !(legalActions s).contains (pay [.body, .body])

-- A Spell played for a reduced cost by another effect still gets the Tomb discount.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, tomb) ← putBf s p "VEN-164"
  let (s, unit) ← putAt s p "VEN-047" tomb
  let (s, _) ← put s p "SFD-023" .banishment
  let e := Effect.prim (.playReduced (.one .friendly .inBanishment [.ofType .spell]) (.const 2) none)
  let s := (s.control p tomb).fund p 0
  let task := Frame.run p tomb {} (.cons e .nil)
  let (casting, _) ← (advance 100 { s with pending := [task] } []).toOption
  let entry ← (casting.zone .chain).head?
  return (casting.cardDef? entry).any (·.id == cid "SFD-023") &&
    (casting.obj? entry).any (fun o => o.extraPaid == 0 && o.targets == [unit])

-- Apprentice Mage can order the two cards it Predicts after paying to Empower.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, mage) ← put s p "VEN-047" .base
  let z := Zone.player p .mainDeck
  let deck := s.zone z
  let first ← deck[0]?
  let second ← deck[1]?
  let drawnLater ← deck[2]?
  let waiting ← activate s p mage 0 [] ⟨2, []⟩
  let (choice, _) ← (step 100 waiting ⟨.player p, .predictPick second false⟩).toOption
  let (done, _) ← (step 100 choice ⟨.player p, .predictPick first false⟩).toOption
  return waiting.mightNow mage == some 4 && done.mightNow mage == some 4 &&
    (waiting.poolOf p).energy + 2 == ((s.rich p).poolOf p).energy &&
    (waiting.zone z) == deck && (legalFrameActions waiting).length == 4 &&
    (step 100 waiting ⟨.player q, .predictPick first false⟩).toOption.isNone &&
    (step 100 waiting ⟨.player p, .predictPick drawnLater true⟩).toOption.isNone &&
    (step 100 choice ⟨.player p, .predictPick second true⟩).toOption.isNone &&
    done.zone z == second :: first :: deck.drop 2 &&
    (activate done p mage 0 [] ⟨2, []⟩).isNone

-- Clairvoyance looks at five, recycles the chosen cards in a random order, and draws the
-- top two in the order the player chose. No card is drawn while the random order is pending.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "VEN-056" .hand
  let z := Zone.player p .mainDeck
  let deck := s.zone z
  let a ← deck[0]?
  let b ← deck[1]?
  let c ← deck[2]?
  let d ← deck[3]?
  let e ← deck[4]?
  let started ← castStop s p spell
  let (passed, _) ← (step 100 started ⟨.player p, .pass⟩).toOption
  let (waiting, lookEvents) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let picks := [(d, false), (a, true), (b, false), (e, true), (c, true)]
  let shuffled ← picks.foldlM (fun t (id, recycle) =>
    (step 100 t ⟨.player p, .predictPick id recycle⟩).toOption.map Prod.fst) waiting
  let order := [a, c, e]
  let (done, events) ← (step 100 shuffled ⟨.chance, .arrange order⟩).toOption
  let drawn := events.filterMap (fun
    | .moved old _ (.player player .hand) => if player == p then some old else none
    | _ => none)
  return lookEvents == (deck.take 5).map (Event.lookedAt p) &&
    shuffled.zone z == deck && shuffled.handN p + 1 == s.handN p &&
    (step 100 shuffled ⟨.player p, .arrange order⟩).toOption.isNone &&
    (step 100 shuffled ⟨.chance, .arrange [a, a, e]⟩).toOption.isNone &&
    drawn == [d, b] && done.zone z == deck.drop 5 ++ order &&
    done.handN p == s.handN p + 1

-- Wild Claw offers looked-at, playable Units and Gear, then Recycles the
-- other looked-at cards before asking whether to Empower the played object.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "VEN-089" .hand
  let (s, unit) ← put s p "VEN-111" .mainDeck
  let (s, gear) ← put s p "VEN-075" .mainDeck
  let (s, expensive) ← put s p "VEN-064" .mainDeck
  let (s, reaction) ← put s p "OGN-095" .mainDeck
  let (s, otherSpell) ← put s p "VEN-085" .mainDeck
  let (s, outside) ← put s p "VEN-075" .mainDeck
  let z := Zone.player p .mainDeck
  let seen := [unit, gear, expensive, reaction, otherSpell]
  let suffix := outside :: (s.zone z).filter (fun id => !(outside :: seen).contains id)
  let s := (s.fund p 8 (body := 1) (chaos := 1)).reorder z (seen ++ suffix)
  let act (t : GameState) (a : ActionKind) := (step 100 t ⟨.player p, a⟩).toOption
  let (casting, _) ← act s (.playCard spell ⟨7, [.body]⟩ [])
  let (passed, _) ← act casting .pass
  let (looking, looked) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let (choosing, _) ← act looking (.decide true)
  let (recycling, played) ← act choosing (.choose unit)
  let unitInPlay ← recycling.firstOf p .base "VEN-111"
  let banished ← banishedPlayId played
  let bottom := [reaction, gear, otherSpell, expensive]
  let (empowerChoice, recycled) ← (step 100 recycling ⟨.chance, .arrange bottom⟩).toOption
  let (empowered, _) ← act empowerChoice (.decide true)
  let (ordinary, _) ← act empowerChoice (.decide false)
  let (declined, _) ← act looking (.decide false)
  let declineOrder := [reaction, gear, otherSpell, expensive, unit]
  let (unchosen, _) ← (step 100 declined ⟨.chance, .arrange declineOrder⟩).toOption
  let (gearRecycling, _) ← act choosing (.choose gear)
  let gearInPlay ← gearRecycling.firstOf p .base "VEN-075"
  let (gearEmpower, _) ←
    (step 100 gearRecycling ⟨.chance, .arrange [unit, reaction, otherSpell, expensive]⟩).toOption
  let (gearPlayed, _) ← act gearEmpower (.decide true)
  return looked == seen.map (.lookedAt p) &&
    (legalFrameActions choosing).map Action.kind == [.choose unit, .choose gear] &&
    played.contains (.moved unit banished (.player p .banishment)) &&
    played.contains (.moved banished unitInPlay (.player p .base)) &&
    played.contains (.played p unitInPlay) && !(played.any (fun | .chosenBySpell .. => true | _ => false)) &&
    (recycling.obj? unitInPlay).any (fun o => o.energyPaid == 1 && o.exhausted && !o.playedFromHand) &&
    (recycling.poolOf p).total == 0 && recycling.zone z == seen.erase unit ++ suffix &&
    (step 100 recycling ⟨.player p, .arrange bottom⟩).toOption.isNone &&
    (step 100 recycling ⟨.chance, .arrange [gear, gear, otherSpell, reaction]⟩).toOption.isNone &&
    recycled.contains (.recycled p) && empowerChoice.zone z == suffix ++ bottom &&
    (empowered.obj? unitInPlay).any (·.empowerCount == 1) &&
    (ordinary.obj? unitInPlay).any (·.empowerCount == 0) &&
    unchosen.zone z == suffix ++ declineOrder && unchosen.countIn p .base "VEN-111" == 0 &&
    (gearPlayed.obj? gearInPlay).any (fun o => o.exhausted && o.empowerCount == 1) &&
    (gearPlayed.poolOf p).energy == 1 && (gearPlayed.poolOf p).chaos == 1

-- Choosing to pay Accelerate for the card played by Wild Claw is separate
-- from choosing that card. The reduction also covers the Energy of Accelerate.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "VEN-089" .hand
  let (s, rearguard) ← put s p "OGN-010" .mainDeck
  let z := Zone.player p .mainDeck
  let s := (s.fund p 7 (fury := 1) (body := 1)).reorder z (rearguard :: (s.zone z).erase rearguard)
  let act (t : GameState) (a : ActionKind) := (step 100 t ⟨.player p, a⟩).toOption.map Prod.fst
  let casting ← act s (.playCard spell ⟨7, [.body]⟩ [])
  let looking ← passToChoice 8 casting
  let choosing ← act looking (.decide true)
  let paying ← act choosing (.choose rearguard)
  let .eitherDo _ _ _ (.finishReducedPermanent _ _ regular) (.finishReducedPermanent _ _ fast) _ :: _ :=
    paying.pending | none
  let normal ← act paying (.decide true)
  let accelerated ← act paying (.decide false)
  let normalUnit ← normal.firstOf p .base "OGN-010"
  let fastUnit ← accelerated.firstOf p .base "OGN-010"
  return regular.cost == ⟨0, []⟩ && !regular.accelerated &&
    fast.cost == ⟨0, [.domain .fury]⟩ && fast.accelerated &&
    (normal.obj? normalUnit).any (fun o => o.exhausted && !o.paid && o.energyPaid == 0) &&
    (accelerated.obj? fastUnit).any (fun o => !o.exhausted && o.paid && o.energyPaid == 0) &&
    (normal.poolOf p).total == 1 && (accelerated.poolOf p).total == 0

-- A Unit with a mandatory play location can only be offered once that
-- Battlefield qualifies. Its reduced play still uses the Battlefield.
#guard vendettaCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, card) ← put s p "SFD-015" .banishment
  let legal := s.modObj field (fun o => { o with scored := [p], held := [] })
  let [plan] := reducedPermanentPlays legal p card 5 | none
  let (done, entered, events) ← applyReducedPermanent legal p card plan
  return (reducedPermanentPlays s p card 5).isEmpty && plan.battlefield == some field &&
    done.locate entered == some .battlefieldZone &&
    (done.obj? entered).any (fun o => o.loc == some field && o.moves == 0) &&
    events.contains (.moved card entered .battlefieldZone) && events.contains (.played p entered)

-- Predict looks at a short deck as it is, including an empty one, without Burn Out.
#guard vendettaCase fun s => do
  let p := s.me
  let z := Zone.player p .mainDeck
  let deck := s.zone z
  let top ← deck[0]?
  let short := (applyEach (sendObj .trash) s (deck.drop 1)).1
  let task := Frame.run p s.bf0 {} (.cons (.prim (.predict (.const 5))) .nil)
  let (waiting, es) ← (advance 100 { short with pending := [task] } []).toOption
  let (recycled, rs) ← (step 100 waiting ⟨.player p, .predictPick top true⟩).toOption
  let empty := (sendObj .trash short top).1
  let (done, noneSeen) ← (advance 100 { empty with pending := [task] } []).toOption
  return es == [.lookedAt p top] && recycled.zone z == [top] &&
    recycled.pending.isEmpty && rs.isEmpty && done.pending.isEmpty && noneSeen.isEmpty

-- Dragon Form changes the base, including through Flow. Equipment, buffs and other arithmetic
-- effects still apply, and the base change expires with other turn effects.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, form) ← put s p "VEN-116" .hand
  let (s, mage) ← put s p "VEN-047" .base
  let (s, giant) ← put s q "VEN-091" .base
  let (s, gear) ← put s p "SFD-033" .base
  let s := (attachTo mage (s.buff mage) gear).1
  let s := (addMightMod ⟨2, .turn⟩ s mage).1
  let changed ← play s p form [mage]
  let trashForm ← changed.firstOf p .trash "VEN-116"
  let (onChain, _) ← (step 100 changed ⟨.player p, .playCard trashForm ⟨3, []⟩ [giant]⟩).toOption
  let flowed := settleChain {} 12 onChain
  let (expired, _) ← (advance 100 { flowed with pending := [.phase .ending] } []).toOption
  let (left, card) ← moveObj flowed mage (.player p .hand)
  let (returned, fresh) ← moveObj left card (.player p .base)
  return s.mightNow mage == some 7 && changed.mightNow mage == some 9 &&
    changed.mightNow giant == some 10 && flowed.mightNow giant == some 5 &&
    flowed.countIn p .banishment "VEN-116" == 1 &&
    expired.mightNow mage == some 5 && expired.mightNow giant == some 10 &&
    returned.mightNow fresh == some 3 && (play s p form [gear]).isNone &&
    (flowed.cardDef? mage).bind (·.might) == some 3

-- Blighted Battleaxe's end-of-turn damage happens while Dragon Form is still active.
-- The mage survives the four damage, then heals and returns to printed Might in Expiration.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, form) ← put s p "VEN-116" .hand
  let (s, mage) ← put s p "VEN-047" .base
  let (s, axe) ← put s p "UNL-019" .base
  let s := (attachTo mage s axe).1
  let transformed ← play s p form [mage]
  let finish (t : GameState) : Option (GameState × GameState) := do
    let (ending, _) ← (advance 100 { t with pending := [.phase .ending] } []).toOption
    return (ending, settleChain {} 16 ending)
  let (ending, expired) ← finish transformed
  let (_, ordinary) ← finish s
  return ending.mightNow mage == some 9 && !(ending.zone .chain).isEmpty &&
    expired.mightNow mage == some 3 && (expired.obj? mage).any (·.damage == 0) &&
    (expired.obj? axe).any (·.attached.isNone) && (expired.poolOf p) == RunePool.empty &&
    expired.pending.isEmpty && ordinary.countIn p .trash "VEN-047" == 1

-- Siphoning Strike has a seven-rune threshold. Its delayed ability belongs to its caster,
-- whether the Unit dies immediately or after the spell has left the Chain.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "VEN-146" .hand
  let (s, bf) ← putBf s q "VEN-158"
  let (s, giant) ← putAt s q "VEN-091" bf
  let s := s.control q bf
  let runes (t : GameState) (r : PlayerId) :=
    (t.zone (.player r .base)).filter (fun id => (t.cardDef? id).any (·.hasType .rune))
  let six := (channel p (6 - (runes s p).length) s).1
  let seven := (channel p 1 six).1
  let low ← play six p spell [giant]
  let high ← play seven p spell [giant]
  let (dead, death) := killOrSave low giant
  let late ← fire dead death
  let expired := { low with turn := low.turn + 1 }
  let (old, oldDeath) := killOrSave expired giant
  let nextTurn ← fire old oldDeath
  let (left, card) ← moveObj low giant (.player q .hand)
  let (returned, fresh) ← moveObj left card .battlefieldZone
  let (gone, freshDeath) := killOrSave returned fresh
  let newUnit ← fire gone freshDeath
  let (waiting, _) ← (step 100 (six.rich p) ⟨.player p, .playCard spell ⟨4, []⟩ [giant]⟩).toOption
  let moved := settleChain {} 12 (recallObj waiting giant).1
  let (later, laterDeath) := killOrSave moved giant
  let missed ← fire later laterDeath
  let channeled ← ((runes late p).filter (fun id => !(runes low p).contains id)).head?
  return (runes low p).length == 6 && (runes high p).length == 7 &&
    (low.obj? giant).any (·.damage == 4) && (high.obj? giant).any (·.damage == 7) &&
    (runes late p).length == 7 && late.tired channeled == some true && runes late q == runes low q &&
    runes nextTurn p == runes low p && runes newUnit p == runes low p &&
    moved.locate giant == some (.player q .base) && (moved.obj? giant).any (·.damage == 0) &&
    runes missed p == runes six p

-- The delayed ability is separate from the target's Deathknell. Karthus repeats the latter
-- while the caster of Siphoning Strike channels exactly one Rune.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "VEN-146" .hand
  let (s, _) ← put s q "OGN-236" .base
  let (s, bf) ← putBf s q "VEN-158"
  let (s, kog) ← putAt s q "OGN-190" bf
  let (s, giant) ← putAt s q "VEN-091" bf
  let s := s.control q bf
  let after ← play s p spell [kog]
  let zone := Zone.player p .runeDeck
  return after.countIn q .trash "OGN-190" == 1 &&
    (after.obj? giant).any (·.damage == 8) &&
    (after.zone zone).length + 1 == (s.zone zone).length

-- Oasis Raider checks the controller's Beginning Phase and the relative rune count.
#guard vendettaCase fun s => do
  let runes := s.zone (.player s.me .base) ++ s.zone (.player s.you .base)
  let s := (applyEach (sendObj .runeDeck) s runes).1
  let (s, raider) ← put s s.me "VEN-006" .base
  let (behind, _) ← put s s.you "OGN-007" .base
  let a ← fire behind [.phaseStarted s.me .beginning]
  let b ← fire s [.phaseStarted s.me .beginning]
  let c ← fire behind [.phaseStarted s.you .beginning]
  return a.mightNow raider == some 6 && (a.keywordsNow raider).any (·.keyword == .ganking) &&
    b.mightNow raider == some 4 && c.mightNow raider == some 4

-- Fretful Feline gains Might when it changes from exhausted to ready.
#guard vendettaCase fun s => do
  let (s, feline) ← put s s.me "VEN-071" .base
  let ready := readyEffect (s.tire feline) feline
  let a ← fire ready.1 ready.2
  let already := readyEffect s feline
  let b ← fire already.1 already.2
  return a.mightNow feline == some 7 && b.mightNow feline == some 5

-- Decree of Unity only accepts enemy Chaos units or gear.
#guard vendettaCase fun s => do
  let (s, spell) ← put s s.me "VEN-131" .hand
  let (s, enemy) ← put s s.you "OGN-193" .base
  let (s, friendly) ← put s s.me "OGN-193" .base
  let (s, otherDomain) ← put s s.you "OGN-051" .base
  let after ← play s s.me spell [enemy]
  return after.countIn s.you .trash "OGN-193" == 1 &&
    (play s s.me spell [friendly]).isNone && (play s s.me spell [otherDomain]).isNone

-- Acceleration Gate accepts mixed targets and permits choosing none of them.
#guard vendettaCase fun s => do
  let (s, spell) ← put s s.me "VEN-150" .hand
  let (s, unit) ← put s s.me "OGN-088" .base
  let (s, gear) ← put s s.me "VEN-058" .base
  let (s, rune) ← put s s.you "OGN-007" .base
  let s := ((s.tire unit).tire gear).tire rune
  let targets := [unit, gear, rune].mergeSort (fun a b => decide (a.n ≤ b.n))
  let chosen ← play s s.me spell targets
  let unchosen ← play s s.me spell []
  return [unit, gear, rune].all (fun id => chosen.tired id == some false) &&
    [unit, gear, rune].all (fun id => unchosen.tired id == some true)

-- Shadow Temple burns three cards. A short deck burns what is available, then processes Burn
-- Out and finishes burning from the refilled deck.
#guard vendettaCase fun s => do
  let (s, temple) ← putBf s s.me "VEN-165"
  let player := s.me
  let deck := Zone.player player .mainDeck
  let trash := Zone.player player .trash
  let before := s.zone deck
  let top ← before[0]?
  let second ← before[1]?
  let third ← before[2]?
  let a ← fire s [.scored player temple false]
  let short := (applyEach (sendObj .banishment) s (before.drop 2)).1
  let b ← fire short [.scored player temple false]
  let (c, events) ← (step 100 b ⟨.chance, .arrange (b.zone trash)⟩).toOption
  let (d, _) ← (step 100 c ⟨.player player, .burnOutTarget s.you⟩).toOption
  let aTrash := a.zone trash
  return a.zone deck == before.drop 3 && (aTrash.take 3).map (fun id =>
      (a.obj? id).bind (·.formerId)) == [some third, some second, some top] &&
    (b.zone deck).isEmpty && (b.zone trash).length == (short.zone trash).length + 2 &&
    events.contains (.burnedOut player) &&
    (d.zone deck).length == (c.zone deck).length - 1 && (d.zone trash).length == 1 &&
    d.pointsOf s.you == s.pointsOf s.you + 1 && d.handN player == s.handN player

-- Brittle Steel uses its printed cost from hand and is sent to the Trash. It uses its Flow
-- cost from the Trash, keeps its normal timing, and is banished when it leaves the Chain.
#guard vendettaCase fun s => do
  let (s, spell) ← put s s.me "VEN-003" .hand
  let (s, gear1) ← put s s.you "VEN-058" .base
  let (s, gear2) ← put s s.you "VEN-058" .base
  let fromHand ← cast (s.rich s.me) s.me spell ⟨2, [.fury]⟩ [gear1]
  let inTrash ← fromHand.firstOf s.me .trash "VEN-003"
  let funded := fromHand.rich s.me
  let flow : Action := ⟨.player s.me, .playCard inTrash ⟨4, [.fury]⟩ [gear2]⟩
  let (onChain, _) ← (step 100 funded flow).toOption
  let item ← (onChain.zone .chain).head?
  let (countered, _) := counterObjTo .hand onChain item
  let resolved := settleChain {} 12 onChain
  let closed := { funded with pending := [.chainPass s.me 0] }
  return (legalActions funded).contains flow &&
    !(legalActions closed).contains flow &&
    (cast funded s.me inTrash ⟨2, [.fury]⟩ [gear2]).isNone &&
    (fromHand.obj? gear1).isNone && (resolved.obj? gear2).isNone &&
    resolved.countIn s.me .banishment "VEN-003" == 1 &&
    countered.countIn s.me .banishment "VEN-003" == 1 &&
    (countered.obj? gear2).isSome

-- Steel Paws pays for the printed ability, gains Might, and cannot activate it twice while
-- Empowered. Disempowering it permits activating the ability again.
#guard vendettaCase fun s => do
  let (s, paws) ← put s s.me "VEN-043" .base
  let card ← s.cardDef? paws
  let idx := card.fullAbilities.findIdx (fun a =>
    match a with | .activated .. => true | _ => false)
  let a ← activate s s.me paws idx [] ⟨7, []⟩
  let b := (disempowerObj a paws).1
  let c ← activate b s.me paws idx [] ⟨7, []⟩
  let (left, moved) ← moveObj c paws (.player s.me .hand)
  return a.mightNow paws == (s.mightNow paws).map (· + 7) &&
    (activate s s.me paws idx [] ⟨6, []⟩).isNone &&
    (activate a s.me paws idx [] ⟨7, []⟩).isNone &&
    b.mightNow paws == s.mightNow paws && c.mightNow paws == a.mightNow paws &&
    (left.obj? moved).any (·.empowerCount == 0)

-- Rage Amplifier can Empower a Gear; its bonus rises from +1 to +2 only for friendly units.
#guard vendettaCase fun s => do
  let (s, friendly) ← put s s.me "OGN-088" .base
  let (s, enemy) ← put s s.you "OGN-088" .base
  let (s, amplifier) ← put s s.me "VEN-018" .base
  let a ← activate s s.me amplifier 2 [] ⟨6, [.fury]⟩
  return s.mightNow friendly == some 9 && a.mightNow friendly == some 10 &&
    s.mightNow enemy == some 8 && a.mightNow enemy == some 8

-- Lacerate checks Might after stripping Empowered. A Solari Sunhawk drops from 4 to 3 Might.
#guard vendettaCase fun s => do
  let (s, spell) ← put s s.me "VEN-127" .trash
  let (s, hawk) ← put s s.you "VEN-122" .base
  let (s, hunter) ← put s s.you "VEN-070" .base
  let s := (empowerObj s.you (empowerObj s.you s hawk).1 hunter).1
  let a ← cast (s.rich s.me) s.me spell ⟨4, [.order, .order]⟩ [hawk]
  let b ← cast (s.rich s.me) s.me spell ⟨4, [.order, .order]⟩ [hunter]
  return s.mightNow hawk == some 4 && a.countIn s.you .trash "VEN-122" == 1 &&
    b.mightNow hunter == some 4 && (b.obj? hunter).any (·.empowerCount == 0)

-- Shadow Assassin cares about the controller's Trash, and enters ready only if it has a copy.
#guard vendettaCase fun s => do
  let (s, card) ← put s s.me "VEN-013" .hand
  let (s, _) ← put s s.you "VEN-013" .trash
  let (copy, _) ← put s s.me "VEN-013" .trash
  let a ← play s s.me card
  let b ← play copy s.me card
  let u ← a.firstOf s.me .base "VEN-013"
  let v ← b.firstOf s.me .base "VEN-013"
  return a.tired u == some true && b.tired v == some false

-- Kayle can resolve Empower three times. Disempower removes one instance and its third-stack
-- keywords, and makes the activated ability available again.
#guard vendettaCase fun s => do
  let (s, kayle) ← put s s.me "VEN-134" .base
  let a ← activate s s.me kayle 2 [] ⟨3, []⟩
  let b ← activate a s.me kayle 2 [] ⟨3, []⟩
  let c ← activate b s.me kayle 2 [] ⟨3, []⟩
  let d := (disempowerObj c kayle).1
  let e ← activate d s.me kayle 2 [] ⟨3, []⟩
  return a.mightNow kayle == some 5 && b.mightNow kayle == some 7 &&
    c.mightNow kayle == some 9 && (c.keywordsNow kayle).any (·.keyword == .ganking) &&
    (activate c s.me kayle 2 [] ⟨3, []⟩).isNone &&
    d.mightNow kayle == some 7 && !(d.keywordsNow kayle).any (·.keyword == .ganking) &&
    e.mightNow kayle == some 9

-- Questionable Tome Disempowers as a cost, before its draw goes on the Chain.
#guard vendettaCase fun s => do
  let (s, tome) ← put s s.me "VEN-054" .base
  let empowered ← activate s s.me tome 0
  let ready := (readyEffect empowered tome).1.rich s.me
  let draw : Action := ⟨.player s.me, .activate tome 1 ⟨1, []⟩ []⟩
  let (pending, _) ← (step 100 ready draw).toOption
  let resolved := settleChain {} 12 pending
  return !(legalActions (s.rich s.me)).contains draw &&
    (empowered.obj? tome).any (·.empowerCount == 1) &&
    (pending.obj? tome).any (·.empowerCount == 0) &&
    pending.handN s.me == s.handN s.me && resolved.handN s.me == s.handN s.me + 1

-- Noxian Emissary's dependent Deathknell checks Empowered immediately before the move to Trash.
#guard vendettaCase fun s => do
  let (s, emissary) ← put s s.me "VEN-128" .base
  let ordinary := killObj s emissary
  let empowered := killObj (empowerObj s.me s emissary).1 emissary
  let a ← fire ordinary.1 ordinary.2
  let b ← fire empowered.1 empowered.2
  let dead ← b.firstOf s.me .trash "VEN-128"
  return a.countNamed s.me .base "Recruit" == 0 &&
    b.countNamed s.me .base "Recruit" == 2 &&
    (b.obj? dead).any (fun o => o.empowerCount == 0 && o.leftEmpowered)

-- Baccai Sandspinner pays two Energy with exactly four runes, and five with five runes.
-- Each state lists only the applicable Empower activation.
#guard vendettaCase fun s => do
  let currentRunes := s.zone (.player s.me .base)
  let clean := (applyEach (sendObj .runeDeck) s currentRunes).1
  let (s, unit) ← put clean s.me "VEN-001" .base
  let low ← (List.range 4).foldlM (fun st _ => (put st s.me "OGN-007" .base).map Prod.fst) s
  let (high, _) ← put low s.me "OGN-007" .base
  let low := low.rich s.me
  let high := high.rich s.me
  let cheap : Action := ⟨.player s.me, .activate unit 0 ⟨2, []⟩ []⟩
  let printed : Action := ⟨.player s.me, .activate unit 0 ⟨5, []⟩ []⟩
  return (legalActions low).contains cheap && !(legalActions low).contains printed &&
    !(legalActions high).contains cheap && (legalActions high).contains printed

-- Stargazer applies the minimum only to its controller's Flow spell from the Trash.
#guard vendettaCase fun s => do
  let (s, _) ← put s s.me "VEN-098" .base
  let (s, ownHand) ← put s s.me "VEN-049" .hand
  let (s, ownTrash) ← put s s.me "VEN-049" .trash
  let (s, enemyTrash) ← put s s.you "VEN-049" .trash
  let d ← s.cardDef? ownTrash
  return (s.directCost s.me ownTrash d).map (·.energy) == some 1 &&
    (s.directCost s.me ownHand d).map (·.energy) == some 2 &&
    (s.directCost s.you enemyTrash d).map (·.energy) == some 2

-- Decree of Rage stays on the Chain when countered; an ordinary spell is removed.
#guard vendettaCase fun s => do
  let (s, rage) ← onChain s s.me "VEN-015"
  let (s, ordinary) ← onChain s s.me "VEN-049"
  let a := counterObj s rage
  let b := counterObj a.1 ordinary
  return (a.1.zone .chain).contains rage && a.2.isEmpty &&
    !(b.1.zone .chain).contains ordinary && (b.1.zone .chain).contains rage

-- Decree of Insight ignores Deflect even outside Heisho. Heisho waives the cost only for
-- things there, even if another target at the player's base still has Deflect.
#guard vendettaCase fun s => do
  let (s, heisho) ← putBf s s.me "VEN-158"
  let (s, there) ← putAt s s.you "SFD-112" heisho
  let (s, base) ← put s s.you "SFD-112" .base
  let (s, spell) ← put s s.me "VEN-061" .hand
  let funded := s.fund s.me 1
  let (after, _) ← (step 100 funded ⟨.player s.me, .playCard spell ⟨1, []⟩ [base]⟩).toOption
  return s.deflectOf there > 0 && s.deflectCost s.me [there, base] == s.deflectOf base &&
    s.deflectCost s.me [there] == 0 && (after.poolOf s.me).totalPower == 0 &&
    !(after.zone .chain).isEmpty

-- Sandstone Chimera limits the Channel Phase only while at a Battlefield.
#guard vendettaCase fun s => do
  let (s, _) ← put s s.me "VEN-036" .base
  let (t, _) ← putAt s s.you "VEN-036" s.bf0
  return s.channelCount == 2 && t.channelCount == 1 &&
    ({ t with turn := 2 } : GameState).channelCount == 1

-- Temporal Breach replays a non-token for its owner at its original Battlefield.
#guard vendettaCase fun s => do
  let (s, spell) ← put s s.me "VEN-066" .hand
  let (s, unit) ← putAt s s.you "OGN-088" s.bf0
  let s := s.modObj unit (fun o => { o with controller := s.me, damage := 2 })
  let result ← play s s.me spell [unit]
  let newId ← (result.unitsAtOf s.bf0 s.you).find? (fun u =>
    u != unit && (result.cardDef? u).any (·.id.code == "OGN-088"))
  return (result.obj? unit).isNone &&
    (result.obj? newId).any (fun o =>
      o.owner == s.you && o.controller == s.you && o.damage == 0 && o.loc == some s.bf0)

-- Twilight Shroud protects from enemy choices for this turn and still allows friendly choices.
#guard vendettaCase fun s => do
  let (s, shroud) ← put s s.me "VEN-031" .hand
  let (s, unit) ← put s s.me "OGN-051" .base
  let a ← play s s.me shroud [unit]
  let next := { a with turn := a.turn + 1 }
  return a.blocksChoice s.you unit && !(a.blocksChoice s.me unit) &&
    !(next.blocksChoice s.you unit) && a.mightNow unit == (s.mightNow unit).map (· + 1)

-- Akali's protection applies outside combat and stops at the Battlefield where she fights.
#guard vendettaCase fun s => do
  let (s, akali) ← putAt s s.me "VEN-038" s.bf0
  let combat := s.inCombatAt s.bf0 s.me
  return s.blocksChoice s.you akali && !(s.blocksChoice s.me akali) &&
    !(combat.blocksChoice s.you akali)

-- Shadows chooses units across Trashes, and the printed Deflect of a card in Trash is inactive.
#guard vendettaCase fun s => do
  let (s, spell) ← put s s.me "VEN-103" .hand
  let (s, ally) ← put s s.me "VEN-014" .trash
  let (s, enemy) ← put s s.you "VEN-043" .trash
  let (s, other) ← put s s.you "VEN-006" .trash
  let (s, nonUnit) ← put s s.you "VEN-003" .trash
  let (s, inHand) ← put s s.you "VEN-014" .hand
  let (s, onBoard) ← put s s.me "VEN-014" .base
  let s := s.fund s.me 3 0 0 0 0 1
  let pay : RunePool.Payment := ⟨3, [.chaos]⟩
  let targets := [ally, enemy]
  let action : Action := ⟨.player s.me, .playCard spell pay targets⟩
  let (onChain, _) ← (step 100 s action).toOption
  let both := settleChain {} 12 onChain
  let one := settleChain {} 12 (sendObj .banishment onChain ally).1
  let none ← cast s s.me spell pay []
  return (legalActions s).contains action &&
    both.countIn s.me .hand "VEN-014" == 1 && both.countIn s.you .hand "VEN-043" == 1 &&
    one.countIn s.me .hand "VEN-014" == 0 && one.countIn s.you .hand "VEN-043" == 1 &&
    none.countIn s.me .trash "VEN-014" == 1 &&
    [[nonUnit], [inHand], [onBoard], [ally, enemy, other]].all (fun ts =>
      !(legalActions s).contains ⟨.player s.me, .playCard spell pay ts⟩ &&
        (cast s s.me spell pay ts).isNone)

-- The Matriarch chooses her own affordable Trash unit when the Empower trigger is put on Chain.
#guard vendettaCase fun s => do
  let (s, matriarch) ← put s s.me "VEN-104" .base
  let (s, eligible) ← put s s.me "VEN-014" .trash
  let (s, _) ← put s s.me "VEN-006" .trash
  let (s, _) ← put s s.me "OGN-150" .trash
  let (s, _) ← put s s.me "VEN-003" .trash
  let (s, _) ← put s s.you "VEN-014" .trash
  let (empowered, events) := empowerObj s.me s matriarch
  let targets ← firePicks empowered events
  let chosen ← fire empowered events { pick := (· == [eligible]) }
  let declined ← fire empowered events { pick := List.isEmpty }
  let unit ← chosen.firstOf s.me .base "VEN-014"
  return targets == [eligible] && (chosen.obj? eligible).isNone &&
    chosen.tired unit == some true && chosen.countIn s.you .trash "VEN-014" == 1 &&
    (declined.obj? eligible).isSome && declined.countIn s.me .base "VEN-014" == 0

-- The Monk targets a Unit and picks the Trash card while resolving, only if the extra cost was paid.
#guard vendettaCase fun s => do
  let (s, monk) ← put s s.me "VEN-101" .hand
  let (s, unit) ← put s s.me "VEN-006" .base
  let (s, card) ← put s s.you "VEN-003" .trash
  let s := s.rich s.me
  let says : Says := { pick := (· == [unit]), obj := (· == card) }
  let paid ← cast s s.me monk ⟨3, []⟩ [] says
  let unpaid ← cast s s.me monk ⟨2, []⟩ [] says
  let played ← paid.firstOf s.me .base "VEN-101"
  return paid.tired played == some true && paid.countIn s.you .banishment "VEN-003" == 1 &&
    (paid.keywordsNow unit).contains ⟨.assault, .amount 2⟩ &&
    unpaid.countIn s.you .trash "VEN-003" == 1 &&
    !(unpaid.keywordsNow unit).contains ⟨.assault, .amount 2⟩

-- The Prefect may banish itself to banish the opposing Gear that caused the trigger.
#guard vendettaCase fun s => do
  let (s, prefect) ← put s s.me "VEN-102" .base
  let (s, gear) ← put s s.you "VEN-058" .base
  let (s, friendly) ← put s s.me "VEN-058" .base
  let chosen ← fire s [.played s.you gear]
  let declined ← fire s [.played s.you gear] { yes := false }
  let ownPlay ← fire s [.played s.me friendly]
  return chosen.countIn s.me .banishment "VEN-102" == 1 &&
    chosen.countIn s.you .banishment "VEN-058" == 1 &&
    (declined.obj? prefect).isSome && (declined.obj? gear).isSome &&
    (ownPlay.obj? prefect).isSome && (ownPlay.obj? friendly).isSome

-- Spiderling counts other friendly units with its own name at the same location.
#guard vendettaCase fun s => do
  let (s, spiderling) ← putAt s s.me "VEN-097" s.bf0
  let (s, sibling) ← putAt s s.me "VEN-097" s.bf0
  let (s, otherPlace) ← put s s.me "VEN-097" .base
  let (s, enemy) ← putAt s s.you "VEN-097" s.bf0
  let (s, _) ← putAt s s.me "VEN-014" s.bf0
  return s.mightNow spiderling == some 2 && s.mightNow sibling == some 2 &&
    s.mightNow otherPlace == some 1 && s.mightNow enemy == some 1

-- Kennen burns two cards on play and grants Flow on conquering only to a spell in his own Trash.
#guard vendettaCase fun s => do
  let (s, kennen) ← putAt s s.me "VEN-113" s.bf0
  let (s, spell) ← put s s.me "SFD-003" .trash
  let (s, _) ← put s s.me "VEN-014" .trash
  let (s, _) ← put s s.you "SFD-003" .trash
  let (s, _) ← put s s.me "SFD-003" .hand
  let s := s.rich s.me
  let played ← fire s [.played s.me kennen]
  let ev := Event.scored s.me s.bf0 true
  let targets ← firePicks s [ev]
  let granted ← fire s [ev] { pick := (· == [spell]) }
  let granted := { granted with pending := [.priority s.me] }
  let flowed : Action := ⟨.player s.me, .playCard spell ⟨1, []⟩ [kennen]⟩
  let (casting, _) ← (step 100 granted flowed).toOption
  let final := settleChain {} 12 casting
  let expired := (advance 100 { granted with pending := [.phase .ending] } []).toOption
  return (played.zone (.player s.me .mainDeck)).length + 2 ==
      (s.zone (.player s.me .mainDeck)).length && targets == [spell] &&
    !(legalActions s).contains flowed && (legalActions granted).contains flowed &&
    final.countIn s.me .banishment "SFD-003" == 1 &&
    expired.any (fun r => !(r.1.playSources s.me).contains spell)

-- Printed Flow and Kennen's grant coexist; Stargazer discounts both of the adjusted costs.
#guard vendettaCase fun s => do
  let (s, kennen) ← putAt s s.me "VEN-113" s.bf0
  let (s, spell) ← put s s.me "VEN-003" .trash
  let (s, _) ← put s s.me "VEN-098" .base
  let (s, gear) ← put s s.you "VEN-058" .base
  let s := s.rich s.me
  let granted ← fire s [.scored s.me s.bf0 true] { pick := (· == [spell]) }
  let granted := { granted with pending := [.priority s.me] }
  let printed : Action := ⟨.player s.me, .playCard spell ⟨2, [.fury]⟩ [gear]
    (some ⟨4, [.domain .fury]⟩)⟩
  let grantedCost : Action := ⟨.player s.me, .playCard spell ⟨1, [.fury]⟩ [gear]
    (some ⟨2, [.domain .fury]⟩)⟩
  return (legalActions granted).contains printed && (legalActions granted).contains grantedCost &&
    (step 100 granted printed).isOk && (step 100 granted grantedCost).isOk &&
    (granted.obj? kennen).isSome

-- A payment can match two Flow costs with different Repeat outcomes. The action distinguishes them.
#guard vendettaCase fun s => do
  let (s, spell) ← put s s.me "SFD-003" .trash
  let (s, unit) ← put s s.me "VEN-014" .base
  let low : Cost := ⟨1, []⟩
  let high : Cost := ⟨2, []⟩
  let s := (addTempKw ⟨.flow, .cost high⟩ .turn (s.rich s.me) spell).1
  let s := (addTempKw ⟨.flow, .cost low⟩ .turn s spell).1
  let action (flow : Option Cost) : Action := ⟨.player s.me, .playCard spell ⟨2, []⟩ [unit] flow⟩
  let (a, _) ← (step 100 s (action (some low))).toOption
  let (b, _) ← (step 100 s (action (some high))).toOption
  let aSpell ← (a.zone .chain).head?
  let bSpell ← (b.zone .chain).head?
  let nA := (a.obj? aSpell).map (·.extraPaid)
  let nB := (b.obj? bSpell).map (·.extraPaid)
  let showdown := { s with pending := [.showdown s.bf0 s.me 0] }
  let reaction := { s with pending := [.chainPass s.me 0] }
  return (legalActions s).contains (action (some low)) &&
    (legalActions s).contains (action (some high)) &&
    (legalActions showdown).contains (action (some low)) &&
    (step 100 showdown (action (some low))).isOk &&
    !(legalActions reaction).contains (action (some low)) &&
    !(step 100 reaction (action (some low))).isOk &&
    !(step 100 s (action none)).isOk && nA == some 1 && nB == some 0

-- Lightning Rush draws any of the looked-at cards or none, and puts only the others in Trash.
#guard vendettaCase fun s => do
  let (s, spell) ← put s s.me "VEN-156" .hand
  let deck := Zone.player s.me .mainDeck
  let before := s.zone deck
  let picked ← before[1]?
  let withDraw ← play s s.me spell [] { obj := (· == picked) }
  let skipped ← play s s.me spell [] { yes := false }
  let short := (applyEach (sendObj .banishment) s (before.drop 2)).1
  let short := (sendObj .trash short spell).1
  let trashSpell ← short.firstOf s.me .trash "VEN-156"
  let flowed ← cast (short.rich s.me) s.me trashSpell ⟨2, [.chaos]⟩ [] { obj := (· == picked) }
  let former (t : GameState) (z : ZoneKind) :=
    (t.zone (.player s.me z)).filterMap (fun id => (t.obj? id).bind (·.formerId))
  return withDraw.zone deck == before.drop 3 && skipped.zone deck == before.drop 3 &&
    (former withDraw .hand).contains picked && !(former withDraw .trash).contains picked &&
    (before.take 3).all ((former skipped .trash).contains ·) &&
    (flowed.zone deck).isEmpty && (former flowed .hand).contains picked &&
    (former flowed .trash).countP (fun id => before.contains id) == 1 &&
    flowed.countIn s.me .banishment "VEN-156" == 1

-- Crossing 10 triggers Brute once. Staying above 10 does not fire the ability again.
#guard vendettaCase fun s => do
  let (s, unit) ← put s s.me "VEN-092" .base
  let s := (addMightMod ⟨5, .turn⟩ s unit).1
  let crossed ← activate s s.me unit 0 [] ⟨1, []⟩
  let above ← activate crossed s.me unit 0 [] ⟨1, []⟩
  let down := (addMightMod ⟨-2, .turn⟩ above unit).1
  let crossedAgain ← activate down s.me unit 0 [] ⟨1, []⟩
  let fired (t : GameState) := (t.obj? unit).map (fun o => o.used.count 1)
  return s.mightNow unit == some 9 && crossed.mightNow unit == some 10 &&
    (crossed.obj? unit).any (·.empowerCount == 1) &&
    (crossed.keywordsNow unit).any (·.keyword == .deflect) &&
    (crossed.keywordsNow unit).any (·.keyword == .ganking) &&
    fired crossed == some 1 && fired above == some 1 && fired crossedAgain == some 2 &&
    (crossedAgain.obj? unit).any (·.empowerCount == 1)

-- Entering already at the threshold does not count as a crossing.
#guard vendettaCase fun s => do
  let (s, unit) ← put s s.me "VEN-092" .hand
  let cards := s.cards.cards.map (fun d =>
    if d.id.code == "VEN-092" then { d with might := some 10 } else d)
  let entered ← play { s with cards := { cards } } s.me unit
  let renekton ← entered.firstOf s.me .base "VEN-092"
  return entered.mightNow renekton == some 10 &&
    (entered.obj? renekton).any (·.empowerCount == 0)

-- A Standard Move can cross the threshold by entering a Battlefield with a passive Might bonus.
#guard vendettaCase fun s => do
  let (s, camp) ← putBf s s.me "OGN-294"
  let (s, unit) ← put s s.me "VEN-092" .base
  let s := (addMightMod ⟨5, .turn⟩ (s.control s.me camp) unit).1
  let (moved, _) ← (step 100 s ⟨.player s.me, .standardMove unit (.battlefield camp)⟩).toOption
  let result := settleChain {} 12 moved
  return result.mightNow unit == some 10 && (result.obj? unit).any (fun o =>
    o.loc == some camp && o.empowerCount == 1)

-- Morgana reads the target's marked damage when the ability resolves.
#guard vendettaCase fun s => do
  let (s, morgana) ← put s s.me "VEN-017" .hand
  let (s, target) ← put s s.you "OGN-088" .base
  let (s, other) ← put s s.you "OGN-088" .base
  let marked := s.modObj target (fun o => { o with damage := 2 })
  let hit ← play marked s.me morgana [] { pick := (· == [target]) }
  let zero ← play s s.me morgana [] { pick := (· == [target]) }
  return (hit.obj? target).any (·.damage == 4) && (hit.obj? other).any (·.damage == 0) &&
    (zero.obj? target).any (·.damage == 0)

-- A controlled Battlefield with exactly two Units makes Keeper payable with only 3 Energy.
#guard vendettaCase fun s => do
  let (s, keeper) ← put s s.me "VEN-119" .hand
  let camp := s.bf0
  let (s, _) ← putAt s s.me "VEN-014" camp
  let (two, _) ← putAt s s.me "VEN-014" camp
  let (three, _) ← putAt two s.me "VEN-014" camp
  let full : Cost := ⟨5, [.domain .order]⟩
  let cost (t : GameState) := (t.cardDef? keeper).bind (t.effCost s.me keeper)
  let funded := (two.control s.me camp).fund s.me 3
  let playKeeper : Action := ⟨.player s.me, .playCard keeper ⟨3, []⟩ []⟩
  return cost (s.control s.me camp) == some full &&
    cost (two.control s.you camp) == some full && cost funded == some ⟨3, []⟩ &&
    cost (three.control s.me camp) == some full &&
    (legalActions funded).contains playKeeper && (step 100 funded playKeeper).isOk

-- Punching Poro pays with a hand card before Empower resolves on the Chain.
#guard vendettaCase fun s => do
  let (s, poro) ← put s s.me "VEN-007" .base
  let (s, card) ← put s s.me "VEN-014" .hand
  let (s, foe) ← put s s.you "VEN-014" .hand
  let action (ds : List ObjId) : Action := ⟨.player s.me, .activate poro 0 ⟨0, []⟩ [] ds⟩
  let (onChain, es) ← (step 100 s (action [card])).toOption
  let discarded ← onChain.firstOf s.me .trash "VEN-014"
  let done := settleChain {} 12 onChain
  return (legalActions s).contains (action [card]) &&
    !(step 100 s (action [])).isOk && !(step 100 s (action [foe])).isOk &&
    es.contains (.discarded s.me discarded true) &&
    !es.contains (.chosenByAbility s.me card) &&
    (onChain.obj? card).isNone && onChain.mightNow poro == some 2 &&
    done.mightNow poro == some 3 && !(step 100 done (action [card])).isOk

-- Sky Cruiser requires a Gear in its own hand and a Unit on a Battlefield.
#guard vendettaCase fun s => do
  let (s, cruiser) ← put s s.me "VEN-060" .base
  let (s, gear) ← put s s.me "VEN-058" .hand
  let (s, wrong) ← put s s.me "VEN-014" .hand
  let (s, victim) ← putAt s s.you "OGN-088" s.bf0
  let (s, baseUnit) ← put s s.you "OGN-088" .base
  let s := s.fund s.me 1
  let action (target discard : ObjId) : Action :=
    ⟨.player s.me, .activate cruiser 0 ⟨1, []⟩ [target] [discard]⟩
  let (onChain, _) ← (step 100 s (action victim gear)).toOption
  let item ← (onChain.zone .chain).head?
  let done := settleChain {} 12 onChain
  return (legalActions s).contains (action victim gear) &&
    !(legalActions s).contains (action victim wrong) &&
    !(step 100 s (action victim wrong)).isOk && !(step 100 s (action baseUnit gear)).isOk &&
    onChain.countIn s.me .trash "VEN-058" == 1 && onChain.tired cruiser == some true &&
    (onChain.poolOf s.me).energy == 0 && (onChain.obj? item).any (·.targets == [victim]) &&
    (done.obj? victim).any (·.damage == 4)

-- Mel needs a Spell as payment. Her Empower trigger banishes only a small enemy on a Battlefield.
#guard vendettaCase fun s => do
  let (s, mel) ← put s s.me "VEN-110" .base
  let (s, spell) ← put s s.me "VEN-003" .hand
  let (s, gear) ← put s s.me "VEN-058" .hand
  let (s, enemy) ← putAt s s.you "VEN-014" s.bf0
  let (s, big) ← putAt s s.you "OGN-088" s.bf0
  let (s, friendly) ← putAt s s.me "VEN-014" s.bf0
  let action (d : ObjId) : Action := ⟨.player s.me, .activate mel 0 ⟨0, []⟩ [] [d]⟩
  let (onChain, _) ← (step 100 s (action spell)).toOption
  let opts ← firePicks s [.empowered s.me mel]
  let done := settleChain { pick := (· == [enemy]) } 14 onChain
  return opts == [enemy] && !(step 100 s (action gear)).isOk &&
    onChain.countIn s.me .trash "VEN-003" == 1 && done.countIn s.you .banishment "VEN-014" == 1 &&
    (done.obj? big).isSome && (done.obj? friendly).isSome &&
    (done.obj? mel).any (·.empowerCount == 1)

-- Forgotten Relic first burns without targets. The reflexive ability has separate
-- priority and still knows the Might if the source and the burned card both leave.
#guard vendettaCase fun s => do
  let (s, relic) ← put s s.me "VEN-108" .hand
  let (s, target) ← put s s.me "OGN-088" .base
  let (s, enemy) ← put s s.you "OGN-088" .base
  let (s, top) ← put s s.me "OGN-001" .mainDeck
  let p := s.me
  let q := s.you
  let code := cid "VEN-108"
  let pass (who : PlayerId) : Action := ⟨.player who, .pass⟩
  let pick (u : ObjId) : Action := ⟨.player p, .putTrigger 0 [u]⟩
  let (first, _) ← (step 100 (s.rich p) ⟨.player p, .playCard relic ⟨5, []⟩ []⟩).toOption
  let source ← first.firstOf p .base "VEN-108"
  let firstItem ← (first.zone .chain).head?
  let withoutSource := (sendObj .trash first source).1
  let (passed, _) ← (step 100 withoutSource (pass p)).toOption
  let (waiting, es) ← (step 100 passed (pass q)).toOption
  let burned ← waiting.firstOf p .trash "OGN-001"
  let (second, _) ← (step 100 waiting (pick target)).toOption
  let secondItem ← (second.zone .chain).head?
  let (passedAgain, _) ← (step 100 (sendObj .banishment second burned).1 (pass p)).toOption
  let (done, _) ← (step 100 passedAgain (pass q)).toOption
  return (first.obj? firstItem).any (fun o =>
      o.kind == .chainAbility code 0 source && o.targets.isEmpty) &&
    (first.zone (.player p .mainDeck)).head? == some top &&
    (waiting.zone .chain).isEmpty && waiting.mightNow target == s.mightNow target &&
    (legalActions waiting).contains (pick target) && !(legalActions waiting).contains (pick enemy) &&
    es.contains (.burnedUnitFor p source code 2 burned 5) &&
    (second.obj? secondItem).any (fun o =>
      o.kind == .chainAbility code 2 source && o.eventAmount == some 5 && o.targets == [target]) &&
    (legalActions passedAgain).contains (pass q) &&
    done.mightNow target == (s.mightNow target).map (· + 5)

-- The Beginning Phase burn belongs to the controller. Other effects' burns and burning a
-- non-Unit have no reflexive trigger. Burning after Burn Out still uses the linked instruction.
#guard vendettaCase fun s => do
  let (s, relic) ← put s s.me "VEN-108" .base
  let (s, target) ← put s s.me "OGN-088" .base
  let (s, top) ← put s s.me "OGN-001" .mainDeck
  let p := s.me
  let q := s.you
  let deck := Zone.player p .mainDeck
  let trash := Zone.player p .trash
  let phase := Event.phaseStarted p .beginning
  let otherPhase ← fire s [.phaseStarted q .beginning]
  let (otherBurn, _, otherEvents) := burnEffect s p relic {} .you (.const 1) .nil
  let unlinked ← fire otherBurn otherEvents
  let normal ← fire s [phase]
  let (gearDeck, gear) ← put s p "VEN-087" .mainDeck
  let gearBurned ← fire gearDeck [phase]
  let (unitGearDeck, _) ← put s p "VEN-058" .mainDeck
  let unitGearBurned ← fire unitGearDeck [phase]
  let empty := (applyEach (sendObj .banishment) s (s.zone deck)).1
  let (empty, refill) ← put empty p "OGN-001" .trash
  let awaiting ← fire empty [phase]
  let order := refill :: (awaiting.zone trash).filter (· != refill)
  let (shuffled, _) ← (step 100 awaiting ⟨.chance, .arrange order⟩).toOption
  let (afterOut, events) ← (step 100 shuffled ⟨.player p, .burnOutTarget q⟩).toOption
  let done := settleChain {} 12 afterOut
  return (otherPhase.zone deck).head? == some top &&
    (unlinked.obj? top).isNone && unlinked.mightNow target == s.mightNow target &&
    normal.mightNow target == (s.mightNow target).map (· + 5) &&
    (gearBurned.obj? gear).isNone && gearBurned.countIn p .trash "VEN-087" == 1 &&
    gearBurned.mightNow target == s.mightNow target &&
    unitGearBurned.mightNow target == (s.mightNow target).map (· + 2) &&
    events.any (fun e => match e with | .burnedUnitFor _ _ _ _ _ 5 => true | _ => false) &&
    done.mightNow target == (s.mightNow target).map (· + 5)

-- Pakaa's Standard Move reveals and draws a Unit, even if that card is also a Gear.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, camp) ← putBf s p "VEN-162"
  let (s, pakaa) ← putAt (s.control p camp) p "VEN-033" camp
  let (s, top) ← put s p "VEN-058" .mainDeck
  let (moved, _) ← (step 100 s ⟨.player p, .standardMove pakaa .base⟩).toOption
  let (passed, _) ← (step 100 moved ⟨.player p, .pass⟩).toOption
  let (done, events) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let revealed := Event.revealed p top
  let drew := Event.drew p
  return events.contains revealed && events.contains drew &&
    events.idxOf revealed < events.idxOf drew && done.countIn p .hand "VEN-058" == 1 &&
    done.mightNow pakaa == s.mightNow pakaa

-- Swapping to Base counts as moving, Recall does not. An empty deck cannot reveal a card
-- and never burns out while resolving this ability (CR 432.1.c).
#guard vendettaCase fun s => do
  let p := s.me
  let (s, camp) ← putBf s p "VEN-162"
  let (s, pakaa) ← putAt (s.control p camp) p "VEN-033" camp
  let (s, friend) ← put s p "OGN-088" .base
  let (s, gear) ← put s p "VEN-087" .mainDeck
  let swap (t : GameState) := applyPrim t p pakaa { slots := [.obj friend] }
    (.swapPlaces .self (.slot 0))
  let (moved, events) ← swap s
  let done ← fire moved events
  let (recalled, recallEvents) := recallFx false s pakaa
  let afterRecall ← fire recalled recallEvents
  let empty := (applyEach (sendObj .banishment) s (s.zone (.player p .mainDeck))).1
  let (movedEmpty, emptyEvents) ← swap empty
  let afterEmpty ← fire movedEmpty emptyEvents
  return events.count (.standardMoved pakaa none) == 1 &&
    events.contains (.movedByEffect p pakaa) &&
    done.countIn p .trash "VEN-087" == 1 && done.handN p == s.handN p &&
    done.mightNow pakaa == (s.mightNow pakaa).map (· + 2) &&
    (afterRecall.zone (.player p .mainDeck)).head? == some gear &&
    afterRecall.mightNow pakaa == s.mightNow pakaa &&
    (afterEmpty.zone .chain).isEmpty && (afterEmpty.zone (.player p .mainDeck)).isEmpty &&
    afterEmpty.mightNow pakaa == s.mightNow pakaa && afterEmpty.pointsOf s.you == s.pointsOf s.you

-- Ol' Poro is restricted on its player's first three turns, including extra turns.
-- Playing for free or for a reduced cost cannot bypass the restriction.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, poro) ← put (s.fund p 2) p "VEN-029" .hand
  let action : Action := ⟨.player p, .playCard poro ⟨2, []⟩ []⟩
  let next (t : GameState) :=
    { beginTurnStep t [] with phase := .main, pending := [.priority t.nextTurnPlayer] }
  let second := next { s with extraTurns := [p, p, p] }
  let third := next second
  let fourth := next third
  let opposing := next { third with extraTurns := [] }
  let (done, _) ← (step 100 fourth action).toOption
  let blocked := playReducedOne p 1 none third poro
  let offTurn := playFree p opposing poro
  return [s, second, third, fourth].map (·.turnsTaken p) == [1, 2, 3, 4] &&
    [s, second, third].all (fun t =>
      !(legalActions t).contains action && !(step 100 t action).isOk) &&
    (legalActions fourth).contains action && done.countIn p .base "VEN-029" == 1 &&
    ((playFree p third poro).1.zone (.player p .hand)).contains poro &&
    (blocked.1.zone (.player p .hand)).contains poro && blocked.2.isEmpty &&
    blocked.1.poolOf p == third.poolOf p &&
    opposing.active == some q && offTurn.1.countIn p .base "VEN-029" == 1

-- Otterpus replaces each Hold point with one draw, even when both players control it.
-- Both Battlefields remain scored, and the replacement expires after each player's second turn.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, _) ← put s p "VEN-053" .base
  let (s, _) ← put s q "VEN-053" .base
  let (s, a) ← putBf s p "VEN-162"
  let (s, b) ← putBf s p "VEN-160"
  let (s, _) ← putAt s p "OGN-088" a
  let (s, _) ← putAt s p "OGN-088" b
  let held := (s.control p a).control p b
  let queued := { held with extraTurns := [p, p] }
  let second := beginTurnStep queued []
  let third := beginTurnStep second []
  let beginning (t : GameState) :=
    (advance 100 { t with pending := [.phase .beginning] } []).toOption
  let (early, es) ← beginning second
  let (late, laterEvents) ← beginning third
  return early.handN p == second.handN p + 2 && early.pointsOf p == second.pointsOf p &&
    es.contains (.scoreDraw p a) && es.contains (.scoreDraw p b) &&
    [a, b].all (fun bf => (early.obj? bf).any (fun o => o.scored.contains p && !o.held.contains p)) &&
    late.handN p == third.handN p && late.pointsOf p == third.pointsOf p + 2 &&
    laterEvents.contains (.pointsGained p 2)

-- The Conquer replacement applies only on the scorer's turn and does not duplicate the
-- normal Final Point draw.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, _) ← put s q "VEN-053" .base
  let (s, bf) ← putBf s p "VEN-158"
  let (s, _) ← putAt s p "OGN-088" bf
  let pass (who : PlayerId) : Action := ⟨.player who, .pass⟩
  let contested := s.modObj bf (fun o => { o with contested := some p })
  let focused := { contested with pending := [.showdown bf p 0] }
  let (passed, _) ← (step 100 focused (pass p)).toOption
  let (done, es) ← (step 100 passed (pass q)).toOption
  let effectPoint ← applyPrim s p bf {} (.score .you (.const 1))
  let offTurn := scoreBf { s with active := some q } p bf true
  let final := scoreBf (s.gainPoints p (s.victoryScore - 1)) p bf true
  return done.controlOf bf == some p && done.pointsOf p == s.pointsOf p &&
    done.handN p == s.handN p + 1 && es.contains (.scoreDraw p bf) &&
    offTurn.1.pointsOf p == s.pointsOf p + 1 && offTurn.2.1.isEmpty &&
    effectPoint.1.pointsOf p == s.pointsOf p + 1 &&
    final.2.1 == [.draw p 1]

-- Dusk Rose Lab can kill Otterpus before the Scoring Step. The other Battlefield then gives
-- a point. Declining leaves Otterpus in play and both Battlefield points become draws.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, dusk) ← putBf s p "UNL-209"
  let (s, other) ← putBf s p "VEN-158"
  let (s, otter) ← putAt s p "VEN-053" dusk
  let (s, _) ← putAt s p "OGN-088" other
  let s := (s.control p dusk).control p other
  let (waiting, es) ← (advance 100 { s with pending := [.phase .beginning] } []).toOption
  let accepted := settleChain { yes := true } 20 waiting
  let declined := settleChain { yes := false } 20 waiting
  return es.contains (.phaseStarted p .beginning) &&
    es.all (fun e => match e with | .scored .. => false | _ => true) &&
    (waiting.obj? otter).isSome && accepted.countIn p .trash "VEN-053" == 1 &&
    accepted.controlOf dusk == none && accepted.pointsOf p == s.pointsOf p + 1 &&
    accepted.handN p == s.handN p + 1 &&
    (declined.obj? otter).isSome && declined.pointsOf p == s.pointsOf p &&
    declined.handN p == s.handN p + 2

-- The draw that replaced Shadow Temple's point is part of scoring. It takes the top card
-- before Shadow Temple's Hold trigger can burn the next three.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, temple) ← putBf s p "VEN-165"
  let (s, _) ← putAt s p "VEN-053" temple
  let (s, top) ← put s p "OGN-001" .mainDeck
  let s := s.control p temple
  let (waiting, es) ← (advance 100 { s with pending := [.phase .beginning] } []).toOption
  let basicDraw := Event.drew p
  let scored := Event.scored p temple false
  let done := settleChain {} 12 waiting
  return es.contains scored && es.contains basicDraw && es.idxOf scored < es.idxOf basicDraw &&
    (waiting.zone .chain).length == 1 && !(waiting.zone (.player p .mainDeck)).contains top &&
    waiting.countIn p .hand "OGN-001" == 1 && done.countIn p .hand "OGN-001" == 1 &&
    done.countIn p .trash "OGN-001" == 0 &&
    (done.zone (.player p .mainDeck)).length + 4 == (s.zone (.player p .mainDeck)).length

-- Kinkou Temple reads Tank after equipment and temporary grants, on both sides.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let outside := s.bf0
  let (s, temple) ← putBf s p "VEN-159"
  let (s, printed) ← putAt s q "VEN-118" temple
  let (s, elsewhere) ← putAt s q "VEN-118" outside
  let (s, equipped) ← putAt s q "OGN-088" temple
  let (s, temporary) ← putAt s p "OGN-088" temple
  let (s, shield) ← put s q "SFD-033" .base
  let (s, eye) ← put s p "VEN-147" .legendZone
  let geared := (attachTo equipped s shield).1
  let granted ← activate geared p eye 0 [temporary]
  let expired := granted.mapObjects endTurnObj
  let detached := (detachObj geared shield).1
  return s.mightNow printed == some 7 && s.mightNow elsewhere == some 6 &&
    s.mightNow equipped == some 8 && geared.mightNow equipped == some 10 &&
    (geared.mightTable.lookup equipped) == some 1 && detached.mightNow equipped == some 8 &&
    geared.mightNow temporary == some 8 && granted.mightNow temporary == some 9 &&
    expired.mightNow temporary == some 8

-- The surviving attackers are recalled before Combat ends. Both still participated; the
-- Witness on Base never did. Damage to the Poro this turn matters even after it is healed.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, bf) ← putBf s p "VEN-158"
  let (s, poro) ← putAt s p "VEN-024" bf
  let (s, witness) ← putAt s p "VEN-028" bf
  let (s, idle) ← put s p "VEN-028" .base
  let (s, defender) ← putAt s q "OGN-088" bf
  let s := ((s.control q bf).modObj bf (fun o => { o with contested := some p })).modObj
    defender (fun o => { o with stunned := true })
  let resolve (t : GameState) : Option (GameState × List Event) := do
    let (openCombat, _) ← (advance 100 { t with pending := [.cleanup, .priority p] } []).toOption
    let (first, _) ← (step 100 openCombat ⟨.player p, .pass⟩).toOption
    let (assigning, _) ← (step 100 first ⟨.player q, .pass⟩).toOption
    let (assigned, _) ← (step 100 assigning ⟨.player p, .assignPick defender⟩).toOption
    let (ended, events) ← (step 100 assigned ⟨.player p, .assignDone⟩).toOption
    return (settleChain {} 16 ended, events)
  let healed := (healOne 1 (dealObj 1 s poro).1 poro).1
  let prevented := (dealObj 1 (s.addTurnFxOn p poro .damagePrevented) poro).1
  let older := { healed with turn := healed.turn + 2 }
  let (fresh, es) ← resolve s
  let (hurt, _) ← resolve healed
  let (safe, _) ← resolve prevented
  let (previous, _) ← resolve older
  let isEnd : Event → Bool
    | .combatEnded where_ units =>
      where_ == bf && units.contains poro && units.contains witness && units.contains defender &&
        !units.contains idle
    | _ => false
  return es.any isEnd && es.idxOf (.recalled witness) < es.findIdx isEnd &&
    fresh.combat.isNone && fresh.locate witness == some (.player p .base) &&
    fresh.mightNow witness == some 4 && fresh.mightNow idle == some 2 &&
    fresh.handN p == s.handN p + 1 && hurt.handN p == s.handN p &&
    (hurt.obj? poro).any (fun o => o.damage == 0 && o.damagedTurn == some s.turn) &&
    safe.handN p == s.handN p + 1 && previous.handN p == s.handN p + 1

-- A defender joins during the Showdown, then Fight or Flight removes the only attacker.
-- The Combat still ends and both participants get their triggers.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, bf) ← putBf s p "VEN-158"
  let (s, witness) ← putAt s p "VEN-028" bf
  let (s, _) ← putAt s q "OGN-088" bf
  let (s, poro) ← put s q "VEN-024" .base
  let (s, arrive) ← put s q "VEN-034" .hand
  let (s, escape) ← put s p "OGN-168" .hand
  let s := (s.control q bf).modObj bf (fun o => { o with contested := some p })
  let (ready, es) ← (advance 100 { s with pending := [.cleanup, .priority p] } []).toOption
  let (defending, _) ← (step 100 ready ⟨.player p, .pass⟩).toOption
  let joined ← play defending q arrive [bf, poro]
  let (attacking, _) ← (step 100 joined ⟨.player q, .pass⟩).toOption
  let moved ← play attacking p escape [witness]
  let (passed, _) ← (step 100 moved ⟨.player p, .pass⟩).toOption
  let (ended, finish) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let done := settleChain {} 12 ended
  return es.contains (.combatStarted bf p) &&
    (ready.combat.any (fun c => !c.units.contains poro)) &&
    (joined.combat.any (fun c => c.units.contains poro)) &&
    moved.locate witness == some (.player p .base) &&
    (moved.combat.any (fun c => c.units.contains witness)) &&
    (finish.any (fun e => match e with
      | .combatEnded at_ units => at_ == bf && units.contains witness && units.contains poro
      | _ => false)) &&
    (finish.all (fun e => match e with | .damaged .. => false | _ => true)) &&
    ended.mightNow witness == some 2 && done.mightNow witness == some 4 &&
    done.handN q == moved.handN q + 1 && done.combat.isNone

/-- Start a contested Showdown and assign all Combat Damage when each side has one Unit. -/
meta def fightOneEach (s : GameState) (attacker defender : ObjId) :
    Option (GameState × List Event) := do
  let p := s.me
  let q := s.you
  let (ready, _) ← (advance 100 { s with pending := [.cleanup, .priority p] } []).toOption
  let (passed, _) ← (step 100 ready ⟨.player p, .pass⟩).toOption
  let (first, _) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let (picked, _) ← (step 100 first ⟨.player p, .assignPick defender⟩).toOption
  let (second, _) ← (step 100 picked ⟨.player p, .assignDone⟩).toOption
  let (counterPick, _) ← (step 100 second ⟨.player q, .assignPick attacker⟩).toOption
  (step 100 counterPick ⟨.player q, .assignDone⟩).toOption

-- Conquer triggers resolve before Combat ends. The temporary Might remains during the
-- Conquer trigger, but expires before the Witness's Empower trigger resolves.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, bf) ← putBf s p "VEN-162"
  let (s, witness) ← putAt s p "VEN-028" bf
  let (s, defender) ← putAt s q "OGN-139" bf
  let s := ((s.rich p).control q bf).modObj bf (fun o => { o with contested := some p })
  let s := s.modObj witness (fun o => { o with mightMods := [⟨2, .combat⟩] })
  let (conquered, events) ← fightOneEach s witness defender
  let item ← (conquered.zone .chain).head?
  let done := settleChain {} 16 conquered
  return events.contains (.scored p bf true) &&
    events.all (fun e => match e with | .combatEnded .. => false | _ => true) &&
    (conquered.obj? item).any (fun o => o.kind == .chainAbility (cid "VEN-162") 0 bf) &&
    (conquered.obj? witness).any (fun o => o.empowerCount == 0 && o.damage == 0) &&
    conquered.mightNow witness == some 4 && done.mightNow witness == some 4 &&
    (done.obj? witness).any (fun o => o.empowerCount == 1 && o.mightMods.isEmpty)

-- Kog'Maw's Deathknell kills the surviving attacker before the Combat result is determined.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, bf) ← putBf s p "VEN-158"
  let (s, witness) ← putAt s p "VEN-028" bf
  let (s, defender) ← putAt s q "OGN-190" bf
  let s := (s.control q bf).modObj bf (fun o => { o with contested := some p })
  let (waiting, events) ← fightOneEach s witness defender
  let item ← (waiting.zone .chain).head?
  let source ← waiting.obj? item
  let done := settleChain {} 16 waiting
  let deathknell := match source.kind with
    | .chainAbility card 0 dead => card == cid "OGN-190" && events.contains (.died dead q)
    | _ => false
  return deathknell &&
    events.all (fun e => match e with | .combatWon .. => false | _ => true) &&
    source.owner == q && waiting.controlOf bf == some q &&
    (waiting.obj? witness).any (fun o => o.loc == some bf && o.damage == 0) &&
    done.controlOf bf == none && done.pointsOf p == s.pointsOf p &&
    done.countIn p .trash "VEN-028" == s.countIn p .trash "VEN-028" + 1 && done.combat.isNone

-- A combat-win ability moves the last unit away. Control is determined after it resolves.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, bf) ← putBf s p "VEN-158"
  let (s, witness) ← putAt s p "VEN-028" bf
  let (s, defender) ← putAt s q "OGN-139" bf
  let card ← s.cardDef? witness
  let retreat := Ability.triggered (.onSelf .winCombat)
    (.of [] (.prim (.move .self .base))) .unlimited
  let card := { card with abilities := retreat :: card.abilities }
  let s := { s with cards := { s.cards with cards := card :: s.cards.cards } }
  let s := (s.control q bf).modObj bf (fun o => { o with contested := some p })
  let (waiting, events) ← fightOneEach s witness defender
  let item ← (waiting.zone .chain).head?
  let done := settleChain {} 16 waiting
  return events.contains (.combatWon bf p) && !events.contains (.scored p bf true) &&
    waiting.controlOf bf == some q && (waiting.obj? item).any (fun o =>
      o.kind == .chainAbility (cid "VEN-028") 0 witness) &&
    done.controlOf bf == none && done.pointsOf p == s.pointsOf p &&
    done.locate witness == some (.player p .base) && done.mightNow witness == some 4

-- Threshold of the Gray goes on the Chain once. In a three-player turn order the two
-- combatants gain Energy, even when the defender is not next in turn order.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let third : PlayerId := ⟨2⟩
  let mode := { s.config.mode with players := 3 }
  let s := { s with config := { s.config with mode := mode }, turnOrder := [p, third, q] }
  let (s, bf) ← putBf s q "VEN-166"
  let (s, _) ← putAt s p "OGN-088" bf
  let (s, defender) ← putAt s q "OGN-088" bf
  let s := (s.control q bf).modObj bf (fun o => { o with contested := some p })
  let setup (t : GameState) :=
    (advance 100 { t with pending := [.cleanup, .priority p] } []).toOption
  let (waiting, es) ← setup s
  let item ← (waiting.zone .chain).head?
  let (alone, noCombat) ← setup (sendObj .trash s defender).1
  let done := settleChain {} 12 waiting
  let energy (t : GameState) (r : PlayerId) := (t.poolOf r).energy
  return waiting.nextPlayer p == third && es.contains (.combatStarted bf p) &&
    waiting.zone .chain == [item] &&
    (waiting.obj? item).any (fun o =>
      o.owner == q && o.kind == .chainAbility (cid "VEN-166") 0 bf) &&
    energy waiting p == energy s p && energy waiting q == energy s q &&
    energy done p == energy s p + 1 && energy done q == energy s q + 1 &&
    energy done third == energy s third && alone.zone .chain == [] &&
    !noCombat.contains (.combatStarted bf p)

-- Fallen Feline leaves a window to react before a name is known. The named
-- spell can be cast by its controller, and a recall to Base lifts the restriction.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, feline) ← put s p "VEN-132" .hand
  let (s, enemySpell) ← put s q "OGN-058" .hand
  let (s, ownSpell) ← put s p "OGN-058" .hand
  let (s, spare) ← put s q "OGN-047" .hand
  let s := ((s.control p field).rich p).rich q
  let (onChain, _) ← (step 100 s ⟨.player p, .playCard feline ⟨2, [.order]⟩ [field]⟩).toOption
  let cat ← (onChain.zone .battlefieldZone).find? (fun u => (onChain.cardDef? u).any (·.id == cid "VEN-132"))
  let .chainPass a _ :: _ := onChain.pending | none
  let (beforeName, _) ← (step 100 onChain ⟨.player a, .pass⟩).toOption
  let .chainPass b _ :: _ := beforeName.pending | none
  let (choice, _) ← (step 100 beforeName ⟨.player b, .pass⟩).toOption
  let .nameCard owner source .. :: _ := choice.pending | none
  let cast (player : PlayerId) (card : ObjId) : Action :=
    ⟨.player player, .playCard card ⟨2, []⟩ [cat]⟩
  let named : Action := ⟨.player p, .nameCard (cid "OGN-058")⟩
  let (blocked, es) ← (step 100 choice named).toOption
  let opponent (t : GameState) := { t with active := some q, pending := [.priority q] }
  let mine := { blocked with active := some p, pending := [.priority p] }
  let returned := (recallFx false blocked cat).1
  let (gone, newCat) ← moveObj blocked cat (.player p .trash)
  return b == q && owner == p && source == cat &&
    (legalActions beforeName).contains (cast q enemySpell) &&
    !(legalActions beforeName).contains named &&
    (legalActions choice).contains named &&
    !(legalActions choice).contains ⟨.player q, named.kind⟩ &&
    !(legalActions choice).contains ⟨.player p, .nameCard (cid "VEN-132")⟩ &&
    !(legalActions choice).contains ⟨.player p, .nameCard (cid "UNKNOWN")⟩ &&
    es.contains (.namedCard p cat (cid "OGN-058")) &&
    (blocked.obj? cat).any (·.namedCard == some (cid "OGN-058")) &&
    !(legalActions (opponent blocked)).contains (cast q enemySpell) &&
    (legalActions (opponent blocked)).any (fun a => match a.kind with
      | .playCard c .. => c == spare
      | _ => false) &&
    (legalActions mine).contains (cast p ownSpell) &&
    (returned.obj? cat).any (·.namedCard == some (cid "OGN-058")) &&
    (legalActions (opponent returned)).contains (cast q enemySpell) &&
    (gone.obj? newCat).any (·.namedCard.isNone)

-- An existing spell on the Chain still resolves once its name is prohibited.
-- The card's restriction also prevents playing a named spell from Hidden.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, cat) ← putAt s p "VEN-132" s.bf0
  let (s, spell) ← onChain s q "OGN-058"
  let (s, hidden) ← put s q "VEN-066" .hidden
  let s := (s.modObj spell (fun o => { o with targets := [cat] })).modObj hidden
    (fun o => { o with hiddenAt := some s.bf0, hiddenTurn := some 0 })
  let pending : List Frame := [.run p cat {} (.ofList [.nameCard .spell]), .chainPass q 0, .priority q]
  let s := { (s.control p s.bf0).rich q with pending }
  let (choice, _) ← (advance 100 s []).toOption
  let (named, _) ← (step 100 choice ⟨.player p, .nameCard (cid "OGN-058")⟩).toOption
  let finished := settleChain {} 12 named
  let hiddenName := named.modObj cat (fun o => { o with namedCard := some (cid "VEN-066") })
  return (named.zone .chain).contains spell && named.mightNow cat == some 3 &&
    finished.mightNow cat == some 5 && !(finished.zone .chain).contains spell &&
    named.abilityZoneOk q hidden 1 && !hiddenName.abilityZoneOk q hidden 1

-- A format's eligible releases and bans constrain naming in Constructed.
#guard vendettaCase fun s => do
  let fakeToken := { RiftboundCards.Vendetta.VEN_132 with id := cid "VEN-T99", types := [.spell] }
  let restricted : LegalityEnv := ⟨[⟨"OGN"⟩], [cid "OGN-047"]⟩
  let config := { s.config with ruleSet := .tournament .constructed, formatLegality := some restricted }
  let s := { s with cards := ⟨fakeToken :: s.cards.cards⟩, config }
  let options := s.nameableCards .spell
  return options.contains (cid "OGN-058") && !options.contains (cid "OGN-047") &&
    !options.contains (cid "VEN-066") && !options.contains (cid "VEN-T99")

-- Dominus uses the Unit's Might at resolution and grants a normal activation.
-- The chosen Power is paid when that activation is put on the Chain.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, dominus) ← put s p "VEN-142" .hand
  let (s, unit) ← put s p "VEN-014" .base
  let d ← s.cardDef? unit
  let s := (s.tire unit).fund p 4 1 0 0 0 0 1
  let (casting, _) ← (step 100 s ⟨.player p, .playCard dominus ⟨4, []⟩ [unit]⟩).toOption
  let modified := casting.modObj unit (fun o => { o with buffed := true })
  let boosted := settleChain {} 10 modified
  let grant : AbilityGrant := ⟨cid "VEN-142", 0⟩
  let idx := d.fullAbilities.length
  let payment : RunePool.Payment := ⟨0, [.fury, .order]⟩
  let use : Action := ⟨.player p, .activate unit idx payment []⟩
  let (queued, es) ← (step 100 boosted use).toOption
  let item ← (queued.zone .chain).head?
  let activated := settleChain {} 10 queued
  let sameTurn := boosted.modObj unit (fun o => { o with buffed := false })
  let expired := sameTurn.mapObjects endTurnObj
  let gone := sendObj .hand queued unit
  let new ← gone.2.findSome? (fun e => match e with
    | .moved _ moved _ => some moved
    | _ => none)
  let afterMove := settleChain {} 10 gone.1
  let pendingWithoutGrant := queued.modObj unit (fun o => { o with tempActivations := [] })
  return (legalActions boosted).contains use && boosted.mightNow unit == some 6 &&
    (boosted.obj? unit).any (·.tempActivations == [grant]) &&
    ((boosted.activationAt unit 0).map Prod.fst) == (d.fullAbilities[0]?.map (fun _ => none)) &&
    !activatable boosted q unit idx payment [] true &&
    !activatable boosted p unit idx ⟨0, [.fury, .fury]⟩ [] true &&
    !activatable boosted p unit idx payment [] false &&
    !activatableSD boosted p unit idx payment [] &&
    (queued.poolOf p).fury == 0 && (queued.poolOf p).order == 0 &&
    es.contains (.activated p unit idx (some 0)) && queued.tired unit == some true &&
    (queued.obj? item).any (fun o =>
      o.kind == .chainAbility d.id idx unit && o.activationGrant == some grant) &&
    activated.tired unit == some false && (settleChain {} 10 pendingWithoutGrant).tired unit == some false &&
    sameTurn.mightNow unit == some 5 && expired.mightNow unit == some 2 &&
    !(legalActions expired).contains use && (afterMove.obj? new).any (·.tempActivations.isEmpty)

-- An opposing Unit is a legal target in a Showdown. A negative Might adds zero,
-- and the Unit's controller owns the newly granted activation.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "VEN-142" .hand
  let (s, target) ← putAt s q "VEN-014" s.bf0
  let (s, gear) ← put s p "VEN-073" .base
  let d ← s.cardDef? target
  let weakened := s.modObj target (fun o => { o with exhausted := true, mightMods := [⟨-4, .turn⟩] })
  let ready := ((weakened.control q s.bf0).rich p).rich q
  let showing := { ready with active := some q, pending := [.showdown s.bf0 p 0, .priority q] }
  let playOn (u : ObjId) : Action := ⟨.player p, .playCard spell ⟨4, []⟩ [u]⟩
  let (casting, _) ← (step 100 showing (playOn target)).toOption
  let resolved := settleChain {} 10 casting
  let shifted := sendObj .hand casting target
  let bounced := settleChain {} 10 shifted.1
  let pay : RunePool.Payment := ⟨0, [.fury, .order]⟩
  return !(legalActions showing).contains (playOn gear) && resolved.mightNow target == some (-2) &&
    activatable resolved q target d.fullAbilities.length pay [] true &&
    !activatable resolved p target d.fullAbilities.length pay [] true &&
    !activatableSD resolved q target d.fullAbilities.length pay [] &&
    bounced.countIn q .hand "VEN-014" == 1 &&
    (bounced.zone (.player q .hand)).all (fun id => (bounced.obj? id).any (·.tempActivations.isEmpty))

-- Glowstone is Empowered with two Power. The second ability chooses its
-- recipient when finalized and pays Disempower and Exhaust before resolving.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, gear) ← put s p "VEN-133" .hand
  let (playing, _) ← (step 100 (s.rich p) ⟨.player p, .playCard gear ⟨2, []⟩ []⟩).toOption
  let current ← playing.firstOf p .base "VEN-133"
  let d ← playing.cardDef? current
  let empower ← (List.range d.fullAbilities.length).find? (fun i =>
    d.fullAbilities[i]?.any Ability.isEmpower)
  let gift (who : Option PlayerId) : Action :=
    ⟨.player p, .activate current 0 ⟨0, []⟩ [] [] who⟩
  let funded := playing.fund p 0 1 0 0 0 0 1
  let (empowering, _) ←
    (step 100 funded ⟨.player p, .activate current empower ⟨0, [.fury, .order]⟩ []⟩).toOption
  let empowered := settleChain {} 12 empowering
  let (sending, _) ← (step 100 empowered (gift (some q))).toOption
  let item ← (sending.zone .chain).head?
  let passed := settleChain {} 12 sending
  let (selfGift, _) ← (step 100 empowered (gift (some p))).toOption
  let kept := settleChain {} 12 selfGift
  return !(legalActions playing).contains (gift (some q)) &&
    (legalActions empowered).contains (gift (some p)) &&
    (legalActions empowered).contains (gift (some q)) &&
    !(legalActions empowered).contains (gift none) &&
    !(legalActions empowered).contains (gift (some ⟨2⟩)) &&
    (sending.obj? item).any (·.targetPlayer == some q) &&
    (sending.obj? current).any (fun o => o.controller == p && o.exhausted && o.empowerCount == 0) &&
    passed.locate current == some (.player q .base) &&
    (passed.obj? current).any (fun o => o.owner == p && o.controller == q && o.exhausted) &&
    kept.locate current == some (.player p .base) && kept.tired current == some true

-- The Ending Step follows the current controller. Killing the Gear and
-- dealing damage are separate instructions, even if it already left the Base.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, gear) ← put s p "VEN-133" .base
  let (s, ownerUnit) ← put s p "VEN-014" .base
  let (s, baseUnit) ← put s q "VEN-014" .base
  let (s, otherGear) ← put s q "VEN-073" .base
  let (s, fieldUnit) ← putAt s q "VEN-014" field
  let s := (s.control q field).modObj gear (fun o => { o with empowerCount := 1 })
  let (queued, _) ←
    (step 100 s ⟨.player p, .activate gear 0 ⟨0, []⟩ [] [] (some q)⟩).toOption
  let passed := settleChain {} 12 queued
  let ending (who : PlayerId) :=
    (advance 100 { passed with active := some who, pending := [.phase .ending] } []).toOption
  let (ownerEnd, _) ← ending p
  let (recipientEnd, _) ← ending q
  let item ← (recipientEnd.zone .chain).head?
  let finish (t : GameState) : Option (GameState × List Event) := do
    let .chainPass a _ :: _ := t.pending | none
    let (s1, es1) ← (step 100 t ⟨.player a, .pass⟩).toOption
    let .chainPass b _ :: _ := s1.pending | none
    let (s2, es2) ← (step 100 s1 ⟨.player b, .pass⟩).toOption
    return (s2, es1 ++ es2)
  let (done, damage) ← finish recipientEnd
  let (alreadyGone, _) ← moveObj recipientEnd gear (.player p .banishment)
  let (afterBanish, stillDamage) ← finish alreadyGone
  return (ownerEnd.zone .chain).isEmpty && ownerEnd.locate gear == some (.player q .base) &&
    (recipientEnd.obj? item).any (fun o => o.owner == q && o.kind == .chainAbility (cid "VEN-133") 1 gear) &&
    damage.contains (.damaged baseUnit 5) && damage.contains (.damaged fieldUnit 5) &&
    !damage.contains (.damaged ownerUnit 5) && !damage.contains (.damaged otherGear 5) &&
    done.countIn p .trash "VEN-133" == 1 && done.countIn q .trash "VEN-014" == 2 &&
    done.countIn q .trash "VEN-133" == 0 && (done.obj? ownerUnit).isSome &&
    stillDamage.contains (.damaged baseUnit 5) && stillDamage.contains (.damaged fieldUnit 5) &&
    afterBanish.countIn p .banishment "VEN-133" == 1

-- The discounted Plaza Guardian still triggers Curator. Exhausting the
-- Legend and choosing distinct targets are both part of finalization.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, curator) ← put s p "VEN-145" .legendZone
  let (s, guardian) ← put s p "VEN-064" .hand
  let (s, third) ← put s q "R1" .base
  let putGear (t : GameState) := (put t p "VEN-073" .base).map Prod.fst
  let s ← putGear s >>= putGear >>= putGear >>= putGear
  let runes (t : GameState) (who : PlayerId) :=
    (t.zone (.player who .base)).filter (fun id => (t.cardDef? id).any (·.hasType .rune))
  let first :: other :: _ := runes s p | none
  let s := (((s.tire first).tire other).tire third).fund p 6
  let playGuardian : Action := ⟨.player p, .playCard guardian ⟨6, []⟩ []⟩
  let (waiting, _) ← (step 100 s playGuardian).toOption
  let answer (ids : List ObjId) : Action := ⟨.player p, .putTrigger 0 ids⟩
  let skip : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (queued, payEvents) ← (step 100 waiting (answer [first, third])).toOption
  let done := settleChain {} 12 queued
  let (declined, _) ← (step 100 waiting skip).toOption
  let (alreadyTired, _) ← (step 100 (s.tire curator) playGuardian).toOption
  let (bounced, _) ← moveObj queued first (.player p .runeDeck)
  let afterBouncing := settleChain {} 12 bounced
  return (s.energyCost? p guardian == some 6) &&
    (legalActions waiting).contains (answer []) &&
    (legalActions waiting).contains (answer [first]) &&
    (legalActions waiting).contains (answer [first, third]) &&
    !(legalActions waiting).contains (answer [first, first]) &&
    !(legalActions waiting).contains (answer [first, other, third]) &&
    !(legalActions waiting).contains (answer [curator]) &&
    (legalActions alreadyTired).contains skip &&
    !(legalActions alreadyTired).contains (answer []) &&
    payEvents.contains (.exhausted curator) && queued.tired curator == some true &&
    queued.tired first == some true && queued.tired third == some true &&
    done.tired first == some false && done.tired third == some false &&
    done.tired other == some true && declined.tired curator == some false &&
    afterBouncing.tired third == some false

-- A qualifying Gear triggers Curator; a Spell with the same base Energy,
-- a cheap permanent, and an opponent's qualifying play do not.
#guard vendettaCase fun s => do
  let p := s.me
  let q := s.you
  let (s, curator) ← put s p "VEN-145" .legendZone
  let (s, gear) ← put s p "VEN-067" .hand
  let (s, spell) ← put s p "VEN-056" .hand
  let (s, cheap) ← put s p "VEN-014" .hand
  let (s, enemyGear) ← put s q "VEN-067" .hand
  let s := (s.rich p).rich q
  let caused (t : GameState) : Bool := match t.pending with
    | .triggerOrder _ first _ _ :: _ => first.source == curator
    | _ => false
  let (fromGear, _) ← (step 100 s ⟨.player p, .playCard gear ⟨10, [.mind, .mind]⟩ []⟩).toOption
  let (fromSpell, _) ← (step 100 s ⟨.player p, .playCard spell (payOf s spell) []⟩).toOption
  let (fromCheap, _) ← (step 100 s ⟨.player p, .playCard cheap ⟨2, []⟩ []⟩).toOption
  let other := { s with active := some q, pending := [.priority q] }
  let (fromOpponent, _) ←
    (step 100 other ⟨.player q, .playCard enemyGear ⟨10, [.mind, .mind]⟩ []⟩).toOption
  return caused fromGear && !caused fromSpell && !caused fromCheap && !caused fromOpponent

-- Core Rules 206.1 uses the activated ability's unadjusted base cost.
#guard vendettaCase fun s => do
  let p := s.me
  let (s, curator) ← put s p "VEN-145" .legendZone
  let (s, gear) ← put s p "VEN-073" .base
  let d ← s.cardDef? gear
  let body := EffectDef.of [] (.prim (.draw .you (.const 1)))
  let abilities := [
    Ability.activated [.pay ⟨12, []⟩, .energyDiscount .always (.const 6)] .normal body .unlimited,
    Ability.activated [.pay ⟨6, []⟩] .normal body .unlimited]
  let d := { d with abilities }
  let s := { s.fund p 6 with cards := ⟨d :: s.cards.cards⟩ }
  let (high, es) ← (step 100 s ⟨.player p, .activate gear 0 ⟨6, []⟩ []⟩).toOption
  let (low, _) ← (step 100 s ⟨.player p, .activate gear 1 ⟨6, []⟩ []⟩).toOption
  let .triggerOrder _ t _ _ :: _ := high.pending | none
  let .chainPass .. :: _ := low.pending | none
  return t.source == curator && (high.poolOf p).energy == 0 &&
    es.contains (.activated p gear 0 (some 12))

end RiftboundTest
