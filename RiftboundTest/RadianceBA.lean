module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Mordekaiser, Twice Slain -/

namespace RiftboundTest

open Riftbound

-- A lethal Unit can sacrifice a friendly Unit from another location, heal, exhaust, and recall.
-- The same Mordekaiser cannot use the replacement again that turn.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, mord) ← putAt s p "RAD-020" field
  let (s, ally) ← put s p "V0" .base
  let (s, foe) ← put s q "V1" .base
  let s := (s.control p field).modObj mord (fun unit => { unit with damage := 6 })
  let (asked, _) ← (advance 100 { s with pending := [.cleanup, .priority p] } []).toOption
  let .eitherDo controller _ _ (.recordDeathSacrifice victim (some cost)) _ _ :: _ := asked.pending
    | none
  let (saved, events) ← (step 100 asked ⟨.player p, .decide true⟩).toOption
  let charged := saved.modObj mord (fun unit => { unit with damage := 8 })
  let (done, _) ← (advance 100 { charged with pending := [.cleanup, .priority p] } []).toOption
  return controller == p && victim == mord && cost == ally &&
    (saved.zone (.player p .base)).contains mord && saved.tired mord == some true &&
    (saved.obj? mord).any (fun unit => unit.damage == 0 && unit.loc.isNone) &&
    saved.countIn p .trash "V0" == 1 && saved.inPlay.contains foe &&
    events.any (fun event => match event with | .died .. => true | _ => false) &&
    events.any (fun event => match event with | .recalled id => id == mord | _ => false) &&
    done.countIn p .trash "RAD-020" == 1).getD false

-- A Kill instruction can offer the optional replacement even without any damage.
-- Choosing Tactical Retreat instead leaves Mordekaiser's allowance available.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let (s, mord) ← put s p "RAD-020" .base
  let (s, ally) ← put s p "V0" .base
  let (s, source) ← put s q "V1" .base
  let theKill := EffectList.ofList [.prim (.kill (.slot 0))]
  let frames := [.run q source { slots := [.obj mord] } theKill, .cleanup, .priority p]
  let armed := s.addTurnFxOn p mord .saveOnce
  let (asked, _) ← (advance 100 { armed with pending := frames } []).toOption
  let .eitherDo _ _ _ (.chooseDeathFree affected none) _ _ :: _ := asked.pending | none
  let (withRetreat, _) ← (step 100 asked ⟨.player p, .decide true⟩).toOption
  let (optional, _) ← (step 100 asked ⟨.player p, .decide false⟩).toOption
  let (sacrificed, _) ← (step 100 optional ⟨.player p, .decide true⟩).toOption
  let (again, _) ← (advance 100 { withRetreat with pending := frames } []).toOption
  let (saved, _) ← (step 100 again ⟨.player p, .decide true⟩).toOption
  return affected == mord && withRetreat.inPlay.contains mord && withRetreat.inPlay.contains ally &&
    (sacrificed.tacticalRetreatFor mord).isSome && sacrificed.countIn p .trash "V0" == 1 &&
    saved.inPlay.contains mord && saved.countIn p .trash "V0" == 1).getD false

-- A limited play still pays its additional cost when Mordekaiser replaces his own death.
#guard (lab.bind fun s => do
  let p := s.me
  let field := s.bf0
  let (s, mord) ← putAt (s.control p field) p "RAD-020" field
  let (s, ally) ← put s p "V0" .base
  let (s, devourer) ← put s p "RAD-125" .hand
  let funded := s.fund p 4 (order := 1)
  let terms : EffectPlayTerms := { price := .reduceEnergy 1 }
  let plan ← (permanentPlayPlans funded p devourer terms).find?
    (fun plan => plan.extraObject == some mord && plan.battlefield.isNone)
  let play : Effect := .finishFundedPermanent devourer terms plan []
  let frames := [.run p field {} (.cons play .nil), .priority p]
  let (asked, _) ← (advance 100 { funded with pending := frames } []).toOption
  let .eitherDo controller _ _ (.recordDeathSacrifice victim (some cost)) _ _ :: _ := asked.pending
    | none
  let (saved, _) ← (step 100 asked ⟨.player p, .decide true⟩).toOption
  return controller == p && victim == mord && cost == ally &&
    asked.poolOf p == funded.poolOf p && asked.countIn p .hand "RAD-125" == 1 &&
    (saved.zone (.player p .base)).contains mord &&
    saved.countIn p .trash "V0" == 1 && saved.countIn p .base "RAD-125" == 1 &&
    (saved.poolOf p).total == 0).getD false

-- A play or ability declaration stays fixed while Mordekaiser's controller chooses.
#guard (lab.bind fun s => do
  let p := s.me
  let field := s.bf0
  let (s, mord) ← putAt (s.control p field) p "RAD-020" field
  let (s, ally) ← put s p "V0" .base
  let (s, devourer) ← put s p "RAD-125" .hand
  let before := s.fund p 5 (order := 1)
  let action : Action := ⟨.player p, .playCard devourer ⟨5, [.order]⟩ [mord]⟩
  let (asked, beforeEvents) ← (step 100 before action).toOption
  let .eitherDo _ _ _ (.recordDeathSacrifice victim (some cost)) _ _ ::
      .resumeCost locked :: _ := asked.pending
    | none
  let (saved, events) ← (step 100 asked ⟨.player p, .decide true⟩).toOption
  return locked == action && victim == mord && cost == ally && beforeEvents.isEmpty &&
    asked.inPlay.contains ally && asked.countIn p .hand "RAD-125" == 1 &&
    ((step 100 asked ⟨.player p, .pass⟩).toOption).isNone &&
    saved.countIn p .base "RAD-125" == 1 && saved.inPlay.contains mord &&
    saved.countIn p .trash "V0" == 1 && (saved.poolOf p).total == 0 &&
    (events.filter (fun | .played .. => true | _ => false)).length == 1).getD false

-- Additional costs of activated and triggered abilities use the same timing.
#guard (lab.bind fun s => do
  let p := s.me
  let (s, mord) ← putAt (s.control p s.bf0) p "RAD-020" s.bf0
  let (s, ally) ← put s p "V0" .base
  let (s, gear) ← put s p "RAD-022" .base
  let (s, amplifier) ← put s p "RAD-017" .base
  let ability : Action := ⟨.player p, .activate gear 2 ⟨0, []⟩ [] [] none none (some mord)⟩
  let (askActivation, _) ← (step 100 s ability).toOption
  let (activated, _) ← (step 100 askActivation ⟨.player p, .decide true⟩).toOption
  let trigger : PendTrigger := { source := amplifier, card := ⟨"RAD-017"⟩, idx := 0, controller := p }
  let before := { s with pending := [.triggerOrder p trigger [] [], .priority p] }
  let (askTrigger, _) ← (step 100 before ⟨.player p, .putTrigger 0 [] (.pay [mord])⟩).toOption
  let (triggered, _) ← (step 100 askTrigger ⟨.player p, .decide true⟩).toOption
  return (askActivation.zone .chain).isEmpty && askActivation.tired gear == some false &&
    askActivation.inPlay.contains ally && askTrigger.inPlay.contains ally &&
    activated.tired gear == some true && !(activated.zone .chain).isEmpty &&
    !(triggered.zone .chain).isEmpty && activated.inPlay.contains mord &&
    triggered.inPlay.contains mord && activated.countIn p .trash "V0" == 1 &&
    triggered.countIn p .trash "V0" == 1).getD false

-- Choosing one of several Banish effects can replace a declared Kill cost.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let (s, mord) ← putAt (s.control p s.bf0) p "RAD-020" s.bf0
  let (s, ally) ← put s p "V0" .base
  let (s, gear) ← put s p "RAD-022" .base
  let marked := (s.addTurnFxOn q mord .banishInstead).addTurnFxOn p mord .banishInstead
  let ability : Action := ⟨.player p, .activate gear 2 ⟨0, []⟩ [] [] none none (some mord)⟩
  let (asked, events) ← (step 100 marked ability).toOption
  let .eitherDo chooser _ _ (.chooseDeathBanisher victim banisher) _ _ ::
      .resumeCost locked :: _ := asked.pending | none
  let (paid, settled) ← (step 100 asked ⟨.player p, .decide true⟩).toOption
  return chooser == p && victim == mord && banisher == q && locked == ability && events.isEmpty &&
    paid.tired gear == some true && !(paid.zone .chain).isEmpty &&
    paid.countIn p .banishment "RAD-020" == 1 && paid.inPlay.contains ally &&
    settled.any (fun | .banished player _ _ => player == q | _ => false)).getD false

-- Temporary is a Kill at the beginning of the turn and can be replaced before it occurs.
#guard (lab.bind fun s => do
  let p := s.me
  let field := s.bf0
  let (s, mord) ← putAt (s.control p field) p "RAD-020" field
  let (s, ally) ← put s p "V0" .base
  let marked := s.modObj mord (fun unit =>
    { unit with tempKws := [({ keyword := .temporary }, .never)] })
  let before := { marked with pending := [.phase .beginning, .priority p] }
  let (asked, _) ← (advance 100 before []).toOption
  let .eitherDo _ _ _ (.recordDeathSacrifice victim (some cost)) _ _ :: _ := asked.pending
    | none
  let (saved, _) ← (step 100 asked ⟨.player p, .decide true⟩).toOption
  return victim == mord && cost == ally && asked.inPlay.contains ally &&
    (saved.zone (.player p .base)).contains mord && saved.countIn p .trash "V0" == 1).getD false

-- Mordekaiser can sacrifice a second copy, which can spend its own replacement on a third Unit.
#guard (lab.bind fun s => do
  let p := s.me
  let field := s.bf0
  let (s, first) ← putAt (s.control p field) p "RAD-020" field
  let (s, second) ← putAt s p "RAD-020" field
  let (s, ally) ← putAt s p "V0" field
  let before := s.modObj first (fun unit => { unit with damage := 6 })
  let (askFirst, es₁) ← (advance 100 { before with pending := [.cleanup, .priority p] } []).toOption
  let .eitherDo _ _ _ a b _ :: _ := askFirst.pending | none
  let choseSecond (effect : Effect) : Bool := match effect with
    | .recordDeathSacrifice victim (some cost) => victim == first && cost == second
    | _ => false
  let (options, es₂) ← (step 100 askFirst ⟨.player p, .decide (choseSecond a)⟩).toOption
  let next ← if choseSecond a || choseSecond b then some options else
    match options.pending with
    | .eitherDo _ _ _ pick _ _ :: _ =>
      ((step 100 options ⟨.player p, .decide (choseSecond pick)⟩).toOption).map Prod.fst
    | _ => none
  let .eitherDo _ _ _ (.recordNestedDeathDecision root used victim (.sacrifice (some cost)) none)
      _ _ :: _ := next.pending
    | none
  let (saved, events) ← (step 100 next ⟨.player p, .decide true⟩).toOption
  return root == first && used == [(first, true)] &&
    victim == second && cost == ally && es₁.isEmpty && es₂.isEmpty &&
    next.inPlay.contains ally && saved.countIn p .base "RAD-020" == 2 &&
    saved.countIn p .trash "V0" == 1 && saved.tired first == some true &&
    saved.tired second == some true &&
    (events.filter (fun | .died .. => true | _ => false)).length == 1).getD false

-- If the replacement sacrifices its own Unit, the resulting death cannot use it again.
#guard (lab.bind fun s => do
  let p := s.me
  let (s, mord) ← put s p "RAD-020" .base
  let run := Frame.run p mord { slots := [.obj mord] } (.ofList [.prim (.kill (.slot 0))])
  let (asked, _) ← (advance 100 { s with pending := [run, .priority p] } []).toOption
  let .eitherDo _ _ _ (.recordDeathSacrifice victim (some cost)) _ _ :: _ := asked.pending
    | none
  let (killed, events) ← (step 100 asked ⟨.player p, .decide true⟩).toOption
  return victim == mord && cost == mord && killed.countIn p .trash "RAD-020" == 1 &&
    (events.filter (fun | .died .. => true | _ => false)).length == 1).getD false

-- The controller chooses the order of simultaneous replacements. Both occur before an ordinary death.
#guard (lab.bind fun s => do
  let p := s.me
  let q := if p.n == 0 then ⟨1⟩ else ⟨0⟩
  let field := s.bf0
  let (s, original) ← putAt (s.control p field) p "RAD-020" field
  let (s, other) ← putAt s p "RAD-020" field
  let (s, firstCost) ← put s p "V0" .base
  let (s, otherCost) ← put s p "V1" .base
  let (s, ordinary) ← put s q "V2" .base
  let lethal (state : GameState) (id : ObjId) := state.modObj id (fun unit => { unit with damage := 8 })
  let ready := [original, other, ordinary].foldl lethal s
  let ready := ready.addTurnFxOn p original (.deathSacrificeChoice (some firstCost))
  let ready := ready.addTurnFxOn p other (.deathSacrificeChoice (some otherCost))
  let (asked, before) ← (advance 100 { ready with pending := [.cleanup, .priority p] } []).toOption
  let .eitherDo controller _ _ (.recordDeathOrder _ first) (.recordDeathOrder _ _) _ :: _ :=
    asked.pending | none
  let (settled, after) ← (step 100 asked ⟨.player p, .decide (first == other)⟩).toOption
  let ordered := after.filterMap (fun
    | .recalled unit => some unit
    | .died id owner => if owner == q then some id else none
    | _ => none)
  let gone ← (settled.zone (.player q .trash)).head?
  return before.isEmpty && controller == p && ordered == [other, original, gone] &&
    (settled.zone (.player p .base)).contains original && (settled.zone (.player p .base)).contains other &&
    !(settled.turnFx.any (fun note => match note.kind with | .deathOrder _ => true | _ => false))).getD false

-- In 2v2 the replacement accepts a teammate's Unit and keeps the opponent in play.
#guard (lab.bind fun labState => do
  let p : PlayerId := ⟨0⟩
  let ally : PlayerId := ⟨1⟩
  let q : PlayerId := ⟨2⟩
  let s := GameState.empty { mode := Mode.teamDuel, ruleSet := .coreOnly } labState.cards
  let s := { s with phase := .main, active := some p, turn := 2, turnOrder := Mode.teamTurnOrder true }
  let (s, mord) ← put s p "RAD-020" .base
  let (s, teammate) ← put s ally "V0" .base
  let (s, opponent) ← put s q "V1" .base
  let run := Frame.run q opponent { slots := [.obj mord] } (.ofList [.prim (.kill (.slot 0))])
  let (asked, _) ← (advance 100 { s with pending := [run, .cleanup, .priority p] } []).toOption
  let .eitherDo controller _ _ (.recordDeathSacrifice victim (some cost)) _ _ :: _ := asked.pending
    | none
  let (settled, events) ← (step 100 asked ⟨.player p, .decide true⟩).toOption
  let dead ← settled.firstOf ally .trash "V0"
  return controller == p && victim == mord && cost == teammate &&
    (settled.obj? opponent).isSome && settled.tired mord == some true &&
    events.contains (.died dead ally)).getD false

-- A limited Spell play still pays its mandatory Kill cost and can replace that death.
#guard (lab.bind fun s => do
  let p := s.me
  let field := s.bf0
  let (s, mord) ← putAt (s.control p field) p "RAD-020" field
  let (s, ally) ← put s p "V0" .base
  let (s, sacrifice) ← put s p "UNL-173" .hand
  let (queued, card) ← queueLimitedSpell s p sacrifice .ignoreBase .normal
  let plan ← (limitedSpellOptions queued p card .ignoreBase).find? (fun o => o.targets == [mord])
  let next := Effect.finishLimitedSpell card plan []
  let pending := [Frame.run p card {} (.cons next .nil), .priority p]
  let (asked, _) ← (advance 100 { queued with pending } []).toOption
  let .eitherDo controller _ _ (.recordDeathSacrifice victim (some cost)) _ _ :: _ := asked.pending
    | none
  let (paid, events) ← (step 100 asked ⟨.player p, .decide true⟩).toOption
  return victim == mord && cost == ally && controller == p &&
    (paid.zone .chain).contains card && (paid.pendingSpell card).isNone &&
    (paid.zone (.player p .base)).contains mord && paid.countIn p .trash "V0" == 1 &&
    events.any (fun | .played _ id => id == card | _ => false)).getD false

end RiftboundTest
