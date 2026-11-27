module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance modal-trigger and movement scenarios -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Riven locks unused modes at finalization and spends the buff only as the chosen mode resolves.
#guard radianceCase fun s => do
  let p := s.me
  let (s, riven) ← put s p "RAD-043" .base
  let (s, enemy) ← put s s.you "RAD-060" .base
  let exhaust (g : GameState) := do
    let ready := g.modObj riven (fun o => { o with exhausted := false })
    let r ← (advance 100 { ready with pending := [.run p riven {}
      (.cons (.prim (.exhaust .self)) .nil), .priority p] } []).toOption
    return r.1
  let choose (mode : Nat) (ts : List ObjId := []) : Action :=
    ⟨.player p, .putTrigger 0 ts (.pay [] (some mode))⟩
  let first ← exhaust s
  let (buffChain, _) ← (step 100 first (choose 0)).toOption
  let buffed := settleChain {} 8 buffChain
  let second ← exhaust buffed
  let (stunChain, _) ← (step 100 second (choose 1 [enemy])).toOption
  let spent := settleChain {} 8 stunChain
  let third ← exhaust spent
  let (readyChain, _) ← (step 100 third (choose 2)).toOption
  let tooLate := settleChain {} 8 readyChain
  let stillPaid := settleChain {} 8 (readyChain.buff riven)
  let following ← exhaust { stillPaid with turn := stillPaid.turn + 1 }
  return !(legalFrameActions second).contains (choose 0) &&
    !(legalFrameActions third).contains (choose 1 [enemy]) &&
    (stunChain.obj? riven).any (·.buffed) && (spent.obj? enemy).any (·.stunned) &&
    !(spent.obj? riven).any (·.buffed) &&
    tooLate.tired riven == some true && stillPaid.tired riven == some false &&
    !(stillPaid.obj? riven).any (·.buffed) && (legalFrameActions following).contains (choose 0)

-- Hunker Down readies the Unit, then prevents standard and effect moves until turn end.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, hunker) ← put s p "RAD-034" .hand
  let (s, unit) ← putAt s p "RAD-011" field
  let (s, other) ← put s q "RAD-011" .base
  let ready ← play (s.tire unit) p hunker [unit]
  let forced := moveByEffect q none ready unit
  let swapped := swapPlaces ready unit other (some q)
  let (expired, _) ← (advance 100 { ready with pending := [.expireTurn] } []).toOption
  return ready.tired unit == some false && ready.handN p == s.handN p &&
    !(moveOk ready p unit .base) && forced.2.isEmpty && swapped.2.isEmpty &&
    (forced.1.obj? unit).any (·.loc == some field) &&
    (swapped.1.obj? unit).any (·.loc == some field) &&
    !expired.moveBlocked unit && !(moveByEffect q none expired unit).2.isEmpty

-- Storm Raptor looks at the stun at death, the dead Unit's controller and its location.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, _) ← putAt s p "RAD-036" field
  let (s, sameField) ← putAt s q "RAD-011" field
  let (s, friendly) ← putAt s p "RAD-011" field
  let (s, away) ← put s q "RAD-011" .base
  let stun (g : GameState) (id : ObjId) := g.modObj id (fun o => { o with stunned := true })
  let kill (g : GameState) (id : ObjId) :=
    let result := killObj g id
    fire result.1 result.2
  let unstunned ← kill s sameField
  let foe ← kill (stun s sameField) sameField
  let ally ← kill (stun s friendly) friendly
  let elsewhere ← kill (stun s away) away
  return unstunned.handN p == s.handN p && foe.handN p == s.handN p + 1 &&
    ally.handN p == s.handN p && elsewhere.handN p == s.handN p

-- Siren's Song can choose an enemy moved by an effect this turn, but not one only played there.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, siren) ← put s p "RAD-098" .hand
  let (s, runner) ← put s q "RAD-011" .base
  let (s, stayed) ← putAt s q "RAD-011" field
  let (s, ally) ← put s p "RAD-011" .base
  let moved := (moveByEffect p (some field) s runner).1
  let moved := (moveByEffect p (some field) moved ally).1
  let sing (g : GameState) (target : ObjId) :=
    cast (g.fund p 2) p siren ⟨2, []⟩ [target] {} (.destination none)
  let done ← sing moved runner
  return (sing moved stayed).isNone && (sing moved ally).isNone &&
    (sing s runner).isNone && (sing { moved with turn := moved.turn + 1 } runner).isNone &&
    (done.obj? runner).any (·.loc.isNone) && (done.obj? stayed).any (·.loc == some field)

-- The Waters' Wage distinguishes an ordinary play, a reveal on this turn, and a reaction.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, hand) ← put s p "RAD-100" .hand
  let (s, hidden) ← put s p "RAD-100" .hidden
  let (s, _) ← putAt s p "RAD-011" field
  let s := (s.control p field).modObj hidden
    (fun o => { o with hiddenAt := some field, hiddenTurn := some (s.turn - 1) })
  let gold (g : GameState) :=
    (g.zone (.player p .base)).filter (fun id => (g.cardDef? id).any (·.name == "Gold"))
  let ordinary ← play s p hand
  let onTurn ← activate s p hidden 1
  let onOpponentTurn ← activate { s with active := some q, pending := [.priority p] } p hidden 1
  return (gold ordinary).length == 1 && (gold ordinary).all (fun id => ordinary.tired id == some true) &&
    (gold onTurn).length == 3 && (gold onTurn).all (fun id => onTurn.tired id == some false) &&
    (gold onOpponentTurn).length == 1 &&
      (gold onOpponentTurn).all (fun id => onOpponentTurn.tired id == some true)

-- The opponent chooses during resolution. Deflect has no cost and Hunker Down excludes the Unit.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, wyrm) ← putAt s p "RAD-113" field
  let (s, first) ← put s q "UNL-T02" .base
  let (s, second) ← put s q "RAD-011" .base
  let (s, grounded) ← put s q "RAD-011" .base
  let s := (s.control p field).addTurnFxOn q grounded .cannotMove
  let useWyrm (g : GameState) (opponent : PlayerId) :=
    (step 100 g ⟨.player p, .activate wyrm 0 ⟨0, [], none⟩ [] [] (some opponent)⟩).toOption.map Prod.fst
  let queued ← useWyrm s q
  let waiting := settleChain {} 2 queued
  let choices := (legalFrameActions waiting).filterMap (fun a =>
    match a.kind with
    | .choose id => if a.actor == .player q then some id else none
    | _ => none)
  let (moved, events) ← (step 100 waiting ⟨.player q, .choose first⟩).toOption
  let allBlocked := (s.addTurnFxOn q first .cannotMove).addTurnFxOn q second .cannotMove
  let blocked ← useWyrm allBlocked q
  let stayed := settleChain {} 8 blocked
  return (useWyrm s p).isNone && queued.tired wyrm == some true &&
    choices.length == 2 && choices.contains first && choices.contains second &&
    !choices.contains grounded &&
    !(events.any (fun | .chosenByAbility .. | .chosenBySpell .. => true | _ => false)) &&
    (moved.obj? first).any (·.loc == some field) &&
    (stayed.obj? first).any (·.loc.isNone) && (stayed.obj? grounded).any (·.loc.isNone)

-- An actual Hunker Down Reaction resolves before the Wyrm asks which Unit should move.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, wyrm) ← putAt (s.control p field) p "RAD-113" field
  let (s, hunker) ← put s q "RAD-034" .hand
  let (s, grounded) ← put s q "RAD-011" .base
  let (s, candidate) ← put s q "RAD-011" .base
  let (queued, _) ← (step 100 s
    ⟨.player p, .activate wyrm 0 ⟨0, [], none⟩ [] [] (some q)⟩).toOption
  let (open_, _) ← (step 100 queued ⟨.player p, .pass⟩).toOption
  let reacted ← cast (open_.fund q 1) q hunker ⟨1, []⟩ [grounded]
  return reacted.moveBlocked grounded && (reacted.obj? grounded).any (·.loc.isNone) &&
    (reacted.obj? candidate).any (·.loc == some field)

-- Mournful Spirit remembers its last location, can target Gear, and allows declining.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, spirit) ← putAt s p "RAD-126" field
  let (s, gear) ← putAt s q "RAD-024" field
  let (s, homeSpirit) ← put s p "RAD-126" .base
  let (s, homeUnit) ← put s p "RAD-011" .base
  let fieldDeath := killObj s spirit
  let baseDeath := killObj s homeSpirit
  let picks ← firePicks fieldDeath.1 fieldDeath.2
  let basePicks ← firePicks baseDeath.1 baseDeath.2
  let destroyed ← fire fieldDeath.1 fieldDeath.2 { pick := (· == [gear]) }
  let declined ← fire fieldDeath.1 fieldDeath.2 { yes := false }
  return picks == [gear] && basePicks.contains homeUnit && !basePicks.contains gear &&
    destroyed.countIn q .trash "RAD-024" == 1 && declined.inPlay.contains gear

-- Battlefield Armorer pays to save the Gear that died at a Battlefield, even from the Base.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, _) ← put s p "RAD-130" .base
  let (s, deployed) ← putAt s p "RAD-024" field
  let (s, atBase) ← put s p "RAD-039" .base
  let pay (g : GameState) (id : ObjId) (says : Says := {}) :=
    let killed := killObj g id
    fire killed.1 killed.2 says
  let funded := s.fund p 1
  let recovered ← pay funded deployed
  let declined ← pay funded deployed { yes := false }
  let unpaid ← pay (s.fund p 0) deployed
  let distant ← pay funded atBase
  return recovered.countIn p .hand "RAD-024" == 1 && (recovered.poolOf p).energy == 0 &&
    declined.countIn p .trash "RAD-024" == 1 && (declined.poolOf p).energy == 1 &&
    unpaid.countIn p .trash "RAD-024" == 1 && distant.countIn p .trash "RAD-039" == 1

end RiftboundTest
