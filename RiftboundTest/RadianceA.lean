module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance card and keyword scenarios -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Deploy can enter an enemy or open Battlefield. Gear does not contest it and only an enemy Hold
-- at that Battlefield kills it. An effect that plays the Gear also has no Base destination.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let site := s.bf0
  let other ← s.battlefields.find? (· != site)
  let (s, banner) ← put s p "RAD-002" .hand
  let (s, nearby) ← putAt s p "VEN-071" site
  let (s, enemy) ← putAt s q "VEN-071" site
  let (s, distant) ← put s p "VEN-071" .base
  let s := s.control q site
  let d ← s.cardDef? banner
  let enemySite ← play s p banner [site]
  let played ← (enemySite.zone .battlefieldZone).find? (fun id =>
    (enemySite.cardDef? id).any (·.id.code == "RAD-002"))
  let openSite ← play s p banner [other]
  let friendlyHold ← fire enemySite [.scored p site false]
  let awayHold ← fire enemySite [.scored q other false]
  let conquered ← fire enemySite [.scored q site true]
  let held ← fire enemySite [.scored q site false]
  return (play s p banner).isNone &&
    effectPlayLocations s p banner d [] == (s.playBfOptions p banner).map some &&
    !((s.playBfOptions p banner).isEmpty) &&
    (enemySite.obj? played).any (·.loc == some site) &&
    (enemySite.obj? site).any (·.contested.isNone) &&
    (openSite.obj? other).any (fun o => o.control.isNone && o.contested.isNone) &&
    enemySite.kwAmount nearby .assault == 1 && enemySite.kwAmount enemy .assault == 0 &&
    enemySite.kwAmount distant .assault == 0 &&
    [friendlyHold, awayHold, conquered].all (fun t => t.inPlay.contains played) &&
    held.countIn p .trash "RAD-002" == 1 && held.kwAmount nearby .assault == 0

-- The Tracker can decline its damage or choose two different Units on either side.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, tracker) ← put s p "RAD-003" .hand
  let (s, friendly) ← put s p "VEN-071" .base
  let (s, enemy) ← put s q "VEN-071" .base
  let (s, untouched) ← put s q "VEN-071" .base
  let waiting ← castStop s p tracker
  let picks := (legalFrameActions waiting).filterMap (fun a => match a.kind with
    | .putTrigger _ targets (.pay ..) => some targets
    | _ => none)
  let hit := settleChain { pick := (· == [friendly, enemy]) } 8 waiting
  let decline := settleChain { pick := List.isEmpty } 8 waiting
  let damage (t : GameState) (id : ObjId) := (t.obj? id).map (·.damage)
  return picks.contains [] && picks.contains [friendly, enemy] &&
    !picks.contains [enemy, enemy] && !picks.contains [friendly, enemy, untouched] &&
    damage hit friendly == some 1 && damage hit enemy == some 1 &&
    damage hit untouched == some 0 && damage decline friendly == some 0

-- The Scout can Accelerate while its play trigger gives a Unit two Might for the turn.
#guard radianceCase fun s => do
  let p := s.me
  let (s, scout) ← put s p "RAD-008" .hand
  let (s, ally) ← put s p "VEN-014" .base
  let ordinary ← cast (s.fund p 3) p scout ⟨3, []⟩ [] { pick := (· == [ally]) }
  let fast ← cast (s.fund p 4 (fury := 1)) p scout ⟨4, [.fury]⟩ [] { pick := (· == [ally]) }
  let tired ← ordinary.firstOf p .base "RAD-008"
  let ready ← fast.firstOf p .base "RAD-008"
  let (expired, _) ← (advance 100 { fast with pending := [.expireTurn] } []).toOption
  return ordinary.tired tired == some true && fast.tired ready == some false &&
    fast.mightNow ally == some 4 && expired.mightNow ally == some 2

-- Consult the Heavens grants Shield this turn and may recycle the top card with Predict.
#guard radianceCase fun s => do
  let p := s.me
  let (s, heavens) ← put s p "RAD-025" .hand
  let (s, defender) ← putAt s p "VEN-014" s.bf0
  let s := s.control p s.bf0
  let original ← (s.zone (.player p .mainDeck)).head?
  let waiting ← play s p heavens [defender]
  let (keep, _) ← (step 100 waiting ⟨.player p, .predictPick original false⟩).toOption
  let (recycle, _) ← (step 100 waiting ⟨.player p, .predictPick original true⟩).toOption
  let (expired, _) ← (advance 100 { keep with pending := [.expireTurn] } []).toOption
  return (keep.zone (.player p .mainDeck)).head? == some original &&
    (recycle.zone (.player p .mainDeck)).head? != some original &&
    keep.kwAmount defender .shield == 2 && expired.kwAmount defender .shield == 0

-- Hush can counter a spell at exactly two Power and cannot choose one costing less.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, hush) ← put s p "RAD-041" .hand
  let (s, unit) ← put s p "VEN-091" .base
  let (s, small) ← onChain s q "VEN-031"
  let (s, large) ← onChain s q "OGN-029"
  let s := s.modObj large (fun o => { o with targets := [unit] })
  let s := { s with pending := [.chainPass p 0, .priority p] }
  let blocked ← play s p hush [large]
  return (play s p hush [small]).isNone &&
    blocked.countIn p .trash "RAD-041" == 1 && blocked.countIn q .trash "OGN-029" == 1 &&
    (blocked.obj? unit).any (·.damage == 0)

-- High Note counts exhausted friendly Units, including across locations, but excludes Gear.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, note) ← put s p "RAD-048" .hand
  let (s, first) ← put s p "VEN-071" .base
  let (s, second) ← putAt s p "VEN-071" s.bf0
  let (s, gear) ← put s p "SFD-117" .base
  let (s, ready) ← put s p "VEN-071" .base
  let (s, enemy) ← put s q "VEN-091" .base
  let exhausted := ((((s.control p s.bf0).tire first).tire second).tire gear).tire enemy
  let done ← play exhausted p note [enemy]
  return done.mightNow enemy == (s.mightNow enemy).map (· - 2) &&
    done.mightNow ready == s.mightNow ready

-- Nazuman Ntofo costs one Energy to Equip, grants Shield 2, and grants no printed Might bonus.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, gear) ← put s p "RAD-071" .base
  let (s, unit) ← putAt s p "VEN-014" field
  let (s, foe) ← put s q "VEN-071" .base
  let s := s.control p field
  let equipped ← activate s p gear 0 [unit] ⟨1, []⟩
  let detached := (detachObj equipped gear).1
  return (activate s p gear 0 [unit] ⟨0, []⟩).isNone &&
    (activate s p gear 0 [foe] ⟨1, []⟩).isNone &&
    equipped.mightNow unit == some 2 && equipped.kwAmount unit .shield == 2 &&
    (equipped.inCombatAt field q).mightNow unit == some 4 &&
    detached.kwAmount unit .shield == 0

-- Wrath of the Freljord enters ready and gets its bonus while defending.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, card) ← put s p "RAD-077" .hand
  let done ← play (s.control p s.bf0) p card [s.bf0]
  let unit ← (done.unitsAtOf s.bf0 p).head?
  return done.tired unit == some false && done.mightNow unit == some 7 &&
    (done.inCombatAt s.bf0 q).mightNow unit == some 10

-- Avalanche damages all Units in both Bases and leaves the Battlefield alone.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "RAD-079" .hand
  let (s, own) ← put s p "VEN-071" .base
  let (s, foe) ← put s q "VEN-071" .base
  let (s, safeUnit) ← putAt s p "VEN-071" s.bf0
  let (s, gear) ← put s p "SFD-117" .base
  let done ← play (s.control p s.bf0) p spell
  let damage (id : ObjId) := (done.obj? id).map (·.damage)
  return damage own == some 3 && damage foe == some 3 &&
    damage safeUnit == some 0 && damage gear == some 0

-- Staunch Survivor's printed Assault 2 and Shield 2 each apply in the right combat role.
#guard radianceCase fun s => do
  let p := s.me
  let (s, unit) ← putAt s p "RAD-088" s.bf0
  return s.mightNow unit == some 2 &&
    (s.inCombatAt s.bf0 p).mightNow unit == some 4 &&
    (s.inCombatAt s.bf0 s.you).mightNow unit == some 4

-- Pitiless Stalker exhausts itself and stuns an enemy Unit, never a friendly one.
#guard radianceCase fun s => do
  let p := s.me
  let (s, stalker) ← put s p "RAD-104" .base
  let (s, ally) ← put s p "VEN-071" .base
  let (s, target) ← put s s.you "VEN-071" .base
  let done ← activate s p stalker 0 [target]
  return (activate s p stalker 0 [ally]).isNone &&
    done.tired stalker == some true && (done.obj? target).any (·.stunned) &&
    (activate done p stalker 0 [target]).isNone

-- For Demacia! grants Shield only to friendly Units at the chosen Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, spell) ← put s p "RAD-117" .hand
  let (s, ally) ← putAt s p "VEN-071" field
  let (s, enemy) ← putAt s s.you "VEN-071" field
  let (s, outside) ← put s p "VEN-071" .base
  let done ← play (s.inShowdownAt field p) p spell [field]
  let (expired, _) ← (advance 100 { done with pending := [.expireTurn] } []).toOption
  return done.kwAmount ally .shield == 2 && done.kwAmount enemy .shield == 0 &&
    done.kwAmount outside .shield == 0 && expired.kwAmount ally .shield == 0

-- The Herald changes base Might to five without removing an existing buff.
#guard radianceCase fun s => do
  let p := s.me
  let (s, herald) ← put s p "RAD-118" .hand
  let (s, ally) ← put s p "VEN-014" .base
  let (s, foe) ← put s s.you "VEN-014" .base
  let waiting ← castStop (s.buff ally) p herald
  let done := settleChain { pick := (· == [ally]) } 8 waiting
  let (expired, _) ← (advance 100 { done with pending := [.expireTurn] } []).toOption
  return waiting.trigPicks.contains ally && !waiting.trigPicks.contains foe &&
    done.mightNow ally == some 6 && expired.mightNow ally == some 3

-- One-Two Punch requires a friendly Unit for the buff and an enemy Unit for the stun.
#guard radianceCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "RAD-121" .hand
  let (s, ally) ← put s p "VEN-071" .base
  let (s, enemy) ← put s s.you "VEN-071" .base
  let done ← play s p spell [ally, enemy]
  return (play s p spell [enemy, ally]).isNone &&
    (done.obj? ally).any (·.buffed) && (done.obj? enemy).any (·.stunned)

-- Protector's Shield Quick-Draws, gives one Might and Tank, and can subsequently be reattached.
#guard radianceCase fun s => do
  let p := s.me
  let (s, shield) ← put s p "RAD-123" .hand
  let (s, first) ← put s p "VEN-014" .base
  let (s, second) ← put s p "VEN-014" .base
  let equipped ← play s p shield [] { pick := (· == [first]) }
  let gear ← equipped.firstOf p .base "RAD-123"
  let moved ← activate equipped p gear 0 [second] ⟨1, []⟩
  return equipped.hasKw first .tank && equipped.mightNow first == some 3 &&
    !moved.hasKw first .tank && moved.hasKw second .tank && moved.mightNow second == some 3

-- The Outrider counts each other friendly Unit or Gear at the same Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, outrider) ← putAt s p "RAD-128" field
  let (s, _) ← putAt s p "VEN-071" field
  let (s, _) ← putAt s s.you "RAD-002" field
  let (s, _) ← put s p "SFD-117" .base
  let (together, _) ← putAt s p "RAD-002" field
  let home := (moveHome together outrider).1
  return s.hasKw outrider .tank && s.mightNow outrider == some 3 &&
    together.mightNow outrider == some 5 && home.mightNow outrider == some 3

-- Raucous Anthem readies and strengthens friendly Units at every location for the turn.
#guard radianceCase fun s => do
  let p := s.me
  let (s, anthem) ← put s p "RAD-134" .hand
  let (s, home) ← put s p "VEN-014" .base
  let (s, away) ← putAt s p "VEN-014" s.bf0
  let (s, enemy) ← put s s.you "VEN-014" .base
  let t := ((((s.control p s.bf0).tire home).tire away).tire enemy)
  let done ← play t p anthem
  let (expired, _) ← (advance 100 { done with pending := [.expireTurn] } []).toOption
  return [home, away].all (fun id => done.tired id == some false &&
      done.mightNow id == some 5 && expired.mightNow id == some 2) &&
    done.tired enemy == some true && done.mightNow enemy == some 2

-- The Chronomancer Predicts two on play and snapshots the total of its Disarm instances on attack.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, chronomancer) ← put s p "RAD-050" .hand
  let (s, target) ← putAt s q "VEN-091" field
  let (s, distant) ← put s q "VEN-071" .base
  let s := s.control q field
  let first ← (s.zone (.player p .mainDeck))[0]?
  let second ← (s.zone (.player p .mainDeck))[1]?
  let waiting ← play s p chronomancer
  let (keeping, _) ← (step 100 waiting ⟨.player p, .predictPick second false⟩).toOption
  let (played, _) ← (step 100 keeping ⟨.player p, .predictPick first false⟩).toOption
  let unit ← played.firstOf p .base "RAD-050"
  let strengthened := (addTempKw ⟨.disarm, .none⟩ .turn played unit).1
  let strengthened := strengthened.modObj unit (fun o => { o with exhausted := false })
  let (attack, _) ← (step 100 strengthened
    ⟨.player p, .standardMove unit (.battlefield field)⟩).toOption
  let (queued, _) ← (step 100 attack ⟨.player p, .putTrigger 0 [target]⟩).toOption
  let stripped := queued.modObj unit (fun o => { o with tempKws := [] })
  let done := settleChain {} 8 stripped
  let (expired, _) ← (advance 100 { done with pending := [.expireTurn] } []).toOption
  return (played.zone (.player p .mainDeck)).take 2 == [second, first] &&
    attack.trigPicks == [target] && !attack.trigPicks.contains distant &&
    queued.kwAmount unit .disarm == 3 && stripped.kwAmount unit .disarm == 2 &&
    (queued.zone .chain).length == 1 && done.mightNow target == some 7 &&
    expired.mightNow target == some 10

-- A Peddler arriving after combat starts Disarms once. Its return during the same combat does not.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, _) ← putAt s p "VEN-071" field
  let (s, target) ← putAt s q "VEN-091" field
  let (s, peddler) ← put s p "RAD-054" .base
  let s := ((s.control q field).modObj field (fun o => { o with contested := some p }))
    |>.inShowdownAt field p
  let entered := (sendToBf field s peddler).1
  let (combat, events) := entered.observeCombat entered.pending
  let updated := { entered with combat }
  let resolved ← fire updated events { pick := (· == [target]) }
  let returned := (sendToBf field (moveHome updated peddler).1 peddler).1
  return events == [.combatJoined field p [peddler]] && resolved.mightNow target == some 9 &&
    (returned.observeCombat returned.pending).2.isEmpty

-- Clanging Sentry is itself a Mech. Two copies grant a single, combined Disarm to each friendly Mech.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, sentry) ← putAt s p "RAD-055" field
  let (s, extra) ← put s p "RAD-055" .base
  let (s, nonMech) ← putAt s p "VEN-071" field
  let (s, enemyMech) ← putAt s q "RAD-009" field
  let (s, target) ← putAt s q "VEN-091" field
  let s := (s.control q field).inShowdownAt field p
  let combat := Event.combatStarted field p
  let triggers := s.detect [combat]
  let defenderTriggers := s.detect [.combatStarted field q]
  let done ← fire s [combat] { pick := (· == [target]) }
  return s.kwAmount sentry .disarm == 2 && s.kwAmount extra .disarm == 2 &&
    s.kwAmount nonMech .disarm == 0 && s.kwAmount enemyMech .disarm == 0 &&
    triggers.length == 1 && triggers.head?.any (fun t =>
      t.source == sentry && t.eventAmount == some 2) &&
    defenderTriggers.all (fun t => t.triggerKeyword != some .disarm) &&
    done.mightNow target == some 8

-- Riptide Mage can pay Accelerate and weakens only an enemy Unit.
#guard radianceCase fun s => do
  let p := s.me
  let (s, mage) ← put s p "RAD-058" .hand
  let (s, enemy) ← put s s.you "VEN-091" .base
  let (s, ally) ← put s p "VEN-071" .base
  let waiting ← castStop s p mage
  let accelerated ← cast (s.fund p 5 (mind := 2)) p mage ⟨5, [.mind, .mind]⟩
    [] { pick := (· == [enemy]) }
  let unit ← accelerated.firstOf p .base "RAD-058"
  return waiting.trigPicks == [enemy] && !waiting.trigPicks.contains ally &&
    accelerated.tired unit == some false && accelerated.mightNow enemy == some 7

-- Supernova pays Mind Power, deals ten and then draws two.
#guard radianceCase fun s => do
  let p := s.me
  let (s, nova) ← put s p "RAD-059" .hand
  let (s, target) ← put s s.you "VEN-091" .base
  let done ← cast (s.fund p 9 (mind := 1)) p nova ⟨9, [.mind]⟩ [target]
  return (cast (s.fund p 9 (order := 1)) p nova ⟨9, [.order]⟩ [target]).isNone &&
    done.countIn s.you .trash "VEN-091" == 1 && done.handN p == s.handN p + 1

-- Disposal Expert enters ready when alone and gives one enemy here −2 Might when attacking.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, expert) ← put s p "RAD-093" .hand
  let (s, defender) ← putAt s q "VEN-091" field
  let (withAlly, _) ← put s p "VEN-071" .base
  let s := s.control q field
  let withAlly := withAlly.control q field
  let ready ← play s p expert
  let exhausted ← play withAlly p expert
  let unit ← ready.firstOf p .base "RAD-093"
  let other ← exhausted.firstOf p .base "RAD-093"
  let (attack, _) ← (step 100 ready ⟨.player p, .standardMove unit (.battlefield field)⟩).toOption
  let weakened := settleChain { pick := (· == [defender]) } 8 attack
  return exhausted.tired other == some true && attack.trigPicks == [defender] &&
    weakened.mightNow defender == some 8

-- Siren uses Ganking to attack directly from another Battlefield and Disarms there.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let origin := s.bf0
  let field ← s.battlefields.find? (· != origin)
  let (s, siren) ← putAt s p "RAD-097" origin
  let (s, target) ← putAt s q "VEN-091" field
  let (s, away) ← putAt s p "VEN-071" origin
  let s := (s.control p origin).control q field
  let (attack, _) ← (step 100 s ⟨.player p, .standardMove siren (.battlefield field)⟩).toOption
  let done := settleChain { pick := (· == [target]) } 8 attack
  return attack.trigPicks == [target] && !attack.trigPicks.contains away &&
    (done.obj? siren).any (·.loc == some field) && done.mightNow target == some 9

end RiftboundTest
