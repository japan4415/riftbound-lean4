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

-- Protector's Shield Quick-Draws, gives one Might and Tank, and can Equip once detached.
#guard radianceCase fun s => do
  let p := s.me
  let (s, shield) ← put s p "RAD-123" .hand
  let (s, first) ← put s p "VEN-014" .base
  let (s, second) ← put s p "VEN-014" .base
  let equipped ← play s p shield [] { pick := (· == [first]) }
  let gear ← equipped.firstOf p .base "RAD-123"
  let pay : RunePool.Payment := ⟨1, []⟩
  let (left, _) ← moveObj equipped first (.player p .trash)
  let (detached, _) ← (advance 100 { left with pending := .cleanup :: left.pending } []).toOption
  let moved ← activate detached p gear 0 [second] pay
  return equipped.hasKw first .tank && equipped.mightNow first == some 3 &&
    (activate equipped p gear 0 [second] pay).isNone &&
    (detached.obj? gear).any (·.attached.isNone) && !detached.hasKw second .tank &&
    (moved.obj? gear).any (·.attached == some second) &&
    moved.hasKw second .tank && moved.mightNow second == some 3

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

/-- Bomb Gear tokens controlled by the player at the given Battlefield. -/
private meta def bombsAt (s : GameState) (p : PlayerId) (field : ObjId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun id =>
    (s.obj? id).any (fun o =>
      o.kind == .token ⟨"RAD-T02"⟩ && o.controller == p && o.loc == some field))

-- Amateur Demolitionist plays a ready Bomb at a Battlefield picked during resolution.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, demolitionist) ← put s p "RAD-001" .hand
  let (s, _) ← putAt s q "VEN-071" field
  let (s, rockfall) ← putBf s p "SFD-216"
  let before := s.control q field
  let placed ← play before p demolitionist [] { obj := (· == field) }
  let atRockfall ← play before p demolitionist [] { obj := (· == rockfall) }
  let bomb ← (bombsAt placed p field).head?
  return (bombsAt placed p field).length == 1 && (bombsAt placed p away).isEmpty &&
    (bombsAt atRockfall p rockfall).length == 1 && placed.tired bomb == some false &&
    (placed.obj? field).any (fun o => o.contested.isNone && o.control == some q)

-- A Bomb's death uses its old Battlefield after it disappears, and chains only to your Bombs there.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, enemy) ← putAt s q "VEN-091" field
  let (s, distant) ← putAt s q "VEN-091" away
  let s := (s.control q field).control q away
  let s := createN ⟨"RAD-T02"⟩ p (some field) true 2 s
  let s := createOne ⟨"RAD-T02"⟩ p (some away) true s
  let s := createOne ⟨"RAD-T02"⟩ q (some field) true s
  let bomb ← (bombsAt s p field).head?
  let (dead, events) := killObj s bomb
  let pending := insertTriggers (dead.detect events) [.cleanup, .priority p]
  let (waiting, _) ← (advance 100 { dead with pending } []).toOption
  let done := settleChain { pick := (· == [enemy]) } 16 waiting
  return waiting.trigPicks == [enemy] && !waiting.trigPicks.contains distant &&
    (done.obj? enemy).any (·.damage == 4) && (done.obj? distant).any (·.damage == 0) &&
    (bombsAt done p field).isEmpty && (bombsAt done p away).length == 1 &&
    (bombsAt done q field).length == 1 && done.offBoardToken.isNone

-- Rally for War chooses an occupied enemy Battlefield and contests it with three exhausted Recruits.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let empty ← s.battlefields.find? (· != field)
  let (s, rally) ← put s p "RAD-007" .hand
  let (s, _) ← putAt s q "VEN-091" field
  let (s, rockfall) ← putBf s q "SFD-216"
  let (s, _) ← putAt s q "VEN-091" rockfall
  let s := ((s.control q field).control q empty).control q rockfall
  let done ← play s p rally [field]
  let blocked ← play s p rally [rockfall]
  let recruits := (done.unitsAtOf field p).filter (fun id =>
    (done.obj? id).any (fun o => o.kind == .token ⟨"VEN-T04"⟩))
  return (play s p rally [empty]).isNone && (play (s.control p field) p rally [field]).isNone &&
    recruits.length == 3 && recruits.all (fun id => done.tired id == some true) &&
    (blocked.unitsAtOf rockfall p).isEmpty &&
    (done.obj? field).any (·.contested == some p)

-- Both Mech makers play their tokens at the same Battlefield. Only the Apparatus readies both.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, anchor) ← putAt s p "VEN-071" field
  let (s, apparatus) ← put s p "RAD-009" .hand
  let (s, smith) ← put s p "RAD-049" .hand
  let s := s.control p field
  let ready ← play s p apparatus [field]
  let exhausted ← play s p smith [field]
  let others (t : GameState) := (t.unitsAtOf field p).erase anchor
  return (others ready).length == 2 && (others exhausted).length == 2 &&
    (others ready).all (fun id => ready.tired id == some false) &&
    (others exhausted).all (fun id => exhausted.tired id == some true) &&
    (others ready).any (fun id => (ready.obj? id).any (·.kind == .token (tokenId "Mech"))) &&
    (others exhausted).any (fun id =>
      (exhausted.obj? id).any (·.kind == .token (tokenId "Mech")) &&
        exhausted.mightNow id == some 3)

-- Short-Fused adds Bonus Damage to an allied Gear's ability even after the Bomb disappears.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, ziggs) ← put s p "RAD-023" .hand
  let (s, curse) ← put s p "VEN-010" .hand
  let (s, enemy) ← putAt s q "VEN-091" field
  let s := s.control q field
  let placed ← play s p ziggs [] { obj := (· == field) }
  let bomb ← (bombsAt placed p field).head?
  let (dead, events) := killObj placed bomb
  let exploded ← fire { dead with pending := [.cleanup, .priority p] } events
    { pick := (· == [enemy]) }
  let cursed ← play { exploded with pending := [.priority p] } p curse [enemy]
  return (exploded.obj? enemy).any (·.damage == 3) &&
    (cursed.obj? enemy).any (·.damage == 5) && exploded.offBoardToken.isNone

-- Dreamroot draws for a combat its controller wins at this Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, card) ← put s p "RAD-024" .hand
  let (s, _) ← putAt s p "VEN-071" field
  let deployed ← play (s.control p field) p card [field]
  let home ← fire deployed [.combatWon field p]
  let awayWin ← fire deployed [.combatWon away p]
  let lost ← fire deployed [.combatWon field q]
  return home.handN p == deployed.handN p + 1 &&
    awayWin.handN p == deployed.handN p && lost.handN p == deployed.handN p

-- Resource Extractor plays exhausted Gold only at its controller's Ending Phase and with control.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, card) ← put s p "RAD-052" .hand
  let (s, _) ← putAt s p "VEN-071" field
  let settled ← play (s.control p field) p card [field]
  let mine ← fire settled [.phaseStarted p .ending]
  let theirs ← fire settled [.phaseStarted q .ending]
  let uncontrolled ← fire (settled.control q field) [.phaseStarted p .ending]
  let gold ← (mine.zone (.player p .base)).find? (fun id => (mine.cardDef? id).any (·.name == "Gold"))
  return mine.countNamed p .base "Gold" == 1 && mine.tired gold == some true &&
    theirs.countNamed p .base "Gold" == 0 && uncontrolled.countNamed p .base "Gold" == 0

-- Traveler checks the location, controller and Deploy keyword of the Gear.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, traveler) ← putAt s p "RAD-072" field
  let (s, _) ← putAt s p "SFD-117" field
  let (s, _) ← putAt s q "RAD-002" field
  let (s, gear) ← putAt s p "RAD-002" away
  let nearby := (sendToBf field s gear).1
  let home := (moveHome nearby traveler).1
  return s.mightNow traveler == some 2 && nearby.mightNow traveler == some 3 &&
    home.mightNow traveler == some 2

-- Pillaged Armory can Buff on play and on a Conquer at its own Battlefield, even for an ally in Base.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, armory) ← put s p "RAD-073" .hand
  let (s, _) ← putAt s p "VEN-071" field
  let (s, first) ← put s p "VEN-071" .base
  let (s, second) ← put s p "VEN-071" .base
  let made ← play (s.control p field) p armory [field] { pick := (· == [first]) }
  let conquered ← fire made [.scored p field true] { pick := (· == [second]) }
  let distant ← fire made [.scored p away true] { pick := (· == [second]) }
  return (made.obj? first).any (·.buffed) && (conquered.obj? second).any (·.buffed) &&
    (distant.obj? second).any (fun o => !o.buffed)

-- Explosimian plays three Bombs together at a single Battlefield after Hold.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, _) ← putAt s p "RAD-094" field
  let s := s.control p field
  let held ← fire s [.scored p field false] { obj := (· == away) }
  let conquered ← fire s [.scored p field true] { obj := (· == away) }
  return (bombsAt held p field).isEmpty && (bombsAt held p away).length == 3 &&
    (bombsAt conquered p away).isEmpty

-- Satchel Charge moves the friendly target to its finalized destination and picks a Bomb location later.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, card) ← put s p "RAD-096" .hand
  let (s, anchor) ← putAt s p "VEN-071" field
  let (s, unit) ← put s p "VEN-071" .base
  let s := (s.control p field).fund p 3 (chaos := 1)
  let (onChain, _) ← (step 100 s
    ⟨.player p, .playCard card ⟨3, [.chaos]⟩ [unit] none none (.destination (some field))⟩).toOption
  let says : Says := { obj := (· == away) }
  let done := settleChain says 12 onChain
  let negated := settleChain says 12 (sendToBf field onChain unit).1
  let ignored := settleChain says 12 (sendObj .trash onChain unit).1
  return (done.unitsAtOf field p).contains unit && (done.unitsAtOf field p).contains anchor &&
    (bombsAt done p field).isEmpty && (bombsAt done p away).length == 1 &&
    (bombsAt negated p away).length == 1 && (bombsAt ignored p away).isEmpty

-- The Good Stuff discards, draws, and returns to hand on a friendly Hold at that Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, card) ← put s p "RAD-106" .hand
  let (s, _) ← putAt s p "VEN-071" field
  let made ← play (s.control p field) p card [field]
  let held ← fire made [.scored p field false]
  let lost ← fire made [.scored q field false]
  return made.handN p == s.handN p + 1 && held.countIn p .hand "RAD-106" == 1 &&
    lost.countIn p .trash "RAD-106" == 1

-- Explosive separately pays for Bomb creation and can sacrifice a friendly Gear when defending.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, ziggs) ← putAt s p "RAD-112" field
  let (s, _) ← putAt s q "VEN-091" field
  let (s, gear) ← put s p "SFD-117" .base
  let s := s.control p field
  let placed ← activate s p ziggs 0 [] ⟨1, []⟩ { obj := (· == field) }
  let defense := s.inShowdownAt field q
  let stronger ← fire defense [.combatStarted field q]
  let declined ← fire defense [.combatStarted field q] { yes := false }
  return (activate s p ziggs 0).isNone &&
    (bombsAt placed p field).length == 1 && placed.tired ziggs == some true &&
    (activate placed p ziggs 0 [] ⟨1, []⟩).isNone &&
    stronger.mightNow ziggs == some 6 && stronger.countIn p .trash "SFD-117" == 1 &&
    declined.inPlay.contains gear && declined.mightNow ziggs == some 4

-- Hexplosives Expert spends one Energy, Power of any domain and its own Exhaust to play a Bomb.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, legend) ← put s p "RAD-141" .legendZone
  let (s, _) ← putAt s s.you "VEN-071" field
  let s := s.control s.you field
  let paid ← activate s p legend 0 [] ⟨1, [.mind]⟩ { obj := (· == field) }
  return (activate s p legend 0 [] ⟨1, []⟩).isNone &&
    (activate s p legend 0 [] ⟨0, [.mind]⟩).isNone &&
    paid.tired legend == some true && (bombsAt paid p field).length == 1

-- Amplifier can sacrifice a friendly Bomb to draw and doubles its Deathknell only at this Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, card) ← put s p "RAD-017" .hand
  let (s, enemy) ← putAt s q "VEN-091" field
  let (s, distant) ← putAt s q "VEN-091" away
  let s := (s.control q field).control q away
  let s := createOne ⟨"RAD-T02"⟩ p (some field) true s
  let skipped ← play s p card [field] { yes := false }
  let paid ← play s p card [field] { pick := (· == [enemy]) }
  let separate := createOne ⟨"RAD-T02"⟩ p (some away) true paid
  let awayBomb ← (bombsAt separate p away).head?
  let (dead, events) := killObj separate awayBomb
  let awayResult ← fire { dead with pending := [.cleanup, .priority p] } events
    { pick := (· == [distant]) }
  return skipped.handN p + 1 == s.handN p && (bombsAt skipped p field).length == 1 &&
    paid.handN p == s.handN p && (bombsAt paid p field).isEmpty &&
    (paid.obj? enemy).any (·.damage == 4) && (awayResult.obj? distant).any (·.damage == 2)

-- The Poster offers an Energy payment on play and on Conquer at its location.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, poster) ← put s p "RAD-116" .hand
  let (s, _) ← putAt s p "VEN-071" field
  let s := s.control p field
  let recruitIds (t : GameState) := (t.zone (.player p .base)).filter (fun id =>
    (t.obj? id).any (·.kind == .token ⟨"VEN-T04"⟩))
  let paid ← cast (s.fund p 2) p poster ⟨1, []⟩ [field]
  let declined ← cast (s.fund p 2) p poster ⟨1, []⟩ [field] { yes := false }
  let broke ← cast (s.fund p 1) p poster ⟨1, []⟩ [field]
  let conquered ← fire (paid.fund p 1) [.scored p field true]
  let distant ← fire (paid.fund p 1) [.scored p away true]
  return (recruitIds paid).length == 1 && (recruitIds declined).isEmpty &&
    (recruitIds broke).isEmpty && (recruitIds conquered).length == 2 &&
    (recruitIds distant).length == 1 && (conquered.poolOf p).energy == 0 &&
    (recruitIds conquered).all (fun id => conquered.tired id == some true)

-- Hunting Dog plays the printed Bird token in Base, exhausted with Might 1 and Deflect.
#guard radianceCase fun s => do
  let p := s.me
  let (s, dog) ← put s p "RAD-119" .base
  let (dead, events) := killObj s dog
  let done ← fire dead events
  let bird ← done.firstOf p .base "UNL-T02"
  return done.mightNow bird == some 1 && done.tired bird == some true &&
    done.deflectOf bird == 1 && (done.obj? bird).any (·.kind == .token ⟨"UNL-T02"⟩)

-- The Construct can reveal a Mech from hand or pick a friendly Mech token to enter ready.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, construct) ← put s p "RAD-011" .hand
  let (s, inHand) ← put s p "RAD-009" .hand
  let (s, enemy) ← put s q "RAD-009" .base
  let s := createOne ⟨"TKN-Mech"⟩ p none true s
  let token ← (s.zone (.player p .base)).find? (fun id =>
    (s.obj? id).any (fun o => match o.kind with | .token .. => true | _ => false))
  let funded := s.fund p 4
  let action (pick : SpellPick) : Action := ⟨.player p, .playCard construct ⟨4, []⟩ [] none none pick⟩
  let (skipped, _) ← (step 100 funded (action .plain)).toOption
  let (fromHand, handEvents) ← (step 100 funded (action (.withShowOff .plain inHand))).toOption
  let (fromBoard, boardEvents) ← (step 100 funded (action (.withShowOff .plain token))).toOption
  let ready (t : GameState) := (t.firstOf p .base "RAD-011").bind t.tired == some false
  return !ready skipped && ready fromHand && ready fromBoard &&
    handEvents.contains (.revealed p inHand) && boardEvents.all (fun ev => match ev with
      | .revealed .. => false | _ => true) && fromHand.countIn p .hand "RAD-009" == 1 &&
    [construct, enemy].all (fun id => !(legalFrameActions funded).contains
      (action (.withShowOff .plain id)))

-- Battle Preparations boosts its Unit with or without Show Off. Only the Gear play enables Runes.
#guard radianceCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "RAD-032" .hand
  let (s, gear) ← put s p "RAD-017" .base
  let (s, unit) ← put s p "RAD-011" .base
  let (s, first) ← put s p "R1" .base
  let (s, second) ← put s p "R1" .base
  let (s, third) ← put s p "R1" .base
  let s := ((s.fund p 2).tire first |>.tire second).tire third
  let paid := ⟨2, []⟩
  let shown := SpellPick.withShowOff .plain gear
  let skipped ← cast s p spell paid [unit]
  let readied ← cast s p spell paid [unit, first, second] (pick := shown)
  let zero ← cast s p spell paid [unit] (pick := shown)
  return skipped.mightNow unit == some 6 && readied.mightNow unit == some 6 &&
    [first, second, third].all (fun r => skipped.tired r == some true && zero.tired r == some true) &&
    readied.tired first == some false && readied.tired second == some false &&
    readied.tired third == some true && (cast s p spell paid [unit, first]).isNone &&
    (cast s p spell paid [unit, first, first] (pick := shown)).isNone &&
    (cast s p spell paid [unit, first, second, third] (pick := shown)).isNone

-- The Empyrean keeps its shown card's Power cost even after its own source leaves the board.
#guard radianceCase fun s => do
  let p := s.me
  let (s, dragon) ← put s p "RAD-060" .hand
  let (s, shown) ← put s p "RAD-082" .hand
  let s := s.fund p 8
  let top := s.zone (.player p .mainDeck)
  let first ← top[0]?
  let second ← top[1]?
  let third ← top[2]?
  let skipped ← cast s p dragon ⟨8, []⟩
  let (played, _) ← (step 100 s
    ⟨.player p, .playCard dragon ⟨8, []⟩ [] none none (.withShowOff .plain shown)⟩).toOption
  let source ← played.firstOf p .base "RAD-060"
  let (gone, _) ← moveObj played source (.player p .trash)
  let predicting := settleChain {} 8 gone
  let (ordered, _) ← (step 100 predicting ⟨.player p, .predictPick second false⟩).toOption
  let (done, _) ← (step 100 ordered ⟨.player p, .predictPick first false⟩).toOption
  return (step 100 predicting ⟨.player p, .predictPick third false⟩).isOk == false &&
    skipped.handN p + 1 == s.handN p && done.handN p == s.handN p + 1 &&
    (done.zone (.player p .mainDeck)).head? == some third

-- Roar can forgo its target. When it has one, the shown ally's old Might survives its departure.
#guard radianceCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "RAD-082" .hand
  let (s, shown) ← put s p "RAD-011" .base
  let (s, target) ← put s s.you "RAD-060" .base
  let s := (s.fund p 4 (body := 2)).modObj shown (fun o => { o with baseMightThisTurn := some 6 })
  let paid := ⟨4, [.body, .body]⟩
  let pick := SpellPick.withShowOff .plain shown
  let skipped ← cast s p spell paid
  let (casted, events) ← (step 100 s
    ⟨.player p, .playCard spell paid [target] none none pick⟩).toOption
  let (gone, _) ← moveObj casted shown (.player p .trash)
  let hit := settleChain {} 8 gone
  return (skipped.obj? target).any (·.damage == 0) && (hit.obj? target).any (·.damage == 6) &&
    (cast s p spell paid [target]).isNone && (cast s p spell paid [] (pick := pick)).isNone &&
    events.contains (.chosenBySpell p target) && !events.contains (.chosenBySpell p shown)

-- A facedown Hidden card is ineligible. A Guardian played from Hidden can still Show Off.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, guardian) ← put s p "RAD-103" .hidden
  let (s, facedown) ← put s p "VEN-097" .hidden
  let (s, inHand) ← put s p "VEN-097" .hand
  let (s, _) ← putAt s p "VEN-014" field
  let (s, _) ← putAt s p "VEN-014" away
  let hide (loc : ObjId) (o : Object) :=
    { o with hiddenAt := some loc, hiddenTurn := some (s.turn - 1) }
  let s := (((s.control p field).control p away).modObj guardian (hide field)).modObj
    facedown (hide away)
  let d ← s.cardDef? guardian
  let (queued, _) ← (step 100 s ⟨.player p, .activate guardian 2 ⟨0, []⟩ []⟩).toOption
  let revealed := settleChain { fromEnd := some 0 } 14 queued
  let declined := settleChain { fromEnd := some 1 } 14 queued
  let entered ← (revealed.unitsAtOf field p).find? (fun id =>
    (revealed.cardDef? id).any (·.id == cid "RAD-103"))
  return s.showOffOptions p guardian d == [inHand] &&
    (revealed.obj? entered).any (·.fromHidden) &&
    (revealed.poolOf p).any == (s.poolOf p).any + 1 &&
    (declined.poolOf p).any == (s.poolOf p).any

-- Rousing Display checks the shown card's printed Energy and plays the resulting Recruits at Base.
#guard radianceCase fun s => do
  let p := s.me
  let (s, display) ← put s p "RAD-127" .hand
  let (s, high) ← put s p "RAD-060" .hand
  let (s, low) ← put s p "RAD-011" .hand
  let s := s.fund p 5
  let small ← cast s p display ⟨5, []⟩
  let large ← cast s p display ⟨5, []⟩ (pick := .withShowOff .plain high)
  let placed := (large.zone (.player p .base)).filter (fun id =>
    (large.cardDef? id).any (·.name == "Recruit"))
  return small.countNamed p .base "Recruit" == 2 && placed.length == 4 &&
    placed.all (fun id => large.tired id == some true && large.mightNow id == some 1) &&
    (cast s p display ⟨5, []⟩ (pick := .withShowOff .plain low)).isNone

end RiftboundTest
