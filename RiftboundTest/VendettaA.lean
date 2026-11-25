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

end RiftboundTest
