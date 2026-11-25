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

end RiftboundTest
