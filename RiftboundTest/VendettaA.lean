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

end RiftboundTest
