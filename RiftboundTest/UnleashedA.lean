module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests: Unleashed (scenario tests of single cards)

As `SpiritforgedA.lean`: each test puts the cards it needs in the lab (the Main Phase of the first
turn), plays or fires, lets the Chain resolve, and reads what happened.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- Run a scenario in the lab; it must say `true`. -/
meta def tun (f : GameState → Option Bool) : Bool :=
  match lab with
  | some s => (f s).getD false
  | none => false

-- Inferna (UNL-002): Ambush: it can be played as a Reaction to a Battlefield where its player has
-- units, and not to the Base or to a Battlefield without units of that player
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "OGN-051" bf
  let (s3, other) ← putBf s2 s.me "OGN-276"
  let (s4, c) ← put s3 s.me "UNL-002" .hand
  let (s5, _) ← onChain s4 s.you "OGN-004"
  let rich := s5.rich s.me
  let pay := payOf rich c
  return reactable rich s.me c pay [bf] && !reactable rich s.me c pay [other] &&
    !reactable rich s.me c pay [] && playable rich s.me c pay (some bf) &&
    !playable rich s.me c pay (some other)

-- Mischievous Marai (UNL-003): when played to a battlefield (an open one, with Miss Fortune in
-- play), 2 damage to an enemy unit there
#guard tun fun s => do
  let (s0, _) ← put s s.me "OGN-193" .base
  let (s1, c) ← put s0 s.me "UNL-003" .hand
  let (s2, e) ← putAt s1 s.you "OGN-088" s.bf0
  let toBf ← play s2 s.me c [s.bf0] { pick := fun ts => ts == [e] }
  let toBase ← play s2 s.me c [] { pick := fun ts => ts == [e] }
  return (toBf.obj? e).any (·.damage == 2) && (toBase.obj? e).any (·.damage == 0)

/-- The state where the legend of the player has `n` XP. -/
meta def withXPOf (s : GameState) (p : PlayerId) (n : Nat) : Option GameState :=
  match s.zone (.player p .legendZone) with
  | l :: _ => some (s.modObj l (fun o => { o with xp := n }))
  | [] => none

/-- The place of the first activated ability of the card. -/
meta def firstAct (s : GameState) (u : ObjId) : Nat :=
  ((s.cardDef? u).map (fun d => d.fullAbilities.findIdx (fun a =>
    match a with | Ability.activated .. => true | _ => false))).getD 0

-- Smite (UNL-007): the unit it kills is banished, not put in the Trash
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-007" .hand
  let (s2, e) ← putAt s1 s.you "UNL-111" s.bf0
  let s3 ← play s2 s.me c [e]
  return s3.countIn s.you .banishment "UNL-111" == 1 && s3.countIn s.you .trash "UNL-111" == 0

-- Lotus Trap (UNL-013): the damage dealt to the unit this turn is doubled
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-013" .hand
  let (s2, e) ← putAt s1 s.you "OGN-088" s.bf0
  let s3 ← play s2 s.me c [e]
  return ((dealObj 1 s3 e).1.obj? e).any (·.damage == 2) &&
    ((dealObj 1 s2 e).1.obj? e).any (·.damage == 1)

-- Scryer's Bloom (UNL-136) enters exhausted
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-136" .hand
  let s2 ← play s1 s.me c
  let g ← s2.firstOf s.me .base "UNL-136"
  return s2.tired g == some true

-- Crowd Favorite (UNL-102): spend 2 XP to buff it; not without the XP
#guard tun fun s => do
  let (s1, u) ← put s s.me "UNL-102" .base
  let s2 ← withXPOf s1 s.me 2
  let s3 ← activate s2 s.me u (firstAct s2 u)
  let s4 ← withXPOf s1 s.me 1
  let s5 := activate s4 s.me u (firstAct s4 u)
  return ((s3.obj? u).any (·.buffed)) && s3.xpOf s.me == 0 &&
    (match s5 with | none => true | some t => !((t.obj? u).any (·.buffed)))

-- Alpha Wildclaw (UNL-057): the units of its player here with less Might can't be chosen by
-- enemies; the stronger ones, and those elsewhere, can
#guard tun fun s => do
  let (s1, _) ← putAt s s.me "UNL-057" s.bf0
  let (s2, weak) ← putAt s1 s.me "UNL-111" s.bf0
  let (s3, base) ← put s2 s.me "UNL-111" .base
  return s3.blocksChoice s.you weak && !s3.blocksChoice s.you base && !s3.blocksChoice s.me weak

-- Vilemaw (UNL-060): the enemy units here with less Might deal no combat damage
#guard tun fun s => do
  let (s1, _) ← putAt s s.me "UNL-060" s.bf0
  let (s2, weak) ← putAt s1 s.you "UNL-111" s.bf0
  let (s3, mine) ← putAt s2 s.me "UNL-111" s.bf0
  return s3.noCombatDamage weak && !s3.noCombatDamage mine

-- Wily Newtfish (UNL-108): +1 Might after the player gained XP this turn
#guard tun fun s => do
  let (s1, u) ← put s s.me "UNL-108" .base
  let s2 := gainXPOf 1 s1 s.me
  return s1.mightNow u == some 4 && s2.mightNow u == some 5

-- Shadow Watcher (UNL-037) enters ready if a unit of its player died in their Beginning Phase
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-037" .hand
  let d ← s1.cardDef? c
  let s2 := { s1 with phase := .beginning }.noteUnitDied s.me
  let s3 := { s2 with phase := .main }
  return !s1.readyNow s.me c d && s3.readyNow s.me c d

end RiftboundTest
