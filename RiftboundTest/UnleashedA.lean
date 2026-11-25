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

-- Valley of Idols (UNL-218): a unit played there is buffed for 1 Energy
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "UNL-218"
  let (s2, u) ← putAt s1 s.me "UNL-111" bf
  let s3 ← fire (s2.rich s.me) [Event.played s.me u]
  return !((s2.obj? u).any (·.buffed)) && ((s3.obj? u).any (·.buffed))

-- Vaults of Helia (UNL-219): after the player holds there, their units cost 1 more this turn
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "UNL-219"
  let (s2, c) ← put s1 s.me "UNL-111" .hand
  let s3 ← fire s2 [Event.scored s.me bf false]
  return s2.energyCost? s.me c == some 1 && s3.energyCost? s.me c == some 2

-- Mirror Image (UNL-200): a ready Reflection token at the Base becomes a copy of the unit, with
-- Temporary
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-200" .hand
  let (s2, e) ← putAt s1 s.you "UNL-111" s.bf0
  let s3 ← play s2 s.me c [e]
  let base := (s3.zone (.player s.me .base)).filter (fun u => (s3.cardDef? u).any (·.id == cid "UNL-111"))
  return base.length == 1 && base.all (fun u => s3.hasKw u .temporary) &&
    base.all (fun u => s3.tired u == some false)

-- Keeper of Masks (UNL-081): two Reflection tokens, copies of it (so with Temporary too)
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-081" .hand
  let s2 ← play s1 s.me c
  return s2.countIn s.me .base "UNL-081" == 3

-- Baron Nashor (UNL-147): the Baron Pit enters the board once, and Baron Nashor goes there
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-147" .hand
  let s2 ← play s1 s.me c
  let pits := (s2.zone .battlefieldZone).filter (fun b => (s2.cardDef? b).any (·.name == "Baron Pit"))
  let nashor := (s2.zone .battlefieldZone).find? (fun u => (s2.cardDef? u).any (·.id == cid "UNL-147"))
  return pits.length == 1 && s2.battlefields.length == s1.battlefields.length + 1 &&
    nashor.any (fun u => (s2.obj? u).any (fun o => o.loc == pits.head?))

-- Arachnoid Horror (UNL-117): it, and the other friendly units, can be played to a Battlefield
-- where an enemy unit is alone
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-117" .hand
  let (s2, _) ← putAt s1 s.you "UNL-111" s.bf0
  let (s3, _) ← putAt s2 s.you "UNL-111" s.bf0
  let (s4, d) ← put s2 s.me "UNL-111" .hand
  let (s5, _) ← put s4 s.me "UNL-117" .base
  let (s6, _) ← putAt s5 s.me "UNL-117" s.bf0
  return (s2.playBfOptions s.me c).contains s.bf0 && !(s3.playBfOptions s.me c).contains s.bf0 &&
    (s5.playBfOptions s.me d).contains s.bf0 && !(s2.playBfOptions s.me d).contains s.bf0 &&
    s6.hasKw c .temporary == false

-- LeBlanc, Everywhere at Once (UNL-090): the Temporary units of its player at its Battlefield are
-- not killed at the start of their Beginning Phase
#guard tun fun s => do
  let (s1, t) ← putAt s s.me "UNL-081" s.bf0
  let (s2, _) ← putAt s1 s.me "UNL-090" s.bf0
  return (tempUnits s1 s.me).contains t && !(tempUnits s2 s.me).contains t

-- Katarina, Reckless (UNL-023): she readies when her player hides a card
#guard tun fun s => do
  let (s1, k) ← put s s.me "UNL-023" .base
  let (s2, c) ← put s1 s.me "UNL-111" .hidden
  let s3 := s2.tire k
  let s4 ← fire s3 [Event.moved c c (.player s.me .hidden)]
  return s3.tired k == some true && s4.tired k == some false

-- Tricksy Tentacles (UNL-054): enemy units of total Might 8 or less are moved to one place
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-054" .hand
  let (s2, a) ← putAt s1 s.you "OGN-135" s.bf0
  let (s3, b) ← putAt s2 s.you "OGN-135" s.bf0
  let s4 ← play s3 s.me c [a, b] { fromEnd := some 1 }
  return (s4.obj? a).any (·.loc != some s.bf0) && (s4.obj? b).any (·.loc != some s.bf0)

-- Elder Dragon (UNL-118): any damage kills enemy units; the other player's units are not affected
#guard tun fun s => do
  let (s1, _) ← putAt s s.me "UNL-118" s.bf0
  let (s2, e) ← putAt s1 s.you "OGN-088" s.bf0
  let (s3, m) ← putAt s2 s.me "OGN-088" s.bf0
  let s4 := s3.modObj e (fun o => { o with damage := 1 })
  let s5 := s4.modObj m (fun o => { o with damage := 1 })
  return !s2.lethal e && s4.lethal e && !s5.lethal m

-- Maduli the Gatekeeper (UNL-144) can't be readied: not by the Awaken Phase, not by an effect
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-144" .hand
  let s2 ← play s1 s.me c
  let m ← s2.firstOf s.me .base "UNL-144"
  let s3 := s2.tire m
  let s4 := s3.mapObjects (readyOf s.me)
  return s3.tired m == some true && s4.tired m == some true && (readyEffect s3 m).1.tired m == some true

-- Syndra, Transcendent (UNL-146): in a showdown, the Spells of her player have Repeat for 2 Energy
-- and a Chaos rune
#guard tun fun s => do
  let (s1, _) ← putAt s s.me "UNL-146" s.bf0
  let (s2, sp) ← put s1 s.me "UNL-159" .hand
  let d ← s2.cardDef? sp
  let s3 := s2.inShowdownAt s.bf0 s.me
  return (s2.extrasRaw s.me sp d).isEmpty && (s3.extrasRaw s.me sp d).length == 1

-- Stalking Wolf (UNL-166): a Bird, Cat, Dog or Poro of its player is killed as it is played
#guard tun fun s => do
  let (s1, w) ← put s s.me "UNL-166" .hand
  let (s2, bird) ← put s1 s.me "UNL-056" .base
  let (s3, other) ← put s2 s.me "UNL-111" .base
  return s3.extraOk s.me w [bird] && !s3.extraOk s.me w [other] && !s3.extraOk s.me w []

-- Blighted Battleaxe (UNL-019): at the end of its turn, the unit that did not conquer is dealt 4
-- and the Equipment is unattached
#guard tun fun s => do
  let (s1, u) ← putAt s s.me "OGN-088" s.bf0
  let (s2, g) ← put s1 s.me "UNL-019" .base
  let s3 := s2.modObj g (fun o => { o with attached := some u })
  let ts := s3.timedTriggers s.me .endOfTurn
  return ts.any (fun t => t.source == u && t.card == cid "UNL-019")

-- Cursed Sarcophagus (UNL-148): the units of its player's Trash are banished with it
#guard tun fun s => do
  let (s1, g) ← put s s.me "UNL-148" .hand
  let (s2, _) ← put s1 s.me "UNL-111" .trash
  let (s3, _) ← put s2 s.me "OGN-007" .trash
  let s4 ← play s3 s.me g
  return s4.countIn s.me .banishment "UNL-111" == 1 && s4.countIn s.me .trash "UNL-111" == 0

-- Frigid Jewel (UNL-074): the second card drawn in the turn gives a friendly unit +2 Might
#guard tun fun s => do
  let (s1, _) ← put s s.me "UNL-074" .base
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let (s3, _) ← put s2 s.me "UNL-111" .hand
  let a ← fire { s3 with drawLog := [(s.me, s3.turn)] } [Event.drew s.me]
  let b ← fire { s3 with drawLog := [(s.me, s3.turn), (s.me, s3.turn)] } [Event.drew s.me]
  let c ← fire { s3 with drawLog := [(s.me, s3.turn), (s.me, s3.turn), (s.me, s3.turn)] }
    [Event.drew s.me]
  return a.mightNow u == s3.mightNow u && c.mightNow u == s3.mightNow u &&
    b.mightNow u == (s3.mightNow u).map (· + 2)

-- Green Father (UNL-195) and Brush (UNL-T03): the Battlefield is replaced by Brush, with its units;
-- scoring there puts the old Battlefield back
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, u) ← putAt s1 s.me "UNL-111" bf
  let some tok := s2.tokenCard "Brush" | none
  let r := replaceBf tok s.me s2 bf
  let s3 := r.1
  let brush := (s3.zone .battlefieldZone).find? (fun b => (s3.cardDef? b).any (·.name == "Brush"))
  let some nb := brush | none
  let r2 := restoreBf s3 nb
  let s4 := r2.1
  return (s3.obj? u).any (·.loc == some nb) && s3.battlefields.length == s2.battlefields.length &&
    !(s3.battlefields.contains bf) &&
    (s4.battlefields.any (fun b => (s4.cardDef? b).any (·.id == cid "OGN-275"))) &&
    !(s4.battlefields.any (fun b => (s4.cardDef? b).any (·.name == "Brush"))) &&
    (s4.obj? u).any (fun o => o.loc.any (fun l => (s4.cardDef? l).any (·.id == cid "OGN-275")))

-- Heedless Resurrection (UNL-142): kill a friendly unit, play a unit from the Trash that costs no
-- more than it
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-142" .hand
  let (s2, k) ← put s1 s.me "UNL-003" .base
  let (s3, _) ← put s2 s.me "UNL-111" .trash
  let s4 ← play s3 s.me c [k] { obj := fun o => (s3.cardDef? o).any (·.id == cid "UNL-111") }
  return s4.countIn s.me .trash "UNL-003" == 1 && s4.countIn s.me .base "UNL-111" == 1

-- Blast Cone (UNL-133): when its player moves an enemy unit with an effect, it can stun it
#guard tun fun s => do
  let (s1, g) ← put s s.me "UNL-133" .base
  let (s2, e) ← putAt s1 s.you "UNL-111" s.bf0
  let a ← fire s2 [Event.movedByEffect s.me e]
  let b ← fire s2 [Event.movedByEffect s.you e]
  return ((a.obj? e).any (·.stunned)) && !((b.obj? e).any (·.stunned)) &&
    (a.tired g == some true)

-- Undying Legion (UNL-025): with another card played this turn, it is played from the Trash
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-111" .hand
  let (s2, l) ← put s1 s.me "UNL-025" .trash
  let before := activate s2 s.me l (firstAct s2 l)
  let s3 ← play s2 s.me c
  let s4 ← activate s3 s.me l (firstAct s3 l) [] ⟨3, [.fury]⟩
  return before.isNone && s4.countIn s.me .trash "UNL-025" == 0 && s4.countIn s.me .base "UNL-025" == 1

-- Virtuoso (UNL-181): four spells banished with it go to the Trash, and its player channels
-- and draws
#guard tun fun s => do
  let (s1, v) ← put s s.me "UNL-181" .legendZone
  let (s2, a) ← put s1 s.me "UNL-159" .banishment
  let (s3, b) ← put s2 s.me "UNL-159" .banishment
  let (s4, c) ← put s3 s.me "UNL-159" .banishment
  let s5 := [a, b, c].foldl (fun t x => t.modObj x (fun o => { o with banishedWith := some v })) s4
  let (s6, sp) ← put s5 s.me "UNL-159" .hand
  let (s7, sp') ← moveObj s6 sp .chain
  let s8 := s7.modObj sp' (fun o => { o with energyPaid := 4, playedTurn := some s7.turn })
  let r ← fire s8 [Event.played s.me sp']
  return r.countIn s.me .trash "UNL-159" == 4 && r.countIn s.me .banishment "UNL-159" == 0

-- Audit fixes: Loyal Poro (UNL-156) draws when it did NOT die alone (the opposite of Lonely Poro)
#guard tun fun s => do
  let (s1, x) ← putAt s s.me "UNL-156" s.bf0
  let (s3, _) ← putAt s1 s.me "OGN-051" s.bf0
  let die (st : GameState) (u : ObjId) : Option GameState :=
    let (st1, evs) := killObj st u
    fire st1 evs
  let alone ← die s1 x
  let company ← die s3 x
  return alone.handN s.me == s1.handN s.me && company.handN s.me == s3.handN s.me + 1

-- Heroic Charge (UNL-155): +1 Might to a friendly unit and stun an enemy at its location
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-155" .hand
  let (s2, u) ← putAt s1 s.me "UNL-111" s.bf0
  let (s3, e) ← putAt s2 s.you "OGN-088" s.bf0
  let s4 ← play s3 s.me c [u, e]
  return (s4.obj? e).any (·.stunned) && s4.mightNow u == (s3.mightNow u).map (· + 1)

-- Flurry of Feathers (UNL-044): the Bird mode needs no spell on the Chain
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-044" .hand
  let s2 ← play s1 s.me c [] { fromEnd := some 0 }
  return s2.countNamed s.me .base "Bird" == 4

-- Back Off (UNL-042): played from the hand, it draws 1
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-042" .hand
  let (s2, e) ← putAt s1 s.you "OGN-088" s.bf0
  let s3 ← play s2 s.me c [e]
  return (s3.obj? e).any (·.stunned) && s3.handN s.me == s2.handN s.me

-- Sacrifice (UNL-173): draw 2 and channel one rune (not two)
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-173" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let big := s2.modObj u (fun o => { o with mightMods := [{ amount := 9, ends := .never }] })
  let s3 ← play big s.me c [u]
  return s3.countIn s.me .trash "UNL-111" == 1

#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-173" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let big := s2.modObj u (fun o => { o with mightMods := [{ amount := 9, ends := .never }] })
  let s3 ← play big s.me c [u]
  let deck (st : GameState) : Nat := (st.zone (.player s.me .runeDeck)).length
  return deck s3 + 1 == deck big

#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-173" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let big := s2.modObj u (fun o => { o with mightMods := [{ amount := 9, ends := .never }] })
  let s3 ← play big s.me c [u]
  return s3.handN s.me == big.handN s.me + 1

-- Ashe, Focused (UNL-169): when played, a card from the opponent's hand is banished with it
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-169" .hand
  let (s2, _) ← put s1 s.you "OGN-007" .hand
  let s3 ← play s2 s.me c
  return s3.countIn s.you .banishment "OGN-007" == 1 && s3.countIn s.you .hand "OGN-007" == 0


-- Green Father (UNL-195): when its player conquers, it may exhaust to replace that Battlefield by
-- Brush (the Battlefield is picked while the effect resolves)
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, g) ← put s1 s.me "UNL-195" .legendZone
  let s3 := s2.modObj bf (fun o => { o with scored := [s.me] })
  let r ← fire s3 [Event.scored s.me bf true]
  return (r.zone .battlefieldZone).any (fun b => (r.cardDef? b).any (·.name == "Brush")) &&
    !((r.zone .battlefieldZone).contains bf) && r.tired g == some true

-- Determined Sentry (UNL-111): it cannot move to the Base; an ordinary unit can
#guard tun fun s => do
  let (s1, u) ← putAt s s.me "UNL-111" s.bf0
  let (s2, v) ← putAt s1 s.me "OGN-088" s.bf0
  return !moveOk s2 s.me u .base && moveOk s2 s.me v .base

-- Abandon (UNL-131): the countered spell returns to its owner's hand, not the Trash
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-131" .hand
  let (s2, sp) ← onChain s1 s.you "OGN-004"
  let before := s2.handN s.you
  let r ← cast (s2.rich s.me) s.me c (payOf s2 c) [sp]
  return r.handN s.you == before + 1 && r.countIn s.you .trash "OGN-004" == 0

-- Frisky Hunter (UNL-033) and Lord Broadmane (UNL-012): played to the Base, "here" is the Base
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-033" .hand
  let s2 ← play s1 s.me c
  return s2.countNamed s.me .base "Bird" == 1

#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-012" .hand
  let (s2, u) ← put s1 s.me "OGN-088" .base
  let s3 ← play s2 s.me c
  return s3.hasKw u .assault

-- Deadly Flourish (UNL-073): when the unit it damaged dies this turn, its caster plays a Gold
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-073" .hand
  let (s2, e) ← putAt s1 s.you "OGN-135" s.bf0
  let s3 ← play s2 s.me c [e]
  return s3.countNamed s.me .base "Gold" == 1 && s3.countNamed s.you .base "Gold" == 0

-- Tactical Retreat (UNL-175): the next time the unit would die this turn it is healed, exhausted and
-- recalled instead (it does not die: no Deathknell, same unit); the next time after that, it dies
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-175" .hand
  let (s2, u) ← putAt s1 s.me "UNL-156" s.bf0
  let (s3, _) ← putAt s2 s.me "OGN-135" s.bf0
  let s4 ← play s3 s.me c [u]
  let hurt := s4.modObj u (fun o => { o with damage := 5 })
  let (saved, evs) := killOrSave hurt u
  let a ← fire saved evs
  let (again, evs2) := killOrSave a u
  let b ← fire again evs2
  return (a.obj? u).any (fun o => o.exhausted && o.damage == 0 && o.loc.isNone) &&
    a.handN s.me == hurt.handN s.me && (b.obj? u).isNone && b.countIn s.me .trash "UNL-156" == 1

-- Soul Sword (UNL-039): +1 Might, and one more at Level 3
#guard tun fun s => do
  let (s1, u) ← put s s.me "OGN-135" .base
  let (s2, g) ← put s1 s.me "UNL-039" .base
  let s3 := s2.modObj g (fun o => { o with attached := some u })
  let lo ← withXPOf s3 s.me 2
  let hi ← withXPOf s3 s.me 3
  return lo.mightNow u == (s2.mightNow u).map (· + 1) && hi.mightNow u == (s2.mightNow u).map (· + 2)

-- Ivern (UNL-051): when the unit it draws is a Poro (or another pet), a friendly unit is buffed
#guard tun fun s => do
  let (s1, iv) ← put s s.me "UNL-051" .base
  let few := s1.setZone (.player s.me .mainDeck) []
  let (p1, _) ← put few s.me "UNL-156" .mainDeck
  let (n1, _) ← put few s.me "UNL-111" .mainDeck
  let pet ← fire p1 [Event.played s.me iv]
  let plain ← fire n1 [Event.played s.me iv]
  return (pet.obj? iv).any (·.buffed) && !((plain.obj? iv).any (·.buffed)) &&
    pet.handN s.me == p1.handN s.me + 1

-- Additional costs are paid as the card is played (CR 357.2): Sacrifice and Heedless Resurrection kill
-- the unit while the spell is cast, before it resolves, and cannot be cast without one
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-173" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let big := s2.modObj u (fun o => { o with mightMods := [{ amount := 9, ends := .never }] })
  let r ← match step 100 (big.rich s.me) ⟨.player s.me, .playCard c (payOf big c) [u]⟩ with
    | .ok (s3, _) => some s3
    | .error _ => none
  return r.countIn s.me .trash "UNL-111" == 1 && r.handN s.me == big.handN s.me - 1 &&
    (play s2 s.me c [u]).isNone

#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-142" .hand
  let (s2, k) ← put s1 s.me "UNL-003" .base
  let (s3, _) ← put s2 s.me "UNL-111" .trash
  let r ← match step 100 (s3.rich s.me) ⟨.player s.me, .playCard c (payOf s3 c) [k]⟩ with
    | .ok (s4, _) => some s4
    | .error _ => none
  return r.countIn s.me .trash "UNL-003" == 1 && r.countIn s.me .base "UNL-111" == 0 &&
    (play (s3.modObj k (fun o => o)) s.me c []).isNone

-- Safety Inspector (UNL-164): the additional cost is 3 XP; if it is paid, only the opponents kill a unit
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-164" .hand
  let (s2, u) ← put s1 s.me "OGN-135" .base
  let (s3, e) ← put s2 s.you "OGN-135" .base
  let s4 ← withXPOf s3 s.me 3
  let leg ← (s4.zone (.player s.me .legendZone)).head?
  let paid ← play s4 s.me c [leg]
  let free ← play s4 s.me c []
  return (paid.obj? u).isSome && (paid.obj? e).isNone && paid.xpOf s.me == 0 &&
    (free.zone (.player s.me .base)).length + 1 == (paid.zone (.player s.me .base)).length &&
    (free.obj? e).isNone && free.xpOf s.me == 3


-- Poppy, Defender of the Meek (UNL-178): the additional cost is 3 XP; paid, she costs 3 Energy less
-- (and only then); not paid, the full cost, and no XP is spent
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-178" .hand
  let s2 ← withXPOf s1 s.me 3
  let leg ← (s2.zone (.player s.me .legendZone)).head?
  let less : RunePool.Payment := ⟨3, [.order]⟩
  let full : RunePool.Payment := ⟨6, [.order]⟩
  let paid ← cast (s2.rich s.me) s.me c less [leg]
  let free ← cast (s2.rich s.me) s.me c full []
  let pu ← paid.firstOf s.me .base "UNL-178"
  let fu ← free.firstOf s.me .base "UNL-178"
  return paid.xpOf s.me == 0 && free.xpOf s.me == 3 &&
    (cast (s2.rich s.me) s.me c less []).isNone &&
    (cast ((withXPOf s1 s.me 2).getD s1 |>.rich s.me) s.me c less [leg]).isNone &&
    paid.tired pu == some true && free.tired fu == some true

-- Atakhan (UNL-170): killing a friendly unit as the additional cost makes it cost that unit's Energy
-- and Power less
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-170" .hand
  let (s2, u) ← put s1 s.me "UNL-111" .base
  let some d := s2.cardDef? u | none
  let some k := d.cost | none
  let some ca := (s2.cardDef? c).bind (·.cost) | none
  let less : RunePool.Payment :=
    ⟨ca.energy - k.energy, (ca.power.drop k.power.length).map (fun x => match x with | .domain d => d | _ => .fury)⟩
  let full : RunePool.Payment := ⟨ca.energy, ca.power.map (fun x => match x with | .domain d => d | _ => .fury)⟩
  let paid ← cast (s2.rich s.me) s.me c less [u]
  let free ← cast (s2.rich s.me) s.me c full []
  return paid.countIn s.me .trash "UNL-111" == 1 && paid.countIn s.me .base "UNL-170" == 1 &&
    free.countIn s.me .base "UNL-111" == 1 && free.countIn s.me .base "UNL-170" == 1 &&
    (cast (s2.rich s.me) s.me c less []).isNone

-- Conscription (UNL-140): a unit with 3 Might or less is chosen for free; a bigger one only with 5 XP,
-- which is spent as the spell is cast
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-140" .hand
  let (s2, small) ← putAt s1 s.you "OGN-135" s.bf0
  let (s3, big) ← putAt s2 s.you "UNL-170" s.bf0
  let rich ← withXPOf s3 s.me 5
  let poor ← withXPOf s3 s.me 4
  let a ← play rich s.me c [small]
  let b ← play rich s.me c [big]
  let bigMightIsOver := (s3.mightNow big).getD 0 > 3
  let afterCast ← match step 100 (rich.rich s.me) ⟨.player s.me, .playCard c (payOf rich c) [big]⟩ with
    | .ok (x, _) => some x
    | .error _ => none
  return bigMightIsOver && (a.obj? small).any (·.controller == s.me) && a.xpOf s.me == 5 &&
    (b.obj? big).any (·.controller == s.me) && b.xpOf s.me == 0 && afterCast.xpOf s.me == 0 &&
    (play poor s.me c [big]).isNone && (play poor s.me c [small]).isSome

-- Showdown (CR 347-348): the player with Focus can play a Spell with Action, but not one without a
-- speed; the Chain resolves above the Showdown, and the Showdown goes on
#guard tun fun s => do
  let (s1, c) ← put s s.me "UNL-155" .hand
  let (s2, d) ← put s1 s.me "UNL-054" .hand
  let (s3, u) ← putAt s2 s.me "UNL-111" s.bf0
  let (s4, e) ← putAt s3 s.you "OGN-088" s.bf0
  let sd := { s4 with pending := .showdown s.bf0 s.me 0 :: s4.pending }
  let r ← play sd s.me c [u, e]
  let back := match r.pending with | .showdown _ q 0 :: _ => q == s.me | _ => false
  let rich := sd.rich s.me
  let acts := legalFrameActions rich
  let inList (card : ObjId) := acts.any (fun a => match a.kind with
    | .playCard x _ _ _ _ => x == card | _ => false)
  return (r.obj? e).any (·.stunned) && back && inList c && !inList d &&
    (cast rich s.me d (payOf rich d) [e]).isNone

-- Shadow (UNL-194): in a Showdown, the defender stuns an attacking enemy unit with its Action ability
#guard tun fun s => do
  let (s1, sh) ← putAt s s.you "UNL-194" s.bf0
  let (s2, a) ← putAt s1 s.me "OGN-088" s.bf0
  let s3 := s2.modObj s.bf0 (fun o => { o with contested := some s.me })
  let sd := { s3 with pending := .showdown s.bf0 s.you 0 :: s3.pending }
  let idx := firstAct sd sh
  let r ← activate sd s.you sh idx [a] ⟨1, [.fury]⟩
  let back := match r.pending with | .showdown _ q 0 :: _ => q == s.you | _ => false
  return (r.obj? a).any (·.stunned) && back && (r.obj? sh).any (·.exhausted)

end RiftboundTest
