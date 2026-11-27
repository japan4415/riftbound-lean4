module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Verified Vendetta scenarios

Each scenario plays its named card through the engine and checks the result of its rule text.
-/

namespace RiftboundTest

open Riftbound

/-- Evaluate a card scenario in the ordinary two-player game. -/
private meta def verifiedCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Consuming Curse counts only copies in its controller's Trash and can be played in a Showdown.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let bf := s.bf0
  let (s, spell) ← put s p "VEN-010" .hand
  let (s, target) ← putAt s q "VEN-091" bf
  let (s, outside) ← put s q "VEN-091" .base
  let (s, _) ← put s q "VEN-010" .trash
  let (s, _) ← put s p "VEN-012" .trash
  let (owned, _) ← put s p "VEN-010" .trash
  let (owned, _) ← put owned p "VEN-010" .trash
  let ordinary ← play s p spell [target]
  let showdown := { (owned.fund p 2) with pending := [.showdown bf p 0] }
  let act (unit : ObjId) : Action := ⟨.player p, .playCard spell ⟨2, []⟩ [unit]⟩
  let (waiting, _) ← (step 100 showdown (act target)).toOption
  let done := settleChain {} 12 waiting
  return (ordinary.obj? target).any (·.damage == 2) &&
    (done.obj? target).any (·.damage == 4) && !(legalActions showdown).contains (act outside)

-- Pendulum Blade grants two additional Might only for movement into a Battlefield.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, blade) ← put s p "VEN-011" .base
  let (s, wearer) ← put s p "VEN-014" .base
  let (s, returnHome) ← put s p "OGN-168" .hand
  let (s, enemy) ← put s s.you "VEN-014" .base
  let s := s.control p field
  let equipped ← activate s p blade 0 [wearer] ⟨0, [.fury]⟩
  let (moving, _) ← (step 100 equipped ⟨.player p, .standardMove wearer (.battlefield field)⟩).toOption
  let arrived := settleChain {} 8 moving
  let home ← play arrived p returnHome [wearer]
  let (expired, _) ← (advance 100 { home with pending := [.expireTurn] } []).toOption
  return (activate s p blade 0 [enemy] ⟨0, [.fury]⟩).isNone &&
    equipped.mightNow wearer == some 3 && arrived.mightNow wearer == some 5 &&
    home.locate wearer == some (.player p .base) && home.mightNow wearer == some 5 &&
    expired.mightNow wearer == some 3

-- Perfect Execution readies its target and grants Assault for both ordinary play and Flow.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, hand) ← put s p "VEN-012" .hand
  let (s, trash) ← put s p "VEN-012" .trash
  let (s, ally) ← put s p "VEN-014" .base
  let s := s.modObj ally (fun o => { o with exhausted := true })
  let ordinary ← play s p hand [ally]
  let flowed ← cast (s.fund p 3 (fury := 1)) p trash ⟨3, [.fury]⟩ [ally]
  return ordinary.tired ally == some false && ordinary.kwAmount ally .assault == 3 &&
    flowed.tired ally == some false && flowed.kwAmount ally .assault == 3 &&
    ordinary.countIn p .trash "VEN-012" == 2 &&
    flowed.countIn p .banishment "VEN-012" == 1 && flowed.locate hand == some (.player p .hand)

-- Shadow Fiend gains Assault 3 through its printed Empower and gets the Might bonus only attacking.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, fiend) ← putAt s p "VEN-014" field
  let s := s.control p field
  let empowered ← activate s p fiend 1 [] ⟨2, [.fury]⟩
  let attacker := empowered.inCombatAt field p
  let defender := empowered.inCombatAt field s.you
  return (activate s p fiend 1 [] ⟨2, []⟩).isNone &&
    s.kwAmount fiend .assault == 0 && empowered.kwAmount fiend .assault == 3 &&
    empowered.mightNow fiend == some 2 && attacker.mightNow fiend == some 5 &&
    defender.mightNow fiend == some 2 && attacker.combatMight fiend true == 5

-- Field Musicians may give three Might to a Unit on either side.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, musicians) ← put s p "VEN-026" .hand
  let (s, ally) ← put s p "VEN-014" .base
  let (s, enemy) ← putAt s s.you "VEN-014" s.bf0
  let friendly ← play s p musicians [] { pick := (· == [ally]) }
  let opposing ← play s p musicians [] { pick := (· == [enemy]) }
  return friendly.mightNow ally == some 5 && friendly.mightNow enemy == some 2 &&
    opposing.mightNow ally == some 2 && opposing.mightNow enemy == some 5

-- Hand Hammer grants +2 in addition to its equipment Might with exactly one other friendly Unit.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, hammer) ← put s p "VEN-027" .base
  let (s, wearer) ← putAt s p "VEN-014" field
  let (s, ally) ← putAt s p "VEN-014" field
  let s := s.control p field
  let equipped ← activate s p hammer 0 [wearer] ⟨0, [.calm]⟩
  let alone := (moveHome equipped ally).1
  let atBase := (moveHome equipped wearer).1
  let (crowded, _) ← putAt equipped p "VEN-014" field
  let detached := (detachObj equipped hammer).1
  return equipped.mightNow wearer == some 5 && equipped.mightTable.lookup wearer == some 2 &&
    alone.mightNow wearer == some 3 &&
    atBase.mightNow wearer == some 3 && crowded.mightNow wearer == some 3 &&
    detached.mightNow wearer == some 2

-- Scourge of Shadows draws on Hold with exactly one other friendly Unit at his Battlefield.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, _) ← putAt s p "VEN-042" field
  let (s, _) ← put s p "VEN-014" .base
  let (paired, _) ← putAt s p "VEN-014" field
  let (crowded, _) ← putAt paired p "VEN-014" field
  let held ← fire paired [.scored p field false]
  let alone ← fire s [.scored p field false]
  let tooMany ← fire crowded [.scored p field false]
  let conquered ← fire paired [.scored p field true]
  return held.handN p == s.handN p + 1 &&
    [alone, tooMany, conquered].all (fun t => t.handN p == s.handN p)

-- Cloud Drake draws exactly one card as its play trigger resolves.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, drake) ← put s p "VEN-048" .hand
  let before := s.zone (.player p .mainDeck)
  let top ← before.head?
  let done ← play s p drake
  return done.countIn p .base "VEN-048" == 1 && done.zone (.player p .mainDeck) == before.drop 1 &&
    (done.zone (.player p .hand)).any (fun id => ((done.obj? id).bind (·.formerId)) == some top)

-- Iterative Design may play its Mech to Base or a controlled Battlefield, including via Flow.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, hand) ← put s p "VEN-051" .hand
  let (s, trash) ← put s p "VEN-051" .trash
  let s := s.control p field
  let resolveToChoice (t : GameState) (spell : ObjId) (pay : RunePool.Payment) := do
    let (casting, _) ← (step 100 t ⟨.player p, .playCard spell pay []⟩).toOption
    let (passed, _) ← (step 100 casting ⟨.player p, .pass⟩).toOption
    (step 100 passed ⟨.player q, .pass⟩).toOption.map Prod.fst
  let chooseDestination (t : GameState) (destination : Option ObjId) : Option GameState := do
    let .eitherDo _ _ _ first second _ :: _ := t.pending | none
    let choice := Effect.prim (.playUnitTokenAt "Mech" destination)
    if first != choice && second != choice then none else
      (step 100 t ⟨.player p, .decide (first == choice)⟩).toOption.map Prod.fst
  let ordinary ← resolveToChoice (s.fund p 4) hand ⟨4, []⟩
  let atBase ← chooseDestination ordinary none
  let withFlow ← resolveToChoice (s.fund p 2 (mind := 1)) trash ⟨2, [.mind]⟩
  let atField ← chooseDestination withFlow (some field)
  let withoutField := s.battlefields.foldl (fun t bf => t.control q bf) s
  let fallback ← resolveToChoice (withoutField.fund p 4) hand ⟨4, []⟩
  let mech ← (atField.unitsAtOf field p).find? (fun id => (atField.cardDef? id).any (·.name == "Mech"))
  return atBase.countNamed p .base "Mech" == 1 &&
    atBase.countIn p .trash "VEN-051" == 2 &&
    atField.mightNow mech == some 3 && atField.tired mech == some true &&
    atField.countIn p .banishment "VEN-051" == 1 &&
    fallback.countNamed p .base "Mech" == 1

-- Grumpy Rockbear counts even exhausted friendly Runes and gains Shield and Deflect together.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, bear) ← put s p "VEN-050" .base
  let s := (channelEx p 0 2 s).1
  let runes := s.runesOf p
  let cost := 12 - runes.length
  let activateBear (pay : Nat) : Action := ⟨.player p, .activate bear 0 ⟨pay, []⟩ []⟩
  let (casting, _) ← (step 100 (s.fund p cost) (activateBear cost)).toOption
  let done := settleChain {} 8 casting
  return runes.length >= 2 && s.deflectOf bear == 0 && s.kwAmount bear .shield == 0 &&
    !(legalActions (s.fund p (cost - 1))).contains (activateBear (cost - 1)) &&
    done.deflectOf bear == 1 && done.kwAmount bear .shield == 3 &&
    (done.poolOf p).total == 0 && !(legalActions (done.fund p cost)).contains (activateBear cost)

-- Applied Researchers discounts its controller's Spells and preserves their Energy floor.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, researchers) ← put s p "VEN-055" .base
  let (s, simple) ← put s p "VEN-061" .hand
  let (s, powered) ← put s p "VEN-052" .hand
  let (s, large) ← put s p "VEN-056" .hand
  let (s, foreign) ← put s q "VEN-052" .hand
  let (s, unit) ← put s p "VEN-014" .hand
  let (s, ally) ← put s p "VEN-014" .base
  let state ← activate s p researchers 1 [] ⟨3, []⟩
  let pay : RunePool.Payment := ⟨1, []⟩
  let castMode := cast (state.fund p 1) p powered pay [ally] {} (.mode 0)
  let done ← castMode
  return state.energyCost? p simple == some 1 && state.energyCost? p large == some 6 &&
    state.energyCost? p unit == s.energyCost? p unit &&
    state.energyCost? q foreign == s.energyCost? q foreign &&
    (cast (s.fund p 1) p powered pay [ally] {} (.mode 0)).isNone &&
    done.countIn p .hand "VEN-014" == 2 && (done.poolOf p).total == 0

-- Covert Informant draws only on its own movement while Empowered.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, informant) ← put s p "VEN-057" .base
  let (s, ally) ← put s p "VEN-014" .base
  let s := s.control p s.bf0
  let empowered ← activate s p informant 1 [] ⟨3, []⟩
  let moveUnit (t : GameState) (u : ObjId) := do
    let (next, _) ← (step 100 t ⟨.player p, .standardMove u (.battlefield s.bf0)⟩).toOption
    return settleChain {} 10 next
  let before ← moveUnit s informant
  let after ← moveUnit empowered informant
  let other ← moveUnit empowered ally
  return before.handN p == s.handN p && after.handN p == s.handN p + 1 &&
    other.handN p == s.handN p && (after.obj? informant).any (·.loc == some s.bf0)

-- Patched Porobot enters exhausted and draws only with at least three other friendly Gear.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, porobot) ← put s p "VEN-058" .hand
  let (s, _) ← put s p "VEN-054" .base
  let (s, _) ← putAt s p "VEN-058" s.bf0
  let (s, _) ← put s s.you "VEN-054" .base
  let (three, _) ← put s p "VEN-054" .base
  let withoutDraw ← play s p porobot
  let withDraw ← play three p porobot
  let robot ← withDraw.firstOf p .base "VEN-058"
  return withoutDraw.handN p + 1 == s.handN p && withDraw.handN p == three.handN p &&
    withDraw.tired robot == some true && withDraw.mightNow robot == some 2

-- Hwei discards Patched Porobot once and puts both reflexive abilities onto the Chain.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, hwei) ← put s p "UNL-080" .base
  let (s, porobot) ← put s p "VEN-058" .hand
  let (s, spell) ← put s p "OGN-095" .hand
  let runes := s.runesOf p
  let firstRune :: secondRune :: _ := runes | none
  let s := ((s.tire firstRune).tire secondRune).control p s.bf0
  let (moving, _) ←
    (step 100 s ⟨.player p, .standardMove hwei (.battlefield s.bf0)⟩).toOption
  let moveItem ← (moving.zone .chain).head?
  let (passed, _) ← (step 100 moving ⟨.player p, .pass⟩).toOption
  let (discarding, _) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let discard (id : ObjId) (t : GameState) :=
    (step 100 t ⟨.player p, .choose id⟩).toOption
  let (waiting, events) ← discard porobot discarding
  let discarded ← waiting.firstOf p .trash "VEN-058"
  let .triggerOrder who firstTrigger otherTriggers _ _ :: _ := waiting.pending | none
  let place (n : Nat) := (step 100 waiting ⟨.player p, .putTrigger n []⟩).toOption
  let (first, _) ← place 0
  let (second, _) ← place 1
  let firstItem ← (first.zone .chain).head?
  let secondItem ← (second.zone .chain).head?
  let done := settleChain {} 18 first
  let reversed := settleChain { yes := false } 18 second
  let (spellOnly, _) ← discard spell discarding
  let extraDraw := settleChain {} 10 spellOnly
  let card := cid "UNL-080"
  return (moving.obj? moveItem).any (fun o => o.kind == .chainAbility card 0 hwei) &&
    discarding.handN p == s.handN p + 1 && who == p &&
    ((firstTrigger :: otherTriggers).map (·.idx)).mergeSort (fun a b => decide (a ≤ b)) == [2, 3] &&
    events.contains (.discardedTypeFor p hwei card 2 discarded) &&
    events.contains (.discardedTypeFor p hwei card 3 discarded) &&
    waiting.countIn p .trash "VEN-058" == 1 && waiting.mightNow hwei == some 5 &&
    (first.obj? firstItem).map (·.kind) != (second.obj? secondItem).map (·.kind) &&
    done.mightNow hwei == some 8 && done.tired firstRune == some false &&
    done.tired secondRune == some false && done.handN p == s.handN p &&
    reversed.mightNow hwei == some 8 && reversed.tired firstRune == some true &&
    extraDraw.handN p == s.handN p + 1 && extraDraw.mightNow hwei == some 5 &&
    extraDraw.tired firstRune == some true

-- Shock Blast applies its discount to an Empowered Gear, keeps its Mind cost and hits only at a Battlefield.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "VEN-059" .hand
  let (s, gear) ← put s p "VEN-054" .base
  let (s, opponentGear) ← put s s.you "VEN-054" .base
  let (s, fieldUnit) ← putAt s s.you "VEN-091" s.bf0
  let (s, baseUnit) ← put s s.you "VEN-091" .base
  let s := (empowerObj s.you s opponentGear).1
  let boosted := (empowerObj p s gear).1
  let funded := boosted.fund p 1 (mind := 1)
  let action (target : ObjId) : Action := ⟨.player p, .playCard spell ⟨1, [.mind]⟩ [target]⟩
  let (casting, _) ← (step 100 funded (action fieldUnit)).toOption
  let done := settleChain {} 8 casting
  return s.energyCost? p spell == some 3 && boosted.energyCost? p spell == some 1 &&
    !(legalActions (boosted.fund p 1)).contains (action fieldUnit) &&
    !(legalActions funded).contains (action baseUnit) &&
    (done.obj? fieldUnit).any (·.damage == 4)

-- Hextech Formula enters exhausted, can Empower an opponent's Gear, and cannot choose itself.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, hand) ← put s p "VEN-062" .hand
  let (s, gear) ← put s s.you "VEN-054" .base
  let (s, unit) ← put s p "VEN-014" .base
  let played ← play s p hand
  let formula ← played.firstOf p .base "VEN-062"
  let ready := (readyEffect played formula).1
  let done ← activate ready p formula 1 [gear]
  let again ← activate (readyEffect done formula).1 p formula 1 [gear]
  return played.tired formula == some true && done.tired formula == some true &&
    (activate played p formula 1 [gear]).isNone &&
    (activate ready p formula 1 [formula]).isNone && (activate ready p formula 1 [unit]).isNone &&
    (done.obj? gear).any (·.empowerCount == 1) && (again.obj? gear).any (·.empowerCount == 1)

-- Nasus channels an exhausted Rune for the first enemy Unit dying at his location each turn.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, nasus) ← putAt s p "VEN-063" s.bf0
  let (s, first) ← putAt s q "VEN-014" s.bf0
  let (s, second) ← putAt s q "VEN-014" s.bf0
  let (s, third) ← putAt s q "VEN-014" s.bf0
  let (s, ally) ← putAt s p "VEN-014" s.bf0
  let (s, remote) ← put s q "VEN-014" .base
  let (s, stolen) ← putAt s p "VEN-014" s.bf0
  let kill (t : GameState) (id : ObjId) := do
    let (next, events) := killObj t id
    fire next events
  let initial := s.runesOf p
  let friendly ← kill s ally
  let farAway ← kill s remote
  let killed ← kill s first
  let rune ← (killed.runesOf p).find? (fun r => !initial.contains r)
  let repeated ← kill killed second
  let nextTurn ← kill { repeated.mapObjects clearScored with turn := repeated.turn + 1 } third
  let opposingBase := (moveHome ((moveHome s nasus).1.modObj stolen
    (fun o => { o with controller := q })) stolen).1
  let distantDeath ← kill opposingBase stolen
  return friendly.runesOf p == initial && farAway.runesOf p == initial &&
    (killed.runesOf p).length == initial.length + 1 && killed.tired rune == some true &&
    repeated.runesOf p == killed.runesOf p && (nextTurn.runesOf p).length == initial.length + 2 &&
    opposingBase.locate nasus == some (.player p .base) &&
    opposingBase.locate stolen == some (.player q .base) && distantDeath.runesOf p == initial

-- Brutal Hunter can Gank after paying for Empower, gaining two Might until Disempowered.
#guard verifiedCase fun s => do
  let p := s.me
  let other ← s.battlefields[1]?
  let (s, hunter) ← putAt s p "VEN-070" s.bf0
  let s := (s.control p s.bf0).control p other
  let move : Action := ⟨.player p, .standardMove hunter (.battlefield other)⟩
  let empowered ← activate s p hunter 1 [] ⟨3, []⟩
  let (moved, _) ← (step 100 empowered move).toOption
  let stripped := (disempowerObj empowered hunter).1
  return s.mightNow hunter == some 4 && !(legalActions s).contains move &&
    moved.mightNow hunter == some 6 && (moved.obj? hunter).any (·.loc == some other) &&
    stripped.mightNow hunter == some 4 && !(legalActions stripped).contains move

-- Legion Marauder has either Empower payment, both of which become unavailable once Empowered.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, marauder) ← put s p "VEN-074" .base
  let energy ← activate s p marauder 0 [] ⟨1, []⟩
  let power ← activate s p marauder 1 [] ⟨0, [.body]⟩
  return energy.mightNow marauder == some 3 && power.mightNow marauder == some 3 &&
    (energy.poolOf p).energy == (s.rich p |>.poolOf p).energy - 1 &&
    (power.poolOf p).body == (s.rich p |>.poolOf p).body - 1 &&
    (activate energy p marauder 1 [] ⟨0, [.body]⟩).isNone &&
    (activate power p marauder 0 [] ⟨1, []⟩).isNone

-- Platewyrm Egg spends one Energy to Empower and adds the correct Energy at Reaction speed.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, hand) ← put s p "VEN-075" .hand
  let played ← play s p hand
  let egg ← played.firstOf p .base "VEN-075"
  let ready := (readyEffect played egg).1
  let empower : Action := ⟨.player p, .activate egg 1 ⟨1, []⟩ []⟩
  let (casting, _) ← (step 100 (ready.fund p 1) empower).toOption
  let empowered := settleChain {} 8 casting
  let (ready, otherItem) ← onChain (ready.fund p 0) q "OGN-095"
  let (boosted, _) ← onChain (((readyEffect empowered egg).1).fund p 0) q "OGN-095"
  let respond (t : GameState) := { t with active := some q, pending := [.chainPass p 0] }
  let add (n : Nat) : Action := ⟨.player p, .manaAbility egg n ⟨0, []⟩⟩
  let (plain, _) ← (step 100 (respond ready) (add 2)).toOption
  let (extra, _) ← (step 100 (respond boosted) (add 3)).toOption
  return played.tired egg == some true && empowered.tired egg == some true &&
    (empowered.poolOf p).total == 0 && (empowered.obj? egg).any (·.empowerCount == 1) &&
    (plain.poolOf p).energy == 1 && (extra.poolOf p).energy == 2 &&
    (plain.zone .chain).contains otherItem && plain.tired egg == some true &&
    !(legalActions (respond ready)).contains (add 3) &&
    !(legalActions (respond boosted)).contains (add 2)

-- Repair Specialist counts only friendly Gear, and its Assault applies when attacking.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, specialist) ← putAt s p "VEN-076" s.bf0
  let (s, _) ← put s s.you "VEN-054" .base
  let (s, _) ← put s p "VEN-054" .base
  let (s, robot) ← putAt s p "VEN-058" s.bf0
  let (fewer, _) := killObj s robot
  return s.kwAmount specialist .assault == 2 && s.mightNow specialist == some 3 &&
    s.combatMight specialist true == 5 && s.combatMight specialist false == 3 &&
    fewer.kwAmount specialist .assault == 1 && fewer.combatMight specialist true == 4

-- Tools of Empire can choose either player's Unit and doubles its temporary bonus when Empowered.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, tools) ← put s p "VEN-077" .base
  let (s, ally) ← put s p "VEN-014" .base
  let (s, enemy) ← put s s.you "VEN-014" .base
  let plain ← activate s p tools 0 [ally]
  let empowered ← activate s p tools 1 [] ⟨2, []⟩
  let boosted ← activate empowered p tools 0 [enemy]
  let (expired, _) ← (advance 100 { boosted with pending := [.expireTurn] } []).toOption
  return plain.tired tools == some true && plain.mightNow ally == some 4 &&
    plain.mightNow enemy == some 2 && boosted.tired tools == some true &&
    boosted.mightNow ally == some 2 && boosted.mightNow enemy == some 6 &&
    expired.mightNow enemy == some 2

-- Guttural Roar adds two Might or four when the chosen Unit is Empowered.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, roar) ← put s p "VEN-072" .hand
  let (s, unit) ← putAt s s.you "VEN-014" s.bf0
  let ordinary ← play s p roar [unit]
  let empowered := (empowerObj s.you (s.fund p 2) unit).1
  let showdown := { empowered with pending := [.showdown s.bf0 p 0] }
  let (waiting, _) ← (step 100 showdown ⟨.player p, .playCard roar ⟨2, []⟩ [unit]⟩).toOption
  let done := settleChain {} 12 waiting
  return ordinary.mightNow unit == some 4 && done.mightNow unit == some 6

-- Baccai Witherclaw's Empowered Deathknell channels exhausted Runes and Karthus doubles it.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, baccai) ← put s p "VEN-078" .base
  let empowered ← activate s p baccai 2 [] ⟨1, [.fury, .body]⟩
  let (withKarthus, _) ← put empowered p "OGN-236" .base
  let runes := empowered.runesOf p
  let die (t : GameState) := do
    let (after, events) := killObj t baccai
    fire after events
  let unempowered ← die s
  let ordinary ← die empowered
  let doubled ← die withKarthus
  let newRunes (t : GameState) := (t.runesOf p).filter (fun id => !runes.contains id)
  return s.mightNow baccai == some 4 && empowered.mightNow baccai == some 6 &&
    unempowered.runesOf p == s.runesOf p &&
    (newRunes ordinary).length == 2 && (newRunes doubled).length == 4 &&
    (newRunes doubled).all (fun id => doubled.tired id == some true)

-- Dame pays five Energy and one Body Power to Empower and cannot Empower again.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, dame) ← put s p "VEN-079" .base
  let action : Action := ⟨.player p, .activate dame 2 ⟨5, [.body]⟩ []⟩
  let funded := s.fund p 5 (body := 1)
  let (waiting, _) ← (step 100 funded action).toOption
  let done := settleChain {} 12 waiting
  return !(legalActions (s.fund p 5)).contains action && (done.poolOf p).total == 0 &&
    (done.obj? dame).any (fun o => o.empowerCount == 1) &&
    !(legalActions (done.fund p 5 (body := 1))).contains action

-- Noxian Demolitionist can kill Gear costing up to its Might, only when conquering.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, demo) ← putAt s p "VEN-080" field
  let (s, cheap) ← put s q "OGN-090" .base
  let (s, expensive) ← put s p "VEN-062" .base
  let (s, _) ← put s q "VEN-014" .base
  let (fortified, _) ← put s p "VEN-018" .base
  let possible ← firePicks s [.scored p field true]
  let nowPossible ← firePicks fortified [.scored p field true]
  let result ← fire fortified [.scored p field true] { pick := (· == [expensive]) }
  let skipped ← fire s [.scored p field true] { yes := false }
  let held ← fire s [.scored p field false]
  return fortified.mightNow demo == some 2 && possible == [cheap] && nowPossible.contains expensive &&
    result.countIn p .trash "VEN-062" == 1 && (result.obj? cheap).isSome &&
    (skipped.obj? cheap).isSome && (held.obj? cheap).isSome

-- Onslaught gives six Might whether played from hand or Trash, and expires at turn end.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, fromHand) ← put s p "VEN-081" .hand
  let (s, fromTrash) ← put s p "VEN-081" .trash
  let (s, unit) ← put s s.you "VEN-014" .base
  let castFrom (card : ObjId) := cast (s.fund p 4) p card ⟨4, []⟩ [unit]
  let plain ← castFrom fromHand
  let flowed ← castFrom fromTrash
  let (expired, _) ← (advance 100 { flowed with pending := [.expireTurn] } []).toOption
  return plain.mightNow unit == some 8 && flowed.mightNow unit == some 8 &&
    plain.countIn p .trash "VEN-081" == 2 && flowed.countIn p .banishment "VEN-081" == 1 &&
    expired.mightNow unit == some 2

-- Profiteer can Disempower Ambessa's Legend to Empower Kayle (Vendetta FAQ).
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, ambessa) ← put s p "VEN-153" .legendZone
  let (s, kayle) ← put s p "VEN-134" .base
  let (s, profiteer) ← put s p "VEN-082" .hand
  let s := (empowerObj p s ambessa).1
  let payment ← castStop s p profiteer
  let (queued, _) ← (step 100 payment ⟨.player p, .putTrigger 0 [kayle]⟩).toOption
  let (passed, _) ← (step 100 queued ⟨.player p, .pass⟩).toOption
  let (choice, _) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let (accepted, _) ← (step 100 choice ⟨.player p, .decide true⟩).toOption
  let (declined, _) ← (step 100 choice ⟨.player p, .decide false⟩).toOption
  let done := settleChain {} 8 accepted
  let stacks (t : GameState) (id : ObjId) := (t.obj? id).map (·.empowerCount)
  return stacks accepted ambessa == some 0 && stacks accepted kayle == some 1 &&
    stacks declined ambessa == some 1 && stacks declined kayle == some 0 &&
    stacks done ambessa == some 1 && stacks done kayle == some 1

-- The Wolf ignores damage outside her Combat when Empowered, including at other Battlefields.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, ambessa) ← putAt s p "VEN-084" s.bf0
  let elsewhere ← s.battlefields[1]?
  let boosted ← activate (s.control p s.bf0) p ambessa 2 [] ⟨3, [.body]⟩
  let hit (t : GameState) := (dealObj 2 t ambessa (some s.you)).1
  let injured (t : GameState) := (t.obj? ambessa).map (·.damage)
  return s.mightNow ambessa == some 4 && boosted.mightNow ambessa == some 7 &&
    injured (hit s) == some 2 && injured (hit boosted) == some 0 &&
    injured (hit (boosted.inCombatAt elsewhere s.you)) == some 0 &&
    injured (hit (boosted.inCombatAt s.bf0 s.you)) == some 2

-- Gangplank replaces only a Stun or Might reduction that would actually occur (Vendetta FAQ).
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, gangplank) ← putAt s q "VEN-086" s.bf0
  let (s, cone) ← put s p "UNL-133" .hand
  let (s, backOff) ← put s q "UNL-042" .hand
  let (s, stupefy) ← put s q "OGN-095" .hand
  let empowered := (empowerObj q (s.control q s.bf0) gangplank).1
  let blasted ← play empowered p cone [] { pick := (· == [gangplank]) }
  let fieldGear ← blasted.firstOf p .base "UNL-133"
  let opponentTurn (t : GameState) := { t with active := some q, pending := [.priority q] }
  let repeated ← play (opponentTurn blasted) q backOff [gangplank]
  let replaced ← play (opponentTurn empowered) q backOff [gangplank]
  let (expired, _) ← (advance 100 { replaced with pending := [.expireTurn] } []).toOption
  let floored := (opponentTurn empowered).modObj gangplank
    (fun o => { o with baseMightThisTurn := some 1 })
  let unchanged ← play floored q stupefy [gangplank]
  return blasted.locate gangplank == some (.player q .base) &&
    blasted.tired fieldGear == some true && (blasted.obj? gangplank).any (·.stunned) &&
    (repeated.obj? gangplank).any (·.stunned) && repeated.mightNow gangplank == some 6 &&
    (replaced.obj? gangplank).any (! ·.stunned) && replaced.mightNow gangplank == some 9 &&
    expired.mightNow gangplank == some 6 && unchanged.mightNow gangplank == some 1

-- Hextech Disc exhausts to Empower, then spends its next exhaust and one Energy on a Base Mech.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, disc) ← put s p "VEN-087" .base
  let s := s.control p s.bf0
  let empowered ← activate s p disc 0
  let ready := (readyEffect empowered disc).1
  let (queued, _) ← (step 100 (ready.fund p 1) ⟨.player p, .activate disc 1 ⟨1, []⟩ []⟩).toOption
  let done := settleChain {} 8 queued
  let mech ← (done.zone (.player p .base)).find? (fun id => (done.cardDef? id).any (·.name == "Mech"))
  return empowered.tired disc == some true &&
    (empowered.obj? disc).any (·.empowerCount == 1) &&
    (activate s p disc 1 [] ⟨1, []⟩).isNone &&
    (activate empowered p disc 1 [] ⟨1, []⟩).isNone &&
    queued.tired disc == some true && (queued.poolOf p).total == 0 &&
    (queued.obj? disc).any (·.empowerCount == 0) &&
    done.mightNow mech == some 3 && done.tired mech == some true

-- Profiteer Disempowers Brute at eleven Might. Staying at ten or more does not Empower him.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, renekton) ← put s p "VEN-092" .base
  let (s, kayle) ← put s p "VEN-134" .base
  let (s, profiteer) ← put s p "VEN-082" .hand
  let (s, stupefy) ← put s q "OGN-095" .hand
  let enlarged := (addMightMod ⟨7, .turn⟩ s renekton).1
  let s := (empowerObj p enlarged renekton).1
  let stripped ← play s p profiteer [] { pick := (· == [kayle]), obj := (· == renekton) }
  let reduced ← play { stripped with active := some q, pending := [.priority q] } q stupefy [renekton]
  let raised ← activate stripped p renekton 0 [] ⟨1, []⟩
  return stripped.mightNow renekton == some 11 && (stripped.obj? kayle).any (·.empowerCount == 1) &&
    reduced.mightNow renekton == some 10 && raised.mightNow renekton == some 12 &&
    [stripped, reduced, raised].all (fun t => (t.obj? renekton).any (·.empowerCount == 0))

-- Kinkou Lifeblade gains one Might and can Gank after paying its printed Empower cost.
#guard verifiedCase fun s => do
  let p := s.me
  let other ← s.battlefields[1]?
  let (s, lifeblade) ← putAt s p "VEN-093" s.bf0
  let s := (s.control p s.bf0).control p other
  let moving : Action := ⟨.player p, .standardMove lifeblade (.battlefield other)⟩
  let boosted ← activate s p lifeblade 1 [] ⟨2, []⟩
  let (moved, _) ← (step 100 boosted moving).toOption
  return s.mightNow lifeblade == some 4 && !(legalActions s).contains moving &&
    moved.mightNow lifeblade == some 5 && (moved.obj? lifeblade).any (·.loc == some other)

-- Shadowblade Lurker's Energy discount counts only same-name cards in its owner's Trash.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, lurker) ← put s p "VEN-096" .hand
  let (s, _) ← put s s.you "VEN-096" .trash
  let (s, _) ← put s p "VEN-014" .trash
  let (one, _) ← put s p "VEN-096" .trash
  let (two, _) ← put one p "VEN-096" .trash
  let (three, _) ← put two p "VEN-096" .trash
  let (done, _) ← (step 100 (three.fund p 0) ⟨.player p, .playCard lurker ⟨0, []⟩ []⟩).toOption
  return [s, one, two, three].map (fun state => state.energyCost? p lurker) ==
    [some 5, some 3, some 1, some 0] && done.countIn p .base "VEN-096" == 1

-- A hidden Spiderling enters its Battlefield and counts its other friendly copy there.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, hidden) ← put s p "VEN-097" .hidden
  let (s, sibling) ← putAt s p "VEN-097" field
  let s := (s.control p field).modObj hidden
    (fun o => { o with hiddenAt := some field, hiddenTurn := some (s.turn - 1) })
  let (queued, _) ← (step 100 s ⟨.player p, .activate hidden 2 ⟨0, []⟩ []⟩).toOption
  let done := settleChain {} 8 queued
  let flipped ← (done.unitsAtOf field p).find? (fun id =>
    id != sibling && (done.cardDef? id).any (·.id == cid "VEN-097"))
  return done.mightNow sibling == some 2 && done.mightNow flipped == some 2 &&
    done.countIn p .hidden "VEN-097" == 0 && (done.obj? flipped).any (·.fromHidden)

-- Wind and Ghosts checks the chosen Unit's current Might to decide where to send it.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, spell) ← put s p "VEN-106" .hand
  let (s, small) ← putAt s q "VEN-014" field
  let (s, atBase) ← put s q "VEN-014" .base
  let s := (s.control q field).fund p 3 (chaos := 1)
  let action (unit : ObjId) : Action := ⟨.player p, .playCard spell ⟨3, [.chaos]⟩ [unit]⟩
  let waiting := { s with pending := [.showdown field p 0] }
  let (casting, _) ← (step 100 waiting (action small)).toOption
  let banished := settleChain {} 8 casting
  let boosted := (addMightMod ⟨2, .turn⟩ casting small).1
  let returned := settleChain {} 8 boosted
  return !(legalActions waiting).contains (action atBase) &&
    banished.countIn q .banishment "VEN-014" == 1 &&
    returned.countIn q .hand "VEN-014" == 1 && returned.countIn q .banishment "VEN-014" == 0

-- Ravenbloom Prefect can banish an opponent's Gold token when the token is played.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, prefect) ← put s p "VEN-102" .base
  let (s, broker) ← put s q "SFD-155" .base
  let (killed, events) := killObj (s.addTurnFx q .unitsBuffed) broker
  let accepted ← fire killed events
  let declined ← fire killed events { yes := false }
  let gold ← (declined.zone (.player q .base)).find? (fun id => (declined.cardDef? id).any (·.name == "Gold"))
  return accepted.countIn p .banishment "VEN-102" == 1 && accepted.countNamed q .base "Gold" == 0 &&
    (declined.obj? prefect).isSome && (declined.obj? gold).any (! ·.buffed) &&
    declined.playLog == killed.playLog && accepted.playLog == killed.playLog

-- Ocean Drake can enter an open Battlefield and return a non-Dragon Unit from either side.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let occupied ← s.battlefields[1]?
  let (s, drake) ← put s p "VEN-115" .hand
  let (s, friendly) ← put s p "VEN-014" .base
  let (s, opposing) ← put s q "VEN-014" .base
  let (s, dragon) ← putAt s q "VEN-091" occupied
  let s := (s.control q occupied).fund p 8 (chaos := 2)
  let playAt (bf : ObjId) : Action := ⟨.player p, .playCard drake ⟨8, [.chaos, .chaos]⟩ [bf]⟩
  let (waiting, _) ← (step 100 s (playAt field)).toOption
  let chosen := settleChain { pick := (· == [opposing]) } 10 waiting
  let back := settleChain { pick := (· == [friendly]) } 10 waiting
  let stayed := settleChain { yes := false } 10 waiting
  return !(legalActions s).contains (playAt occupied) && !(waiting.trigPicks.contains dragon) &&
    (waiting.unitsAtOf field p).any (fun id => (waiting.cardDef? id).any (·.id == cid "VEN-115")) &&
    chosen.countIn q .hand "VEN-014" == 1 && back.countIn p .hand "VEN-014" == 1 &&
    (stayed.obj? friendly).isSome && (stayed.obj? opposing).isSome

-- Disciple of Shen can reveal at a Battlefield and has Shield 3 only with one other friendly Unit.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, hidden) ← put s p "VEN-117" .hidden
  let (s, ally) ← putAt s p "VEN-014" field
  let s := (s.control p field).modObj hidden
    (fun o => { o with hiddenAt := some field, hiddenTurn := some (s.turn - 1) })
  let (queued, _) ← (step 100 s ⟨.player p, .activate hidden 2 ⟨0, []⟩ []⟩).toOption
  let done := settleChain {} 8 queued
  let unit ← (done.unitsAtOf field p).find? (fun id => (done.cardDef? id).any (·.id == cid "VEN-117"))
  let (extra, _) ← putAt done p "VEN-014" field
  let alone := (moveHome done ally).1
  let offField := (moveHome done unit).1
  return (done.obj? unit).any (·.fromHidden) && done.kwAmount unit .shield == 3 &&
    done.combatMight unit false == 4 && done.combatMight unit true == 1 &&
    extra.kwAmount unit .shield == 0 && alone.kwAmount unit .shield == 0 &&
    offField.kwAmount unit .shield == 0

-- Masa stuns an enemy at a Battlefield only if its additional Order Power was paid.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, masa) ← put s p "VEN-120" .hand
  let (s, target) ← putAt s q "VEN-014" s.bf0
  let (s, baseUnit) ← put s q "VEN-014" .base
  let (s, ally) ← putAt s p "VEN-014" (s.battlefields[1]?.getD s.bf0)
  let s := (s.control q s.bf0).fund p 4 (order := 1)
  let (paid, _) ← (step 100 s
    ⟨.player p, .playCard masa ⟨4, [.order]⟩ []⟩).toOption
  let ordinary ← cast s p masa ⟨4, []⟩
  let chosen := settleChain { pick := (· == [target]) } 10 paid
  return paid.trigPicks == [target] && (paid.poolOf p).total == 0 &&
    (chosen.obj? target).any (·.stunned) && (chosen.obj? baseUnit).any (! ·.stunned) &&
    (chosen.obj? ally).any (! ·.stunned) && (ordinary.obj? target).any (! ·.stunned)

-- Reluctant Leader grows for a friendly Unit card and a friendly Unit token.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, leader) ← put s p "VEN-121" .hand
  let (s, unit) ← put s p "VEN-014" .hand
  let (s, maker) ← put s p "VEN-051" .hand
  let (s, foeMaker) ← put s q "VEN-051" .hand
  let entered ← play s p leader
  let source ← entered.firstOf p .base "VEN-121"
  let ally ← play entered p unit
  let mech ← play ally p maker
  let opponent ← play { mech with active := some q, pending := [.priority q] } q foeMaker
  let (expired, _) ← (advance 100 { opponent with pending := [.expireTurn] } []).toOption
  return entered.mightNow source == some 3 && ally.mightNow source == some 5 &&
    mech.mightNow source == some 7 && opponent.mightNow source == some 7 &&
    expired.mightNow source == some 3 && mech.countNamed p .base "Mech" == 1

-- Solari Sunhawk gains one Might and Deflect 2 when its two-Energy Empower resolves.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, sunhawk) ← put s p "VEN-122" .base
  let strengthened ← activate s p sunhawk 1 [] ⟨2, []⟩
  let stripped := (disempowerObj strengthened sunhawk).1
  return (activate s p sunhawk 1 [] ⟨1, []⟩).isNone &&
    s.mightNow sunhawk == some 3 && s.deflectOf sunhawk == 0 &&
    strengthened.mightNow sunhawk == some 4 && strengthened.deflectOf sunhawk == 2 &&
    stripped.mightNow sunhawk == some 3 && stripped.deflectOf sunhawk == 0

-- Soulspinner can use Ambush in response only at a Battlefield with a friendly Unit.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, spinner) ← put s p "VEN-123" .hand
  let (s, ally) ← putAt s p "VEN-014" field
  let (s, item) ← onChain s s.you "OGN-095"
  let s := { s.fund p 3 with pending := [.chainPass p 0, .priority p] }
  let act (destination : List ObjId) : Action := ⟨.player p, .playCard spinner ⟨3, []⟩ destination⟩
  let (played, _) ← (step 100 s (act [field])).toOption
  return !(legalActions s).contains (act []) &&
    !(legalActions (moveHome s ally).1).contains (act [field]) &&
    (played.zone .chain).contains item &&
    (played.unitsAtOf field p).any (fun id => (played.cardDef? id).any (·.id == cid "VEN-123"))

-- Sacred Protector contributes its combat damage only with exactly one other friendly Unit there.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, protector) ← putAt s p "VEN-129" field
  let (s, _) ← putAt s s.you "VEN-014" field
  let (paired, _) ← putAt s p "VEN-014" field
  let (crowded, _) ← putAt paired p "VEN-014" field
  let damage (t : GameState) (attacker : Bool) := t.combatMight protector attacker
  return damage s true == 0 && damage paired false == 6 && damage paired true == 6 &&
    damage crowded true == 0 && damage (moveHome paired protector).1 true == 0

-- Aurok General grants two Might to its controller's Empowered Units, including itself.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, general) ← put s p "VEN-130" .base
  let (s, ally) ← put s p "VEN-071" .base
  let (s, ordinary) ← put s p "VEN-071" .base
  let (s, enemy) ← put s q "VEN-071" .base
  let s := (empowerObj q (empowerObj p s ally).1 enemy).1
  let strengthened ← activate s p general 1 [] ⟨3, [.order]⟩
  let stripped := (disempowerObj strengthened general).1
  return s.mightNow general == some 5 && strengthened.mightNow general == some 7 &&
    strengthened.mightNow ally == some 7 && strengthened.mightNow ordinary == some 5 &&
    strengthened.mightNow enemy == some 5 && stripped.mightNow ally == some 5

-- An attacking, Empowered Ambessa includes Assault when comparing her Might to a target's.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, ambessa) ← put s p "VEN-136" .base
  let (s, weaker) ← putAt s q "VEN-118" field
  let (s, equal) ← putAt s q "VEN-115" field
  let (s, elsewhere) ← put s q "VEN-014" .base
  let s := s.control q field
  let powered ← activate s p ambessa 2 [] ⟨1, [.order, .order]⟩
  let move : Action := ⟨.player p, .standardMove ambessa (.battlefield field)⟩
  let (ordinary, _) ← (step 100 s move).toOption
  let (attack, _) ← (step 100 powered move).toOption
  let (queued, _) ← (step 100 attack ⟨.player p, .putTrigger 0 [weaker]⟩).toOption
  let killed := settleChain {} 8 queued
  let shielded := (addTempKw ⟨.shield, .amount 1⟩ .turn queued weaker).1
  let survived := settleChain {} 8 shielded
  return ordinary.trigPicks.isEmpty && powered.mightNow ambessa == some 5 &&
    attack.mightNow ambessa == some 7 && attack.combatMight ambessa true == 7 &&
    attack.trigPicks.contains weaker && !attack.trigPicks.contains equal &&
    !attack.trigPicks.contains elsewhere && killed.countIn q .trash "VEN-118" == 1 &&
    (survived.obj? weaker).isSome

-- A Sand Soldier remains a token and gains a fresh copied Azir ability on each attachment.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, spectacles) ← put s p "VEN-137" .base
  let (s, azir) ← put s p "SFD-050" .base
  let soldier := tokenId "Sand Soldier"
  let s := createOne soldier p none false s
  let unit ← s.firstOf p .base soldier.code
  let model : Says := { obj := (· == azir) }
  let equip (t : GameState) := activate t p spectacles 1 [unit] ⟨1, [.order]⟩ model
  let use : Action := ⟨.player p, .activate unit 0 ⟨0, [.calm]⟩ [azir]⟩
  let first ← equip s
  let stamp ← first.copyStamp? unit
  let (queued, _) ← (step 100 (first.rich p) use).toOption
  let used := settleChain {} 10 queued
  let detached := (detachObj used spectacles).1
  let again ← equip detached
  return (first.obj? unit).any (·.kind == .token soldier) &&
    (detached.cardDef? unit).any (·.id == soldier) &&
    (again.cardDef? unit).any (·.id == cid "SFD-050") && again.copyStamp? unit != some stamp &&
    !(legalActions (used.rich p)).contains use && (legalActions (again.rich p)).contains use

-- Shen gains the extra Hold point only with exactly one other friendly Unit at his Battlefield.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, shen) ← putAt s p "VEN-138" field
  let (s, _) ← put s p "VEN-014" .base
  let (withOne, _) ← putAt s p "VEN-014" field
  let (withTwo, _) ← putAt withOne p "VEN-014" field
  let held ← fire withOne [.scored p field false]
  let alone ← fire s [.scored p field false]
  let crowded ← fire withTwo [.scored p field false]
  let conquered ← fire withOne [.scored p field true]
  return s.kwAmount shen .shield == 1 && held.pointsOf p == s.pointsOf p + 1 &&
    alone.pointsOf p == s.pointsOf p && crowded.pointsOf p == s.pointsOf p &&
    conquered.pointsOf p == s.pointsOf p

-- Decree of Unity also kills opposing Chaos Gear and leaves friendly Chaos Gear alone.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "VEN-131" .hand
  let (s, enemy) ← put s q "VEN-108" .base
  let (s, ally) ← put s p "VEN-108" .base
  let (s, otherDomain) ← put s q "VEN-054" .base
  let result ← play s p spell [enemy]
  return result.countIn q .trash "VEN-108" == 1 && (result.obj? ally).isSome &&
    (play s p spell [ally]).isNone && (play s p spell [otherDomain]).isNone

-- Rogue Assassin leaves a Unit exhausted on its own turn unless the Legend is Empowered.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let other ← s.battlefields[1]?
  let (s, legend) ← put s p "VEN-139" .legendZone
  let (s, ally) ← putAt s p "VEN-014" field
  let (s, foe) ← putAt s q "VEN-014" field
  let (s, outside) ← putAt s p "VEN-014" other
  let s := ((s.control q field).control p other).tire ally
  let empowered ← activate (moveHome s foe).1 p legend 1 [] ⟨3, [.fury]⟩
  let (empowered, _) ← putAt empowered q "VEN-014" field
  let showdown (t : GameState) := t.inShowdownAt field p
  let ordinary ← activate (showdown s) p legend 0 [ally]
  let ready ← activate (showdown empowered) p legend 0 [ally]
  let onOtherTurn ← activate { (showdown s) with active := some q } p legend 0 [ally]
  return ordinary.locate ally == some (.player p .base) && ordinary.tired ally == some true &&
    ready.locate ally == some (.player p .base) && ready.tired ally == some false &&
    onOtherTurn.locate ally == some .battlefieldZone && onOtherTurn.tired legend == some true &&
    (activate (showdown s) p legend 0 [foe]).isNone &&
    (activate (showdown s) p legend 0 [outside]).isNone

-- Heimerdinger gains Jayce's whole dependent ability and checks his own Empowered status (FAQ).
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, jayce) ← put s p "VEN-149" .legendZone
  let (s, heimer) ← put s p "OGN-111" .base
  let (s, friendly) ← put s p "VEN-054" .base
  let (s, opposing) ← put s q "VEN-062" .base
  let s := (s.tire friendly).tire opposing
  let d ← s.cardDef? heimer
  let borrowed ← (s.activationList heimer d).findIdx? (fun (grant, _) =>
    grant.any (fun g => g.card == cid "VEN-149" && g.index == 1))
  let cost : RunePool.Payment := ⟨1, []⟩
  let ordinary ← activate s p jayce 0 [friendly] cost
  let poweredJayce ← activate s p jayce 2 [] ⟨2, [.body, .mind]⟩
  let poweredHeimer := (empowerObj p s heimer).1
  let two ← activate poweredHeimer p heimer borrowed [friendly, opposing] cost
  let both ← activate poweredJayce p jayce 1 [friendly, opposing] cost
  return ordinary.tired friendly == some false && ordinary.tired opposing == some true &&
    (activate s p jayce 1 [friendly, opposing] cost).isNone &&
    (activate s p heimer borrowed [friendly, opposing] cost).isNone &&
    (activate poweredJayce p heimer borrowed [friendly, opposing] cost).isNone &&
    (activate poweredHeimer p heimer borrowed [friendly, friendly] cost).isNone &&
    two.tired heimer == some true && two.tired jayce == some false &&
    two.tired friendly == some false && two.tired opposing == some false &&
    both.tired jayce == some true && both.tired friendly == some false && both.tired opposing == some false

-- Soul's Reflection gains Empower from its controller and spends it to weaken a Battlefield Unit.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, legend) ← put s p "VEN-151" .legendZone
  let (s, ally) ← put s p "VEN-014" .base
  let (s, opponent) ← putAt s q "VEN-071" s.bf0
  let s := s.control q s.bf0
  let (afterAlly, allyEvents) := empowerObj p s ally
  let (afterOpponent, opponentEvents) := empowerObj q s opponent
  let source ← fire afterAlly allyEvents
  let source := { source with pending := [.priority p] }
  let unrelated ← fire afterOpponent opponentEvents
  let spent ← activate source p legend 1 [opponent]
  let (expired, _) ← (advance 100 { spent with pending := [.expireTurn] } []).toOption
  return (source.obj? legend).any (·.empowerCount == 1) &&
    (unrelated.obj? legend).any (·.empowerCount == 0) &&
    (activate source p legend 1 [ally]).isNone && (activate s p legend 1 [opponent]).isNone &&
    (spent.obj? legend).any (fun o => o.empowerCount == 0 && o.exhausted) &&
    spent.mightNow opponent == some 3 && expired.mightNow opponent == some 5

-- Matriarch of War gains Empower and pays one Power, Exhaust and Disempower to ready a Unit.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, legend) ← put s p "VEN-153" .legendZone
  let (s, ally) ← put s p "VEN-014" .base
  let (s, target) ← put s s.you "VEN-071" .base
  let (s, gear) ← put s p "VEN-054" .base
  let s := (s.tire target).tire gear
  let (empowered, events) := empowerObj p s ally
  let source ← fire empowered events
  let now := { source.fund p 0 (mind := 1) with pending := [.priority p] }
  let act (id : ObjId) : Action := ⟨.player p, .activate legend 1 ⟨0, [.mind]⟩ [id]⟩
  let (waiting, _) ← (step 100 now (act target)).toOption
  let done := settleChain {} 8 waiting
  return !(legalActions now).contains (act gear) &&
    (waiting.obj? legend).any (fun o => o.empowerCount == 0 && o.exhausted) &&
    waiting.tired target == some true && done.tired target == some false &&
    (waiting.poolOf p).totalPower == 0

-- Public Execution compares its two Units' current Might and works from hand or through Flow.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, hand) ← put s p "VEN-154" .hand
  let (s, trash) ← put s p "VEN-154" .trash
  let (s, judge) ← put s p "VEN-071" .base
  let (s, smaller) ← put s q "VEN-014" .base
  let (s, equal) ← put s q "VEN-071" .base
  let (s, sameSide) ← put s p "VEN-014" .base
  let ordinary ← play s p hand [judge, smaller]
  let flowed ← cast (s.fund p 5 (fury := 1) (order := 1)) p trash ⟨5, [.fury, .order]⟩ [judge, smaller]
  return ordinary.countIn q .trash "VEN-014" == 1 && flowed.countIn q .trash "VEN-014" == 1 &&
    ordinary.countIn p .trash "VEN-154" == 2 && flowed.countIn p .banishment "VEN-154" == 1 &&
    (play s p hand [judge, equal]).isNone && (play s p hand [judge, sameSide]).isNone

-- Heart of the Tempest Empowers for a Flow play and can grant temporary Assault in a Showdown.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, legend) ← put s p "VEN-155" .legendZone
  let (s, hand) ← put s p "VEN-049" .hand
  let (s, trash) ← put s p "VEN-049" .trash
  let (s, unit) ← putAt s p "VEN-014" field
  let (s, _) ← putAt s s.you "VEN-071" field
  let s := s.control s.you field
  let ordinary ← play s p hand
  let empowered ← cast (s.fund p 2) p trash ⟨2, []⟩
  let boosted ← activate (empowered.inShowdownAt field p) p legend 1 [unit]
  let (expired, _) ← (advance 100 { boosted with pending := [.expireTurn] } []).toOption
  return (ordinary.obj? legend).any (·.empowerCount == 0) &&
    (empowered.obj? legend).any (·.empowerCount == 1) &&
    ordinary.handN p == s.handN p && empowered.handN p == s.handN p + 1 &&
    (boosted.obj? legend).any (fun o => o.empowerCount == 0 && o.exhausted) &&
    boosted.kwAmount unit .assault == 2 && expired.kwAmount unit .assault == 0

-- Heisho waives Deflect on all six targets of Icathian Rain if even one is there (FAQ).
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, heisho) ← putBf s q "VEN-158"
  let (s, irelia) ← put s q "SFD-057" .base
  let (s, rain) ← put s p "OGN-248" .hand
  let definition ← s.tokenCard "Recruit"
  let s := createOne definition.id q (some heisho) false (s.control q heisho)
  let recruit ← (s.unitsAtOf heisho q).head?
  let s := s.fund p 7 (fury := 3)
  let pay : RunePool.Payment := ⟨7, [.fury, .fury, .fury]⟩
  let allBase := List.replicate 6 irelia
  let withHeisho := recruit :: List.replicate 5 irelia
  let castAt (ts : List ObjId) : Action := ⟨.player p, .playCard rain pay ts⟩
  let (casting, _) ← (step 100 s (castAt withHeisho)).toOption
  let item ← (casting.zone .chain).head?
  return definition.id == cid "VEN-T04" && s.mightNow recruit == some 1 &&
    s.deflectCost p withHeisho == 0 && s.deflectCost p allBase == 6 &&
    (step 100 s (castAt allBase)).toOption.isNone &&
    (casting.poolOf p).total == 0 && (casting.obj? item).any (·.targets == withHeisho)

-- Protective Sands offers a draw on Conquer at four Runes, and offers none at five or on Hold.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, sands) ← putBf s p "VEN-162"
  let four := (channel p (4 - (s.runesOf p).length) s).1
  let five := (channel p 1 four).1
  let draw (t : GameState) (says : Says) (conquer : Bool) :=
    fire (t.fund p 1) [.scored p sands conquer] says
  let paid ← draw four {} true
  let declined ← draw four { yes := false } true
  let over ← draw five {} true
  let held ← draw four {} false
  return (four.runesOf p).length == 4 && (five.runesOf p).length == 5 &&
    paid.handN p == s.handN p + 1 && (paid.poolOf p).energy == 0 &&
    [declined, over, held].all (fun t => t.handN p == s.handN p && (t.poolOf p).energy == 1)

-- Death Mark can Flow from Trash, burns three cards, and plays the Shadow Clone into the Base.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "VEN-144" .trash
  let deck := Zone.player p .mainDeck
  let before := s.zone deck
  let done ← cast (s.fund p 1 (fury := 1) (chaos := 1)) p spell ⟨1, [.fury, .chaos]⟩
  let clone ← done.firstOf p .base "TKN-Shadow Clone"
  return done.zone deck == before.drop 3 && done.countIn p .banishment "VEN-144" == 1 &&
    done.mightNow clone == some 0 && done.tired clone == some true

-- With Flow, Shadow Dash locks a friendly destination and increases both friendly Units there.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, spell) ← put s p "VEN-148" .trash
  let (s, first) ← putAt s p "VEN-014" field
  let (s, second) ← putAt s p "VEN-014" field
  let (s, enemy) ← put s q "VEN-091" .base
  let funded := (s.control p field).fund p 5 (mind := 1) (body := 1)
  let done ← cast funded p spell ⟨5, [.mind, .body]⟩ [enemy] {} (.destination (some field))
  return done.countIn p .banishment "VEN-148" == 1 &&
    (done.obj? enemy).any (·.loc == some field) &&
    done.mightNow first == some 3 && done.mightNow second == some 3

-- Baccai Sandspinner gains Deflect and Assault 2 only after its discounted Empower resolves.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, unit) ← put s p "VEN-001" .base
  let s := s.fund p 2
  let action : Action := ⟨.player p, .activate unit 0 ⟨2, []⟩ []⟩
  let (casting, _) ← (step 100 s action).toOption
  let done := settleChain {} 8 casting
  return s.deflectOf unit == 0 && casting.kwAmount unit .assault == 0 &&
    done.deflectOf unit == 1 && done.kwAmount unit .assault == 2 && (done.poolOf p).total == 0

-- Decree of Rage deals four damage to an enemy Calm Unit in a Showdown.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "VEN-015" .hand
  let (s, defender) ← putAt s q "VEN-042" s.bf0
  let (s, wrongDomain) ← putAt s q "VEN-014" s.bf0
  let (s, ally) ← putAt s p "VEN-042" s.bf0
  let showdown := { (s.fund p 1 (fury := 1)) with pending := [.showdown s.bf0 p 0] }
  let act (target : ObjId) : Action := ⟨.player p, .playCard spell ⟨1, [.fury]⟩ [target]⟩
  let (casting, _) ← (step 100 showdown (act defender)).toOption
  let item ← (casting.zone .chain).head?
  let (resists, counterEvents) := counterObj casting item
  let done := settleChain {} 8 resists
  return !(legalActions showdown).contains (act wrongDomain) &&
    !(legalActions showdown).contains (act ally) && counterEvents.isEmpty &&
    (resists.zone .chain).contains item && (done.obj? defender).any (·.damage == 4)

-- Eclipse Dragon's movement draws at four Runes and stops drawing at five.
#guard verifiedCase fun s => do
  let p := s.me
  let (s, dragon) ← put s p "VEN-016" .base
  let s := (s.control p s.bf0).modObj dragon (fun o => { o with exhausted := false })
  let four := (channel p (4 - (s.runesOf p).length) s).1
  let five := (channel p 1 four).1
  let act : Action := ⟨.player p, .standardMove dragon (.battlefield s.bf0)⟩
  let (early, _) ← (step 100 four act).toOption
  let (late, _) ← (step 100 five act).toOption
  let early := settleChain {} 12 early
  let late := settleChain {} 12 late
  return (four.runesOf p).length == 4 && (five.runesOf p).length == 5 &&
    early.handN p == four.handN p + 1 && late.handN p == five.handN p &&
    (early.obj? dragon).any (·.loc == some s.bf0) && (late.obj? dragon).any (·.loc == some s.bf0)

-- Morgana can use Ambush to join her Units while another Chain item waits.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, morgana) ← put s p "VEN-017" .hand
  let (s, ally) ← putAt s p "VEN-014" field
  let (s, _) ← onChain s q "OGN-095"
  let s := { (s.fund p 5 (fury := 1)) with pending := [.chainPass p 0, .priority p] }
  let ambush : Action := ⟨.player p, .playCard morgana ⟨5, [.fury]⟩ [field]⟩
  let base : Action := ⟨.player p, .playCard morgana ⟨5, [.fury]⟩ []⟩
  let (played, _) ← (step 100 s ambush).toOption
  return !(legalActions s).contains base &&
    !(legalActions (moveHome s ally).1).contains ambush &&
    (played.unitsAtOf field p).any (fun id => (played.cardDef? id).any (·.id == cid "VEN-017"))

-- Twilight Shroud can be played for Flow and protects the boosted friendly Unit for the turn.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, shroud) ← put s p "VEN-031" .trash
  let (s, ally) ← put s p "VEN-014" .base
  let (s, enemy) ← put s q "VEN-014" .base
  let s := s.fund p 2
  let chooseEnemy : Action := ⟨.player p, .playCard shroud ⟨2, []⟩ [enemy]⟩
  let done ← cast s p shroud ⟨2, []⟩ [ally]
  let (expired, _) ← (advance 100 { done with pending := [.expireTurn] } []).toOption
  return !(legalActions s).contains chooseEnemy && done.countIn p .banishment "VEN-031" == 1 &&
    done.mightNow ally == some 3 && done.blocksChoice q ally && !done.blocksChoice p ally &&
    expired.mightNow ally == some 2 && !expired.blocksChoice q ally

-- Resonating Strike's corrected Reaction timing permits responding from hand in the Ending Phase.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, spell) ← put s p "VEN-034" .hand
  let (s, ally) ← put s p "VEN-014" .base
  let (s, _) ← onChain s s.you "OGN-095"
  let funded := (s.control p field).fund p 2 (calm := 1)
  let ending := { funded with phase := .ending, pending := [.chainPass p 0] }
  let act : Action := ⟨.player p, .playCard spell ⟨2, [.calm]⟩ [field, ally]⟩
  let (casting, _) ← (step 100 ending act).toOption
  let done := settleChain {} 8 casting
  return !(legalActions (ending.control s.you field)).contains act &&
    (done.obj? ally).any (·.loc == some field) && done.mightNow ally == some 4

-- The official Akali example: Flash takes her out of combat before Star-Crossed resolves.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, akali) ← putAt s q "VEN-038" field
  let (s, ally) ← putAt s p "VEN-014" field
  let (s, stars) ← put s p "UNL-128" .hand
  let (s, flash) ← put s q "OGS-011" .hand
  let s := ((s.fund p 3 (chaos := 1)).fund q 2).control q field
  let shooting : Action := ⟨.player p, .playCard stars ⟨3, [.chaos]⟩ [ally, akali]⟩
  let (casting, _) ← (step 100 (s.inShowdownAt field p) shooting).toOption
  let (answer, _) ← (step 100 casting ⟨.player p, .pass⟩).toOption
  let (flashing, _) ← (step 100 answer ⟨.player q, .playCard flash ⟨2, []⟩ [akali]⟩).toOption
  let avoided := settleChain {} 12 flashing
  let uncovered := settleChain {} 12 casting
  return !(legalActions s).contains shooting &&
    avoided.locate akali == some (.player q .base) && avoided.countIn q .hand "VEN-038" == 0 &&
    avoided.countIn p .hand "VEN-014" == 1 && uncovered.countIn q .hand "VEN-038" == 1

-- Akali's movement grants Might when she arrives at a Battlefield.
#guard verifiedCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, akali) ← put s p "VEN-038" .base
  let s := (s.control p field).modObj akali (fun o => { o with exhausted := false })
  let (moving, _) ← (step 100 s ⟨.player p, .standardMove akali (.battlefield field)⟩).toOption
  let arrived := settleChain {} 8 moving
  let (home, events) := moveHome arrived akali
  let afterRecall ← fire home events
  return arrived.mightNow akali == (s.mightNow akali).map (· + 2) &&
    afterRecall.mightNow akali == arrived.mightNow akali &&
    afterRecall.locate akali == some (.player p .base)

-- Rage Fueled can Accelerate and hits every enemy Unit at his Battlefield with at most four Runes.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, renekton) ← put s p "VEN-019" .hand
  let (s, first) ← putAt s q "VEN-071" field
  let (s, second) ← putAt s q "VEN-071" field
  let (s, friendly) ← put s p "VEN-071" .base
  let s := (s.control q field).modObj friendly (fun o => { o with exhausted := false })
  let (s, elsewhere) ← put s q "VEN-071" .base
  let runes (t : GameState) := (t.zone (.player p .base)).countP
    (fun id => (t.cardDef? id).any (·.hasType .rune))
  let s ← (List.range (4 - runes s)).foldlM (fun t _ =>
    return (← put t p "OGN-007" .base).1) s
  let (five, _) ← put s p "OGN-007" .base
  let attack (t : GameState) : Option (GameState × ObjId) := do
    let played ← cast (t.fund p 7 (fury := 1)) p renekton ⟨7, [.fury]⟩
    let unit ← played.firstOf p .base "VEN-019"
    let send (state : GameState) (kind : ActionKind) := (step 100 state ⟨.player p, kind⟩).toOption
    let (group, _) ← send played (.startGroupMove (.battlefield field) Cost.zero)
    let (group, _) ← send group (.choose unit)
    let (group, _) ← send group (.choose friendly)
    let (moving, _) ← send group (.decide true)
    return (settleChain {} 8 moving, unit)
  let (fourRunes, attacker) ← attack s
  let (fiveRunes, _) ← attack five
  let damage (t : GameState) (id : ObjId) := (t.obj? id).map (·.damage)
  return runes s == 4 && runes five == 5 && fourRunes.locate attacker == some .battlefieldZone &&
    [first, second].all (fun id => damage fourRunes id == some 2 && damage fiveRunes id == some 0) &&
    [friendly, elsewhere].all (fun id => damage fourRunes id == some 0)

-- Twilight Reveler can ready an ally in base, while the Reveler and enemy Units stay exhausted.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, reveler) ← put s p "VEN-020" .base
  let (s, ally) ← put s p "VEN-071" .base
  let (s, foe) ← putAt s q "VEN-071" field
  let ready := ((s.tire ally).tire foe).control q field
  let (attacking, _) ← (step 100 ready
    ⟨.player p, .standardMove reveler (.battlefield field)⟩).toOption
  let done := settleChain { pick := (· == [ally]) } 8 attacking
  return attacking.trigPicks.contains ally && !attacking.trigPicks.contains reveler &&
    !attacking.trigPicks.contains foe && done.tired ally == some false &&
    done.tired reveler == some true && done.tired foe == some true

-- Deadly Weapon chooses at the origin or destination Battlefield and can decline the damage.
#guard verifiedCase fun s => do
  let p := s.me
  let origin := s.bf0
  let to ← s.battlefields.find? (· != origin)
  let (s, akali) ← putAt s p "VEN-021" origin
  let (s, first) ← putAt s p "VEN-071" origin
  let (s, second) ← putAt s p "VEN-071" to
  let (s, base) ← put s p "VEN-071" .base
  let s := (addTempKw ⟨.ganking, .none⟩ .turn ((s.control p origin).control p to) akali).1
  let powered ← activate s p akali 2 [] ⟨2, [.fury]⟩
  let move (t : GameState) := (step 100 t
    ⟨.player p, .standardMove akali (.battlefield to)⟩).toOption
  let (moving, _) ← move s
  let (movingEmpowered, _) ← move powered
  let done := settleChain { pick := (· == [first]) } 8 moving
  let stronger := settleChain { pick := (· == [second]) } 8 movingEmpowered
  let declined := settleChain { yes := false } 8 moving
  let damage (t : GameState) (id : ObjId) := (t.obj? id).map (·.damage)
  return s.mightNow akali == some 3 && powered.mightNow akali == some 4 &&
    moving.trigPicks.contains first && moving.trigPicks.contains second &&
    !moving.trigPicks.contains base && damage done first == some 1 &&
    damage stronger second == some 2 && damage declined first == some 0 &&
    damage declined second == some 0

-- Hidden Blade can remove Akali in response, but the chosen Unit still takes her damage (FAQ).
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, akali) ← put s p "VEN-021" .base
  let (s, target) ← putAt s q "VEN-071" field
  let (s, blade) ← put s q "OGN-213" .hidden
  let s := (s.control q field).modObj blade
    (fun o => { o with hiddenAt := some field, hiddenTurn := some 0 })
  let (moving, _) ← (step 100 s ⟨.player p, .standardMove akali (.battlefield field)⟩).toOption
  let (queued, _) ← (step 100 moving ⟨.player p, .putTrigger 0 [target]⟩).toOption
  let (answering, _) ← (step 100 queued ⟨.player p, .pass⟩).toOption
  let (withBlade, _) ← (step 100 answering
    ⟨.player q, .activate blade 1 ⟨0, []⟩ [akali]⟩).toOption
  let resolved := settleChain {} 12 withBlade
  return resolved.countIn p .trash "VEN-021" == 1 &&
    resolved.countIn q .trash "OGN-213" == 1 &&
    (resolved.obj? target).any (·.damage == 1)

-- Serene Ascetic's Empower adds Deflect and Shield 3, with the Might applied in defense.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, ascetic) ← putAt s p "VEN-030" field
  let s := s.control p field
  let empowered ← activate s p ascetic 1 [] ⟨3, []⟩
  let attacker := empowered.inCombatAt field p
  let defender := empowered.inCombatAt field q
  return (activate s p ascetic 1 [] ⟨2, []⟩).isNone &&
    s.deflectCost q [ascetic] == 0 && empowered.deflectCost q [ascetic] == 1 &&
    empowered.deflectCost p [ascetic] == 0 && empowered.kwAmount ascetic .shield == 3 &&
    empowered.mightNow ascetic == some 3 && attacker.mightNow ascetic == some 3 &&
    defender.mightNow ascetic == some 6 && defender.combatMight ascetic false == 6

-- Frostcoat Mother counts its controller's ready and exhausted Runes toward Empower, down to zero.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, mother) ← put s p "VEN-032" .base
  let (s, _) ← put s q "OGN-007" .base
  let (s, exhausted) ← put s p "OGN-007" .base
  let s := s.tire exhausted
  let runes := (s.zone (.player p .base)).countP
    (fun id => (s.cardDef? id).any (·.hasType .rune))
  let discount := 12 - runes
  let empowered ← activate s p mother 0 [] ⟨discount, []⟩
  let many ← (List.range (13 - runes)).foldlM (fun t _ =>
    return (← put t p "OGN-007" .base).1) s
  let free ← activate many p mother 0 [] ⟨0, []⟩
  return (activate s p mother 0 [] ⟨discount - 1, []⟩).isNone &&
    (activate empowered p mother 0 [] ⟨discount, []⟩).isNone &&
    s.mightNow mother == some 3 && empowered.mightNow mother == some 6 &&
    free.mightNow mother == some 6

-- At seven Runes, Barbara kills enemy Gear or Disempowers it if it was already Empowered.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, barbara) ← put s p "VEN-037" .hand
  let (s, enemy) ← put s q "VEN-045" .base
  let (s, friendly) ← put s p "VEN-045" .base
  let (s, _) ← put s q "OGN-007" .base
  let runes := (s.zone (.player p .base)).countP
    (fun id => (s.cardDef? id).any (·.hasType .rune))
  let six ← (List.range (6 - runes)).foldlM (fun t _ =>
    return (← put t p "OGN-007" .base).1) s
  let (seven, _) ← put six p "OGN-007" .base
  let enemyEmpowered := (empowerObj q seven enemy).1
  let waiting ← castStop seven p barbara
  let zero ← play six p barbara
  let killed ← play seven p barbara [] { pick := (· == [enemy]) }
  let stripped ← play enemyEmpowered p barbara [] { pick := (· == [enemy]) }
  return waiting.trigPicks == [enemy] && zero.locate enemy == some (.player q .base) &&
    killed.countIn q .trash "VEN-045" == 1 && !killed.inPlay.contains enemy &&
    (stripped.obj? enemy).any (·.empowerCount == 0) && stripped.inPlay.contains enemy &&
    stripped.inPlay.contains friendly

-- Riven's Weaponmaster pays Hand Hammer's Calm cost, and her attack counts both Equipment.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, riven) ← put s p "VEN-041" .hand
  let (s, other) ← put s p "VEN-071" .base
  let (s, helm) ← put s p "VEN-027" .base
  let (s, brutalizer) ← put s p "SFD-042" .base
  let (s, elsewhere) ← put s q "VEN-071" .base
  let (s, target) ← putAt s q "VEN-091" field
  let initial := (attachTo other (s.control q field) helm).1
  let played ← cast (initial.fund p 3 (calm := 2)) p riven ⟨3, [.calm]⟩
    [] { pick := (· == [helm]) }
  let unit ← played.firstOf p .base "VEN-041"
  let geared ← activate played p brutalizer 0 [unit] ⟨0, [.calm]⟩
  let attack (t : GameState) := (step 100 ((t.control q field).modObj unit
    (fun o => { o with exhausted := false }))
    ⟨.player p, .standardMove unit (.battlefield field)⟩).toOption
  let (waiting, _) ← attack geared
  let (oneGear, _) ← attack played
  let struck := settleChain { pick := (· == [target]) } 8 waiting
  let single := settleChain { pick := (· == [target]) } 8 oneGear
  return (initial.obj? helm).any (·.attached == some other) &&
    (played.obj? helm).any (·.attached == some unit) &&
    (played.poolOf p).calm == 0 &&
    waiting.trigPicks == [target] && !waiting.trigPicks.contains elsewhere &&
    (struck.obj? target).any (·.damage == 4) && (single.obj? target).any (·.damage == 2)

-- Helm of Suppression taxes only opposing Spells, with a Power surcharge only while Empowered.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let (s, helm) ← put s p "VEN-045" .base
  let (s, foeSpell) ← put s q "VEN-049" .hand
  let (s, allySpell) ← put s p "VEN-049" .hand
  let (s, foeUnit) ← put s q "VEN-014" .hand
  let spell ← s.cardDef? foeSpell
  let unit ← s.cardDef? foeUnit
  let empowered ← activate s p helm 2 [] ⟨4, [.calm]⟩
  let cost (t : GameState) := t.effCost q foeSpell spell
  return (activate s p helm 2 [] ⟨4, []⟩).isNone &&
    cost s == some ⟨3, []⟩ && cost empowered == some ⟨3, [.any]⟩ &&
    empowered.effCost p allySpell spell == spell.cost &&
    empowered.effCost q foeUnit unit == unit.cost

-- Nasus always has Deflect 2 and only earns a bonus for his own Conquer while Empowered.
#guard verifiedCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let other ← s.battlefields.find? (· != field)
  let (s, nasus) ← putAt s p "VEN-046" field
  let s := (s.control p field).control p other
  let powered ← activate s p nasus 1 [] ⟨8, []⟩
  let hold ← fire powered [.scored p field false]
  let elsewhere ← fire powered [.scored p other true]
  let ordinary ← fire s [.scored p field true]
  let bonus ← fire powered [.scored p field true]
  return (activate s p nasus 1 [] ⟨7, []⟩).isNone && s.deflectCost q [nasus] == 2 &&
    powered.deflectCost q [nasus] == 2 && powered.deflectCost p [nasus] == 0 &&
    [hold, elsewhere, ordinary].all (fun t => t.pointsOf p == s.pointsOf p) &&
    bonus.pointsOf p == s.pointsOf p + 1

end RiftboundTest
