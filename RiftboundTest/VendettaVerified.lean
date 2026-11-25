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

end RiftboundTest
