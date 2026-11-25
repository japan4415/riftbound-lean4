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

end RiftboundTest
