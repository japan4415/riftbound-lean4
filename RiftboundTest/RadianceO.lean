module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance replay and repeated Hidden play -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Ekko's controller pays the full action cost and plays even a borrowed Ekko ready at their base.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, ekko) ← putAt s q "RAD-021" s.bf0
  let (s, discard) ← put s p "RAD-011" .hand
  let s := (s.rich p).modObj ekko (fun o => { o with controller := p, exhausted := true })
  let noDiscard := step 100 s ⟨.player p, .activate ekko 0 ⟨1, [.fury], none⟩ []⟩
  let wrongPower := step 100 s ⟨.player p, .activate ekko 0 ⟨1, [.body], none⟩ [] [discard]⟩
  let (started, _) ← (step 100 s ⟨.player p, .activate ekko 0 ⟨1, [.fury], none⟩ [] [discard]⟩).toOption
  let returned := settleChain {} 12 started
  let newEkko ← returned.firstOf p .base "RAD-021"
  let reentered ← returned.obj? newEkko
  return noDiscard.toOption.isNone && wrongPower.toOption.isNone &&
    returned.countIn p .trash "RAD-011" == 1 && returned.where? ekko == none &&
    newEkko != ekko && reentered.owner == q && reentered.controller == p && !reentered.exhausted

-- Evelynn readies on each Hidden play and retains both Might boosts through the rest of the turn.
#guard radianceCase fun s => do
  let p := s.me
  let first ← s.battlefields[0]?
  let second ← s.battlefields[1]?
  let (s, evelynn) ← put s p "RAD-090" .base
  let (s, inHand) ← put s p "RAD-100" .hand
  let (s, hiddenSpell) ← put s p "RAD-100" .hidden
  let (s, hiddenUnit) ← put s p "RAD-095" .hidden
  let (s, _) ← putAt s p "RAD-011" first
  let (s, _) ← putAt s p "RAD-011" second
  let mark (bf : ObjId) (o : Object) := { o with hiddenAt := some bf, hiddenTurn := some (s.turn - 1) }
  let s := ((s.control p first).control p second).modObj hiddenSpell (mark first)
  let s := (s.modObj hiddenUnit (mark second)).tire evelynn
  let ordinary ← play s p inHand
  let revealedSpell ← activate s p hiddenSpell 1
  let revealedUnit ← activate (revealedSpell.tire evelynn) p hiddenUnit 2
  let (expired, _) ← (advance 100 { revealedUnit with pending := [.expireTurn, .priority p] } []).toOption
  return ordinary.mightEff evelynn == 5 && ordinary.tired evelynn == some true &&
    revealedSpell.mightEff evelynn == 6 && revealedSpell.tired evelynn == some false &&
    revealedUnit.mightEff evelynn == 7 && revealedUnit.tired evelynn == some false &&
    expired.mightEff evelynn == 5

end RiftboundTest
