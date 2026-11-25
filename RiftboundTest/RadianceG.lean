module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance Hidden scenarios -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Agony's Embrace triggers once for Hidden plays and draws before its off-turn discard.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let first ← s.battlefields[0]?
  let second ← s.battlefields[1]?
  let (s, _) ← put s p "RAD-153" .legendZone
  let (s, spell) ← put s p "RAD-100" .hidden
  let (s, unit) ← put s p "RAD-095" .hidden
  let (s, _) ← putAt s p "RAD-011" first
  let (s, _) ← putAt s p "RAD-011" second
  let mark (bf : ObjId) (o : Object) := { o with hiddenAt := some bf, hiddenTurn := some (s.turn - 1) }
  let s := ((s.control p first).control p second).modObj spell (mark first)
  let s := s.modObj unit (mark second)
  let drawn ← activate s p spell 1
  let limited ← activate drawn p unit 2
  let (fresh, _) ← (advance 100 { drawn with pending := [.expireTurn, .beginTurn] } []).toOption
  let otherTurn := { fresh with pending := [.priority p] }
  let changed ← activate otherTurn p unit 2
  return fresh.active == some q && drawn.handN p == s.handN p + 1 && limited.handN p == drawn.handN p &&
    changed.handN p == otherTurn.handN p &&
    (changed.zone (.player p .trash)).length == (otherTurn.zone (.player p .trash)).length + 1 &&
    changed.drawLog.contains (p, otherTurn.turn)

-- Academy pays its actual hiding player only at this Battlefield, regardless of the card's owner.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let away := s.bf0
  let (s, academy) ← putBf s q "RAD-157"
  let (s, hidden) ← put s p "RAD-100" .hand
  let (s, _) ← putAt s p "RAD-011" away
  let (s, _) ← putAt s p "RAD-011" academy
  let s := (s.control p academy).control p away
  let atAcademy ← activate s p hidden 0 [academy] ⟨0, [.calm]⟩
  let elsewhere ← activate s p hidden 0 [away] ⟨0, [.calm]⟩
  let gold ← (atAcademy.zone (.player p .base)).find? (fun id =>
    (atAcademy.cardDef? id).any (·.name == "Gold"))
  return atAcademy.countNamed p .base "Gold" == 1 && atAcademy.countNamed q .base "Gold" == 0 &&
    atAcademy.tired gold == some true && elsewhere.countNamed p .base "Gold" == 0

-- Evelynn's Hold bonus checks both the player and the location of the facedown card.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field ← s.battlefields[0]?
  let away ← s.battlefields[1]?
  let (s, _) ← putAt (s.control p field) p "RAD-SP3" field
  let (s, allyHidden) ← put s p "RAD-100" .hidden
  let (s, theirHidden) ← put s q "RAD-100" .hidden
  let place (g : GameState) (object loc : ObjId) :=
    g.modObj object (fun o => { o with hiddenAt := some loc, hiddenTurn := some g.turn })
  let event := Event.scored p field false
  let right ← fire (place s allyHidden field) [event]
  let wrongPlace ← fire (place s allyHidden away) [event]
  let wrongPlayer ← fire (place s theirHidden field) [event]
  return right.pointsOf p == s.pointsOf p + 1 &&
    wrongPlace.pointsOf p == s.pointsOf p && wrongPlayer.pointsOf p == s.pointsOf p

end RiftboundTest
