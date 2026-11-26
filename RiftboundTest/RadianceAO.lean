module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Hexplosive Minefield -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

private meta def bombsAt (s : GameState) (p : PlayerId) (field : ObjId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun id =>
    (s.obj? id).any (fun o =>
      o.kind == .token ⟨"RAD-T02"⟩ && o.controller == p && o.loc == some field))

-- Only the two chosen Bombs are replaced. A third Bomb from a Deathknell is excluded,
-- and the replacement tokens arrive together at the Battlefield chosen during resolution.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, minefield) ← put s p "RAD-142" .hand
  let (s, _) ← putAt s q "VEN-091" field
  let (s, _) ← putAt s q "VEN-091" away
  let s := (s.control q field).control q away
  let s := createN ⟨"RAD-T02"⟩ p (some field) true 2 s
  let s := createOne ⟨"RAD-T02"⟩ p (some away) true s
  let first ← (bombsAt s p field).head?
  let second ← (bombsAt s p away).head?
  let after ← play s p minefield [first, second]
  let atEnd ← fire after [.phaseStarted p .ending] { obj := (· == away) }
  return (bombsAt after p field).isEmpty && (bombsAt after p away).isEmpty &&
    after.countIn p .trash "RAD-142" == 1 && (bombsAt atEnd p field).isEmpty &&
    (bombsAt atEnd p away).length == 2 &&
    (bombsAt atEnd p away).all (fun bomb => atEnd.tired bomb == some false)

-- Choosing zero is legal. Enemy Bombs and friendly Units are illegal targets.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, minefield) ← put s p "RAD-142" .hand
  let (s, unit) ← putAt s p "VEN-091" field
  let s := createOne ⟨"RAD-T02"⟩ q (some field) true s
  let enemy ← (bombsAt s q field).head?
  let after ← play s p minefield []
  let atEnd ← fire after [.phaseStarted p .ending]
  return (play s p minefield [enemy]).isNone && (play s p minefield [unit]).isNone &&
    (bombsAt atEnd p field).isEmpty && bombsAt atEnd q field == [enemy] &&
    (atEnd.fxTriggers .endOfTurn).isEmpty

end RiftboundTest
