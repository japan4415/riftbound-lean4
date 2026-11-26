module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance an attack group and Deploy -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Demacian Standard fires once for the group and only chooses among that group's units.
-- A later attacker forms a new group, and the Gear's return on Hold can be declined.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, standard) ← putAt (s.control p field) p "RAD-156" field
  let (s, first) ← putAt s p "RAD-088" field
  let (s, second) ← putAt s p "RAD-088" field
  let (s, defender) ← putAt s q "RAD-088" field
  let (s, base) ← put s p "RAD-088" .base
  let initial := (s.detect [.combatStarted field p]).filter (·.source == standard)
  let [one] := initial | none
  let (offered, _) ← (advance 100 (s.withTriggers [.combatStarted field p]) []).toOption
  let legal (id : ObjId) := (legalFrameActions offered).any (fun a =>
    match a.kind with
    | .putTrigger _ ts (.pay ..) => ts == [id]
    | _ => false)
  let buffed := settleChain { pick := (· == [second]) } 25 offered
  let (withLater, later) ← putAt s p "RAD-088" field
  let singleton := (withLater.detect [.combatJoined field p [later, defender]]).filter (·.source == standard)
  let [joined] := singleton | none
  let (held, _) ← (advance 100 (s.withTriggers [.scored p field false]) []).toOption
  let returned := settleChain {} 20 held
  let leftOnBoard := settleChain { yes := false } 20 held
  return one.eventObjects.length == 2 && legal first && legal second && !legal defender && !legal base &&
    buffed.mightEff second == s.mightEff second + 2 && buffed.mightEff first == s.mightEff first &&
    joined.eventObjects == [later] &&
    returned.countIn p .hand "RAD-156" == 1 && leftOnBoard.inPlay.contains standard

end RiftboundTest
