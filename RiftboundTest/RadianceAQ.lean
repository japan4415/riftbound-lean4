module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Ahri, Confident -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Ahri's own Disarm can trigger her when the enemy's Might actually drops.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, ahri) ← put s p "RAD-SP1" .base
  let (s, enemy) ← putAt s q "VEN-091" field
  let s := (s.control q field).modObj ahri (fun o => { o with exhausted := false })
  let (attack, _) ← (step 100 s ⟨.player p, .standardMove ahri (.battlefield field)⟩).toOption
  let (queued, _) ← (step 100 attack ⟨.player p, .putTrigger 0 [enemy]⟩).toOption
  let done := settleChain {} 16 queued
  return done.mightNow enemy == some 9 && done.mightNow ahri == some 5

-- Multiple points lost by one enemy give one bonus. Another Battlefield and friendly
-- Units do not count, and an opposing player's instruction cannot trigger this Ahri.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, ahri) ← putAt s p "RAD-SP1" field
  let (s, friend) ← putAt s p "VEN-091" field
  let (s, enemy) ← putAt s q "VEN-091" field
  let (s, far) ← putAt s q "VEN-091" away
  let run (who : PlayerId) (source : ObjId) (targets : List ObjId) := do
    let env : Env := { slots := targets.map Value.obj }
    let effect := Effect.grant (.slotsFrom 0) (.mightMinus .it (.const 2)) .thisTurn
    let (state, _) ← (advance 100
      { s with pending := [.run who source env (.cons effect .nil)] } []).toOption
    return settleChain {} 16 state
  let own ← run p ahri [enemy, far, friend]
  let other ← run q enemy [enemy]
  return own.mightNow enemy == some 8 && own.mightNow far == some 8 &&
    own.mightNow friend == some 8 && own.mightNow ahri == some 5 &&
    other.mightNow enemy == some 8 && other.mightNow ahri == some 4

end RiftboundTest
