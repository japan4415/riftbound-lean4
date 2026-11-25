module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance split damage -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Scorched Earth locks a nonempty group at one Battlefield, then chooses the amounts during
-- resolution. Both damage events follow the same allocation choice.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let other ← s.battlefields.find? (· != field)
  let (s, spell) ← put s p "RAD-006" .hand
  let (s, a) ← putAt (s.control p field) p "RAD-060" field
  let (s, b) ← putAt s p "RAD-067" field
  let (s, far) ← putAt (s.control p other) p "RAD-060" other
  let (s, home) ← put s p "RAD-060" .base
  let ready := s.fund p 4 (fury := 1)
  let play (ids : List ObjId) : Action := ⟨.player p, .playCard spell ⟨4, [.fury]⟩ ids⟩
  let (casted, events) ← (step 100 ready (play [a, b])).toOption
  let (passed, _) ← (step 100 casted ⟨.player p, .pass⟩).toOption
  let (asking, _) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let (after, damage) ← (step 100 asking ⟨.player p, .decide true⟩).toOption
  return (step 100 ready (play [])).toOption.isNone &&
    (step 100 ready (play [a, far])).toOption.isNone &&
    (step 100 ready (play [home])).toOption.isNone &&
    events.contains (.chosenBySpell p a) && events.contains (.chosenBySpell p b) &&
    (asking.obj? a).any (·.damage == 0) && (asking.obj? b).any (·.damage == 0) &&
    damage.contains (.damaged a 1) && damage.contains (.damaged b 4) &&
    (after.obj? a).any (·.damage == 1) && (after.obj? b).any (·.damage == 4)

-- Moving original targets apart leaves one whole legal group at either Battlefield. Moving a new
-- unit into one of those groups does not let the spell target it.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let other ← s.battlefields.find? (· != field)
  let (s, spell) ← put s p "RAD-006" .hand
  let (s, a) ← putAt (s.control p field) p "RAD-060" field
  let (s, b) ← putAt s p "RAD-060" field
  let (s, c) ← putAt s p "RAD-060" field
  let (s, unchosen) ← putAt (s.control p other) p "RAD-060" other
  let (casted, _) ← (step 100 (s.fund p 4 (fury := 1))
    ⟨.player p, .playCard spell ⟨4, [.fury]⟩ [a, b, c]⟩).toOption
  let shifted := casted.modObj c (fun obj => { obj with loc := some other })
  let (passed, _) ← (step 100 shifted ⟨.player p, .pass⟩).toOption
  let (groups, _) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let (two, _) ← (step 100 groups ⟨.player p, .choose a⟩).toOption
  let (firstGroup, firstEvents) ← (step 100 two ⟨.player p, .decide true⟩).toOption
  let (secondGroup, secondEvents) ← (step 100 groups ⟨.player p, .choose c⟩).toOption
  return (step 100 groups ⟨.player p, .choose unchosen⟩).toOption.isNone &&
    (firstGroup.obj? a).any (·.damage == 1) && (firstGroup.obj? b).any (·.damage == 4) &&
    (firstGroup.obj? c).any (·.damage == 0) && (secondGroup.obj? a).any (·.damage == 0) &&
    (secondGroup.obj? c).any (·.damage == 5) && (secondGroup.obj? unchosen).any (·.damage == 0) &&
    firstEvents.contains (.damaged b 4) && secondEvents.contains (.damaged c 5)

-- Bonus Damage increases the split budget once. If the bonus source leaves before resolution,
-- the caster keeps exactly as many original targets as the smaller budget can damage.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, spell) ← put s p "RAD-006" .hand
  let (s, annie) ← put s p "OGS-001" .base
  let (s, a) ← putAt (s.control p field) p "RAD-060" field
  let (s, b) ← putAt s p "RAD-060" field
  let (s, c) ← putAt s p "RAD-060" field
  let (s, d) ← putAt s p "RAD-060" field
  let (s, e) ← putAt s p "RAD-060" field
  let (s, f) ← putAt s p "RAD-060" field
  let targets := [a, b, c, d, e, f]
  let ready := s.fund p 4 (fury := 1)
  let action := ⟨.player p, .playCard spell ⟨4, [.fury]⟩ targets⟩
  let (casted, _) ← (step 100 ready action).toOption
  let full := settleChain {} 20 casted
  let reduced := settleChain { obj := fun id => id != f } 20 (killOrSave casted annie).1
  return (step 100 (killOrSave ready annie).1 action).toOption.isNone &&
    targets.all (fun id => (full.obj? id).any (·.damage == 1)) &&
    (targets.erase f).all (fun id => (reduced.obj? id).any (·.damage == 1)) &&
    (reduced.obj? f).any (·.damage == 0)

end RiftboundTest
