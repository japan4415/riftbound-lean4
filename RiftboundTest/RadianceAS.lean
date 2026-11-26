module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Boy Who Shattered Time -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Empower and the discount each have their printed exhaust cost. A Gear play leaves the
-- discount, which removes two Energy and one Power from the first Unit and marks it for death.
#guard radianceCase fun s => do
  let p := s.me
  let (s, legend) ← put s p "RAD-139" .legendZone
  let (s, gear) ← put s p "RAD-024" .hand
  let (s, ekko) ← put s p "RAD-021" .hand
  let (s, other) ← put s p "RAD-011" .hand
  let empowered ← activate s p legend 0 (pay := ⟨1, []⟩)
  let ready := empowered.modObj legend (fun o => { o with exhausted := false })
  let discounted ← activate ready p legend 1
  let followingGear ← play discounted p gear [discounted.bf0]
  let played ← cast (followingGear.fund p 3) p ekko ⟨3, []⟩
  let second ← play played p other
  let atEnd ← fire second [.phaseStarted p .ending]
  return (activate s p legend 1).isNone &&
    (empowered.obj? legend).any (fun o => o.exhausted && o.empowerCount == 1) &&
    (discounted.obj? legend).any (fun o => o.exhausted && o.empowerCount == 0) &&
    followingGear.nextUnitDiscount p == (2, 1) && played.nextUnitDiscount p == (0, 0) &&
    (cast (played.fund p 2) p other ⟨2, []⟩).isNone &&
    atEnd.countIn p .trash "RAD-021" == 1 && atEnd.countIn p .base "RAD-011" == 1

-- A Unit token is also a Unit play. The first of two tokens receives the delayed ability.
#guard radianceCase fun s => do
  let p := s.me
  let (s, legend) ← put s p "RAD-139" .legendZone
  let s := s.modObj legend (fun o => { o with empowerCount := 1, exhausted := false })
  let discounted ← activate s p legend 1
  let body := Effect.prim (.create "Recruit" (.const 2) .atBase false)
  let (created, events) ← (advance 100 { discounted with
    pending := [.run p legend {} (.cons body .nil), .priority p] } []).toOption
  let newUnits := events.filterMap (fun
    | .tokenPlayed _ id => some id
    | _ => none)
  let [first, other] := newUnits | none
  let ended ← fire created [.phaseStarted p .ending]
  return created.nextUnitDiscount p == (0, 0) &&
    !(ended.inPlay.contains first) && ended.inPlay.contains other

end RiftboundTest
