module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance Gear and its controller -/

namespace RiftboundTest

open Riftbound

-- The owner gets the killed Gear in Trash, and its last controller plays the exhausted Gold.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "RAD-101" .hand
  let (s, gear) ← putAt s p "RAD-012" s.bf0
  let s := s.modObj gear (fun o => { o with controller := q })
  let after ← play s p spell [gear]
  let gold ← (after.zone (.player q .base)).find? (fun id =>
    (after.cardDef? id).any (·.name == "Gold"))
  return after.countIn p .trash "RAD-012" == 1 && after.tired gold == some true &&
    after.countNamed p .base "Gold" == s.countNamed p .base "Gold").getD false

end RiftboundTest
