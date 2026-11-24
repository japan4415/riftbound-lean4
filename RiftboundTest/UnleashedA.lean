module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests: Unleashed (scenario tests of single cards)

As `SpiritforgedA.lean`: each test puts the cards it needs in the lab (the Main Phase of the first
turn), plays or fires, lets the Chain resolve, and reads what happened.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- Run a scenario in the lab; it must say `true`. -/
meta def tun (f : GameState → Option Bool) : Bool :=
  match lab with
  | some s => (f s).getD false
  | none => false

-- Inferna (UNL-002): Ambush: it can be played as a Reaction to a Battlefield where its player has
-- units, and not to the Base or to a Battlefield without units of that player
#guard tun fun s => do
  let (s1, bf) ← putBf s s.me "OGN-275"
  let (s2, _) ← putAt s1 s.me "OGN-051" bf
  let (s3, other) ← putBf s2 s.me "OGN-276"
  let (s4, c) ← put s3 s.me "UNL-002" .hand
  let (s5, _) ← onChain s4 s.you "OGN-004"
  let rich := s5.rich s.me
  let pay := payOf rich c
  return reactable rich s.me c pay [bf] && !reactable rich s.me c pay [other] &&
    !reactable rich s.me c pay [] && playable rich s.me c pay (some bf) &&
    !playable rich s.me c pay (some other)

-- Mischievous Marai (UNL-003): when played to a battlefield (an open one, with Miss Fortune in
-- play), 2 damage to an enemy unit there
#guard tun fun s => do
  let (s0, _) ← put s s.me "OGN-193" .base
  let (s1, c) ← put s0 s.me "UNL-003" .hand
  let (s2, e) ← putAt s1 s.you "OGN-088" s.bf0
  let toBf ← play s2 s.me c [s.bf0] { pick := fun ts => ts == [e] }
  let toBase ← play s2 s.me c [] { pick := fun ts => ts == [e] }
  return (toBf.obj? e).any (·.damage == 2) && (toBase.obj? e).any (·.damage == 0)

end RiftboundTest
