module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance additional hiding capacity -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Each Trap at the controlled Battlefield adds one slot. A Trap controlled by the
-- opponent grants nothing there, and a Trap at another Battlefield doesn't increase this limit.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, _) ← putAt (s.control p field) p "RAD-011" field
  let (s, existing) ← put s p "RAD-100" .hidden
  let (s, next) ← put s p "RAD-100" .hand
  let (s, third) ← put s p "RAD-100" .hand
  let (s, _) ← putAt s q "RAD-108" field
  let (s, _) ← putAt s p "RAD-108" away
  let base := (s.fund p 0 (calm := 2)).modObj existing (fun o => { o with
    hiddenAt := some field, hiddenTurn := some s.turn })
  let hide (id : ObjId) : Action :=
    ⟨.player p, .activate id 0 ⟨0, [.calm], none⟩ [field]⟩
  let (supported, _) ← putAt base p "RAD-108" field
  let (choosing, _) ← (step 100 supported (hide next)).toOption
  let two := settleChain {} 20 choosing
  let (more, _) ← putAt two p "RAD-108" field
  let (choosingThird, _) ← (step 100 more (hide third)).toOption
  let three := settleChain {} 20 choosingThird
  let hides (g : GameState) := (g.zone (.player p .hidden)).countP (fun id =>
    (g.obj? id).any (·.hiddenAt == some field))
  return !(legalFrameActions base).contains (hide next) && hides two == 2 &&
    !(legalFrameActions two).contains (hide third) && hides three == 3

end RiftboundTest
