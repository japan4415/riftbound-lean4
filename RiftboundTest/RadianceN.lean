module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance Shield and the Might of Units in play -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Neither enemy Gear here nor friendly Gear elsewhere enables Orianna's combat contribution.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, orianna) ← putAt s p "RAD-042" field
  let (s, _) ← put s p "RAD-012" .base
  let (s, _) ← putAt s q "RAD-012" field
  let (withGear, gear) ← putAt s q "RAD-012" field
  let withGear := withGear.modObj gear (fun o => { o with controller := p })
  return s.combatMight orianna true == 0 && s.combatMight orianna false == 0 &&
    s.mightEff orianna == 4 && withGear.combatMight orianna true == 4 &&
    withGear.combatMight orianna false == 5

-- Both combat designations double the chosen Unit's accumulated Shield for the turn.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, _) ← putAt s p "RAD-045" field
  let (s, shielded) ← putAt s p "RAD-042" field
  let (s, bare) ← putAt s p "RAD-061" field
  let (s, _) ← putAt s q "RAD-067" field
  let s := (addTempKw ⟨.shield, .amount 2⟩ .never s shielded).1
  let says : Says := { pick := fun ids => ids == [shielded] }
  let attacking ← startCombatNow s field p says
  let defending ← startCombatNow s field q says
  let zero ← startCombatNow s field p { pick := fun ids => ids == [bare] }
  let (expired, _) ← (advance 100 { attacking with pending := [.expireTurn, .priority p] } []).toOption
  return attacking.kwAmount shielded .shield == 6 && defending.kwAmount shielded .shield == 6 &&
    expired.kwAmount shielded .shield == 3 &&
    zero.kwAmount bare .shield == 0 && !zero.hasKw bare .shield

-- Shrine compares current Might, rejects ties, and exhausts only when accepted.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, shrine) ← put s p "RAD-089" .base
  let (s, orianna) ← put s p "RAD-042" .hand
  let (s, rival) ← put s q "RAD-014" .base
  let clear ← play s p orianna
  let tied ← play (s.buff rival) p orianna
  let declined ← play s p orianna [] { yes := false }
  return clear.tired shrine == some true && clear.handN p == s.handN p &&
    tied.tired shrine == some false && tied.handN p + 1 == s.handN p &&
    declined.tired shrine == some false && declined.handN p + 1 == s.handN p

end RiftboundTest
