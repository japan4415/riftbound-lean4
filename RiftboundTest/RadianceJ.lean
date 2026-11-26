module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance conditional Spell timing -/

namespace RiftboundTest

open Riftbound

-- Kai'Sa enables an ordinary Spell as a response only for her controller, in her Showdown.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let field ← s.battlefields[0]?
  let away ← s.battlefields[1]?
  let (s, kaisa) ← putAt (s.rich p) p "RAD-SP4" field
  let (s, spell) ← put s p "RAD-100" .hand
  let (s, enemySpell) ← put s q "RAD-100" .hand
  let (s, unit) ← put s p "RAD-011" .hand
  let (s, _) ← addObject s (newCard s.cards s q (cid "RAD-100")) .chain
  let responding := { s with pending := [.chainPass p 0, .showdown field p 0] }
  let elsewhere := { responding with pending := [.chainPass p 0, .showdown away p 0] }
  let ended := { responding with pending := [.chainPass p 0] }
  let action : Action := ⟨.player p, .playCard spell ⟨1, []⟩ []⟩
  let (resolved, _) ← (step 100 responding action).toOption
  return (legalActions responding).contains action && resolved.zone .chain != responding.zone .chain &&
    !(legalActions elsewhere).contains action && !(legalActions ended).contains action &&
    !responding.cardHasReaction enemySpell && !responding.cardHasReaction unit &&
    responding.kwAmount kaisa .disarm == 1).getD false

end RiftboundTest
