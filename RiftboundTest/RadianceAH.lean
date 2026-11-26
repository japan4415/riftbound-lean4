module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance Gear with Action -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Jarvan lets his Deploy Gear be played with Focus, without allowing opponents' Gear,
-- ordinary Gear, or a response to a Chain item. The play actually puts it at the chosen field.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, jarvan) ← putAt s p "RAD-091" field
  let (s, _) ← putAt (s.control p field) p "RAD-088" field
  let (s, deploy) ← put s p "RAD-024" .hand
  let (s, plain) ← put s p "RAD-089" .hand
  let (s, rival) ← put s q "RAD-024" .hand
  let focus := ((s.fund p 3).fund q 3)
  let offered := { focus with pending := [.showdown field p 0, .priority p] }
  let wait := { offered with pending := .chainPass p 0 :: offered.pending }
  let other := { offered with pending := [.showdown field q 0, .priority p] }
  let action := ⟨.player p, .playCard deploy ⟨2, []⟩ [away]⟩
  let (played, _) ← (step 100 offered action).toOption
  let gone := (killOrSave offered jarvan).1
  return (legalFrameActions offered).contains action && !(legalFrameActions wait).contains action &&
    !(legalFrameActions gone).contains action &&
    !(legalFrameActions offered).contains ⟨.player p, .playCard plain ⟨3, []⟩ []⟩ &&
    !(legalFrameActions other).contains ⟨.player q, .playCard rival ⟨2, []⟩ [away]⟩ &&
    played.inPlay.any (fun id =>
      (played.cardDef? id).any (·.id == ⟨"RAD-024"⟩) && (played.obj? id).any (·.loc == some away)) &&
    (played.obj? away).any (·.contested.isNone)

-- Only a friendly Deploy Gear at Jarvan's Battlefield satisfies his conquer trigger.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, jarvan) ← putAt (s.control p field) p "RAD-091" field
  let (s, _) ← putAt s q "RAD-024" field
  let (s, _) ← putAt s p "RAD-024" away
  let scored := Event.scored p field true
  let (supported, _) ← putAt s p "RAD-024" field
  let nextRune ← (s.zone (.player p .runeDeck)).head?
  let (triggered, _) ← (advance 100 (supported.withTriggers [scored]) []).toOption
  let done := settleChain {} 20 triggered
  return !(s.detect [scored]).any (·.source == jarvan) &&
    (done.zone (.player p .base)).any (fun id =>
      (done.obj? id).any (fun o => o.formerId == some nextRune && o.exhausted)) &&
    done.zone (.player p .runeDeck) == (s.zone (.player p .runeDeck)).tail

end RiftboundTest
