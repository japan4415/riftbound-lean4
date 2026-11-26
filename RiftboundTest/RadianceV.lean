module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance optional readiness and dynamic keyword amounts -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Both entry choices cost the same. The elected option prevents Standard Moves and effect Moves
-- this turn, including on a play instructed by an effect.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, card) ← put s p "RAD-026" .hand
  let funded := s.fund p 2
  let playBoar (elections : List Nat) : Action :=
    ⟨.player p, .playCard card ⟨2, []⟩ [] none none (.withPermanentCosts elections)⟩
  let ready := playBoar [0]
  let exhausted := playBoar []
  let (readyState, readyEvents) ← (step 100 funded ready).toOption
  let (defaultState, _) ← (step 100 funded exhausted).toOption
  let boar ← readyState.firstOf p .base "RAD-026"
  let other ← defaultState.firstOf p .base "RAD-026"
  let (next, _) ← (advance 100 { readyState with pending := [.expireTurn, .priority p] } []).toOption
  let free := (funded.control p field)
  let choice ← (permanentPlayOptions free p card { price := .ignoreBase }).find?
    (fun opt => opt.additionalPaid && opt.battlefield == some field)
  let (effectPlay, effectBoar, _) ← applyReducedPermanent free p card choice
  return (legalFrameActions funded).contains ready && (legalFrameActions funded).contains exhausted &&
    (readyState.obj? boar).any (fun o => !o.exhausted) && readyState.moveBlocked boar &&
    !readyEvents.contains (.readied boar) && !moveOk readyState p boar (.battlefield field) &&
    (moveByEffect p (some field) readyState boar).2.isEmpty &&
    (defaultState.obj? other).any (·.exhausted) && !defaultState.moveBlocked other &&
    moveOk next p boar (.battlefield field) &&
    (effectPlay.obj? effectBoar).any (fun o => !o.exhausted && o.loc == some field) &&
    effectPlay.moveBlocked effectBoar

-- Each granted Assault instance uses the current Shield total, including Shield added later.
#guard radianceCase fun s => do
  let p := s.me
  let (s, legend) ← put s p "RAD-147" .legendZone
  let (s, unit) ← put s p "RAD-088" .base
  let (queued, _) ← (step 100 (s.fund p 1)
    ⟨.player p, .activate legend 0 ⟨1, []⟩ [unit]⟩).toOption
  let buffed := settleChain {} 12 queued
  let extra := (addTempKw ⟨.shield, .amount 3⟩ .turn buffed unit).1
  let (expired, _) ← (advance 100 { extra with pending := [.expireTurn, .priority p] } []).toOption
  return (queued.obj? legend).any (·.exhausted) &&
    s.kwAmount unit .assault == 2 && buffed.kwAmount unit .assault == 4 &&
    extra.kwAmount unit .shield == 5 && extra.kwAmount unit .assault == 7 &&
    expired.kwAmount unit .assault == 2 && expired.kwAmount unit .shield == 2

end RiftboundTest
