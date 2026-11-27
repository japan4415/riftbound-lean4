module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance card-type guesses -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Only the selected opponent guesses, then the controller reveals their own top card.
-- A correct guess recycles that card and an incorrect guess draws it.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let r : PlayerId := ⟨2⟩
  let mode := { s.config.mode with players := 3 }
  let config := { s.config with mode := mode }
  let s := { s with config := config, turnOrder := [p, q, r] }
  let (s, scope) ← put s p "RAD-064" .base
  let (s, top) ← put s p "RAD-024" .mainDeck
  let s := s.fund p 1
  let deck := Zone.player p .mainDeck
  let before := s.zone deck
  let qDeck := s.zone (.player q .mainDeck)
  let (activated, _) ← (step 100 s ⟨.player p, .activate scope 0 ⟨1, [], none⟩ [] [] (some r)⟩).toOption
  let guessing := settleChain {} 15 activated
  let choices := (legalFrameActions guessing).filterMap (fun a => match a.kind with
    | .guessCardType kind => some (a.actor, kind)
    | _ => none)
  let guess (kind : CardTypeGuess) : Action := ⟨.player r, .guessCardType kind⟩
  let ((correct, correctEvents), correctDisclosures) ← (stepWithDisclosures 100 guessing (guess .gear)).toOption
  let ((wrong, wrongEvents), wrongDisclosures) ← (stepWithDisclosures 100 guessing (guess .spell)).toOption
  let revealedToAll (entries : List CardDisclosure) : Bool :=
    entries.any (fun entry => entry.cards == [⟨"RAD-024"⟩] && [p, q, r].all entry.visibleTo)
  return chainAnswerWorkSupported guessing (guess .gear) && chainAnswerWorkSupported guessing (guess .spell) &&
    revealedToAll correctDisclosures && revealedToAll wrongDisclosures &&
    choices == [(.player r, .unit), (.player r, .gear), (.player r, .spell)] &&
    (step 100 guessing ⟨.player q, .guessCardType .gear⟩).toOption.isNone &&
    guessing.zone deck == before && (guessing.obj? scope).any (·.exhausted) &&
    correctEvents.contains (.revealed p top) && wrongEvents.contains (.revealed p top) &&
    correct.zone deck == before.erase top ++ [top] && wrong.zone deck == before.erase top &&
    correct.zone (.player p .hand) == s.zone (.player p .hand) &&
    wrong.countIn p .hand "RAD-024" == s.countIn p .hand "RAD-024" + 1 &&
    correct.zone (.player q .mainDeck) == qDeck && wrong.zone (.player q .mainDeck) == qDeck

end RiftboundTest
