module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Zero Point Inflection and draw groups -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

private meta def fillHand (s : GameState) (p : PlayerId) (size : Nat) : Option GameState :=
  (List.range (size - (s.zone (.player p .hand)).length)).foldlM
    (fun g _ => (put g p "RAD-011" .hand).map Prod.fst) s

-- Playing Zero Point Inflection itself counts as playing a card. Its draw of two cards
-- checks the hand from before both draws.
#guard radianceCase fun s => do
  let p := s.me
  let (s, inflection) ← put s p "RAD-069" .hand
  let s ← fillHand s p 9
  let (s, _) ← put s p "RAD-011" .mainDeck
  let (s, _) ← put s p "RAD-011" .mainDeck
  let ready := s.fund p 9 (mind := 2)
  let (casted, _) ← (step 200 ready ⟨.player p, .playCard inflection ⟨9, [.mind, .mind]⟩ []⟩).toOption
  let done := settleChain {} 25 casted
  return (done.zone (.player p .hand)).length == 10 &&
    done.countIn p .base "RAD-069" == 1 && done.pointsOf s.you == ready.pointsOf s.you

-- A two-card draw that starts with nine cards fires one ability. The original hand is
-- discarded along with both draws, the source is killed, and only the chosen opponent scores.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let r : PlayerId := ⟨2⟩
  let mode := { s.config.mode with players := 3 }
  let config := { s.config with mode := mode }
  let s := { s with config := config, turnOrder := [p, q, r] }
  let s ← fillHand s p 9
  let (s, _) ← put s p "RAD-069" .base
  let (s, _) ← put s p "RAD-011" .mainDeck
  let (s, _) ← put s p "RAD-011" .mainDeck
  let drawing := { s with pending := .draw p 2 :: s.pending }
  let (question, events) ← (advance 150 drawing []).toOption
  let choice ← (legalFrameActions question).find? (fun action => match action.kind with
    | .putTrigger _ _ (.pay _ _ (some opponent) _) => opponent == r
    | _ => false)
  let (queued, _) ← (step 150 question choice).toOption
  let done := settleChain {} 30 queued
  return (events.filter (· == .drew p)).length == 2 &&
    (events.filter (· == .drewGroup p 9)).length == 1 && (queued.zone .chain).length == 1 &&
    (done.zone (.player p .hand)).isEmpty && done.countIn p .trash "RAD-069" == 1 &&
    done.pointsOf q == s.pointsOf q && done.pointsOf r == s.pointsOf r + 1

end RiftboundTest
