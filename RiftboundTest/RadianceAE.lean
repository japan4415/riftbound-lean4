module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance revealed deck tops in games with multiple opponents -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

private meta def withThirdPlayer (s : GameState) : GameState :=
  let mode := { s.config.mode with players := 3 }
  let config := { s.config with mode := mode }
  { s with config := config, turnOrder := [s.me, s.you, ⟨2⟩] }

-- The Packmaster plays the chosen opponent's Spell for no cost and Recycles only the
-- original top of the other opponent's deck.
#guard radianceCase fun s => do
  let s := withThirdPlayer s
  let p := s.me
  let q := s.you
  let r : PlayerId := ⟨2⟩
  let (s, pack) ← put s p "RAD-018" .hand
  let (s, _) ← put s p "RAD-011" .mainDeck
  let (s, _) ← put s p "RAD-011" .mainDeck
  let (s, underSpell) ← put s q "RAD-088" .mainDeck
  let (s, spell) ← put s q "OGN-144" .mainDeck
  let (s, underGear) ← put s r "RAD-088" .mainDeck
  let (s, gear) ← put s r "RAD-024" .mainDeck
  let drawBefore := s.drawLog.count (p, s.turn)
  let (placed, _) ← (step 100 (s.fund p 9 (fury := 2))
    ⟨.player p, .playCard pack ⟨9, [.fury, .fury]⟩ []⟩).toOption
  let done := settleChain { obj := (· == spell) } 55 placed
  return done.countIn q .trash "OGN-144" == 1 && done.countIn q .banishment "OGN-144" == 0 &&
    (done.zone (.player q .mainDeck)).head? == some underSpell &&
    done.zone (.player r .mainDeck) == [underGear, gear] &&
    done.drawLog.count (p, s.turn) == drawBefore + 2 && (done.poolOf p).total == 0

-- A tie on printed Energy is enough for Mechanical Bandit to draw its controller's card.
-- If any other top card has a lower Energy cost, all three revealed cards are Recycled.
#guard radianceCase fun s => do
  let s := withThirdPlayer s
  let p := s.me
  let q := s.you
  let r : PlayerId := ⟨2⟩
  let (s, bandit) ← put s p "RAD-111" .base
  let (s, pSecond) ← put s p "RAD-047" .mainDeck
  let (s, own) ← put s p "RAD-088" .mainDeck
  let (s, cheap) ← put s q "RAD-034" .mainDeck
  let (s, tie) ← put s q "RAD-024" .mainDeck
  let (s, rSecond) ← put s r "RAD-088" .mainDeck
  let (s, expensive) ← put s r "RAD-047" .mainDeck
  let pp := Zone.player p .mainDeck
  let qp := Zone.player q .mainDeck
  let rp := Zone.player r .mainDeck
  let original := s.zone pp
  let withoutTie := (s.zone qp).erase tie
  let cheaper := s.reorder qp (cheap :: (s.zone qp).erase cheap)
  let beginPhase (g : GameState) := do
    let (started, _) ← (advance 100 (g.withTriggers [.phaseStarted p .beginning]) []).toOption
    return settleChain {} 35 started
  let draws ← beginPhase s
  let recycles ← beginPhase cheaper
  return ((s.detect [.phaseStarted q .beginning]).filter (·.source == bandit)).isEmpty &&
    draws.drawLog.count (p, s.turn) == s.drawLog.count (p, s.turn) + 1 &&
    (draws.zone pp).head? == some pSecond && draws.zone qp == withoutTie ++ [tie] &&
    draws.zone rp == [rSecond, expensive] &&
    recycles.drawLog == s.drawLog && recycles.zone pp == original.erase own ++ [own] &&
    (recycles.zone qp).getLast? == some cheap && recycles.zone rp == [rSecond, expensive]

end RiftboundTest
