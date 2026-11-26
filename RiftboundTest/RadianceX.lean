module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance Channel replacements -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Each friendly Wyvern adds one exhausted Rune in either kind of Channel. Original Runes keep
-- their requested status, and a Channel belonging to another player gets their own replacements.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, _) ← put s p "RAD-092" .base
  let (s, _) ← put s p "RAD-092" .base
  let s ← (List.range 6).foldlM (fun g _ =>
    (put g p "OGN-042" .runeDeck).map Prod.fst) s
  let s ← (List.range 4).foldlM (fun g _ =>
    (put g q "OGN-042" .runeDeck).map Prod.fst) s
  let statuses (g : GameState) (events : List Event) :=
    (movedNew events).filterMap (fun id => (g.obj? id).map (·.exhausted))
  let (phase, events) ← microStep0 { s with pending := [.phase .channel] }
  let (effect, effectEvents) ← applyPrim s p s.bf0 {} (.channel .you (.const 1) (.const 1))
  let rival := channelEx q 0 1 s
  let zero := channelEx p 0 0 s
  return statuses phase events == List.replicate s.channelCount false ++ [true, true] &&
    statuses effect effectEvents == [false, true, true, true] &&
    statuses rival.1 rival.2 == [true] && zero.2.isEmpty

-- The extra Rune doesn't count against Catalyst's success. A deck of two satisfies the spell.
#guard radianceCase fun s => do
  let p := s.me
  let (s, _) ← put s p "RAD-092" .base
  let (s, _) ← put s p "OGN-042" .runeDeck
  let (s, _) ← put s p "OGN-042" .runeDeck
  let (s, catalyst) ← put s p "OGN-138" .hand
  let (s, _) ← put s p "RAD-011" .mainDeck
  let z := Zone.player p .runeDeck
  let limited ← (s.zone z |>.drop 2).foldlM
    (fun g id => (moveObj g id (.player p .base)).map Prod.fst) s
  let done ← play limited p catalyst
  let top ← (limited.zone z).head?
  let (short, _) ← moveObj limited top (.player p .base)
  let didDraw ← play short p catalyst
  return (done.zone z).isEmpty && (didDraw.zone z).isEmpty &&
    done.drawLog.count (p, done.turn) == limited.drawLog.count (p, limited.turn) &&
    didDraw.drawLog.count (p, didDraw.turn) == short.drawLog.count (p, short.turn) + 1

end RiftboundTest
