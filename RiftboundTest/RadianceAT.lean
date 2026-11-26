module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Neeko, Blending In -/

namespace RiftboundTest

open Riftbound

private meta def registeredNames (s : GameState) (p : PlayerId) (zone : ZoneKind) : List CardId :=
  (s.zone (.player p zone)).filterMap (fun id => (s.cardDef? id).map (·.id))

-- The allowance belongs to the registered card pool. Legends have distinct names and a
-- Constructed player may register them with a Neeko in their sideboard.
#guard (lab.bind fun s => do
  let a : CardId := ⟨"RAD-139"⟩
  let b : CardId := ⟨"RAD-145"⟩
  let neeko : CardId := ⟨"RAD-167"⟩
  let added := { goodDeck with main := goodDeck.main ++ [neeko], reserveLegends := [a, b] }
  let duplicated := { added with reserveLegends := [a, a] }
  let mainOnly := { goodDeck with reserveLegends := [a, b] }
  let constructed : ConstructedDeck := { deck := mainOnly, sideboard := [neeko] }
  let env : LegalityEnv := { legalSets := [testSet, ⟨"RAD"⟩], banned := [] }
  let config : GameConfig := { mode := Mode.duel, ruleSet := .tournament .constructed }
  let opening ← GameState.initialConstructed s.cards env config [constructed, { deck := goodDeck, sideboard := [] }]
  return (registeredNames opening ⟨0⟩ .reserveLegends) == [a, b] &&
    decide (DeckValid s.cards Mode.duel added) &&
    !decide (DeckValid s.cards Mode.duel duplicated) &&
    !decide (DeckValid s.cards Mode.duel mainOnly) &&
    decide (ConstructedDeckValid s.cards env constructed)).getD false

-- A Neeko takes an additional Legend from the controller's own registered choices. It
-- remains the second Legend, then returns to the same reserve when Neeko leaves the Board.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let starting := registeredNames s p .legendZone
  let (s, neeko) ← put s p "RAD-167" .hand
  let (s, first) ← put s p "RAD-139" .reserveLegends
  let (s, own) ← put s p "RAD-145" .reserveLegends
  let (s, enemy) ← put s q "RAD-151" .reserveLegends
  let played ← play s p neeko [] { obj := (· == own) }
  let onBoard ← played.firstOf p .base "RAD-167"
  let (removed, _) := killObj played onBoard
  let (settled, _) ← (advance 100 { removed with pending := [.cleanup, .priority p] } []).toOption
  return registeredNames played p .legendZone == starting ++ [⟨"RAD-145"⟩] &&
    (played.zone (.player p .reserveLegends)).contains first &&
    (played.zone (.player q .reserveLegends)).contains enemy &&
    registeredNames settled p .legendZone == starting &&
    (registeredNames settled p .reserveLegends).contains ⟨"RAD-145"⟩).getD false

end RiftboundTest
