module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: a game set up from Limited decks (TR 602.4)

A Limited deck may go without a Legend or a Chosen Champion. The game is set up from legal Limited
decks only; the zones of a missing Legend or Chosen Champion are empty, and the player draws one
more card in their first Beginning Phase (TR 602.4.a.5.b).
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- A Limited deck of `n` vanilla Units, with the given Legend and Chosen Champion. -/
meta def limDeck (n : Nat) (legend champ : Option String) : LimitedDeck :=
  { identity := [.fury, .calm, .mind], legend := legend.map cid, chosenChampion := champ.map cid,
    main := (champ.map cid).toList ++ (List.range n).map (fun i => cid s!"V{i % 20}"),
    runes := List.replicate 12 (cid "R1"), battlefields := [cid "B0", cid "B1", cid "B2"] }

meta def sealedCfg : GameConfig := { ruleSet := .tournament .sealed, mode := Mode.duel }

meta def start (cfg : GameConfig) (d : LimitedDeck) : Option GameState :=
  GameState.initialLimited db env cfg [d, d]

-- a legal Sealed deck (25 cards or more) with neither Legend nor Chosen Champion starts a game
#guard (start sealedCfg (limDeck 25 none none)).isSome
#guard (start sealedCfg (limDeck 25 (some "L1") none)).isSome
#guard (start sealedCfg (limDeck 24 (some "L1") (some "C1"))).isSome
-- a Draft deck needs 20, Sealed 25 (TR 602.4.a.2, 602.4.b.3)
#guard !(start sealedCfg (limDeck 24 none none)).isSome
#guard (start { sealedCfg with ruleSet := .tournament .draft } (limDeck 20 none none)).isSome
#guard !(start { sealedCfg with ruleSet := .tournament .draft } (limDeck 19 none none)).isSome
-- A Legend's domains and one chosen domain form a set. Choosing one of the Legend's own
-- domains is legal in both Limited formats (TR 602.4.a.3, 602.4.b.4).
#guard (start sealedCfg { limDeck 25 (some "L1") none with identity := [.calm, .fury] }).isSome
#guard (start { sealedCfg with ruleSet := .tournament .draft }
  { limDeck 20 (some "L1") none with identity := [.calm, .fury] }).isSome
#guard !(start sealedCfg { limDeck 25 (some "L1") none with identity := [.fury, .mind] }).isSome
#guard !(start sealedCfg { limDeck 25 none none with identity := [.calm, .fury] }).isSome
#guard !(start sealedCfg { limDeck 25 (some "L1") none with identity := [.calm, .fury, .fury] }).isSome
-- not a Limited format: no game
#guard !(start { sealedCfg with ruleSet := .tournament .constructed } (limDeck 25 none none)).isSome
#guard !(start { sealedCfg with ruleSet := .coreOnly } (limDeck 25 none none)).isSome
-- no Battlefield to pick, or an illegal card: no game
#guard !(start sealedCfg { limDeck 25 none none with battlefields := [] }).isSome
#guard !(start sealedCfg { limDeck 25 none none with runes := List.replicate 11 (cid "R1") }).isSome
#guard !(start sealedCfg { limDeck 25 none none with main := cid "X1" :: (limDeck 25 none none).main
  }).isSome
-- two decks for two players
#guard !(GameState.initialLimited db env sealedCfg [limDeck 25 none none]).isSome

-- the zones of the Legend and the Chosen Champion are empty when the deck has none
#guard match start sealedCfg (limDeck 25 none none) with
  | some s => (s.zone (.player ⟨0⟩ .legendZone)).isEmpty &&
      (s.zone (.player ⟨1⟩ .championZone)).isEmpty &&
      (s.zone (.player ⟨0⟩ .mainDeck)).length == 25 && s.chosenChampions.isEmpty
  | none => false
#guard match start sealedCfg (limDeck 24 (some "L1") (some "C1")) with
  | some s => (s.zone (.player ⟨0⟩ .legendZone)).length == 1 &&
      (s.zone (.player ⟨0⟩ .championZone)).length == 1 &&
      (s.zone (.player ⟨0⟩ .mainDeck)).length == 24 &&
      s.players.all (fun p => (s.zone (.player p .championZone)).any (s.chosenOf p))
  | none => false

/-- The hands in the Main Phase of turn `n`. -/
meta def handsOf (d : LimitedDeck) (n : Nat) : Option (Nat × Nat) :=
  match start sealedCfg d with
  | none => none
  | some s0 =>
    match runUntilTurn 100 n 4000 (Rng.ofSeed 1) s0 with
    | .ok s =>
      some ((s.zone (.player ⟨0⟩ .hand)).length, (s.zone (.player ⟨1⟩ .hand)).length)
    | .error _ => none

-- the player of a deck without a Legend draws one more in their first turn, once; a deck with
-- both does not
#guard match handsOf (limDeck 30 (some "L1") (some "C1")) 1, handsOf (limDeck 30 none none) 1,
    handsOf (limDeck 30 (some "L1") none) 1, handsOf (limDeck 30 none (some "C1")) 1 with
  | some (a0, _), some (a1, _), some (a2, _), some (a3, _) =>
    a1 == a0 + 1 && a2 == a0 + 1 && a3 == a0 + 1
  | _, _, _, _ => false
#guard match handsOf (limDeck 30 (some "L1") (some "C1")) 2, handsOf (limDeck 30 none none) 2 with
  | some (a0, b0), some (a1, b1) => a1 == a0 + 1 && b1 == b0 + 1
  | _, _ => false

end RiftboundTest
