module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: the Rune Pool, Rune abilities and paying (CR 164, 166, 167, 430, 445)
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def rcfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The game in the Main Phase of the first turn. -/
meta def mainPhase (seed : Nat) : Option GameState :=
  match GameState.initial db rcfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed seed) s with
      | .ok s => some s
      | .error _ => none

meta def rc (p : PlayerId) (k : ZoneKind) (s : GameState) : Nat := (s.zone (.player p k)).length

-- the Runes know their domain (the Fury Rune of the fixtures)
#guard match mainPhase 1 with
  | some s =>
    let first := s.turnOrder.headD ⟨0⟩
    (s.zone (.player first .base)).all fun id =>
      (s.obj? id).any fun o => o.runeDomain == some .fury
  | none => false

-- exhausting a ready Rune adds one Energy, and the Rune is exhausted (CR 164.2, 415, 430)
#guard match mainPhase 1 with
  | some s =>
    let first := s.turnOrder.headD ⟨0⟩
    match s.zone (.player first .base) with
    | c1 :: c2 :: _ =>
      match step 100 s ⟨.player first, .runeAbility c1 .exhaust⟩ with
      | .ok (s1, _) =>
        (s1.poolOf first).energy == 1 && (s1.obj? c1).any (·.exhausted) &&
        -- the same Rune cannot be exhausted again; the other can
        (match step 100 s1 ⟨.player first, .runeAbility c1 .exhaust⟩ with
          | .error .illegal => true | _ => false) &&
        (match step 100 s1 ⟨.player first, .runeAbility c2 .exhaust⟩ with
          | .ok (s2, _) => (s2.poolOf first).energy == 2 && (s2.poolOf first).total == 2
          | _ => false) &&
        -- still the same question: the turn player has priority
        (match s1.pending with | [.priority q] => q == first | _ => false)
      | .error _ => false
    | _ => false
  | none => false

-- recycling a Rune adds one Power of its domain, and the Rune goes to the Rune Deck
-- (CR 164.2, 417, 430): the number of Runes on the Base and in the Rune Deck stays 12
#guard match mainPhase 2 with
  | some s =>
    let first := s.turnOrder.headD ⟨0⟩
    match s.zone (.player first .base) with
    | c1 :: _ =>
      match step 100 s ⟨.player first, .runeAbility c1 .recycle⟩ with
      | .ok (s1, _) =>
        (s1.poolOf first).fury == 1 && (s1.poolOf first).energy == 0 &&
        rc first .base s1 + 1 == rc first .base s &&
        rc first .runeDeck s1 == rc first .runeDeck s + 1 &&
        rc first .base s1 + rc first .runeDeck s1 == 12
      | .error _ => false
    | _ => false
  | none => false

-- only the turn player can use a Rune, and only a Rune on their own Base
#guard match mainPhase 3 with
  | some s =>
    let first := s.turnOrder.headD ⟨0⟩
    let second : PlayerId := if first == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match s.zone (.player first .base) with
    | c1 :: _ =>
      (match step 100 s ⟨.player second, .runeAbility c1 .exhaust⟩ with
        | .error .illegal => true | _ => false) &&
      (match step 100 s ⟨.chance, .runeAbility c1 .exhaust⟩ with
        | .error .illegal => true | _ => false) &&
      -- a card that is not on the Base
      (match s.zone (.player first .hand) with
        | h1 :: _ => (match step 100 s ⟨.player first, .runeAbility h1 .exhaust⟩ with
            | .error .illegal => true | _ => false)
        | [] => false)
    | _ => false
  | none => false

-- the Pool is empty at the end of the turn and when the next Main Phase starts (CR 167)
#guard match mainPhase 4 with
  | some s =>
    let first := s.turnOrder.headD ⟨0⟩
    let second : PlayerId := if first == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match s.zone (.player first .base) with
    | c1 :: _ =>
      match step 100 s ⟨.player first, .runeAbility c1 .exhaust⟩ with
      | .ok (s1, _) =>
        (s1.poolOf first).energy == 1 &&
        (match step 100 s1 ⟨.player first, .pass⟩ with
          | .ok (s2, _) =>
            (s2.poolOf first) == RunePool.empty && (s2.poolOf second) == RunePool.empty
          | .error _ => false)
      | .error _ => false
    | _ => false
  | none => false

-- paying (CR 445): the Pool loses what is paid, and a payment it cannot cover is refused
#guard (RunePool.spend { energy := 3, fury := 2 } ⟨1, [.fury]⟩).map (·.total) == some 3
#guard (RunePool.spend { energy := 3, fury := 2 } ⟨1, [.fury]⟩) ==
  some { energy := 2, fury := 1, spent := 1 }
#guard (RunePool.spend { energy := 3, fury := 2 } ⟨4, []⟩).isNone
#guard (RunePool.spend { energy := 3, fury := 2 } ⟨0, [.calm]⟩).isNone
#guard (RunePool.spend { energy := 3, fury := 2 } ⟨0, [.fury, .fury, .fury]⟩).isNone
#guard (RunePool.spend { energy := 3, fury := 2 } ⟨0, []⟩) == some { energy := 3, fury := 2 }

end RiftboundTest
