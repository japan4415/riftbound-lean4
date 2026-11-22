module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: the extra draw of Limited (TR 602.4.a.5.b)

A player of a Limited format whose deck has no Legend or no Chosen Champion draws 1 card at the
start of their first Beginning Phase. The deck without a Legend is made by emptying its zone.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- The hand of each player in the Main Phase of turn `n`, in a game under the rules, after the
zones of the kinds listed were emptied for both players. -/
meta def handsAt (rules : RuleSet) (empty : List ZoneKind) (n : Nat) : Option (Nat × Nat) :=
  match GameState.initial db { ruleSet := rules, mode := Mode.duel } [goodDeck, goodDeck] with
  | none => none
  | some s0 =>
    let s1 := empty.foldl
      (fun s k => (s.setZone (.player ⟨0⟩ k) []).setZone (.player ⟨1⟩ k) []) s0
    match runUntilTurn 100 n 4000 (Rng.ofSeed 1) s1 with
    | .ok s =>
      some ((s.zone (.player ⟨0⟩ .hand)).length, (s.zone (.player ⟨1⟩ .hand)).length)
    | .error _ => none

-- in Sealed, a deck without a Legend draws 1 more in its first turn: turn 1 is player 0's
#guard match handsAt (.tournament .sealed) [] 1, handsAt (.tournament .sealed) [.legendZone] 1 with
  | some (a0, b0), some (a1, b1) => a1 == a0 + 1 && b1 == b0
  | _, _ => false

-- the same for the Chosen Champion, and 1 only when there is neither
#guard match handsAt (.tournament .sealed) [] 1, handsAt (.tournament .draft) [.championZone] 1,
    handsAt (.tournament .sealed) [.legendZone, .championZone] 1 with
  | some (a0, _), some (a1, _), some (a2, _) => a1 == a0 + 1 && a2 == a0 + 1
  | _, _, _ => false

-- player 1 draws it in turn 2, their first turn; player 0 does not draw it again in turn 3
#guard match handsAt (.tournament .draft) [] 2, handsAt (.tournament .draft) [.legendZone] 2,
    handsAt (.tournament .draft) [] 3, handsAt (.tournament .draft) [.legendZone] 3 with
  | some (a0, b0), some (a1, b1), some (c0, d0), some (c1, d1) =>
    a1 == a0 + 1 && b1 == b0 + 1 && c1 == c0 + 1 && d1 == d0 + 1
  | _, _, _, _ => false

-- Constructed and the Core Rules do not draw it
#guard match handsAt (.tournament .constructed) [] 1,
    handsAt (.tournament .constructed) [.legendZone] 1, handsAt .coreOnly [] 1,
    handsAt .coreOnly [.legendZone, .championZone] 1 with
  | some (a0, _), some (a1, _), some (c0, _), some (c1, _) => a1 == a0 && c1 == c0
  | _, _, _, _ => false

end RiftboundTest
