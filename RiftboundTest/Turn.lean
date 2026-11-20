module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: the turn structure (CR 301-317, 649-651)

Two players with the fixture deck. The driver passes at every Main Phase, so the game goes round.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def tcfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

meta def tp0 : PlayerId := ⟨0⟩
meta def tp1 : PlayerId := ⟨1⟩

meta def cnt (p : PlayerId) (k : ZoneKind) (s : GameState) : Nat := (s.zone (.player p k)).length

/-- The game after `turns` turns, seed `seed`. -/
meta def afterTurns (seed turns : Nat) : Option GameState :=
  match GameState.initial tcfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 turns 2000 (Rng.ofSeed seed) s with
      | .ok s => some s
      | .error _ => none

-- ten turns: the players alternate, and each turn has the same shape (CR 118, 301, 315)
#guard (List.range 6).all fun seed => match afterTurns seed 10 with
  | some s =>
    let first := s.turnOrder.headD tp0
    let second := if first == tp0 then tp1 else tp0
    s.turn == 10 && s.phase == .main && s.result == none &&
    -- the tenth turn is the second player's
    s.active == some second &&
    (match s.pending with | [.priority q] => q == second | _ => false) &&
    -- five turns each: one card drawn each turn (CR 315.4), four to start with
    cnt first .hand s == 9 && cnt second .hand s == 9 &&
    cnt first .mainDeck s == 30 && cnt second .mainDeck s == 30 &&
    -- Runes channeled: two a turn (CR 315.3), and one more for the second player's first turn
    -- (CR 487.7): 5 * 2 = 10 for the first player, 3 + 4 * 2 = 11 for the second
    cnt first .base s == 10 && cnt first .runeDeck s == 2 &&
    cnt second .base s == 11 && cnt second .runeDeck s == 1
  | none => false

-- turn by turn: the active player alternates
#guard (List.range 6).all fun seed =>
  (List.range 8).all fun k => match afterTurns seed (k + 1), afterTurns seed (k + 2) with
    | some a, some b => a.active != b.active && b.turn == a.turn + 1
    | _, _ => false

-- Awaken (CR 315.1, 416): an object the turn player controls that is exhausted becomes ready;
-- the other player's stays as it was
#guard match afterTurns 1 2 with
  | some s =>
    let first := s.turnOrder.headD tp0
    let second := if first == tp0 then tp1 else tp0
    -- exhaust every Rune on both bases, then begin the third turn (the first player's)
    let exhaustAll : GameState := s.mapObjects (fun o => { o with exhausted := true })
    let ready := exhaustAll.mapObjects (readyOf first)
    (ready.zone (.player first .base)).all (fun id =>
      (ready.obj? id).all (fun o => !o.exhausted)) &&
    (ready.zone (.player second .base)).all (fun id =>
      (ready.obj? id).all (fun o => o.exhausted))
  | none => false

-- concede (CR 649-651): at any time; the other player wins; nothing can be answered after
#guard match afterTurns 2 3 with
  | some s =>
    let first := s.turnOrder.headD tp0
    let second := if first == tp0 then tp1 else tp0
    -- at the Main Phase of the third turn, the player without priority concedes
    (match step 100 s ⟨.player second, .concede⟩ with
      | .ok (s', _) => s'.result == some (.won [first]) && s'.pending.isEmpty &&
          (match step 100 s' ⟨.player first, .pass⟩ with
            | .error .illegal => true | _ => false) &&
          (match step 100 s' ⟨.player first, .concede⟩ with
            | .error .illegal => true | _ => false)
      | .error _ => false)
  | none => false

-- a concession by someone who is not a player, or a pass by the wrong player, is refused
#guard match afterTurns 2 3 with
  | some s =>
    let first := s.turnOrder.headD tp0
    let second := if first == tp0 then tp1 else tp0
    (match step 100 s ⟨.chance, .concede⟩ with | .error .illegal => true | _ => false) &&
    (match step 100 s ⟨.player second, .pass⟩ with | .error .illegal => true | _ => false) &&
    (match step 100 s ⟨.player first, .pass⟩ with | .ok _ => true | _ => false) &&
    -- passing in the Main Phase begins the next turn, up to the next Main Phase
    (match step 100 s ⟨.player first, .pass⟩ with
      | .ok (s', _) => s'.turn == s.turn + 1 && s'.active == some second
      | _ => false)
  | none => false

-- the legal answers in the Main Phase: pass for the turn player, and the concessions
#guard match afterTurns 2 1 with
  | some s =>
    let first := s.turnOrder.headD tp0
    (legalActions s).length == 3 &&
    (legalActions s).contains ⟨.player first, .pass⟩ &&
    (legalActions s).contains ⟨.player tp0, .concede⟩ &&
    (legalActions s).contains ⟨.player tp1, .concede⟩ &&
    (legalActions s).all (fun a => decide (Legal s a))
  | none => false

end RiftboundTest
