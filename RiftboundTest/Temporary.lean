module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: Temporary (CR 816)

A unit with Temporary is killed at the start of its controller's Beginning Phase, before Scoring.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- The game in the Main Phase of the first turn, with the tokens known. -/
meta def mainTk : Option GameState :=
  match GameState.initial db { ruleSet := .coreOnly, mode := Mode.duel } [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s => some { s with cards := { cards := db.cards ++ RiftboundCards.db.cards } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putTk (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

-- the Temporary units of the player are found, those of the other player and the units without
-- Temporary are not
#guard match mainTk with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let o : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match putTk s0 p "TKN-Sprite" .base with
    | some (s1, sp) =>
      match putTk s1 p "TKN-Mech" .base with
      | some (s2, _) =>
        match putTk s2 o "TKN-Sprite" .base with
        | some (s3, _) => tempUnits s3 p == [sp]
        | none => false
      | none => false
    | none => false
  | none => false

-- the Beginning Phase kills them and leaves the others: the Sprite is in the Trash with a new
-- identifier (a token, it ceases to exist at the next Cleanup), the Mech stays, and the event is
-- a death
#guard match mainTk with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putTk s0 p "TKN-Sprite" .base with
    | some (s1, sp) =>
      match putTk s1 p "TKN-Mech" .base with
      | some (s2, mech) =>
        let r := beginStep s2 p
        !(r.1.zone (.player p .base)).contains sp && (r.1.zone (.player p .base)).contains mech &&
        (r.1.zone (.player p .trash)).length == (s2.zone (.player p .trash)).length + 1 &&
        r.2.any (fun e => match e with | .died .. => true | _ => false)
      | none => false
    | none => false
  | none => false

-- in a real game: the Sprite put on the Base on turn 1 is still there when the other player's turn
-- is over, and gone at the start of its controller's next turn, while the Mech stays
#guard match mainTk with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putTk s0 p "TKN-Sprite" .base with
    | some (s1, _) =>
      match putTk s1 p "TKN-Mech" .base with
      | some (s2, _) =>
        let tokens (s : GameState) : Nat :=
          ((s.zone (.player p .base)).filter (fun u => (s.obj? u).any (fun o =>
            match o.kind with | .token c => c == cid "TKN-Sprite" | _ => false))).length
        let run (n : Nat) := runUntilTurn 100 n 20000 (Rng.ofSeed 2) s2
        match run 2, run 3 with
        | .ok sa, .ok sb => tokens sa == 1 && tokens sb == 0 && sb.turn == 3 && sb.active == some p
        | _, _ => false
      | none => false
    | none => false
  | none => false

end RiftboundTest
