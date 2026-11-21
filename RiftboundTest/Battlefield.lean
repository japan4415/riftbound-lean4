module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: Battlefields, Move, Cleanup, Showdown and scoring (CR 144, 318-324, 341-348, 471-474)

The turn player has two ready Units on their Base and there are two Battlefields. A Unit goes to a
Battlefield by a Standard Move; the Battlefield is Contested, the Showdown ends with the Control of
the Battlefield and a point by Conquer; later turns score it by Hold.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def bcfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The other player. -/
meta def otherP (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- The game in the Main Phase of the first turn. -/
meta def mainB (seed : Nat) : Option GameState :=
  match GameState.initial db bcfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed seed) s with
      | .ok s => some s
      | .error _ => none

/-- A Vanilla Unit of `p`'s hand, put on `p`'s Base, ready. -/
meta def readyUnit (s : GameState) (p : PlayerId) : Option (GameState × ObjId) :=
  match (s.zone (.player p .hand)).find?
      (fun c => (s.cardDef? c).any (·.name.startsWith "Vanilla")) with
  | none => none
  | some c =>
    match moveObj s c (.player p .base) with
    | none => none
    | some (s1, c') => some (s1.modObj c' (fun o => { o with exhausted := false }), c')

/-- The turn player in the Main Phase with two ready Units on their Base: the state, the player,
the Units, and the two Battlefields. -/
meta def bfReady : Option (GameState × PlayerId × ObjId × ObjId × ObjId × ObjId) :=
  (List.range 40).findSome? fun seed =>
    match mainB seed with
    | none => none
    | some s =>
      let p := s.active.getD ⟨0⟩
      match readyUnit s p with
      | none => none
      | some (s1, u1) =>
        match readyUnit s1 p with
        | none => none
        | some (s2, u2) =>
          match s2.battlefields with
          | [b1, b2] => some (s2, p, u1, u2, b1, b2)
          | _ => none

#guard bfReady.isSome

/-- Whether an action is a Standard Move. -/
meta def isMove (a : Action) : Bool :=
  match a.kind with | .standardMove _ _ => true | _ => false

-- the Standard Moves that can be made: each Unit to each Battlefield, and nothing else (CR 144)
#guard match bfReady with
  | some (s, p, u1, _, b1, _) =>
    moveOk s p u1 (.battlefield b1) &&
    (legalActions s).contains ⟨.player p, .standardMove u1 (.battlefield b1)⟩ &&
    ((legalActions s).filter isMove).length == 4 &&
    -- not from the Base to the Base; not another player's Unit; not outside the Main Phase;
    -- not an exhausted Unit
    !moveOk s p u1 .base && !moveOk s (otherP p) u1 (.battlefield b1) &&
    !moveOk { s with phase := .draw } p u1 (.battlefield b1) &&
    !moveOk (s.modObj u1 (fun o => { o with exhausted := true })) p u1 (.battlefield b1)
  | none => false

/-- A Standard Move of the first Unit to the first Battlefield, and what it caused. -/
meta def afterMove : Option (GameState × List Event) :=
  match bfReady with
  | some (s, p, u1, _, b1, _) =>
    match step 100 s ⟨.player p, .standardMove u1 (.battlefield b1)⟩ with
    | .ok r => some r
    | .error _ => none
  | none => none

-- the Unit is exhausted, at the Battlefield, and the Battlefield is Contested by its player; the
-- Cleanup opens the Showdown, and the mover has Focus (CR 144, 190.3, 323.11, 345)
#guard match bfReady, afterMove with
  | some (_, p, u1, _, b1, _), some (s1, es) =>
    es.contains (.standardMoved u1 (some b1)) &&
    (s1.obj? u1).any (fun o => o.exhausted && o.loc == some b1) &&
    (s1.zone .battlefieldZone).contains u1 &&
    (s1.obj? b1).any (·.contested == some p) && s1.controlOf b1 == none &&
    (match s1.pending with
      | .showdown b q 0 :: .cleanup :: [.priority r] => b == b1 && q == p && r == p
      | _ => false)
  | _, _ => false

-- while the Showdown is open the only answer is to pass, by the player with Focus (CR 347)
#guard match bfReady, afterMove with
  | some (_, p, _, _, _, _), some (s1, _) =>
    legalFrameActions s1 == [⟨.player p, .pass⟩] &&
    (match step 100 s1 ⟨.player (otherP p), .pass⟩ with | .error .illegal => true | _ => false)
  | _, _ => false

/-- Everyone passes in the Showdown. -/
meta def afterShowdown : Option (GameState × List Event) :=
  match bfReady, afterMove with
  | some (_, p, _, _, _, _), some (s1, _) =>
    match step 100 s1 ⟨.player p, .pass⟩ with
    | .ok (s2, _) =>
      match step 100 s2 ⟨.player (otherP p), .pass⟩ with
      | .ok r => some r
      | .error _ => none
    | .error _ => none
  | _, _ => none

-- when everyone has passed, the player whose Unit is alone there controls the Battlefield and
-- scores it by Conquer: one point (CR 348.2, 471, 473)
#guard match bfReady, afterShowdown with
  | some (_, p, _, _, b1, _), some (s3, es) =>
    s3.controlOf b1 == some p && s3.pointsOf p == 1 && s3.pointsOf (otherP p) == 0 &&
    (s3.obj? b1).any (fun o => o.contested == none && o.scored == [p]) &&
    es.contains (.controlChanged b1 (some p)) && es.contains (.scored p b1 true) &&
    es.contains (.pointsGained p 1) &&
    (match s3.pending with | [.priority r] => r == p | _ => false) &&
    (cleanupStep s3).isNone
  | _, _ => false

-- a second Unit goes to the Battlefield the player controls: it is not Contested, and there is no
-- Showdown (CR 190.3)
#guard match bfReady, afterShowdown with
  | some (_, p, _, u2, b1, _), some (s3, _) =>
    match step 100 s3 ⟨.player p, .standardMove u2 (.battlefield b1)⟩ with
    | .ok (s4, _) =>
      (s4.obj? b1).any (·.contested == none) && (s4.unitsOf p b1).length == 2 &&
      (match s4.pending with | [.priority r] => r == p | _ => false) && s4.pointsOf p == 1
    | .error _ => false
  | _, _ => false

-- an opponent's Unit cannot go to a Battlefield where the player's Unit is (until Combat), but
-- can go to the other one
#guard match bfReady, afterShowdown with
  | some (_, p, _, _, b1, b2), some (s3, _) =>
    match readyUnit s3 (otherP p) with
    | some (s4, v) =>
      !moveOk s4 (otherP p) v (.battlefield b1) && moveOk s4 (otherP p) v (.battlefield b2)
    | none => false
  | _, _ => false

-- the Unit goes back to the Base: it is exhausted and has no Battlefield; with no Unit left there,
-- the player loses the Control at the Cleanup (CR 144, 323.5)
#guard match bfReady, afterShowdown with
  | some (_, p, u1, _, b1, _), some (s3, _) =>
    let s3r := s3.modObj u1 (fun o => { o with exhausted := false })
    moveOk s3r p u1 .base &&
    match step 100 s3r ⟨.player p, .standardMove u1 .base⟩ with
    | .ok (s4, _) =>
      (s4.obj? u1).any (fun o => o.exhausted && o.loc == none) &&
      (s4.zone (.player p .base)).contains u1 && s4.controlOf b1 == none &&
      s4.pointsOf p == 1
    | .error _ => false
  | _, _ => false

-- a Unit with lethal damage is killed by the Cleanup, and the player then loses the Control of the
-- Battlefield (CR 323.4, 323.5)
#guard match bfReady, afterShowdown with
  | some (_, p, u1, _, b1, _), some (s3, _) =>
    let s4 := s3.modObj u1 (fun o => { o with damage := 2 })
    s4.lethal u1 && (cleanupStep s4).isSome &&
    match advance 100 { s4 with pending := [.cleanup] } [] with
    | .ok (s5, _) =>
      (s5.obj? u1).isNone && s5.controlOf b1 == none && s5.pointsOf p == 1 &&
      (cleanupStep s5).isNone
    | .error _ => false
  | _, _ => false

-- a Battlefield stays Contested only while the player has a Unit there (CR 323.10)
#guard match bfReady with
  | some (s, p, _, _, b1, _) =>
    let s1 := s.modObj b1 (fun o => { o with contested := some p })
    match cleanupStep s1 with
    | some (s2, _) => (s2.obj? b1).any (·.contested == none)
    | none => false
  | none => false

/-- A state with these points for player 0 and player 1. -/
meta def withPoints (s : GameState) (a b : Nat) : GameState :=
  { s with points := (s.points.insert 0 a).insert 1 b }

-- the winner has the Victory Score (8) and more points than every opponent (CR 323.1)
#guard match bfReady with
  | some (s, _, _, _, _, _) =>
    (withPoints s 8 7).winner == some ⟨0⟩ && (withPoints s 7 8).winner == some ⟨1⟩ &&
    (withPoints s 8 8).winner == none && (withPoints s 7 0).winner == none &&
    (withPoints s 0 9).winner == some ⟨1⟩ &&
    (cleanupFrame (withPoints s 8 7) []).1.result == some (.won [⟨0⟩]) &&
    (cleanupFrame (withPoints s 8 7) []).2 == [Event.won ⟨0⟩] &&
    (cleanupFrame (withPoints s 7 7) []).1.result == none
  | none => false

-- once the game is won, nobody can answer (CR 323.1)
#guard match bfReady with
  | some (s, _, _, _, _, _) =>
    match advance 100 { withPoints s 8 7 with pending := [.cleanup] } [] with
    | .ok (s1, _) => s1.result == some (.won [⟨0⟩]) && (legalActions s1).isEmpty
    | .error _ => false
  | none => false

-- Hold: at the Scoring Step the turn player scores each Battlefield they control and have not
-- scored this turn: once (CR 315.2.b, 472)
#guard match bfReady, afterShowdown with
  | some (_, p, _, _, b1, _), some (s3, _) =>
    let s4 := s3.mapObjects clearScored
    let h1 := hold s4 p
    let h2 := hold h1.1 p
    h1.1.pointsOf p == 2 && h1.2.contains (.scored p b1 false) &&
    -- the same turn again: nothing more
    h2.1.pointsOf p == 2 && h2.2 == [] &&
    -- not the Battlefield of another player's control
    (hold s4 (otherP p)).1.pointsOf (otherP p) == 0
  | _, _ => false

-- scoring twice in a turn does nothing the second time, by Conquer or by Hold (CR 472)
#guard match bfReady, afterShowdown with
  | some (_, p, _, _, b1, _), some (s3, _) =>
    let again := scoreBf s3 p b1 true
    let again2 := scoreBf s3 p b1 false
    again.1 == s3 && again.2 == ([], []) && again2.1 == s3 && (s3.holds p).isEmpty
  | _, _ => false

-- Final Point: a Conquer one point short of the Victory Score gives the last point only if every
-- Battlefield has been scored this turn, and a card drawn instead otherwise (CR 473.1.b)
#guard match bfReady with
  | some (s, p, _, _, b1, b2) =>
    let s7 := withPoints s 7 0
    let drawn := scoreBf s7 ⟨0⟩ b1 true
    let s7b := s7.modObj b2 (fun o => { o with scored := [⟨0⟩] })
    let full := scoreBf s7b ⟨0⟩ b1 true
    let holdOnly := scoreBf s7 ⟨0⟩ b1 false
    p == p &&
    drawn.1.pointsOf ⟨0⟩ == 7 && drawn.2.1 == [Frame.draw ⟨0⟩ 1] &&
    full.1.pointsOf ⟨0⟩ == 8 && full.2.1 == [] &&
    -- a Hold has no such limit
    holdOnly.1.pointsOf ⟨0⟩ == 8
  | none => false

end RiftboundTest
