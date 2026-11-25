module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: "here" and the triggers of a move (CR 106, 144)

"Here" is the Battlefield an object is at. A Unit that moves can have a trigger.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def hereCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The other player. -/
meta def otherH (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- A Unit: "When I move, draw 1." -/
meta def traveller : CardDef :=
  { id := cid "T-TRV", name := "Traveller", types := [.unit], domains := [.fury], might := some 2,
    abilities := [.triggered (Trigger.onSelf .move)
      (EffectDef.of [] (.prim (.draw .you (.const 1)))) .unlimited] }

/-- A Unit: "When I conquer, deal 1 to all enemy units here." -/
meta def sweeper : CardDef :=
  { id := cid "T-SWP", name := "Sweeper", types := [.unit], domains := [.fury], might := some 2,
    abilities := [.triggered (Trigger.onSelf .hold)
      (EffectDef.of [] (.prim (.deal (Selector.all .enemy .here [.ofType .unit]) (.const 1))))
      .unlimited] }

/-- The game in the Main Phase of the first turn, with the test cards in its database. -/
meta def mainH : Option GameState :=
  match GameState.initial db hereCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s => some { s with cards := { cards := db.cards ++ [traveller, sweeper] } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putH (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- Put a Unit of the player on the Battlefield. -/
meta def sendTo (s : GameState) (u bf : ObjId) : Option (GameState × ObjId) :=
  match moveObj s u .battlefieldZone with
  | some (s1, u') => some (s1.modObj u' (fun o => { o with loc := some bf }), u')
  | none => none

-- "here" for a Unit at a Battlefield: the Units there, of both players, and the Battlefield; not
-- the Units at another place; for a Unit at a Base, "here" is that Base (CR 106)
#guard match mainH with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match s0.battlefields, putH s0 p "V0" .base with
    | b1 :: b2 :: _, some (s1, a) =>
      match putH s1 (otherH p) "V1" .base with
      | some (s2, d) =>
        match sendTo s2 a b1, sendTo s2 d b1 with
        | some (s3, a'), some (_, _) =>
          match sendTo s3 d b1 with
          | some (s4, d') =>
            (s4.candidates p a' {} .enemy .here (FilterList.ofList [.ofType .unit])) == some [d'] &&
            (s4.candidates p a' {} .friendly .here (FilterList.ofList [.ofType .unit])) ==
              some [a'] &&
            s4.hereOf a' == some b1 && s4.hereOf b1 == some b1 &&
            (s2.candidates p a {} .enemy .here (FilterList.ofList [.ofType .unit])) == some [] &&
            (s4.candidates p b2 {} .any .here (FilterList.ofList [.ofType .unit])) == some []
          | none => false
        | _, _ => false
      | none => false
    | _, _ => false
  | none => false

-- a Unit that moves: the trigger fires when it moves to a Battlefield (CR 144)
#guard match mainH with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match s0.battlefields, putH s0 p "T-TRV" .base with
    | b :: _, some (s1, u) =>
      match step 100 s1 ⟨.player p, .standardMove u (.battlefield b)⟩ with
      | .ok (s2, es) =>
        es.contains (.standardMoved u (some b)) &&
        (s2.zone .chain).any (fun i => (s2.obj? i).any (fun o =>
          match o.kind with | .chainAbility c _ src => c == cid "T-TRV" && src == u | _ => false))
      | .error _ => false
    | _, _ => false
  | none => false

end RiftboundTest
