module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: additional costs that the player may pay (CR 357.2, 805, 820)

A Unit with Accelerate may pay 1 Energy and a Power of its domain more, to enter ready. A Spell with
Repeat may pay the cost of the keyword more, to do its effect twice. The payment tells which: the
player pays the cost, or the cost with the additional cost.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- A Unit with Accelerate. -/
meta def swift : CardDef :=
  { id := cid "T-ACC", name := "Swift", types := [.unit], domains := [.fury],
    cost := some ⟨2, []⟩, might := some 2, keywords := [{ keyword := .accelerate }] }

/-- A Unit without it. -/
meta def plain : CardDef :=
  { id := cid "T-PLN", name := "Plain", types := [.unit], domains := [.fury],
    cost := some ⟨2, []⟩, might := some 2 }

/-- A Spell with Repeat 1 Energy: draw a card. -/
meta def echo : CardDef :=
  { id := cid "T-RPT", name := "Echo", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩, keywords := [{ keyword := .repeat_, arg := .cost ⟨1, []⟩ }],
    spellEffect := some (EffectDef.of [] (.prim (.draw .you (.const 1)))) }

/-- The game in the Main Phase of the first turn, with the test cards known. -/
meta def mainOp : Option GameState :=
  match GameState.initial db { ruleSet := .coreOnly, mode := Mode.duel } [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s =>
        some { s with cards := { cards := db.cards ++ RiftboundCards.db.cards ++
          [swift, plain, echo] } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putOp (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- The payments with which the player can play the card. -/
meta def paysOf (s : GameState) (c : ObjId) : List RunePool.Payment :=
  (legalFrameActions s).filterMap (fun a =>
    match a.kind with
    | .playCard c' pay [] => if c' == c then some pay else none
    | _ => none)

-- Accelerate: the Unit can be played for its cost, or for its cost and 1 Energy and a Power of its
-- domain; the Pool decides which payments are there
#guard match mainOp with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putOp s0 p "T-ACC" .hand with
    | some (s1, u) =>
      match putOp s1 p "T-PLN" .hand with
      | some (s2, v) =>
        let rich := s2.setPool p { energy := 3, fury := 1 }
        let poor := s2.setPool p { energy := 2, fury := 1 }
        (paysOf rich u).contains ⟨2, []⟩ && (paysOf rich u).contains ⟨3, [.fury]⟩ &&
        (paysOf poor u).contains ⟨2, []⟩ && !(paysOf poor u).contains ⟨3, [.fury]⟩ &&
        (paysOf rich v) == [⟨2, []⟩]
      | none => false
    | none => false
  | none => false

-- paying the additional cost, the Unit enters ready; paying the cost only, it enters exhausted
#guard match mainOp with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putOp s0 p "T-ACC" .hand with
    | some (s1, u) =>
      let s2 := s1.setPool p { energy := 3, fury := 1 }
      let exh (s : GameState) : Option Bool :=
        (s.zone (.player p .base)).findSome? (fun x =>
          if (s.cardDef? x).any (·.name == "Swift") then (s.obj? x).map (·.exhausted) else none)
      match step 100 s2 ⟨.player p, .playCard u ⟨2, []⟩ []⟩,
          step 100 s2 ⟨.player p, .playCard u ⟨3, [.fury]⟩ []⟩ with
      | .ok (a, _), .ok (b, _) =>
        exh a == some true && exh b == some false &&
        (a.poolOf p).total == 2 && (b.poolOf p).total == 0
      | _, _ => false
    | none => false
  | none => false

/-- Play the Spell with the payment and let both players pass: the effect runs. -/
meta def castOp (s : GameState) (p : PlayerId) (pay : RunePool.Payment) :
    Option (GameState × GameState) :=
  match putOp s p "T-RPT" .hand with
  | none => none
  | some (s1, c) =>
    let s2 := s1.setPool p { energy := 2 }
    match step 100 s2 ⟨.player p, .playCard c pay []⟩ with
    | .ok (s3, _) =>
      match step 100 s3 ⟨.player p, .pass⟩ with
      | .ok (s4, _) =>
        match step 100 s4 ⟨.player (if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩), .pass⟩ with
        | .ok (s5, _) => some (s2, s5)
        | .error _ => none
      | .error _ => none
    | .error _ => none

-- Repeat: for the cost only the effect is done once; with the additional cost, twice
#guard match mainOp with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match castOp s0 p ⟨1, []⟩, castOp s0 p ⟨2, []⟩ with
    | some (a0, a5), some (b0, b5) =>
      (a5.zone (.player p .hand)).length == (a0.zone (.player p .hand)).length &&
      (b5.zone (.player p .hand)).length == (b0.zone (.player p .hand)).length + 1 &&
      (a5.poolOf p).total == 1 && (b5.poolOf p).total == 0
    | _, _ => false
  | none => false

end RiftboundTest
