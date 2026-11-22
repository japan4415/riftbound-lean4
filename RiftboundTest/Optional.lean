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

/-- A Unit that draws a card when it is played, if another card was played in the turn (Legion). -/
meta def legionary : CardDef :=
  { id := cid "T-LEG", name := "Legionary", types := [.unit], domains := [.fury],
    cost := some ⟨1, []⟩, might := some 1,
    abilities := [.triggered { Trigger.onSelf .play with condition := .legion }
      (EffectDef.of [] (.prim (.draw .you (.const 1)))) .unlimited] }

/-- A Unit that may be played for 1 Energy more, and then draws a card. -/
meta def thrifty : CardDef :=
  { id := cid "T-THR", name := "Thrifty", types := [.unit], domains := [.fury],
    cost := some ⟨1, []⟩, might := some 1, additionalCost := some ⟨1, []⟩,
    abilities := [.triggered { Trigger.onSelf .play with condition := .paid }
      (EffectDef.of [] (.prim (.draw .you (.const 1)))) .unlimited] }

/-- The game in the Main Phase of the first turn, with the test cards known. -/
meta def mainOp : Option GameState :=
  match GameState.initial db { ruleSet := .coreOnly, mode := Mode.duel } [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s =>
        some { s with cards := { cards := db.cards ++ RiftboundCards.db.cards ++
          [swift, plain, echo, legionary, thrifty] } }
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

/-- Let the Chain resolve: the players pass while the Chain is being answered. -/
meta def settle : Nat → GameState → GameState
  | 0, s => s
  | n + 1, s =>
    match s.pending with
    | .chainPass q _ :: _ =>
      match step 100 s ⟨.player q, .pass⟩ with
      | .ok (s', _) => settle n s'
      | .error _ => s
    | _ => s

/-- Play the card with the payment and let what it sets off resolve. -/
meta def playSettle (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment) :
    Option GameState :=
  match step 100 s ⟨.player p, .playCard c pay []⟩ with
  | .ok (s1, _) => some (settle 6 s1)
  | .error _ => none

-- Legion: the effect comes only if another card was played in the turn (CR 812)
#guard match mainOp with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putOp s0 p "T-LEG" .hand with
    | some (s1, l) =>
      match putOp s1 p "T-PLN" .hand with
      | some (s2, v) =>
        let s3 := s2.setPool p { energy := 3 }
        let hand (s : GameState) := (s.zone (.player p .hand)).length
        match playSettle s3 p l ⟨1, []⟩, playSettle s3 p v ⟨2, []⟩ with
        | some alone, some withOther =>
          match playSettle withOther p l ⟨1, []⟩ with
          | some both =>
            hand alone == hand s3 - 1 && hand both == hand withOther
          | none => false
        | _, _ => false
      | none => false
    | none => false
  | none => false

-- "if you paid the additional cost": the effect comes only when the cost with the additional cost
-- was paid
#guard match mainOp with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putOp s0 p "T-THR" .hand with
    | some (s1, u) =>
      let s2 := s1.setPool p { energy := 2 }
      let hand (s : GameState) := (s.zone (.player p .hand)).length
      (paysOf s2 u).contains ⟨1, []⟩ && (paysOf s2 u).contains ⟨2, []⟩ &&
      (match playSettle s2 p u ⟨1, []⟩, playSettle s2 p u ⟨2, []⟩ with
        | some a, some b => hand a == hand s2 - 1 && hand b == hand s2
        | _, _ => false)
    | none => false
  | none => false

end RiftboundTest
