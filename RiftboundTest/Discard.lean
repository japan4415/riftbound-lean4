module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: Discard and Channel as effects (CR 415, 431)

A discard is a choice: the player picks the cards of their hand one at a time. A player with an
empty hand discards nothing. Channel as an effect puts Runes on the Base, some of them exhausted.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def dscCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- A Spell: discard a card, then draw a card. -/
meta def looting : CardDef :=
  { id := cid "T-DSC", name := "Looting", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of []
      (.seqOf [.prim (.discard .you (.const 1)), .prim (.draw .you (.const 1))])) }

/-- A Spell: channel one Rune exhausted. -/
meta def surge : CardDef :=
  { id := cid "T-CHN", name := "Rune Surge", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of [] (.prim (.channel .you (.const 0) (.const 1)))) }

/-- The game in the Main Phase of the first turn, with the test Spells known. -/
meta def mainDs : Option GameState :=
  match GameState.initial db dscCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s =>
        some { s with
          cards := { cards := db.cards ++ RiftboundCards.db.cards ++ [looting, surge] } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putDs (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- Play the Spell and let both players pass: its effect runs. -/
meta def castDs (s : GameState) (p : PlayerId) (card : String) : Option (GameState × GameState) :=
  match putDs s p card .hand with
  | none => none
  | some (s1, c) =>
    let s2 := s1.setPool p { energy := 1 }
    match step 100 s2 ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
    | .ok (s3, _) =>
      match step 100 s3 ⟨.player p, .pass⟩ with
      | .ok (s4, _) =>
        match step 100 s4 ⟨.player (if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩), .pass⟩ with
        | .ok (s5, _) => some (s2, s5)
        | .error _ => none
      | .error _ => none
    | .error _ => none

-- a discard waits for the player to pick: the cards of the hand, and nothing else (CR 415)
#guard match mainDs with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match castDs s0 p "T-DSC" with
    | some (_, s5) =>
      (match s5.pending with | .discard q 1 :: _ => q == p | _ => false) &&
      (legalFrameActions s5).length == (s5.zone (.player p .hand)).length &&
      (legalFrameActions s5).all (fun a => a.actor == .player p &&
        match a.kind with | .discardPick c => (s5.zone (.player p .hand)).contains c | _ => false)
    | none => false
  | none => false

-- the pick puts the card in the Trash; then the draw gives the player a card
#guard match mainDs with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match castDs s0 p "T-DSC" with
    | some (_, s5) =>
      match (legalFrameActions s5).head? with
      | some a =>
        match step 100 s5 a with
        | .ok (s6, _) =>
          (s6.zone (.player p .hand)).length == (s5.zone (.player p .hand)).length &&
          (s6.zone (.player p .trash)).length == (s5.zone (.player p .trash)).length + 1 &&
          (s6.zone (.player p .mainDeck)).length + 1 == (s5.zone (.player p .mainDeck)).length &&
          s6.physIds.length == s5.physIds.length &&
          (match s6.pending with | .discard .. :: _ => false | _ => true)
        | .error _ => false
      | none => false
    | none => false
  | none => false

-- with nothing left to discard (or an empty hand), the only answer is to finish (CR 415.1)
#guard match mainDs with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match castDs s0 p "T-DSC" with
    | some (_, s5) =>
      let s7 := { s5 with pending := .discard p 0 :: (s5.pending.drop 1) }
      let s8 := s5.setZone (Zone.player p .hand) []
      let s9 := { s8 with pending := .discard p 2 :: (s5.pending.drop 1) }
      (legalFrameActions s7).map (·.kind) == [.discardDone] &&
      (legalFrameActions s9).map (·.kind) == [.discardDone] &&
      (match step 100 s9 ⟨.player p, .discardDone⟩ with
        | .ok (s10, _) => (match s10.pending with | .discard .. :: _ => false | _ => true)
        | .error _ => false) &&
      (step 100 s7 ⟨.player p, .discardPick ⟨0⟩⟩).toOption.isNone
    | none => false
  | none => false

-- Channel as an effect: a Rune from the Rune Deck onto the Base, exhausted (CR 431)
#guard match mainDs with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match castDs s0 p "T-CHN" with
    | some (s2, s5) =>
      let exh (s : GameState) : Nat :=
        ((s.zone (.player p .base)).filter (fun r => (s.obj? r).any (·.exhausted))).length
      (s5.zone (.player p .base)).length == (s2.zone (.player p .base)).length + 1 &&
      exh s5 == exh s2 + 1 &&
      (s5.zone (.player p .runeDeck)).length + 1 == (s2.zone (.player p .runeDeck)).length
    | none => false
  | none => false

end RiftboundTest
