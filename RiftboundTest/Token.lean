module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: tokens (CR 179-187)

A token has a definition and no physical card. Playing tokens makes the objects on the player's Base
or at a Battlefield, exhausted unless they are played ready. A token that leaves the Board ceases to
exist when the Cleanup next runs.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def tokCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- A Spell: play two Recruit tokens to your Base, and a ready Sprite token. -/
meta def muster : CardDef :=
  { id := cid "T-MUS", name := "Muster", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of []
      (.seqOf [.prim (.create "Recruit" (.const 2) .atBase false),
        .prim (.create "Sprite" (.const 1) .atBase true)])) }

/-- The game in the Main Phase of the first turn, with the tokens and the test Spell known. -/
meta def mainTk : Option GameState :=
  match GameState.initial db tokCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s =>
        some { s with cards := { cards := db.cards ++ RiftboundCards.db.cards ++ [muster] } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putTk (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- The tokens on a zone. -/
meta def tokensOn (s : GameState) (z : Zone) : List ObjId :=
  (s.zone z).filter (fun id => (s.obj? id).any (fun o => match o.kind with
    | .token _ => true | _ => false))

-- the tokens are in the database, and have a Might and the keywords they print
#guard (RiftboundCards.Tokens.cards.length == 5) &&
  (RiftboundCards.db.find? (tokenId "Sprite")).any (·.hasKeyword .temporary) &&
  decide RiftboundCards.db.WF

-- the tokens the data prints are found by name (CR 179): Recruit, Bird, Gold; the others by the
-- name the model gives them
#guard match mainTk with
  | some s =>
    let s' := { s with cards := RiftboundCards.db }
    (s'.tokenCard "Recruit").any (·.might == some 1) &&
    (s'.tokenCard "Bird").any (·.hasKeyword .deflect) &&
    (s'.tokenCard "Gold").any (·.hasType .gear) &&
    (s'.tokenCard "Mech").any (·.might == some 3) &&
    (s'.tokenCard "Nonesuch").isNone
  | none => false

-- a Spell that plays tokens: two exhausted Recruits and a ready Sprite on the Base, with no
-- physical card (CR 183, 359)
#guard match mainTk with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putTk s0 p "T-MUS" .hand with
    | some (s1, c) =>
      let s2 := s1.setPool p { energy := 1 }
      match step 100 s2 ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
      | .ok (s3, _) =>
        match step 100 s3 ⟨.player p, .pass⟩ with
        | .ok (s4, _) =>
          match step 100 s4 ⟨.player (if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩), .pass⟩ with
          | .ok (s5, _) =>
            let before := tokensOn s2 (.player p .base)
            let toks := tokensOn s5 (.player p .base)
            let exhaustedBefore := (before.filter (fun t => (s2.obj? t).any (·.exhausted))).length
            let exhaustedAfter := (toks.filter (fun t => (s5.obj? t).any (·.exhausted))).length
            toks.length == before.length + 3 && exhaustedAfter == exhaustedBefore + 2 &&
            s5.physIds.length == s2.physIds.length &&
            (toks.filter (fun t => s5.mightOf t == some 3)).length == 1 &&
            (s5.zone (.player p .trash)).length == (s2.zone (.player p .trash)).length
          | .error _ => false
        | .error _ => false
      | .error _ => false
    | none => false
  | none => false

-- "here": the token is made at the Battlefield the object is at, with its place; for an object at a
-- Base "here" is the Base, and a token that is unknown or a place that is not understood gives
-- nothing (CR 183)
#guard match mainTk with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match s0.battlefields, putTk s0 p "V0" .base with
    | b :: _, some (s1, u) =>
      match moveObj s1 u .battlefieldZone with
      | some (s2, u') =>
        let s3 := s2.modObj u' (fun o => { o with loc := some b })
        let _ := s2
        (match applyCreate s3 p u' {} "Mech" (.const 2) .here true with
          | some (s4, _) =>
            let ts := (s4.zone .battlefieldZone).filter (fun t => t != u' &&
              (s4.obj? t).any (fun o =>
              o.loc == some b && o.controller == p && !o.exhausted &&
              (match o.kind with | .token _ => true | _ => false)))
            ts.length == 2
          | none => false) &&
        (applyCreate s1 p u {} "Mech" (.const 1) .here true).isSome &&
        (applyCreate s3 p u' {} "Nonesuch" (.const 1) .here true).isNone &&
        (applyCreate s3 p u' {} "Mech" (.const 1) .atBattlefield true).isNone
      | none => false
    | _, _ => false
  | none => false

-- a token that is off the Board ceases to exist at the next Cleanup; the other objects there do not
#guard match mainTk with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putTk s0 p "TKN-Recruit" .trash, putTk s0 p "V0" .trash with
    | some (s1, _), some (s2, _) =>
      match putTk s1 p "TKN-Recruit" .base with
      | some (s3, onBoard) =>
        let s4 := { s3 with pending := .cleanup :: s3.pending }
        (cleanupStep s4).isSome &&
        (match advance 20 s4 [] with
          | .ok (s5, _) =>
            tokensOn s5 (.player p .trash) == [] && tokensOn s5 (.player p .base) ==
              tokensOn s3 (.player p .base) && s5.obj? onBoard == s3.obj? onBoard &&
            (s5.zone (.player p .trash)).length == (s3.zone (.player p .trash)).length - 1 &&
            (cleanupStep s5).isNone
          | .error _ => false) && (let _ := s2; true)
      | none => false
    | _, _ => false
  | none => false

end RiftboundTest
