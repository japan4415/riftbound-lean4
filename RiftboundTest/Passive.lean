module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: passive abilities (CR 363-366)

A passive ability changes the game while its object is in play and its condition holds: a Unit
that enters ready, a Unit that gives other Units Might, a Unit that has more Might while its
player has enough Runes. The Might the rules read (lethal damage, Combat) counts them.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def passCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The other player. -/
meta def otherA (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- A Unit that enters ready. -/
meta def scout : CardDef :=
  { id := cid "T-SCT", name := "Scout", types := [.unit], domains := [.fury], might := some 1,
    cost := some ⟨1, []⟩, abilities := [.passive .always [.entersReady .self]] }

/-- A Unit that gives the other friendly Units +1 Might. -/
meta def banner : CardDef :=
  { id := cid "T-BAN", name := "Banner", types := [.unit], domains := [.fury], might := some 1,
    abilities := [.passive .always
      [.mightPlus (Selector.all .friendly .anywhere [.ofType .unit, .notSelf]) (.const 1)]] }

/-- A Unit with `n` more Might than it prints while its player has at least `k` Runes. -/
meta def eager (k : Nat) : CardDef :=
  { id := cid "T-EAG", name := "Eager", types := [.unit], domains := [.fury], might := some 2,
    abilities := [.passive
      (.cmp .ge (.count (Selector.all .friendly .anywhere [.ofType .rune])) (.const k))
      [.mightPlus .self (.const 4)]] }

/-- A Unit with less Might while the other player has a Unit. -/
meta def weakened : CardDef :=
  { id := cid "T-WEK", name := "Weakened", types := [.unit], domains := [.fury], might := some 3,
    abilities := [.passive .always [.mightMinus .self (.const 5)]] }

/-- The game in the Main Phase of the first turn, with the test cards in its database. -/
meta def mainA (k : Nat) : Option GameState :=
  match GameState.initial db passCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s =>
        some { s with cards := { cards := db.cards ++ [scout, banner, eager k, weakened] } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putA (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

-- a Unit with the passive ability enters ready; any other Unit enters exhausted (CR 359)
#guard match mainA 0 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putA s0 p "T-SCT" .hand with
    | none => false
    | some (s1, a) =>
    match putA s1 p "V0" .hand with
    | none => false
    | some (s2, b) =>
      let s3 := s2.setPool p { energy := 2 }
      (match step 100 s3 ⟨.player p, .playCard a ⟨1, []⟩ []⟩ with
        | .ok (s4, es) => es.any (fun e => match e with
            | .moved _ n _ => (s4.obj? n).any (fun o => !o.exhausted)
            | _ => false)
        | .error _ => false) &&
      (match step 100 s3 ⟨.player p, .playCard b ⟨1, []⟩ []⟩ with
        | .ok (s4, es) => es.any (fun e => match e with
            | .moved _ n _ => (s4.obj? n).any (fun o => o.exhausted)
            | _ => false)
        | .error _ => false)
  | none => false

-- a Unit that gives the other friendly Units +1 Might: they have 1 more, it does not, the other
-- player's Units do not; the Might that the effects select by is the one without it (CR 479.4)
#guard match mainA 0 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putA s0 p "T-BAN" .base with
    | none => false
    | some (s1, ban) =>
    match putA s1 p "V0" .base with
    | none => false
    | some (s2, mine) =>
    match putA s2 (otherA p) "V1" .base with
    | none => false
    | some (s3, theirs) =>
      s3.mightNow ban == some 1 && s3.mightNow mine == some 3 && s3.mightNow theirs == some 2 &&
      s3.mightOf mine == some 2 &&
      -- gone from play, the change is gone
      (match moveObj s3 ban (.player p .trash) with
        | some (s4, _) => s4.mightNow mine == some 2
        | none => false)
  | none => false

-- the Might counted for lethal damage and for Combat is the one with the passive changes
#guard match mainA 0 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putA s0 p "T-BAN" .base with
    | none => false
    | some (s1, _) =>
    match putA s1 p "V0" .base with
    | none => false
    | some (s2, mine) =>
      let s3 := s2.modObj mine (fun o => { o with damage := 2 })
      !s3.lethal mine && s3.mightEff mine == 3
  | none => false

-- a passive ability with a condition: the Unit has 4 more Might while its player has enough Runes
#guard match mainA 0 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let runes := ((s0.zone (.player p .base)).filter
      (fun r => (s0.cardDef? r).any (·.hasType .rune))).length
    match mainA (runes + 1), mainA runes with
    | some t0, some u0 =>
      match putA t0 p "T-EAG" .base, putA u0 p "T-EAG" .base with
      | some (t1, e), some (u1, f) =>
        -- one Rune too few: the printed Might; enough Runes: 4 more
        t1.mightNow e == some 2 && u1.mightNow f == some 6 &&
        (match putA t1 p "R1" .base with
          | some (t2, _) => t2.mightNow e == some 6
          | none => false)
      | _, _ => false
    | _, _ => false
  | none => false

-- a passive change that lowers Might, and a Might below 0 counts as 0 for damage (CR 143.2.c)
#guard match mainA 0 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putA s0 p "T-WEK" .base with
    | some (s1, w) => s1.mightNow w == some (-2) && s1.mightEff w == 0
    | none => false
  | none => false

-- a card that is not in play has no passive change: the object in the hand has its printed Might
#guard match mainA 0 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putA s0 p "T-BAN" .hand with
    | none => false
    | some (s1, _) =>
    match putA s1 p "V0" .base with
    | none => false
    | some (s2, mine) => s2.mightNow mine == some 2
  | none => false

-- the card has the passive ability that says it enters ready, and the others do not
#guard scout.entersReady && !banner.entersReady && !(vanilla 0).entersReady

end RiftboundTest
