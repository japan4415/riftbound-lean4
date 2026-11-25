module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: Deflect (CR 809)

An opponent who chooses a Unit with Deflect X, with a Spell, an activated ability or a triggered
ability, pays X Power of any domain more. The pick is legal only when the Pool covers it, and the
Power leaves the Pool with the answer.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

/-- A Unit with Deflect 2. -/
meta def guarded : CardDef :=
  { id := cid "T-DEF", name := "Guarded", types := [.unit], domains := [.fury], might := some 1,
    keywords := [{ keyword := .deflect, arg := .amount 2 }] }

/-- A Spell: 1 damage to an enemy Unit at a Base. -/
meta def zapFoe : CardDef :=
  { id := cid "T-ZAP", name := "Zap", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
      (.prim (.deal (.slot 0) (.const 1)))) }

/-- A Spell: 1 damage to a friendly Unit at a Base. -/
meta def zapOwn : CardDef :=
  { id := cid "T-ZPO", name := "Zap Own", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of [Choice.targetOf .one .friendly .atBase [.ofType .unit]]
      (.prim (.deal (.slot 0) (.const 1)))) }

/-- A Unit that deals 1 damage to an enemy Unit when it is played. -/
meta def archer : CardDef :=
  { id := cid "T-ARC", name := "Archer", types := [.unit], domains := [.fury],
    cost := some ⟨1, []⟩, might := some 1,
    abilities := [.triggered (Trigger.onSelf .play)
      (EffectDef.of [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 1)))) .unlimited] }

/-- A Unit that exhausts to deal 1 damage to an enemy Unit. -/
meta def pinger : CardDef :=
  { id := cid "T-PNG", name := "Pinger", types := [.unit], domains := [.fury],
    cost := some ⟨1, []⟩, might := some 1,
    abilities := [.activated [.exhaustSelf] .normal
      (EffectDef.of [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 1)))) .unlimited] }

/-- The game in the Main Phase of the first turn, with the test cards known. -/
meta def mainDf : Option GameState :=
  match GameState.initial db { ruleSet := .coreOnly, mode := Mode.duel } [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s =>
        some { s with cards := { cards := db.cards ++ RiftboundCards.db.cards ++
          [guarded, zapFoe, zapOwn, archer, pinger] } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putDf (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- The player can play the card with these targets, paying the cost only. -/
meta def canPlay (s : GameState) (c : ObjId) (ts : List ObjId) : Bool :=
  (legalFrameActions s).any (fun a =>
    match a.kind with
    | .playCard c' _ ts' _ _ _ => c' == c && ts' == ts
    | _ => false)

/-- The player can use the ability at place 0 of the object with these targets. -/
meta def canUse (s : GameState) (src : ObjId) (ts : List ObjId) : Bool :=
  (legalFrameActions s).any (fun a =>
    match a.kind with
    | .activate src' 0 _ ts' _ _ _ => src' == src && ts' == ts
    | _ => false)

-- the Deflect of the Unit is paid by the opponents of its controller, for each time it is chosen
#guard match mainDf with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let o : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match putDf s0 o "T-DEF" .base with
    | some (s1, foe) =>
      match putDf s1 p "T-DEF" .base with
      | some (s2, mine) =>
        s2.deflectCost p [foe] == 2 && s2.deflectCost p [mine] == 0 &&
        s2.deflectCost p [foe, foe] == 4 && s2.deflectCost p [] == 0 &&
        s2.deflectCost o [mine] == 2
      | none => false
    | none => false
  | none => false

-- a Spell that chooses a Unit with Deflect 2 is legal only when the Pool has 2 Power more (CR 809)
#guard match mainDf with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let o : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match putDf s0 o "T-DEF" .base with
    | some (s1, foe) =>
      match putDf s1 p "T-ZAP" .hand with
      | some (s2, z) =>
        let s3 := s2.setPool p { energy := 1 }
        let s4 := s2.setPool p { energy := 1, fury := 1 }
        let s5 := s2.setPool p { energy := 1, fury := 2 }
        !(canPlay s3 z [foe]) && !(canPlay s4 z [foe]) && canPlay s5 z [foe] &&
        (match step 100 s5 ⟨.player p, .playCard z ⟨1, []⟩ [foe]⟩ with
          | .ok (s6, _) => (s6.poolOf p).total == 0 && (s6.zone .chain).length == 1
          | .error _ => false)
      | none => false
    | none => false
  | none => false

-- a Unit of the player's own costs nothing more to choose, and a Power of any domain pays
#guard match mainDf with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putDf s0 p "T-DEF" .base with
    | some (s1, mine) =>
      match putDf s1 p "T-ZPO" .hand with
      | some (s2, z) =>
        let s3 := s2.setPool p { energy := 1 }
        canPlay s3 z [mine] &&
        (match step 100 s3 ⟨.player p, .playCard z ⟨1, []⟩ [mine]⟩ with
          | .ok (s4, _) => (s4.poolOf p).total == 0
          | .error _ => false)
      | none => false
    | none => false
  | none => false

-- the Power of a domain is paid first and the Power of any domain last
#guard
  let pool : RunePool := { calm := 1, any := 2, energy := 3 }
  let after := pool.takeN 2
  after.calm == 0 && after.any == 1 && after.energy == 3 && after.total + 2 == pool.total

-- an activated ability that chooses the Unit pays for it too (CR 809)
#guard match mainDf with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let o : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match putDf s0 o "T-DEF" .base with
    | some (s1, foe) =>
      match putDf s1 p "T-PNG" .base with
      | some (s2, src) =>
        let s3 := s2.setPool p { fury := 1 }
        let s4 := s2.setPool p { fury := 2 }
        !(canUse s3 src [foe]) && canUse s4 src [foe] &&
        (match step 100 s4 ⟨.player p, .activate src 0 ⟨0, []⟩ [foe]⟩ with
          | .ok (s5, _) => (s5.poolOf p).total == 0
          | .error _ => false)
      | none => false
    | none => false
  | none => false

-- A trigger can choose the guarded Unit when Power is already in the Pool or can be
-- added from a Rune. An unfunded trigger has no valid target (CR 355, 357.1.a, 809).
#guard match mainDf with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let o : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match putDf s0 o "T-DEF" .base with
    | some (s1, foe) =>
      match putDf s1 p "T-ARC" .hand with
      | some (s2, arc) =>
        let rich := s2.setPool p { energy := 1, fury := 2 }
        let poor := s2.setPool p { energy := 1, fury := 1 }
        let kinds (s : GameState) : List ActionKind :=
          match step 100 s ⟨.player p, .playCard arc ⟨1, []⟩ []⟩ with
          | .ok (s3, _) => (legalFrameActions s3).map (·.kind)
          | .error _ => []
        let disableRunes (s : GameState) := (s.runesOf p).foldl (fun t rune =>
          t.modObj rune (fun r => { r with runeDomain := none })) s
        kinds (disableRunes rich) == [.putTrigger 0 [foe]] &&
        kinds (disableRunes poor) == [.putTrigger 0 []] &&
        (kinds poor).contains (.prepareTrigger 0 [foe] (.pay [])) &&
        (match step 100 rich ⟨.player p, .playCard arc ⟨1, []⟩ []⟩ with
          | .ok (s3, _) =>
            (match step 100 s3 ⟨.player p, .putTrigger 0 [foe]⟩ with
              | .ok (s4, _) => (s4.poolOf p).total == 0
              | .error _ => false)
          | .error _ => false)
      | none => false
    | none => false
  | none => false

end RiftboundTest
