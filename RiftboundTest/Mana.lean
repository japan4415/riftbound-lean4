module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: Add abilities (CR 430, 164.2)

An ability that only exhausts the object and adds Energy or Power resolves at once: no Chain, and
the player can use it whenever they have priority, with the Chain empty or not.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def manaCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The other player. -/
meta def otherN (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- A Gear: "[Exhaust]: [Add] 1 Energy". -/
meta def energyGear : CardDef :=
  { id := cid "T-ENG", name := "Energy Gear", types := [.gear], domains := [.fury],
    abilities := [.activated [.exhaustSelf] .reaction
      (EffectDef.of [] (.prim (.addEnergy .you (.const 1) none))) .unlimited] }

/-- A Gear: "[Exhaust]: [Add] 1 Power of any domain". -/
meta def rainbowGear : CardDef :=
  { id := cid "T-RBW", name := "Rainbow Gear", types := [.gear], domains := [.fury],
    abilities := [.activated [.exhaustSelf] .reaction
      (EffectDef.of [] (.prim (.addPower .you (.const 1) none none))) .unlimited] }

/-- A Gear: "[Exhaust]: [Add] 1 Fury Power". -/
meta def furyGear : CardDef :=
  { id := cid "T-FUR", name := "Fury Gear", types := [.gear], domains := [.fury],
    abilities := [.activated [.exhaustSelf] .reaction
      (EffectDef.of [] (.prim (.addPower .you (.const 1) (some .fury) none))) .unlimited] }

/-- The game in the Main Phase of the first turn, with the test cards in its database. -/
meta def mainN : Option GameState :=
  match GameState.initial db manaCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s =>
        some { s with cards := { cards := db.cards ++ [energyGear, rainbowGear, furyGear] } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putN (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

-- an Add is not an activated ability of the Chain: it is listed apart, and `activatable` refuses it
#guard match mainN with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putN s0 p "T-ENG" .base with
    | some (s1, g) =>
      manaReady s1 p g 0 && !manaReady s1 (otherN p) g 0 &&
      !activatable s1 p g 0 ⟨0, []⟩ [] true &&
      (legalActions s1).contains ⟨.player p, .manaAbility g 0⟩ &&
      !(legalActions s1).any (fun a => match a.kind with | .activate .. => true | _ => false)
    | none => false
  | none => false

-- using it exhausts the object and adds the Energy at once; nothing goes on the Chain and the
-- player keeps priority; it cannot be used again while exhausted (CR 430.2)
#guard match mainN with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putN s0 p "T-ENG" .base with
    | some (s1, g) =>
      match step 100 s1 ⟨.player p, .manaAbility g 0⟩ with
      | .ok (s2, _) =>
        (s2.poolOf p).energy == (s1.poolOf p).energy + 1 && (s2.obj? g).any (·.exhausted) &&
        (s2.zone .chain).isEmpty && s2.pending == s1.pending && !manaReady s2 p g 0
      | .error _ => false
    | none => false
  | none => false

-- Power of a domain, and Power of any domain, which pays a Power symbol of any domain (CR 430, 445)
#guard match mainN with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putN s0 p "T-FUR" .base, putN s0 p "T-RBW" .base with
    | some (s1, f), some (s2, _) =>
      match putN s1 p "T-RBW" .base with
      | some (s3, r) =>
        match step 100 s3 ⟨.player p, .manaAbility f 0⟩,
            step 100 s3 ⟨.player p, .manaAbility r 0⟩ with
        | .ok (sf, _), .ok (sr, _) =>
          (sf.poolOf p).fury == (s3.poolOf p).fury + 1 && (sr.poolOf p).any == 1 &&
          ((sr.poolOf p).spend ⟨0, [.calm]⟩).isSome &&
          ((sr.poolOf p).spend ⟨0, [.calm]⟩).any (fun q => q.any == 0) &&
          ((sr.poolOf p).spend ⟨0, [.calm, .fury]⟩).isNone && (let _ := s2; true)
        | _, _ => false
      | none => false
    | _, _ => false
  | none => false

-- an Add can be used while the Chain holds an item (it is a Reaction), and the Chain stays
#guard match mainN with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putN s0 p "T-ENG" .base with
    | none => false
    | some (s1, g) =>
    match putN s1 p "SP0" .hand with
    | none => false
    | some (s2, c) =>
      match step 100 (s2.setPool p { energy := 1 }) ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
      | .ok (s3, _) =>
        (legalFrameActions s3).contains ⟨.player p, .manaAbility g 0⟩ &&
        (match step 100 s3 ⟨.player p, .manaAbility g 0⟩ with
          | .ok (s4, _) => s4.pending == s3.pending && (s4.zone .chain).length == 1 &&
              (s4.poolOf p).energy == (s3.poolOf p).energy + 1
          | .error _ => false)
      | .error _ => false
  | none => false

end RiftboundTest
