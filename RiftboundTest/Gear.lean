module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: Equipment (CR 137, 825)

An Equipment is a Gear that is attached to a Unit by its Equip ability (an activated ability that
comes from the keyword). While it is attached the Unit has its Might bonus and the abilities it
gives. When the Unit is gone the Equipment is not attached any more.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def gearCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The other player. -/
meta def otherG (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- An Equipment: Equip for 1 Energy, +2 Might, gives Tank and Shield 2, and "When I attack, draw
1". -/
meta def blade : CardDef :=
  { id := cid "T-BLD", name := "Blade", types := [.gear], domains := [.fury],
    keywords := [{ keyword := .equip, arg := .cost ⟨1, []⟩ }], mightBonus := some 2,
    grants := [.passive .always [.keyword .self { keyword := .tank }],
      .passive .always [.keyword .self { keyword := .shield, arg := .amount 2 }],
      .triggered (Trigger.onSelf .attack)
        (EffectDef.of [] (.prim (.draw .you (.const 1)))) .unlimited] }

/-- The game in the Main Phase of the first turn, with the test card in its database. -/
meta def mainG : Option GameState :=
  match GameState.initial db gearCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s => some { s with cards := { cards := db.cards ++ [blade] } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putG (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- Take an answer, if it is legal. -/
meta def stepG (s : GameState) (a : Action) : Option GameState :=
  match step 100 s a with | .ok (s', _) => some s' | .error _ => none

/-- The turn player with the Blade and a Unit on their Base, and the other player's Unit, and the
Energy to Equip: the state, the player, the Blade, the Unit, the other Unit. -/
meta def gearScene : Option (GameState × PlayerId × ObjId × ObjId × ObjId) :=
  match mainG with
  | none => none
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putG s0 p "T-BLD" .base with
    | none => none
    | some (s1, g) =>
      match putG s1 p "V0" .base with
      | none => none
      | some (s2, u) =>
        match putG s2 (otherG p) "V1" .base with
        | none => none
        | some (s3, e) => some (s3.setPool p { energy := 2 }, p, g, u, e)

/-- The Equip is used on the Unit and the Chain resolves. -/
meta def equipped : Option GameState :=
  match gearScene with
  | some (s, p, g, u, _) =>
    (stepG s ⟨.player p, .activate g 0 ⟨1, []⟩ [u]⟩).bind fun s1 =>
    (stepG s1 ⟨.player p, .pass⟩).bind fun s2 => stepG s2 ⟨.player (otherG p), .pass⟩
  | none => none

-- the keyword Equip is an activated ability of the Equipment: it can be used on a friendly Unit,
-- not on the other player's Unit (CR 825)
#guard match gearScene with
  | some (s, p, g, u, e) =>
    blade.keywordAbilities.length == 1 &&
    (legalActions s).contains ⟨.player p, .activate g 0 ⟨1, []⟩ [u]⟩ &&
    !(legalActions s).contains ⟨.player p, .activate g 0 ⟨1, []⟩ [e]⟩
  | none => false

-- the Unit has the Equipment attached, its Might bonus, and what it gives: Tank, Shield 2; the
-- Equipment itself has none of that (CR 137)
#guard match gearScene, equipped with
  | some (s, _, g, u, _), some s1 =>
    (s1.obj? g).any (·.attached == some u) &&
    s.mightNow u == some 2 && s1.mightNow u == some 4 && s1.mightNow g == none &&
    s1.hasKw u .tank && !s.hasKw u .tank && s1.kwAmount u .shield == 2 && !s1.hasKw g .tank
  | _, _ => false

-- the Unit's ability from the Equipment: it fires when the Unit attacks; the Equipment's own does
-- not
#guard match gearScene, equipped with
  | some (_, p, g, u, _), some s1 =>
    (triggersOf s1 u p .attack).length == 1 &&
    (triggersOf s1 u p .attack).all
      (fun t => t.source == u && t.card == cid "T-BLD" && t.idx == 3) &&
    (triggersOf s1 g p .attack).isEmpty
  | _, _ => false

-- the Unit goes away: the Cleanup detaches the Equipment, which stays on the Base (CR 137)
#guard match gearScene, equipped with
  | some (_, p, g, u, _), some s1 =>
    match moveObj s1 u (.player p .trash) with
    | some (s2, _) =>
      (cleanupStep s2).isSome &&
      (match advance 20 { s2 with pending := .cleanup :: s2.pending } [] with
        | .ok (s3, _) => (s3.obj? g).any (·.attached == none) &&
            (s3.zone (.player p .base)).contains g
        | .error _ => false)
    | none => false
  | _, _ => false

-- attached to another Unit, the Equipment is not attached to the first one any more
#guard match gearScene, equipped with
  | some (_, p, g, u, _), some s1 =>
    match putG s1 p "V2" .base with
    | some (s2, w) =>
      let s3 := s2.setPool p { energy := 1 }
      match (stepG s3 ⟨.player p, .activate g 0 ⟨1, []⟩ [w]⟩).bind
          (fun s4 => stepG s4 ⟨.player p, .pass⟩) with
      | some s5 =>
        match stepG s5 ⟨.player (otherG p), .pass⟩ with
        | some s6 => (s6.obj? g).any (·.attached == some w) && s6.mightNow u == some 2 &&
            s6.mightNow w == some 4
        | none => false
      | none => false
    | none => false
  | _, _ => false

end RiftboundTest
