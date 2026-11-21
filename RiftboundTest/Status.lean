module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: Buff, Stun and XP (CR 701, 424, 728, 823-824)

A buff gives a Unit +1 Might (once). A stunned Unit deals no combat damage this turn. XP is the
number a player has; Hunt gains it when the Unit conquers or holds, and Level turns an ability on
while the player has enough.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def statCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The other player. -/
meta def otherS (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- A Spell with the effect on the friendly Unit chosen. -/
meta def spellOn (id name : String) (e : Effect) : CardDef :=
  { id := cid id, name := name, types := [.spell], domains := [.fury], cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of [Choice.targetOf .one .any .atBase [.ofType .unit]] e) }

/-- A Unit with Hunt 2 and a Level ability: +3 Might while its player has 3 XP. -/
meta def hunter : CardDef :=
  { id := cid "T-HNT", name := "Hunter", types := [.unit], domains := [.fury], might := some 2,
    keywords := [{ keyword := .hunt, arg := .amount 2 }],
    abilities := [.passive (.cmp .ge .xp (.const 3)) [.mightPlus .self (.const 3)]] }

/-- The game in the Main Phase of the first turn, with the test cards in its database. -/
meta def mainS : Option GameState :=
  match GameState.initial db statCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s => some { s with cards := { cards := db.cards ++ [
          spellOn "T-BUF" "Buff" (.prim (.buff (.slot 0))),
          spellOn "T-STN" "Stun" (.prim (.stun (.slot 0))),
          spellOn "T-XPG" "Study" (.prim (.gainXP .you (.const 2))), hunter] } }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putS (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- Take an answer, if it is legal. -/
meta def stepS (s : GameState) (a : Action) : Option GameState :=
  match step 100 s a with | .ok (s', _) => some s' | .error _ => none

/-- Cast the Spell on the target, and let the Chain resolve. -/
meta def castS (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId) : Option GameState :=
  (stepS (s.setPool p { energy := 1 }) ⟨.player p, .playCard c ⟨1, []⟩ ts⟩).bind fun s1 =>
  (stepS s1 ⟨.player p, .pass⟩).bind fun s2 => stepS s2 ⟨.player (otherS p), .pass⟩

/-- The turn player with a Unit (Might 2) and the Legend, and the Spell in hand. -/
meta def statScene (spell : String) : Option (GameState × PlayerId × ObjId × ObjId × ObjId) :=
  match mainS with
  | none => none
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putS s0 p "V0" .base with
    | none => none
    | some (s1, u) =>
      match putS s1 p spell .hand with
      | none => none
      | some (s2, c) =>
        match putS s2 p "L1" .legendZone with
        | none => none
        | some (s3, l) => some (s3, p, u, c, l)

-- a buff: +1 Might, once; the filters see it; it ends when the Unit leaves the Board (CR 701)
#guard match statScene "T-BUF" with
  | some (s, p, u, c, _) =>
    match castS s p c [u] with
    | some s1 =>
      s1.mightNow u == some 3 && (s1.obj? u).any (·.buffed) &&
      (Filter.buffed.holds s1 u {} u == some true) &&
      (Filter.buffed.holds s u {} u == some false) &&
      (match buffObj s1 u with | (s2, _) => s2.mightNow u == some 3) &&
      (match moveObj s1 u (.player p .trash) with
        | some (s2, u') => (s2.obj? u').any (fun o => !o.buffed)
        | none => false)
    | none => false
  | none => false

-- a stunned Unit deals no combat damage, and it is not stunned after the end of the turn (CR 424)
#guard match statScene "T-STN" with
  | some (s, p, u, c, _) =>
    match castS s p c [u] with
    | some s1 =>
      s.combatMight u true == 2 && s1.combatMight u true == 0 && s1.combatMight u false == 0 &&
      (Filter.stunned.holds s1 u {} u == some true) &&
      (match stepS s1 ⟨.player p, .pass⟩ with
        | some s2 => (s2.obj? u).any (fun o => !o.stunned) && s2.combatMight u true == 2
        | none => false)
    | none => false
  | none => false

-- XP goes to the Legend of the player and is read as an amount (CR 728)
#guard match statScene "T-XPG" with
  | some (s, p, u, c, l) =>
    match castS s p c [u] with
    | some s1 => s.xpOf p == 0 && s1.xpOf p == 2 && s1.xpOf (otherS p) == 0 &&
        (s1.obj? l).any (·.xp == 2) && (Amount.xp.evalS s1 p u {} == some 2)
    | none => false
  | none => false

-- Hunt gains XP when the Unit conquers or holds; Level turns on an ability with enough XP
-- (CR 823, 824)
#guard match statScene "T-XPG" with
  | some (s, p, u, _, l) =>
    hunter.keywordAbilities.length == 2 &&
    (match putS s p "T-HNT" .base with
      | some (s1, h) =>
        s1.mightNow h == some 2 &&
        (s1.modObj l (fun o => { o with xp := 3 })).mightNow h == some 5 &&
        (s1.modObj l (fun o => { o with xp := 2 })).mightNow h == some 2 &&
        (triggersOf s1 h p .conquer).length == 1 && (triggersOf s1 h p .hold).length == 1 &&
        (triggersOf s1 h p .die).isEmpty && (let _ := u; true)
      | none => false)
  | none => false

end RiftboundTest
