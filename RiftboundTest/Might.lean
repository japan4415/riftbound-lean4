module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: lasting changes of Might (CR 475-478)

An effect that gives Might "this turn" changes the Might of the object until the end of the turn:
the Might that every rule reads (lethal damage, Combat, the filters of effects) is the printed Might
and the changes together.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def mightCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The other player. -/
meta def otherM (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- A Spell: give a friendly Unit +3 Might this turn. -/
meta def surge : CardDef :=
  { id := cid "T-SRG", name := "Surge", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of [Choice.targetOf .one .friendly .atBase [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)) }

/-- A Spell: give an enemy Unit -10 Might this turn. -/
meta def smite : CardDef :=
  { id := cid "T-SMT", name := "Smite", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
      (.grant (.slot 0) (.mightMinus .it (.const 10)) .thisTurn)) }

/-- A Spell: give a friendly Unit +1 Might for the rest of the game. -/
meta def boon : CardDef :=
  { id := cid "T-BON", name := "Boon", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of [Choice.targetOf .one .friendly .atBase [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it (.const 1)) .permanent)) }

/-- A Spell that is not understood: a lasting change that ends with the Showdown. -/
meta def combatBoost : CardDef :=
  { id := cid "T-CMB", name := "Combat Boost", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩,
    spellEffect := some (EffectDef.of [Choice.targetOf .one .friendly .atBase [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it (.const 1)) .thisShowdown)) }

/-- The fixtures and the test cards. -/
meta def mightDB : CardDB := { cards := db.cards ++ [surge, smite, boon, combatBoost] }

/-- The game in the Main Phase of the first turn, with the test cards in its database. -/
meta def mainM (seed : Nat) : Option GameState :=
  match GameState.initial db mightCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed seed) s with
      | .ok s => some { s with cards := mightDB }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putM (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- Take an answer, if it is legal. -/
meta def stepM (s : GameState) (a : Action) : Option GameState :=
  match step 100 s a with | .ok (s', _) => some s' | .error _ => none

/-- Both players pass: the Chain resolves. -/
meta def resolveM (s : GameState) (p : PlayerId) : Option GameState :=
  (stepM s ⟨.player p, .pass⟩).bind (fun s1 => stepM s1 ⟨.player (otherM p), .pass⟩)

/-- Cast the Spell on the target, and let the Chain resolve. -/
meta def castM (s : GameState) (p : PlayerId) (c t : ObjId) : Option GameState :=
  (stepM s ⟨.player p, .playCard c ⟨1, []⟩ [t]⟩).bind (fun s1 => resolveM s1 p)

/-- The turn player with a Vanilla Unit (Might 2) on their Base, the other player with one on
theirs, and a Spell in hand with the Energy to cast it. -/
meta def mightScene (spell : String) :
    Option (GameState × PlayerId × ObjId × ObjId × ObjId) :=
  match mainM 1 with
  | none => none
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putM s0 p "V0" .base with
    | none => none
    | some (s1, mine) =>
      match putM s1 (otherM p) "V1" .base with
      | none => none
      | some (s2, theirs) =>
        match putM s2 p spell .hand with
        | none => none
        | some (s3, c) => some (s3.setPool p { energy := 1 }, p, mine, theirs, c)

-- the Spell is cast on a friendly Unit and resolved: its Might is the printed Might and 3 more;
-- the other Unit is as it was (CR 475-478)
#guard match mightScene "T-SRG" with
  | some (s, p, mine, theirs, c) =>
    s.mightOf mine == some 2 &&
    (match stepM s ⟨.player p, .playCard c ⟨1, []⟩ [mine]⟩ with
      | some s1 =>
        (match resolveM s1 p with
          | some s2 => s2.mightOf mine == some 5 && s2.mightOf theirs == some 2 &&
              (s2.obj? mine).any (·.mightMods.length == 1)
          | none => false)
      | none => false)
  | none => false

-- the change ends with the turn: at the end of the turn the Might is the printed one again, and the
-- damage is healed as before (CR 317.2, 478)
#guard match mightScene "T-SRG" with
  | some (s, p, mine, _, c) =>
    match castM s p c mine with
    | some s2 =>
      (match stepM s2 ⟨.player p, .pass⟩ with
        | some s3 => s3.mightOf mine == some 2 && (s3.obj? mine).any (·.mightMods.isEmpty)
        | none => false)
    | none => false
  | none => false

-- a lasting change that never ends stays through the end of the turn
#guard match mightScene "T-BON" with
  | some (s, p, mine, _, c) =>
    match castM s p c mine with
    | some s2 =>
      s2.mightOf mine == some 3 &&
      (match stepM s2 ⟨.player p, .pass⟩ with
        | some s3 => s3.mightOf mine == some 3
        | none => false)
    | none => false
  | none => false

-- a change that lowers Might: the Unit with 2 Might and -10 has less than 0, counted as 0 where
-- Might is a number of points (`Might.eff`), and dies when it is dealt any damage (CR 323.4)
#guard match mightScene "T-SMT" with
  | some (s, p, _, theirs, c) =>
    match castM s p c theirs with
    | some s2 =>
      s2.mightOf theirs == some (-8) &&
      (s2.obj? theirs).any (fun o => Might.eff (-8) ≤ o.damage + 1) &&
      s2.mightEff theirs == 0
    | none => false
  | none => false

-- the change is read by the filters of effects: a Unit with Might at least 5 is now there
#guard match mightScene "T-SRG" with
  | some (s, p, mine, _, c) =>
    match castM s p c mine with
    | some s2 => (Filter.might .ge (.const 5)).holds s2 mine {} mine == some true &&
        (Filter.might .ge (.const 6)).holds s2 mine {} mine == some false &&
        (Filter.might .ge (.const 5)).holds s mine {} mine == some false
    | none => false
  | none => false

-- leaving the Board clears the changes: the object that goes to the Trash has none
#guard match mightScene "T-BON" with
  | some (s, p, mine, _, c) =>
    match castM s p c mine with
    | some s2 =>
      match moveObj s2 mine (.player p .trash) with
      | some (s3, m') => (s3.obj? m').any (·.mightMods.isEmpty)
      | none => false
    | none => false
  | none => false

-- the interpreter knows the changes that end with the turn, the combat or never, not the others
#guard surge.spellRuns && smite.spellRuns && boon.spellRuns && !combatBoost.spellRuns

end RiftboundTest
