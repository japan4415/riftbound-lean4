module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: triggered abilities (CR 382-385)

A step leaves events; the abilities they set off wait on the stack until a player would next
receive priority, then go on the Chain as objects of their own, the turn player's first, and
resolve like any item of the Chain.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def trigCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The other player. -/
meta def otherT (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- Draw a card. -/
meta def drawOne : EffectDef := EffectDef.of [] (.prim (.draw .you (.const 1)))

/-- A Unit that draws a card when it is played. -/
meta def herald : CardDef :=
  { id := cid "T-HER", name := "Herald", types := [.unit], domains := [.fury], might := some 2,
    cost := some ⟨1, []⟩,
    abilities := [.triggered (Trigger.onSelf .play) drawOne .unlimited] }

/-- A Unit that draws a card when it dies. -/
meta def martyr : CardDef :=
  { id := cid "T-MAR", name := "Martyr", types := [.unit], domains := [.fury], might := some 2,
    abilities := [.triggered (Trigger.onSelf .die) drawOne .unlimited] }

/-- A Unit that draws a card when it conquers. -/
meta def victor : CardDef :=
  { id := cid "T-VIC", name := "Victor", types := [.unit], domains := [.fury], might := some 2,
    abilities := [.triggered (Trigger.onSelf .conquer) drawOne .unlimited] }

/-- A Unit that draws when it attacks, and when it defends. -/
meta def fighter : CardDef :=
  { id := cid "T-FIG", name := "Fighter", types := [.unit], domains := [.fury], might := some 2,
    abilities := [.triggered (Trigger.onSelf .attack) drawOne .unlimited,
      .triggered (Trigger.onSelf .defend) drawOne .unlimited] }

/-- A Legend that draws when its player holds a Battlefield. -/
meta def keeper : CardDef :=
  { id := cid "T-KEE", name := "Keeper", types := [.legend], domains := [.fury],
    abilities := [.triggered (Trigger.onSelf .youHold) drawOne .unlimited] }

/-- A Unit whose trigger can fire once each turn. -/
meta def onceUnit : CardDef :=
  { id := cid "T-ONC", name := "Once", types := [.unit], domains := [.fury], might := some 2,
    abilities := [.triggered (Trigger.onSelf .play) drawOne (.perTurn 1)] }

/-- A Unit whose trigger needs a target. -/
meta def aimed : CardDef :=
  { id := cid "T-AIM", name := "Aimed", types := [.unit], domains := [.fury], might := some 2,
    cost := some ⟨1, []⟩,
    abilities := [.triggered (Trigger.onSelf .play)
      (EffectDef.of [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 1)))) .unlimited] }

/-- The fixtures and the test cards. -/
meta def trigDB : CardDB :=
  { cards := db.cards ++ [herald, martyr, victor, fighter, keeper, onceUnit, aimed] }

/-- The game in the Main Phase of the first turn, with the test cards in its database. -/
meta def mainT (seed : Nat) : Option GameState :=
  match GameState.initial db trigCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed seed) s with
      | .ok s => some { s with cards := trigDB }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putT (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- Take an answer, if it is legal. -/
meta def stepT (s : GameState) (a : Action) : Option GameState :=
  match step 100 s a with | .ok (s', _) => some s' | .error _ => none

/-- The turn player with a Herald in hand and the Energy to play it. -/
meta def heraldScene : Option (GameState × PlayerId × ObjId) :=
  match mainT 1 with
  | none => none
  | some s =>
    let p := s.active.getD ⟨0⟩
    match putT s p "T-HER" .hand with
    | some (s1, c) => some (s1.setPool p { energy := 1 }, p, c)
    | none => none

#guard heraldScene.isSome

/-- The Herald is played, and what it caused. -/
meta def afterHerald : Option (GameState × List Event) :=
  match heraldScene with
  | some (s, p, c) =>
    match step 100 s ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
    | .ok r => some r
    | .error _ => none
  | none => none

-- playing the Unit says so; its ability is on the Chain as an object of its own, controlled by the
-- player; the player has priority with it, above the Main Phase priority (CR 382, 383)
#guard match heraldScene, afterHerald with
  | some (_, p, _), some (s1, es) =>
    es.any (fun e => match e with | .played q _ => q == p | _ => false) &&
    (s1.zone .chain).length == 1 &&
    (match (s1.zone .chain).head?.bind s1.obj? with
      | some o => (match o.kind with | .chainAbility c 0 _ => c == cid "T-HER" | _ => false) &&
          o.controller == p
      | none => false) &&
    (match s1.pending with
      | .chainPass r 0 :: .priority r2 :: _ => r == p && r2 == p
      | _ => false)
  | _, _ => false

-- both players pass: the ability resolves, the player draws a card, the Chain is empty and the
-- player has priority again
#guard match heraldScene, afterHerald with
  | some (s, p, _), some (s1, _) =>
    match (stepT s1 ⟨.player p, .pass⟩).bind
        (fun s2 => stepT s2 ⟨.player (otherT p), .pass⟩) with
    | some s3 =>
      (s3.zone .chain).isEmpty &&
      (s3.zone (.player p .hand)).length == (s.zone (.player p .hand)).length &&
      (s3.zone (.player p .mainDeck)).length + 1 == (s.zone (.player p .mainDeck)).length &&
      (match s3.pending with | .priority r :: _ => r == p | _ => false)
    | none => false
  | _, _ => false

-- nothing fires when nothing happened, nor during the setup
#guard match heraldScene with
  | some (s, _, _) => s.withTriggers [] == s && ({ s with phase := .setup }).withTriggers
      [.played ⟨0⟩ ⟨1⟩] == { s with phase := .setup }
  | none => false

-- a Unit that dies: the Cleanup kills it after a Spell dealt damage, and its ability goes on the
-- Chain for the player who controlled it (CR 323.4, 389)
#guard match mainT 1 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let q := otherT p
    match putT s0 p "SP1" .hand with
    | some (s1, spell) =>
      match putT s1 q "T-MAR" .base with
      | some (s2, m) =>
        let s3 := s2.setPool p { energy := 1 }
        match stepT s3 ⟨.player p, .playCard spell ⟨1, []⟩ [m]⟩ with
        | some s4 =>
          match (stepT s4 ⟨.player p, .pass⟩).bind
              (fun s5 => stepT s5 ⟨.player q, .pass⟩) with
          | some s6 =>
            -- the Unit is dead; its ability is on the Chain; the turn player has priority
            -- the Unit is a token in the test: off the Board, it ceases to exist (CR 183)
            (s6.zone (.player q .trash)).length == (s3.zone (.player q .trash)).length &&
            (s6.zone .chain).length == 1 &&
            (match (s6.zone .chain).head?.bind s6.obj? with
              | some o => o.controller == q &&
                  (match o.kind with | .chainAbility c _ _ => c == cid "T-MAR" | _ => false)
              | none => false) &&
            (match s6.pending with | .chainPass r 0 :: _ => r == p | _ => false) &&
            (match (stepT s6 ⟨.player p, .pass⟩).bind
                (fun s7 => stepT s7 ⟨.player q, .pass⟩) with
              | some s8 => (s8.zone .chain).isEmpty &&
                  (s8.zone (.player q .hand)).length == (s6.zone (.player q .hand)).length + 1
              | none => false)
          | none => false
        | none => false
      | none => false
    | none => false
  | none => false

-- a Unit that conquers: the Standard Move to a Battlefield, the Showdown, and the Conquer put its
-- ability on the Chain (CR 348, 471)
#guard match mainT 1 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let q := otherT p
    match putT s0 p "T-VIC" .base, s0.battlefields with
    | some (s1, u), b :: _ =>
      match stepT s1 ⟨.player p, .standardMove u (.battlefield b)⟩ with
      | some s2 =>
        match (stepT s2 ⟨.player p, .pass⟩).bind
            (fun s3 => stepT s3 ⟨.player q, .pass⟩) with
        | some s4 =>
          s4.pointsOf p == 1 && (s4.zone .chain).length == 1 &&
          (match (s4.zone .chain).head?.bind s4.obj? with
            | some o => o.controller == p &&
                (match o.kind with
                  | .chainAbility c _ src => c == cid "T-VIC" && src == u
                  | _ => false)
            | none => false)
        | none => false
      | none => false
    | _, _ => false
  | none => false

-- the abilities that fire: a Legend that watches its player, the Units of the Battlefield, and in a
-- Combat the Attacker's Units attack and the others' defend (CR 389, 466)
#guard match mainT 1 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let q := otherT p
    match putT s0 p "T-KEE" .legendZone, putT s0 p "T-FIG" .base, putT s0 q "T-FIG" .base,
        s0.battlefields with
    | some (s1, l), some (_, _), some (_, _), b :: _ =>
      match putT s1 p "T-FIG" .base with
      | some (s2, a) =>
        match putT s2 q "T-FIG" .base with
        | some (s3, d) =>
          match moveObj s3 a .battlefieldZone, moveObj s3 d .battlefieldZone with
          | some (s4, a'), some (_, _) =>
            match moveObj s4 d .battlefieldZone with
            | some (s5, d') =>
              let s6 := (s5.modObj a' (fun o => { o with loc := some b })).modObj d'
                (fun o => { o with loc := some b })
              let fires := s6.detect [.combatStarted b p]
              fires.length == 2 &&
              fires.any (fun t => t.source == a' && t.idx == 0 && t.controller == p) &&
              fires.any (fun t => t.source == d' && t.idx == 1 && t.controller == q) &&
              -- the player's Legend fires when the player holds a Battlefield, not when conquering
              (s6.detect [.scored p b false]).any (fun t => t.source == l) &&
              !(s6.detect [.scored p b true]).any (fun t => t.source == l)
            | none => false
          | _, _ => false
        | none => false
      | none => false
    | _, _, _, _ => false
  | none => false

-- the turn player's abilities go first (CR 383.3)
#guard match mainT 1 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let q := otherT p
    match putT s0 q "T-MAR" .trash, putT s0 p "T-MAR" .trash with
    | some (s1, mq), some (_, _) =>
      match putT s1 p "T-MAR" .trash with
      | some (s3, mp') =>
        (s3.detect [.died mq q, .died mp' p]).map (·.controller) == [p, q]
      | none => false
    | _, _ => false
  | none => false

-- an ability that fires once each turn does not fire again; an ability that needs a target fires
-- (CR 371, 386, 355)
#guard match mainT 1 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putT s0 p "T-ONC" .base, putT s0 p "T-AIM" .base with
    | some (s1, o), some (s2, a) =>
      (triggersOf s1 o p .play).length == 1 &&
      (triggersOf (s1.modObj o (fun x => { x with used := [0] })) o p .play).isEmpty &&
      (triggersOf s2 a p .play).length == 1 && (triggersOf s1 o p .die).isEmpty
    | _, _ => false
  | none => false

/-- The turn player with an Aimed in hand and the Energy to play it, and an enemy Unit on the other
player's Base if `target`. -/
meta def aimedScene (target : Bool) :
    Option (GameState × PlayerId × PlayerId × ObjId × ObjId) :=
  match mainT 1 with
  | none => none
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    let q := otherT p
    match putT s0 p "T-AIM" .hand with
    | none => none
    | some (s1, c) =>
      let s2 := s1.setPool p { energy := 1 }
      if target then
        match putT s2 q "V0" .base with
        | some (s3, e) => some (s3, p, q, c, e)
        | none => none
      else some (s2, p, q, c, c)

-- an ability with a target asks its player for the target: the only answers are the legal picks;
-- the ability goes on the Chain with it, and resolves against it (CR 383.3.d, 355)
#guard match aimedScene true with
  | some (s, p, q, c, e) =>
    match stepT s ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
    | some s1 =>
      (match s1.pending with | .triggerOrder r _ [] [] :: _ => r == p | _ => false) &&
      (legalFrameActions s1) == [⟨.player p, .putTrigger 0 [e]⟩] &&
      (match stepT s1 ⟨.player p, .putTrigger 0 [e]⟩ with
        | some s2 =>
          (s2.zone .chain).length == 1 &&
          (match (s2.zone .chain).head?.bind s2.obj? with
            | some o => o.targets == [e] | none => false) &&
          (match (stepT s2 ⟨.player p, .pass⟩).bind
              (fun s3 => stepT s3 ⟨.player q, .pass⟩) with
            | some s4 => (s4.obj? e).any (·.damage == 1) && (s4.zone .chain).isEmpty
            | none => false)
        | none => false)
    | none => false
  | none => false

-- an ability with no legal target is removed: the only answer picks nothing, and the Chain stays
-- empty (CR 355)
#guard match aimedScene false with
  | some (s, p, _, c, _) =>
    match stepT s ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
    | some s1 =>
      (legalFrameActions s1) == [⟨.player p, .putTrigger 0 []⟩] &&
      (match stepT s1 ⟨.player p, .putTrigger 0 []⟩ with
        | some s2 => (s2.zone .chain).isEmpty &&
            (match s2.pending with | .priority r :: _ => r == p | _ => false)
        | none => false)
    | none => false
  | none => false

-- several abilities of one player: the player chooses which goes on the Chain first; the one put
-- last is on top and resolves first (CR 383.3.d, 340)
#guard match mainT 1 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putT s0 p "T-HER" .base, putT s0 p "T-MAR" .base with
    | some (_, a), some (s2, b) =>
      let ta : PendTrigger := { source := a, card := cid "T-HER", idx := 0, controller := p }
      let tb : PendTrigger := { source := b, card := cid "T-MAR", idx := 0, controller := p }
      match advance 10 { s2 with pending := .triggers [ta, tb] :: s2.pending } [] with
      | .ok (s3, _) =>
        (match s3.pending with | .triggerOrder _ _ [_] [] :: _ => true | _ => false) &&
        (legalFrameActions s3).filter (fun x => x.kind != .concede) ==
          [⟨.player p, .putTrigger 0 []⟩, ⟨.player p, .putTrigger 1 []⟩] &&
        (match stepT s3 ⟨.player p, .putTrigger 1 []⟩ with
          | some s4 =>
            (s4.zone .chain).length == 2 &&
            (match (s4.zone .chain).head?.bind s4.obj? with
              | some o => (match o.kind with | .chainAbility c _ _ => c == cid "T-HER" | _ => false)
              | none => false) &&
            (match s4.pending with | .chainPass r 0 :: _ => r == p | _ => false)
          | none => false)
      | .error _ => false
    | _, _ => false
  | none => false

-- every answer listed is accepted by the engine with a trigger on the Chain
#guard match afterHerald with
  | some (s1, _) => (legalActions s1).all (fun a => (stepT s1 a).isSome)
  | none => false

end RiftboundTest
