module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: playing cards from the hand (CR 349-359, 356, 357, 340)

The fixture Units cost 1 Energy. The turn player makes the Energy by exhausting a Rune, then plays.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def pcfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The game in the Main Phase of the first turn. -/
meta def mainPhaseP (seed : Nat) : Option GameState :=
  match GameState.initial db pcfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed seed) s with
      | .ok s => some s
      | .error _ => none

/-- The turn player, with a Rune exhausted for 1 Energy. -/
meta def withEnergy (s : GameState) : Option (GameState × PlayerId) :=
  let first := s.turnOrder.headD ⟨0⟩
  match s.zone (.player first .base) with
  | c :: _ =>
    match step 100 s ⟨.player first, .runeAbility c .exhaust⟩ with
    | .ok (s1, _) => some (s1, first)
    | .error _ => none
  | [] => none

/-- A vanilla Unit in the hand. -/
meta def vanillaInHand (s : GameState) (p : PlayerId) : Option ObjId :=
  (s.zone (.player p .hand)).find? fun c =>
    (s.cardDef? c).any (fun d => d.name.startsWith "Vanilla")

/-- The answer was refused as illegal. -/
meta def isIllegal (r : Except RuleError (GameState × List Event)) : Bool :=
  match r with | .error .illegal => true | _ => false

meta def cnt (p : PlayerId) (k : ZoneKind) (s : GameState) : Nat := (s.zone (.player p k)).length

-- with 1 Energy, a Unit of the hand is played: it goes from the hand to the Base, exhausted,
-- and the Energy is spent (CR 349, 357, 359)
#guard match mainPhaseP 1 >>= withEnergy with
  | some (s, p) =>
    match vanillaInHand s p with
    | some c =>
      match step 100 s ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
      | .ok (s1, es) =>
        cnt p .hand s1 + 1 == cnt p .hand s && cnt p .base s1 == cnt p .base s + 1 &&
        (s1.poolOf p).total == 0 &&
        (match es with
          | [.moved c' id' _, .played _ id''] => c' == c && id'' == id' &&
              (s1.obj? id').any (fun (o : Object) => o.exhausted)
          | _ => false) &&
        -- still the same question: the turn player has priority
        (match s1.pending with | [.priority q] => q == p | _ => false)
      | .error _ => false
    | none => false
  | none => false

-- without the Energy the same play is refused; so is the wrong payment (CR 357, 445)
#guard match mainPhaseP 1 with
  | some s =>
    let p := s.turnOrder.headD ⟨0⟩
    match vanillaInHand s p with
    | some c =>
      isIllegal (step 100 s ⟨.player p, .playCard c ⟨1, []⟩ []⟩)
    | none => false
  | none => false
#guard match mainPhaseP 1 >>= withEnergy with
  | some (s, p) =>
    match vanillaInHand s p with
    | some c =>
      isIllegal (step 100 s ⟨.player p, .playCard c ⟨2, []⟩ []⟩) &&
      isIllegal (step 100 s ⟨.player p, .playCard c ⟨1, [.fury]⟩ []⟩)
    | none => false
  | none => false

-- the other player cannot play, and a card that is not in the hand cannot be played
#guard match mainPhaseP 1 >>= withEnergy with
  | some (s, p) =>
    let q : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match vanillaInHand s p, vanillaInHand s q with
    | some c, some d =>
      isIllegal (step 100 s ⟨.player q, .playCard c ⟨1, []⟩ []⟩) &&
      isIllegal (step 100 s ⟨.player p, .playCard d ⟨1, []⟩ []⟩)
    | _, _ => false
  | none => false

-- the plays are listed: one for each vanilla Unit in the hand, with the Energy to pay for it
#guard match mainPhaseP 1 >>= withEnergy with
  | some (s, p) =>
    let plays := (legalActions s).filter fun a =>
      match a.kind with | .playCard _ _ _ _ _ _ => true | _ => false
    let vanillas := (s.zone (.player p .hand)).filter fun c =>
      (s.cardDef? c).any (fun d => d.name.startsWith "Vanilla")
    plays.length == vanillas.length && !plays.isEmpty &&
      plays.all (fun a => match a.kind with | .playCard _ pay _ _ _ _ => pay == ⟨1, []⟩ | _ => false)
  | none => false
-- and nothing is listed without Energy
#guard match mainPhaseP 1 with
  | some s => ((legalActions s).filter fun a =>
      match a.kind with | .playCard _ _ _ _ _ _ => true | _ => false).isEmpty
  | none => false

-- ---- Spells and the Chain (CR 311-313, 340, 354) ----

/-- A legal deck with three Spells that draw a card, in place of the last Unit. -/
meta def spellDeck : Deck :=
  { goodDeck with
    main := cid "C1" :: (List.range 12).flatMap (fun n => List.replicate 3 (cid s!"V{n}")) ++
      List.replicate 3 (cid "SP0") }

#guard decide (DeckValid db Mode.duel spellDeck)

/-- The Main Phase of the first turn, with decks that hold Spells. -/
meta def mainPhaseS (seed : Nat) : Option GameState :=
  match GameState.initial db pcfg [spellDeck, spellDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed seed) s with
      | .ok s => some s
      | .error _ => none

/-- A Spell that draws a card, in the hand. -/
meta def spellInHand (s : GameState) (p : PlayerId) : Option ObjId :=
  (s.zone (.player p .hand)).find? fun c => (s.cardDef? c).any (·.name == "Quick Study")

/-- A game in the Main Phase whose turn player holds a Spell and has 1 Energy. -/
meta def spellReady : Option (GameState × PlayerId × ObjId) :=
  (List.range 40).findSome? fun seed =>
    match mainPhaseS seed >>= withEnergy with
    | some (s, p) => (spellInHand s p).map fun c => (s, p, c)
    | none => none

#guard spellReady.isSome

-- casting: the Spell goes from the hand to the Chain, the cost is paid, and the players are to
-- pass, the turn player first (CR 311, 354, 357)
#guard match spellReady with
  | some (s, p, c) =>
    match step 100 s ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
    | .ok (s1, es) =>
      cnt p .hand s1 + 1 == cnt p .hand s && s1.zone .chain == [match es with
        | [.moved _ id _, .played _ _] => id | _ => c] &&
      (s1.poolOf p).total == 0 &&
      (match s1.pending with
        | [.chainPass q 0, .priority q'] => q == p && q' == p
        | _ => false)
    | .error _ => false
  | none => false

-- when everyone has passed, the Spell resolves: the player draws, and the Spell goes to the
-- Trash; the turn player has priority again (CR 340, 359.3.d)
#guard match spellReady with
  | some (s, p, c) =>
    let q : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match step 100 s ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
    | .ok (s1, _) =>
      -- the wrong player cannot pass, and the first pass hands the priority on
      isIllegal (step 100 s1 ⟨.player q, .pass⟩) &&
      (match step 100 s1 ⟨.player p, .pass⟩ with
        | .ok (s2, _) =>
          (match s2.pending with
            | [.chainPass r 1, .priority _] => r == q
            | _ => false) &&
          (match step 100 s2 ⟨.player q, .pass⟩ with
            | .ok (s3, es) =>
              cnt p .hand s3 == cnt p .hand s && cnt p .mainDeck s3 + 1 == cnt p .mainDeck s &&
              cnt p .trash s3 == cnt p .trash s + 1 && (s3.zone .chain).isEmpty &&
              (match s3.pending with | [.priority r] => r == p | _ => false) &&
              (match es with
                | [.moved .., .drew who, .moved _ discarded (.player owner .trash),
                    .spellResolved whoResolved resolved] =>
                  who == p && owner == p && whoResolved == p && discarded == resolved
                | _ => false)
            | .error _ => false)
        | .error _ => false)
    | .error _ => false
  | none => false

-- the plays of a Spell are listed; while the Chain holds it, the answers are the pass and the Rune
-- abilities (Reactions): no plays of other cards, no moves (CR 311-313, 430, 813)
#guard match spellReady with
  | some (s, p, c) =>
    (legalActions s).any (fun a => a.kind == .playCard c ⟨1, []⟩ []) &&
    (match step 100 s ⟨.player p, .playCard c ⟨1, []⟩ []⟩ with
      | .ok (s1, _) =>
        let answers := (legalActions s1).filter (fun a => a.kind != .concede)
        answers.contains ⟨.player p, .pass⟩ &&
        answers.all (fun a => a.actor == .player p &&
          (a.kind == .pass || (match a.kind with | .runeAbility .. => true | _ => false)))
      | .error _ => false)
  | none => false

-- Spells with targets (CR 355, 340): a Spell that deals damage to an enemy Unit is cast with the
-- Unit chosen among those on the enemy's Base; when the Chain resolves, the damage is dealt, and a
-- Unit whose damage reaches its Might goes to the Trash.

/-- A deck with Spells that draw and Spells that deal damage. -/
meta def sparkDeck : Deck :=
  { goodDeck with
    main := cid "C1" :: (List.range 11).flatMap (fun n => List.replicate 3 (cid s!"V{n}")) ++
      List.replicate 3 (cid "SP0") ++ List.replicate 3 (cid "SP1") }

#guard decide (DeckValid db Mode.duel sparkDeck)

/-- The game in the Main Phase of the first turn, with the damage Spells in the decks. -/
meta def mainPhaseK (seed : Nat) : Option GameState :=
  match GameState.initial db pcfg [sparkDeck, sparkDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed seed) s with
      | .ok s => some s
      | .error _ => none

/-- A card of the hand with the name. -/
meta def inHandNamed (s : GameState) (p : PlayerId) (n : String) : Option ObjId :=
  (s.zone (.player p .hand)).find? fun c => (s.cardDef? c).any (·.name == n)

/-- A game in the Main Phase: the turn player holds Spark and has 1 Energy, and an enemy Unit
(a Vanilla, Might 2) is on the enemy's Base. The state, the turn player, the Spark, and the
Unit. -/
meta def sparkReady : Option (GameState × PlayerId × ObjId × ObjId) :=
  (List.range 60).findSome? fun seed =>
    match mainPhaseK seed >>= withEnergy with
    | some (s, p) =>
      let q : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
      match inHandNamed s p "Spark", vanillaInHand s q with
      | some c, some v =>
        match moveObj s v (.player q .base) with
        | some (s1, v') => some (s1, p, c, v')
        | none => none
      | _, _ => none
    | none => none

#guard sparkReady.isSome

/-- The other player. -/
meta def other (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

-- the selector that names all enemy Units on a Base finds the enemy Unit, and no friendly one
#guard match sparkReady with
  | some (s, p, c, v) =>
    (Selector.all .enemy .atBase [.ofType .unit]).eval s p c {} == some [v] &&
    (Selector.all .friendly .atBase [.ofType .unit]).eval s p c {} == some [] &&
    (Selector.slot 0).eval s p c { slots := [.obj v] } == some [v] &&
    (Selector.slot 0).eval s p c {} == none
  | none => false

-- the plays of Spark are listed with the enemy Unit as the target, and with no other target
#guard match sparkReady with
  | some (s, _, c, v) =>
    let plays := (legalActions s).filter fun a =>
      match a.kind with | .playCard c' _ _ _ _ _ => c' == c | _ => false
    plays.length == 1 &&
    plays.all (fun a => match a.kind with | .playCard _ _ ts _ _ _ => ts == [v] | _ => false)
  | none => false

-- Spark with no target, with a target of the wrong side, or with an object that is not in play is
-- not legal
#guard match sparkReady with
  | some (s, p, c, v) =>
    let mine := (s.zone (.player p .hand)).find? fun x => x != c
    isIllegal (step 100 s ⟨.player p, .playCard c ⟨1, []⟩ []⟩) &&
    isIllegal (step 100 s ⟨.player p, .playCard c ⟨1, []⟩ [⟨999⟩]⟩) &&
    isIllegal (step 100 s ⟨.player p, .playCard c ⟨1, []⟩ [v, v]⟩) &&
    (match mine with
      | some m => isIllegal (step 100 s ⟨.player p, .playCard c ⟨1, []⟩ [m]⟩)
      | none => true)
  | none => false

-- casting Spark puts it on the Chain with the target chosen (CR 355, 354)
#guard match sparkReady with
  | some (s, p, c, v) =>
    match step 100 s ⟨.player p, .playCard c ⟨1, []⟩ [v]⟩ with
    | .ok (s1, _) =>
      match s1.zone .chain with
      | [item] => (s1.obj? item).any (fun o => o.targets == [v]) &&
          (s1.poolOf p).total == 0
      | _ => false
    | .error _ => false
  | none => false

-- when everyone has passed, Spark deals 2 damage to the Unit (Might 2), and the Unit goes to its
-- owner's Trash; Spark goes to the Trash (CR 340, 142, 417)
#guard match sparkReady with
  | some (s, p, c, v) =>
    let q := other p
    match step 100 s ⟨.player p, .playCard c ⟨1, []⟩ [v]⟩ with
    | .ok (s1, _) =>
      match step 100 s1 ⟨.player p, .pass⟩ with
      | .ok (s2, _) =>
        match step 100 s2 ⟨.player q, .pass⟩ with
        | .ok (s3, es) =>
          cnt q .base s3 + 1 == cnt q .base s && cnt q .trash s3 == cnt q .trash s + 1 &&
          cnt p .trash s3 == cnt p .trash s + 1 && (s3.zone .chain).isEmpty &&
          es.any (fun e => match e with | .damaged t 2 => t == v | _ => false) &&
          (match s3.pending with | [.priority r] => r == p | _ => false)
        | .error _ => false
      | .error _ => false
    | .error _ => false
  | none => false

-- damage stays on the Unit until the Cleanup: it is lethal when it reaches the Might, and the
-- Cleanup kills the Unit then (CR 323.4)
#guard match sparkReady with
  | some (s, _, _, v) =>
    let r1 := dealObj 1 s v
    let r2 := dealObj 2 s v
    (r1.1.obj? v).any (·.damage == 1) && r1.2 == [Event.damaged v 1] && !r1.1.lethal v &&
    (r2.1.obj? v).any (·.damage == 2) && r2.1.lethal v &&
    (cleanupStep r1.1).isNone &&
    ((cleanupStep r2.1).map fun r => (r.1.obj? v).isNone) == some true &&
    r2.1.zone .battlefieldZone == s.zone .battlefieldZone
  | none => false

/-- The exhausted flag of an object after a change, if the change was made and the object is
there. -/
meta def exhaustedAfter (r : Option (GameState × List Event)) (v : ObjId) : Option Bool :=
  r.bind fun x => (x.1.obj? v).map fun o => o.exhausted

/-- The damage of an object after a change. -/
meta def damageAfter (r : Option (GameState × List Event)) (v : ObjId) : Option Nat :=
  r.bind fun x => (x.1.obj? v).map fun o => o.damage

/-- The object is no longer on any zone after a change. -/
meta def goneAfter (r : Option (GameState × List Event)) (v : ObjId) : Option Bool :=
  r.map fun x => (x.1.obj? v).isNone

-- ready, exhaust, kill, heal act on the Unit that a slot names; an object that has left play is
-- nothing, and what is not understood yet is not done
#guard match sparkReady with
  | some (s, p, c, v) =>
    let env : Env := { slots := [.obj v] }
    let exh := applyPrim s p c env (.exhaust (.slot 0))
    let rdy := exh.bind fun r => applyPrim r.1 p c env (.ready (.slot 0))
    let healed := applyPrim (dealObj 1 s v).1 p c env (.heal (.slot 0) (.const 1))
    let killed := applyPrim s p c env (.kill (.slot 0))
    let again := killed.bind fun r => applyPrim r.1 p c env (.kill (.slot 0))
    exhaustedAfter exh v == some true && exhaustedAfter rdy v == some false &&
    damageAfter healed v == some 0 && goneAfter killed v == some true &&
    (again.map fun r => r.2) == some [] &&
    (applyPrim s p c env (.draw .you (.const 1))).isNone
  | none => false

-- the effect language (M4d): run a body from a state, with the Chain out of the way
meta def runBody (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect) :
    Option GameState :=
  match advance 100 { s with pending := [.run p src env (.cons e .nil)] } [] with
  | .ok (s', _) => some s'
  | .error _ => none

/-- Every enemy Unit on a Base. -/
meta def enemyUnits : Selector := Selector.all .enemy .atBase [.ofType .unit]

#guard match sparkReady with
  | some (s, p, c, v) =>
    let hit (k : Nat) : Effect := .prim (.deal .it (.const k))
    let dmg (r : Option GameState) : Option Nat :=
      r.bind fun s' => (s'.obj? v).map fun o => o.damage
    -- forEach: each enemy Unit is dealt damage, `it` being the Unit
    dmg (runBody s p c {} (.forEach enemyUnits (hit 1))) == some 1 &&
    -- ifThen: the branch is chosen by the condition
    dmg (runBody s p c {} (.ifThen (.exists enemyUnits) (.forEach enemyUnits (hit 1)) .nop)) ==
      some 1 &&
    dmg (runBody s p c {} (.ifThen (.not (.exists enemyUnits)) (.forEach enemyUnits (hit 1)) .nop))
      == some 0 &&
    dmg (runBody s p c {} (.ifThen (.cmp .ge (.count enemyUnits) (.const 2))
      (.forEach enemyUnits (hit 1)) .nop)) == some 0 &&
    -- repeatN: twice makes lethal damage (Might 2); the Cleanup then sends the Unit to the Trash
    ((runBody s p c {} (.repeatN (.const 2) (.forEach enemyUnits (hit 1)))).bind
      fun s' => (cleanupStep s').map (·.1)).map
      (fun s' => (s'.obj? v).isNone && cnt (other p) .trash s' == cnt (other p) .trash s + 1) ==
        some true &&
    -- bind: an amount that counts is bound, then used
    dmg (runBody s p c {} (.bind ⟨"n"⟩ (.count enemyUnits)
      (.forEach enemyUnits (.prim (.deal .it (.var ⟨"n"⟩)))))) == some 1 &&
    -- what is not understood is skipped, and the rest goes on
    dmg (runBody s p c {} (.seqOf [.prim (.extraTurn .you), .forEach enemyUnits (hit 1)])) ==
      some 1
  | none => false

-- an effect that names one object to choose while it resolves, with one candidate, takes it
#guard match sparkReady with
  | some (s, p, c, v) =>
    let one := Selector.one .enemy .atBase [.ofType .unit]
    let st (e : Effect) : Option Object := (runBody s p c {} e).bind fun s' => s'.obj? v
    (st (.prim (.deal one (.const 1)))).map (·.damage) == some 1 &&
    (st (.prim (.stun one))).map (·.stunned) == some true &&
    (st (.prim (.buff one))).map (·.buffed) == some true &&
    (st (.prim (.exhaust one))).map (·.exhausted) == some true
  | none => false

-- banish and return to hand send the Unit to its owner's Banishment and hand
#guard match sparkReady with
  | some (s, p, c, v) =>
    let q := other p
    let env : Env := { slots := [.obj v] }
    (runBody s p c env (.prim (.banish (.slot 0)))).map
      (fun s' => cnt q .banishment s' == cnt q .banishment s + 1 && (s'.obj? v).isNone) ==
        some true &&
    (runBody s p c env (.prim (.returnToHand (.slot 0)))).map
      (fun s' => cnt q .hand s' == cnt q .hand s + 1 && (s'.obj? v).isNone) == some true
  | none => false

end RiftboundTest
