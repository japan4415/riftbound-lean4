module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: playing a Unit from the hand (CR 349-359, 356, 357)

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
      match step 100 s ⟨.player p, .playCard c ⟨1, []⟩⟩ with
      | .ok (s1, es) =>
        cnt p .hand s1 + 1 == cnt p .hand s && cnt p .base s1 == cnt p .base s + 1 &&
        (s1.poolOf p).total == 0 &&
        (match es with
          | [.moved c' id' _] => c' == c && (s1.obj? id').any (·.exhausted)
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
      isIllegal (step 100 s ⟨.player p, .playCard c ⟨1, []⟩⟩)
    | none => false
  | none => false
#guard match mainPhaseP 1 >>= withEnergy with
  | some (s, p) =>
    match vanillaInHand s p with
    | some c =>
      isIllegal (step 100 s ⟨.player p, .playCard c ⟨2, []⟩⟩) &&
      isIllegal (step 100 s ⟨.player p, .playCard c ⟨1, [.fury]⟩⟩)
    | none => false
  | none => false

-- the other player cannot play, and a card that is not in the hand cannot be played
#guard match mainPhaseP 1 >>= withEnergy with
  | some (s, p) =>
    let q : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩
    match vanillaInHand s p, vanillaInHand s q with
    | some c, some d =>
      isIllegal (step 100 s ⟨.player q, .playCard c ⟨1, []⟩⟩) &&
      isIllegal (step 100 s ⟨.player p, .playCard d ⟨1, []⟩⟩)
    | _, _ => false
  | none => false

-- the plays are listed: one for each vanilla Unit in the hand, with the Energy to pay for it
#guard match mainPhaseP 1 >>= withEnergy with
  | some (s, p) =>
    let plays := (legalActions s).filter fun a =>
      match a.kind with | .playCard _ _ => true | _ => false
    let vanillas := (s.zone (.player p .hand)).filter fun c =>
      (s.cardDef? c).any (fun d => d.name.startsWith "Vanilla")
    plays.length == vanillas.length && !plays.isEmpty &&
      plays.all (fun a => match a.kind with | .playCard _ pay => pay == ⟨1, []⟩ | _ => false)
  | none => false
-- and nothing is listed without Energy
#guard match mainPhaseP 1 with
  | some s => ((legalActions s).filter fun a =>
      match a.kind with | .playCard _ _ => true | _ => false).isEmpty
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
    match step 100 s ⟨.player p, .playCard c ⟨1, []⟩⟩ with
    | .ok (s1, es) =>
      cnt p .hand s1 + 1 == cnt p .hand s && s1.zone .chain == [match es with
        | [.moved _ id _] => id | _ => c] &&
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
    match step 100 s ⟨.player p, .playCard c ⟨1, []⟩⟩ with
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
              es.length == 2
            | .error _ => false)
        | .error _ => false)
    | .error _ => false
  | none => false

-- the plays of a Spell are listed, and the passes of the Chain are the only answers then
#guard match spellReady with
  | some (s, p, c) =>
    (legalActions s).any (fun a => a.kind == .playCard c ⟨1, []⟩) &&
    (match step 100 s ⟨.player p, .playCard c ⟨1, []⟩⟩ with
      | .ok (s1, _) => (legalActions s1).filter (fun a => a.kind != .concede) ==
          [⟨.player p, .pass⟩]
      | .error _ => false)
  | none => false

end RiftboundTest
