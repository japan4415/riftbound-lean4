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

end RiftboundTest
