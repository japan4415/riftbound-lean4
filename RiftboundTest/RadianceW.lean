module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance Battlefield abilities and continuous Legend grants -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- The active player may use Black Market even if the opponent controls it, once per turn.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, market) ← putBf s q "RAD-158"
  let (s, _) ← put s p "RAD-011" .mainDeck
  let (s, _) ← put s q "RAD-011" .mainDeck
  let action (who : PlayerId) : Action := ⟨.player who, .activate market 1 ⟨0, [.fury, .mind]⟩ []⟩
  let money (g : GameState) (who : PlayerId) := g.fund who 0 (fury := 1) (mind := 1)
  let before := money (s.control q market) p
  let (used, _) ← (step 100 before (action p)).toOption
  let done := settleChain {} 12 used
  let opponentPriority := money { before with pending := [.priority q] } q
  let next := beginTurnStep done []
  let opponentTurn := money { next with phase := .main, pending := [.priority q] } q
  let (usedNext, _) ← (step 100 (opponentTurn.control p market) (action q)).toOption
  let nextDone := settleChain {} 12 usedNext
  return (legalFrameActions before).contains (action p) &&
    !activatable opponentPriority q market 1 ⟨0, [.fury, .mind]⟩ [] true &&
    !(legalFrameActions (money done p)).contains (action p) &&
    done.drawLog.count (p, done.turn) == before.drawLog.count (p, before.turn) + 1 &&
    nextDone.drawLog.count (q, nextDone.turn) == 1

-- Soul readies a chosen friendly Legend. Its continuous grant stops when it leaves the board,
-- while an activated instance that was already put on the Chain still resolves.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, soul) ← put s p "RAD-040" .hand
  let (s, first) ← put s p "RAD-149" .legendZone
  let (s, second) ← put s p "RAD-147" .legendZone
  let (s, enemy) ← put s q "RAD-149" .legendZone
  let (s, unit) ← put s q "RAD-088" .base
  let before := ((s.exhaustObj first).exhaustObj second).exhaustObj enemy
  let entered ← play before p soul [] { pick := (· == [first]) }
  let soul ← entered.firstOf p .base "RAD-040"
  let grantIndex (g : GameState) (legend : ObjId) := do
    let d ← g.cardDef? legend
    ((g.activationList legend d).zipIdx.find? (fun (entry, _) =>
      entry.1.any (·.card == ⟨"RAD-040"⟩))).map Prod.snd
  let index ← grantIndex entered first
  let (queued, _) ← (step 100 entered ⟨.player p, .activate first index ⟨0, []⟩ [unit]⟩).toOption
  let afterKill := (killOrSave queued soul).1
  let resolved := settleChain {} 12 afterKill
  return (entered.obj? first).any (fun o => !o.exhausted) &&
    (entered.obj? second).any (·.exhausted) && (entered.obj? enemy).any (·.exhausted) &&
    (grantIndex entered second).isSome && (grantIndex entered enemy).isNone &&
    (grantIndex resolved first).isNone && (resolved.obj? first).any (·.exhausted) &&
    resolved.mightEff unit == entered.mightEff unit + 3

-- The Ball's play and its Move offer independent modes. Only the current Battlefield takes damage.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let other ← s.battlefields.find? (· != field)
  let (s, ball) ← put s p "RAD-146" .hand
  let (s, victim) ← putAt s q "RAD-088" field
  let (s, distant) ← putAt s q "RAD-088" other
  let (s, _) ← put s p "RAD-011" .mainDeck
  let s := (s.control q field).control q other
  let selectMode (g : GameState) (i : Nat) := do
    let a ← (legalFrameActions g).find? (fun a => match a.kind with
      | .putTrigger _ [] (.pay [] mode ..) => mode == some i
      | _ => false)
    let (queued, _) ← (step 100 g a).toOption
    return settleChain {} 12 queued
  let (playing, _) ← (step 100 (s.fund p 5 (mind := 1))
    ⟨.player p, .playCard ball ⟨5, [.mind]⟩ [field]⟩).toOption
  let onField ← playing.inPlay.find? (fun id =>
    (playing.cardDef? id).any (·.id == ⟨"RAD-146"⟩))
  let damaged ← selectMode playing 1
  let moved := moveByEffect p (some other) damaged onField
  let (moving, _) ← (advance 100 (moved.1.withTriggers moved.2) []).toOption
  let draw ← selectMode moving 0
  return !(damaged.inPlay.contains victim) && damaged.inPlay.contains distant &&
    (damaged.obj? distant).any (·.damage == 0) &&
    (draw.obj? onField).any (·.loc == some other) &&
    draw.drawLog.count (p, draw.turn) == damaged.drawLog.count (p, damaged.turn) + 1

end RiftboundTest
