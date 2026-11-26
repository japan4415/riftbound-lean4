module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance optional plays from other zones -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Returning a temporary 5-Might Unit allows a 4-Might Unit to be played at a controlled
-- Battlefield. The equal-Might card and opponent's hand are outside the offer.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, source) ← put s p "RAD-115" .base
  let (s, returned) ← put s p "RAD-088" .base
  let (s, _) ← putAt (s.control p field) p "RAD-088" field
  let (s, replacement) ← put s p "RAD-115" .hand
  let (s, equal) ← put s p "RAD-030" .hand
  let (s, rival) ← put s q "RAD-088" .hand
  let powered := (addMightMod ⟨3, .turn⟩ (s.fund p 0 (chaos := 1)) returned).1
  let act (g : GameState) (who : PlayerId) (kind : ActionKind) := (step 100 g ⟨.player who, kind⟩).toOption
  let (queued, _) ← act powered p (.activate source 0 ⟨0, [.chaos]⟩ [returned])
  let (passed, _) ← act queued p .pass
  let (offering, _) ← act passed q .pass
  let (choosing, _) ← act offering p (.decide true)
  let (declined, _) ← act offering p (.decide false)
  let (places, choiceEvents) ← act choosing p (.choose replacement)
  let .eitherDo _ _ _ (.finishFundedPermanent _ _ base []) (.finishFundedPermanent _ _ away [])
    _ :: _ := places.pending | none
  let (played, _) ← act places p (.decide false)
  let arrived ← played.inPlay.find? (fun id =>
    (played.cardDef? id).any (·.id == ⟨"RAD-115"⟩) && id != source)
  return powered.mightEff returned == 5 &&
    !(legalFrameActions choosing).contains ⟨.player p, .choose equal⟩ &&
    !(legalFrameActions choosing).contains ⟨.player p, .choose rival⟩ &&
    (declined.zone (.player p .hand)).contains replacement &&
    declined.countIn p .hand "RAD-088" == 1 &&
    choiceEvents.isEmpty && base.battlefield.isNone && away.battlefield == some field &&
    (played.obj? arrived).any (·.loc == some field)

-- A player can stop at zero or play three eligible cards. The Deploy Gear requires a Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let (s, spell) ← put s p "RAD-135" .hand
  let (s, gear) ← put s p "RAD-024" .trash
  let (s, a) ← put s p "RAD-088" .trash
  let (s, b) ← put s p "RAD-088" .trash
  let (s, c) ← put s p "RAD-130" .trash
  let (s, expensive) ← put s p "RAD-019" .trash
  let (s, cheaperSpell) ← put s p "RAD-047" .trash
  let z := Zone.player p .trash
  let (queued, _) ← (step 100 (s.fund p 8 (order := 2))
    ⟨.player p, .playCard spell ⟨8, [.order, .order]⟩ []⟩).toOption
  let nonePlayed := settleChain { yes := false } 50 queued
  let done := settleChain { obj := (· == gear) } 50 queued
  let arrived ← done.inPlay.find? (fun id => (done.cardDef? id).any (·.id == ⟨"RAD-024"⟩))
  return (done.obj? arrived).any (·.loc.isSome) &&
    [gear, a, b, c].all (nonePlayed.zone z).contains &&
    ([gear, a, b, c].filter (fun id => !(done.zone z).contains id)).length == 3 &&
    (done.zone z).contains expensive && (done.zone z).contains cheaperSpell &&
    !(done.pending.any (fun | .mayDo .. => true | _ => false))

-- Both entry and Hold offer Predict 3.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let s ← (List.range 3).foldlM
    (fun g _ => (put g p "RAD-011" .mainDeck).map Prod.fst) s
  let (s, hand) ← put s p "RAD-067" .hand
  let (s, atField) ← putAt (s.control p field) p "RAD-067" field
  let entering ← cast (s.fund p 8 (mind := 2)) p hand ⟨8, [.mind, .mind]⟩
  let (queued, _) ← (advance 100 (s.withTriggers [.scored p field false]) []).toOption
  let holding := settleChain {} 30 queued
  let predicts (g : GameState) := match g.pending with
    | .predict who n _ more _ _ :: _ => who == p && n == 3 && more.length == 2
    | _ => false
  return predicts entering && predicts holding && holding.inPlay.contains atField

-- Deathknell banishes the original top card even when declined or unaffordable. It ignores
-- only Energy, and can finalize a Spell from Banishment as well as a Unit.
#guard radianceCase fun s => do
  let p := s.me
  let (s, guardian) ← put s p "RAD-067" .base
  let (s, _) ← put s p "RAD-088" .mainDeck
  let resolveDeath (g : GameState) (says : Says) := do
    let killed := killOrSave g guardian
    let (queued, _) ← (advance 100 (killed.1.withTriggers killed.2) []).toOption
    return settleChain says 50 queued
  let unfunded ← resolveDeath (s.fund p 0) {}
  let funded ← resolveDeath (s.fund p 0 (body := 1)) {}
  let declined ← resolveDeath (s.fund p 0 (body := 1)) { yes := false }
  let (s, _) ← put s p "RAD-011" .mainDeck
  let (s, _) ← put s p "OGN-144" .mainDeck
  let spell ← resolveDeath (s.fund p 0 (body := 1)) {}
  return unfunded.countIn p .banishment "RAD-088" == 1 &&
    declined.countIn p .banishment "RAD-088" == 1 &&
    funded.countIn p .banishment "RAD-088" == 0 && funded.countIn p .base "RAD-088" == 1 &&
    (funded.poolOf p).body == 0 &&
    spell.countIn p .trash "OGN-144" == 1 &&
    spell.drawLog.count (p, spell.turn) == s.drawLog.count (p, s.turn) + 2 &&
    (spell.poolOf p).body == 0

end RiftboundTest
