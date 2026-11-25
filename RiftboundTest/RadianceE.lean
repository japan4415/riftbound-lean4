module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance conquest and combat scenarios -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Bloodscent Swarm's discount counts own Conquers, leaving its Power and Hold unchanged.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let a ← s.battlefields[0]?
  let b ← s.battlefields[1]?
  let (s, card) ← put s p "RAD-080" .hand
  let d ← s.cardDef? card
  let cost (g : GameState) := g.effCost p card d
  let held := s.modObj a (markScored p true)
  let enemy := (scoreBf s q a true).1
  let first := (scoreBf s p a true).1
  let second := (scoreBf first p b true).1
  let after := (scoreBf held p b true).1
  let played ← cast (second.fund p 4 (body := 2)) p card ⟨4, [.body, .body]⟩
  return cost held == cost s && cost enemy == cost s &&
    cost first == some ⟨6, [.domain .body, .domain .body]⟩ &&
    cost second == some ⟨4, [.domain .body, .domain .body]⟩ &&
    cost after == cost first && played.countIn p .base "RAD-080" == 1

-- Graves' triggered damage uses his current Might. He contributes no assigned combat damage.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, graves) ← putAt s p "RAD-085" field
  let (s, first) ← putAt s q "VEN-091" field
  let (s, second) ← putAt s q "RAD-060" field
  let (s, ally) ← putAt s p "VEN-071" field
  let (s, distant) ← put s q "VEN-071" .base
  let s := s.buff graves
  let attacking ← startCombatNow s field p
  let defending ← startCombatNow s field q
  let hit (g : GameState) (id : ObjId) (n : Nat) := (g.obj? id).any (·.damage == n)
  return [attacking, defending].all (fun g =>
    hit g first 5 && hit g second 5 && hit g ally 0 && hit g distant 0) &&
    attacking.combatMight graves true == 0 && defending.combatMight graves false == 0

-- Only a defending player's Unit at Durand Memorial may gain Tank, and only in that combat.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s p "RAD-161"
  let (s, defender) ← putAt s p "VEN-071" field
  let (s, other) ← putAt s p "RAD-060" field
  let (s, distant) ← put s p "VEN-071" .base
  let (s, attacker) ← putAt s q "VEN-071" field
  let before := (s.control p field).inCombatAt field q
  let triggers := before.detect [.combatStarted field q]
  let (waiting, _) ← (advance 100 { before with pending := .triggers triggers :: before.pending } []).toOption
  let pick (id : ObjId) := (step 100 waiting ⟨.player p, .putTrigger 0 [id]⟩).toOption
  let (chosen, _) ← pick defender
  let after := settleChain {} 8 chosen
  let (finished, _) ← (advance 100 { after with pending := [.combatFinish field, .priority p] } []).toOption
  return (pick other).isSome && (pick distant).isNone && (pick attacker).isNone &&
    after.hasKw defender .tank && !after.hasKw other .tank &&
    !after.hasKw distant .tank && !after.hasKw attacker .tank && !finished.hasKw defender .tank

end RiftboundTest
