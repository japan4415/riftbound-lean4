module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance death and Battlefield history -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Animus follows the controller of the dead permanent and does not count a Banish.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, animus) ← put s p "RAD-005" .hand
  let (s, removal) ← put s p "RAD-101" .hand
  let (s, friend) ← put s p "RAD-012" .base
  let (s, borrowed) ← putAt s p "RAD-012" s.bf0
  let s := s.modObj borrowed (fun o => { o with controller := q })
  let (s, unit) ← put s p "RAD-061" .base
  let (s, swimmer) ← put s p "RAD-014" .hand
  let friendlyDeath ← play s p removal [friend]
  let enemyDeath ← play s p removal [borrowed]
  let unitDeath ← play s p swimmer [unit]
  let gone := banishObj p s friend
  let entersReady (g : GameState) := do
    let played ← play g p animus
    let id ← played.firstOf p .base "RAD-005"
    return played.tired id == some false
  let byGear ← entersReady friendlyDeath
  let byEnemy ← entersReady enemyDeath
  let byUnit ← entersReady unitDeath
  -- Resolve the Anvil's leave-board ability before playing Animus.
  let (afterBanish, _) ← (advance 100 (gone.1.withTriggers gone.2) []).toOption
  let byBanish ← entersReady (settleChain {} 12 afterBanish)
  return byGear && byUnit && !byEnemy && !byBanish

-- A simultaneous kill gives one ability even when the watching Unit also died.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, watchers) ← putAt s q "RAD-131" s.bf0
  let s := s.modObj watchers (fun o => { o with controller := p })
  let (s, a) ← put s p "RAD-011" .base
  let (s, b) ← put s p "RAD-011" .base
  let (s, recipient) ← put s p "RAD-061" .base
  let count (g : GameState) (events : List Event) :=
    (g.detect events).countP (fun t => t.card == cid "RAD-131" && t.controller == p)
  let batch := applyEach (killOrSaveInGroup s) s [a, b]
  let aDead := killObj s a
  let bDead := killObj aDead.1 b
  let selfDead := applyEach (killOrSaveInGroup s) s [watchers, a, b]
  let result ← fire selfDead.1 selfDead.2 { pick := fun ids => ids == [recipient] }
  return count batch.1 batch.2 == 1 && count aDead.1 aDead.2 == 1 &&
    count bDead.1 bDead.2 == 1 && count selfDead.1 selfDead.2 == 1 &&
    (result.obj? recipient).any (·.buffed)

-- Sanctum tracks the first non-token Unit by Battlefield, player, and turn.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let away := s.bf0
  let (s, field) ← putBf s q "RAD-159"
  let (s, a) ← putAt s p "RAD-061" field
  let (s, b) ← putAt s p "RAD-061" field
  let (s, c) ← putAt s p "RAD-061" field
  let (s, d) ← putAt s q "RAD-061" field
  let (s, elsewhere) ← putAt s p "RAD-061" away
  let recruit ← s.tokenCard "Recruit"
  let (s, token) ← addObject s
    { newCard s.cards s p recruit.id with kind := .token recruit.id, loc := some field }
    .battlefieldZone
  let afterDeath (g : GameState) (ids : List ObjId) := do
    let (killed, events) := applyEach (killOrSaveInGroup g) g ids
    let (queued, _) ← (advance 100 (killed.withTriggers events) []).toOption
    return settleChain {} 12 queued
  let irrelevant ← afterDeath s [token, elsewhere]
  let shared ← afterDeath irrelevant [a, b, d]
  let repeated ← afterDeath shared [c]
  let (next, later) ← putAt { repeated with turn := repeated.turn + 1 } p "RAD-061" field
  let following ← afterDeath next [later]
  return irrelevant.countNamed p .base "Recruit" == 0 &&
    shared.countNamed p .base "Recruit" == 1 && shared.countNamed q .base "Recruit" == 1 &&
    repeated.countNamed p .base "Recruit" == 1 && following.countNamed p .base "Recruit" == 2

end RiftboundTest
