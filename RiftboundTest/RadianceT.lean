module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance readiness and token play history -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

private meta def exhausted (s : GameState) (id : ObjId) : Bool :=
  (s.obj? id).any (·.exhausted)

private meta def playRecruitAt (s : GameState) (p : PlayerId) (field : ObjId) :
    Option (GameState × List Event) :=
  applyCreateAt s p field { slots := [.obj field] } "Recruit" (.const 1) (.slot 0) false

-- Raider readies enemy Units on play. Its Awaken restriction applies to both players and leaves
-- Gear and ordinary Ready effects alone outside that phase.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, raider) ← put s p "RAD-019" .hand
  let (s, friend) ← put s p "RAD-088" .base
  let (s, enemy) ← putAt (s.control q s.bf0) q "RAD-088" s.bf0
  let (s, gear) ← put s q "RAD-089" .base
  let (s, incoming) ← put s q "RAD-088" .hand
  let s := ((s.exhaustObj friend).exhaustObj enemy).exhaustObj gear
  let (entered, _) ← (step 100 (s.fund p 6 1)
    ⟨.player p, .playCard raider ⟨6, [.fury]⟩ []⟩).toOption
  let entered := settleChain {} 12 entered
  let raider ← entered.firstOf p .base "RAD-019"
  let played ← play { entered with pending := [.priority q] } q incoming
  let newcomer ← played.firstOf q .base "RAD-088"
  let before := (played.exhaustObj enemy).exhaustObj raider
  let (awakened, events) ← microStep0 { before with active := some q, pending := [.phase .awaken] }
  let (ours, _) ← microStep0 { before with active := some p, pending := [.phase .awaken] }
  let during := (readyEffect awakened enemy).1
  let after := (readyEffect { awakened with phase := .main } enemy).1
  return !exhausted entered raider && !exhausted entered enemy && exhausted entered friend &&
    exhausted entered gear && !exhausted played newcomer &&
    exhausted awakened enemy && exhausted ours raider && exhausted ours friend &&
    !exhausted awakened gear && (events.filterMap (fun
      | .readied id => some id
      | _ => none)) == [gear] &&
    exhausted during enemy && !exhausted after enemy

-- The Exile affects its controller's physical Units and Unit tokens at controlled Battlefields.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, _) ← put s p "RAD-149" .legendZone
  let (s, toField) ← put s p "RAD-088" .hand
  let (s, toBase) ← put s p "RAD-088" .hand
  let s := s.control p field
  let entered ← play s p toField [field]
  let located ← entered.inPlay.find? (fun id =>
    (entered.cardDef? id).any (·.id == ⟨"RAD-088"⟩) && (entered.obj? id).any (·.loc == some field))
  let based ← play entered p toBase
  let atBase ← based.firstOf p .base "RAD-088"
  let funded := (s.control p field).fund p 2 0 0 1
  let plan ← (permanentPlayOptions funded p toField { price := .reduceEnergy 0 }).find?
    (fun option => option.battlefield == some field)
  let (effectPlayed, effectUnit, _) ← applyReducedPermanent funded p toField plan
  let (free, freeEvents) := playFreeAt p field s toField
  let freeUnit ← freeEvents.findSome? (fun | .played _ unit => some unit | _ => none)
  let recruit : ObjId := ⟨based.nextId⟩
  let (friendly, _) ← playRecruitAt based p field
  let (enemy, _) ← playRecruitAt based q field
  let (uncontrolled, _) ← playRecruitAt (based.control q field) p field
  return !exhausted entered located && exhausted based atBase &&
    (effectPlayed.obj? effectUnit).any (fun o => o.loc == some field && !o.exhausted) &&
    (free.obj? freeUnit).any (fun o => o.loc == some field && !o.exhausted) &&
    (friendly.obj? recruit).any (fun o => o.loc == some field && !o.exhausted) &&
    exhausted enemy recruit && exhausted uncontrolled recruit

-- Recruits count for Fanfare. A Bomb played to Rakelstake gives Predict and enables Hold 'Em.
#guard radianceCase fun s => do
  let p := s.me
  let recruitField := s.bf0
  let (s, field) ← putBf s p "RAD-165"
  let (s, fanfare) ← put s p "RAD-047" .hand
  let (s, bombMaker) ← put s p "RAD-001" .hand
  let (s, combatTrick) ← put s p "RAD-070" .hand
  let (s, _) ← put s p "RAD-011" .mainDeck
  let (s, _) ← put s p "RAD-011" .mainDeck
  let (s, _) ← put s p "RAD-011" .mainDeck
  let waiting ← play s p fanfare
  let drawn := waiting.drawLog.count (p, waiting.turn)
  let (played, events) ← playRecruitAt (waiting.control p recruitField) p recruitField
  let triggered := played.withTriggers events
  let (recruits, _) ← (advance 100 triggered []).toOption
  let recruits := settleChain {} 12 recruits
  let bombs ← play waiting p bombMaker [] { obj := (· == field) }
  let prediction := match bombs.pending with
    | .predict who .. :: _ => who == p
    | _ => false
  return recruits.drawLog.count (p, waiting.turn) == drawn + 1 &&
    waiting.energyCost? p combatTrick == some 3 && recruits.energyCost? p combatTrick == some 1 &&
    bombs.energyCost? p combatTrick == some 1 && prediction

end RiftboundTest
