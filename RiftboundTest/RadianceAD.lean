module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance modal spells with a Move destination -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Command: Attack declares a different destination with its move mode, only targets friendly
-- Deploy Gear, and doesn't start a contest even when that Gear enters enemy territory.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let origin := s.bf0
  let away ← s.battlefields.find? (· != origin)
  let (s, card) ← put s p "RAD-033" .hand
  let (s, gear) ← putAt (s.control p origin) p "RAD-024" origin
  let (s, _) ← putAt s p "RAD-088" origin
  let (s, opposingGear) ← putAt s q "RAD-024" away
  let (s, _) ← putAt (s.control q away) q "RAD-088" away
  let (s, stationary) ← put s p "RAD-089" .base
  let s := s.fund p 1 (calm := 1)
  let present (targets : List ObjId) (pick : SpellPick) :=
    (legalFrameActions s).contains ⟨.player p, .playCard card ⟨1, [.calm]⟩ targets none none pick⟩
  let moved ← cast s p card ⟨1, [.calm]⟩ [gear] {} (.modeDestination 0 (some away))
  return present [gear] (.modeDestination 0 (some away)) &&
    !(present [gear] (.modeDestination 0 (some origin))) && !(present [gear] (.mode 0)) &&
    !(present [stationary] (.modeDestination 0 (some away))) &&
    !(present [opposingGear] (.modeDestination 0 (some origin))) &&
    !(present [] (.modeDestination 1 (some away))) &&
    (moved.obj? gear).any (·.loc == some away) &&
    (moved.obj? away).any (fun o => o.control == some q && o.contested.isNone)

-- The search mode has no target at finalization. It may draw one of the five looked-at Gear
-- and the four others are Recycled in the chosen order.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, command) ← put s p "RAD-033" .hand
  let (s, chosen) ← put s p "RAD-089" .mainDeck
  let (s, fifth) ← put s p "RAD-024" .mainDeck
  let (s, outside) ← put s p "RAD-024" .mainDeck
  let (s, a) ← put s p "RAD-011" .mainDeck
  let (s, b) ← put s p "RAD-047" .mainDeck
  let (s, c) ← put s p "RAD-088" .mainDeck
  let deck := Zone.player p .mainDeck
  let seen := [a, b, c, chosen, fifth]
  let suffix := outside :: (s.zone deck).filter (fun id => !(outside :: seen).contains id)
  let s := (s.reorder deck (seen ++ suffix)).fund p 1 (calm := 1)
  let act (g : GameState) (who : Actor) (a : ActionKind) := (step 100 g ⟨who, a⟩).toOption
  let (casted, _) ← act s (.player p) (.playCard command ⟨1, [.calm]⟩ [] none none (.mode 1))
  let (passed, _) ← act casted (.player p) .pass
  let (asked, looked) ← act passed (.player q) .pass
  let (choosing, _) ← act asked (.player p) (.decide true)
  let (recycling, drawn) ← act choosing (.player p) (.choose fifth)
  let order := [c, a, chosen, b]
  let (finished, _) ← act recycling .chance (.arrange order)
  return seen.all (fun id => looked.contains (.lookedAt p id)) &&
    (legalFrameActions choosing).map Action.kind == [.choose chosen, .choose fifth] &&
    drawn.contains (.revealed p fifth) && drawn.contains (.drew p) &&
    finished.countIn p .hand "RAD-024" == 1 && finished.zone deck == suffix ++ order

-- Demon Shade can move to an open Battlefield from Hidden. Its target is still restricted to
-- the hiding place. Choosing the Ganking mode checks for open Battlefields on resolution.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let origin := s.bf0
  let away ← s.battlefields.find? (· != origin)
  let (s, unit) ← putAt (s.control p origin) p "RAD-088" origin
  let (s, atBase) ← put s p "RAD-088" .base
  let (s, hidden) ← put s p "RAD-102" .hidden
  let (s, hand) ← put s p "RAD-102" .hand
  let s := s.modObj hidden (fun o => { o with
    hiddenAt := some origin, hiddenTurn := some (s.turn - 1) })
  let pick := SpellPick.modeDestination 0 (some away)
  let moved ← cast (s.fund p 0) p hidden ⟨0, []⟩ [unit] {} pick
  let fromBase := cast (s.fund p 0) p hidden ⟨0, []⟩ [atBase] {} pick
  let ready := s.fund p 3
  let (queued, _) ← (step 100 ready
    ⟨.player p, .playCard hand ⟨3, []⟩ [unit] none none (.mode 1)⟩).toOption
  let (closed, _) ← putAt (queued.control q away) q "RAD-088" away
  let finish (g : GameState) := settleChain {} 20 g
  return (moved.obj? unit).any (·.loc == some away) && moved.countIn p .trash "RAD-102" == 1 &&
    fromBase.isNone && !((finish queued).hasKw unit .ganking) &&
    (finish closed).hasKw unit .ganking

end RiftboundTest
