module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance costs paid with permanents and Battlefield targets -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Twirligig can pay a Kill cost with itself. A death replacement still pays the cost.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, gear) ← put s p "RAD-022" .base
  let (s, ally) ← putAt s p "RAD-011" s.bf0
  let (s, foe) ← put s q "RAD-011" .base
  let action (index : Nat) (cost : Option ObjId) :=
    Action.mk (.player p) (.activate gear index ⟨0, []⟩ [] [] none none cost)
  let (buyGold, _) ← (step 100 s (action 0 none)).toOption
  let gold := settleChain {} 12 buyGold
  let goldToken ← (gold.zone (.player p .base)).find? (fun id =>
    (gold.cardDef? id).any (·.name == "Gold"))
  let sacrificeGear := action 1 (some gear)
  let (recruitCost, events) ← (step 100 s sacrificeGear).toOption
  let recruit := settleChain {} 12 recruitCost
  let saved := (s.modObj ally (fun o => { o with damage := 1 })).addTurnFxOn p ally .saveOnce
  let (mechCost, _) ← (step 100 saved (action 2 (some ally))).toOption
  let mech := settleChain {} 12 mechCost
  let replacing := (s.addTurnFxOn p ally .banishInstead).addTurnFxOn q ally .banishInstead
  let chooseBanish := Action.mk (.player p)
    (.activate gear 2 ⟨0, []⟩ [] [] none (some q) (some ally))
  let (banished, replacementEvents) ← (step 100 replacing chooseBanish).toOption
  let banishedCard ← banished.firstOf p .banishment "RAD-011"
  return (legalFrameActions s).contains sacrificeGear &&
    (step 100 s (action 1 none)).toOption.isNone &&
    (step 100 s (action 1 (some ally))).toOption.isNone &&
    (step 100 s (action 2 (some foe))).toOption.isNone &&
    gold.tired goldToken == some true && gold.tired gear == some true &&
    recruitCost.locate gear == none && recruitCost.countIn p .trash "RAD-022" == 1 &&
    events.contains (.exhausted gear) && !events.contains (.chosenByAbility p gear) &&
    recruit.countNamed p .base "Recruit" == 1 &&
    mechCost.locate ally == some (.player p .base) &&
    (mechCost.obj? ally).any (fun o => o.exhausted && o.damage == 0) &&
    mech.countNamed p .base "Mech" == 1 &&
    replacementEvents.contains (.banished q p banishedCard) &&
    !replacementEvents.contains (.died banishedCard p)

-- Stranger checks the threshold on resolution and permits declining the return.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field ← s.battlefields[0]?
  let hiddenField ← s.battlefields[1]?
  let (s, stranger) ← put s p "RAD-107" .hidden
  let (s, _) ← putAt s p "RAD-011" hiddenField
  let (s, removed) ← putAt s p "RAD-011" field
  let (s, _) ← putAt s p "RAD-011" field
  let (s, _) ← putAt s p "RAD-011" field
  let (s, foe) ← putAt s q "RAD-067" field
  let s := (s.control p hiddenField).modObj stranger (fun o =>
    { o with hiddenAt := some hiddenField, hiddenTurn := some (s.turn - 1) })
  let (revealing, _) ← (step 100 s ⟨.player p, .activate stranger 2 ⟨0, []⟩ []⟩).toOption
  let rec passToTrigger : Nat → GameState → Option GameState
    | 0, _ => none
    | steps + 1, state =>
      match state.pending with
      | .triggerOrder .. :: _ => some state
      | .chainPass who _ :: _ =>
        ((step 100 state ⟨.player who, .pass⟩).toOption.map Prod.fst).bind (passToTrigger steps)
      | _ => none
  let waiting ← passToTrigger 8 revealing
  let (chosen, _) ← (step 100 waiting ⟨.player p, .putTrigger 0 [field, foe] (.pay [])⟩).toOption
  let returned := settleChain {} 12 chosen
  let declined := settleChain { yes := false } 12 chosen
  let reduced := settleChain {} 12 (recallFx true chosen removed).1
  return returned.countIn q .hand "RAD-067" == 1 &&
    declined.locate foe == some .battlefieldZone && reduced.locate foe == some .battlefieldZone &&
    (returned.inPlay.find? (fun id => (returned.cardDef? id).any (·.id == ⟨"RAD-107"⟩))).any
      (fun id => (returned.obj? id).any (·.loc == some hiddenField))

end RiftboundTest
