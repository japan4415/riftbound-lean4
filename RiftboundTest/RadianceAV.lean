module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Iron Revenant -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Pay one chosen card from Trash, as part of the Add. The Banish does not put the Add on the Chain.
#guard radianceCase fun s => do
  let p := s.me
  let (s, legend) ← put s p "RAD-143" .legendZone
  let (s, unit) ← put s p "RAD-021" .trash
  let (s, gear) ← put s p "RAD-022" .trash
  let (s, spell) ← put s p "RAD-013" .trash
  let (s, respondingTo) ← onChain s s.you "RAD-013"
  let before := { s with pending := [.chainPass p 0] }
  let action (choice : Option ObjId) : Action := ⟨.player p, .manaAbility legend 0 ⟨0, []⟩ choice⟩
  let (added, events) ← (step 100 before (action (some gear))).toOption
  return (legalFrameActions before).contains (action (some unit)) &&
    (legalFrameActions before).contains (action (some gear)) &&
    !(legalFrameActions before).contains (action (some spell)) &&
    !(legalFrameActions before).contains (action none) &&
    added.zone .chain == [respondingTo] && added.tired legend == some true &&
    added.countIn p .banishment "RAD-022" == 1 && added.restrictedFor p false false == 1 &&
    events.any (fun | .banished byPlayer owner _ => byPlayer == p && owner == p | _ => false)

-- The single Power can finalize a Unit or a Gear. It cannot pay for a Spell's Power.
#guard radianceCase fun s => do
  let p := s.me
  let (s, legend) ← put s p "RAD-143" .legendZone
  let (s, fodder) ← put s p "RAD-011" .trash
  let (s, unit) ← put s p "RAD-021" .hand
  let (s, gear) ← put s p "RAD-022" .hand
  let (s, spell) ← put s p "RAD-013" .hand
  let (s, enemyGear) ← put s s.you "RAD-022" .base
  let s := s.fund p 7
  let (added, _) ← (step 100 s ⟨.player p, .manaAbility legend 0 ⟨0, []⟩ (some fodder)⟩).toOption
  let playUnit : Action := ⟨.player p, .playCard unit ⟨5, [.fury]⟩ []⟩
  let playGear : Action := ⟨.player p, .playCard gear ⟨4, [.fury]⟩ []⟩
  let playSpell : Action := ⟨.player p, .playCard spell ⟨3, [.fury]⟩ [enemyGear] none none (.mode 1)⟩
  let (afterUnit, _) ← (step 100 added playUnit).toOption
  let (afterGear, _) ← (step 100 added playGear).toOption
  let ordinary := added.setPool p { added.poolOf p with fury := 1 }
  return (step 100 added playSpell).toOption.isNone && (step 100 ordinary playSpell).toOption.isSome &&
    (afterUnit.poolOf p).any == 0 && (afterGear.poolOf p).any == 0 &&
    afterUnit.restrictedPowerNotes p .permanentMana == 0 &&
    afterGear.restrictedPowerNotes p .permanentMana == 0

-- Paying the additional cost of a Unit token's play uses the Permanent-only Power as well.
#guard radianceCase fun s => do
  let p := s.me
  let (s, legend) ← put s p "RAD-143" .legendZone
  let (s, fodder) ← put s p "RAD-011" .trash
  let (s, hideout) ← putBf s p "RAD-162"
  let granted ← fire (s.control p hideout) [.scored p hideout true]
  let before := { granted.fund p 1 with pending := [.priority p] }
  let (added, _) ← (step 100 before
    ⟨.player p, .manaAbility legend 0 ⟨0, []⟩ (some fodder)⟩).toOption
  let body := Effect.prim (.create "Recruit" (.const 1) .atBase false)
  let (offered, _) ← (advance 100 { added with
    pending := [.run p hideout {} (.cons body .nil), .priority p] } []).toOption
  let (selecting, _) ← (step 100 offered ⟨.player p, .decide false⟩).toOption
  let paid := settleChain {} 10 selecting
  let token ← (paid.zone (.player p .base)).find? (fun id =>
    (paid.cardDef? id).any (·.name == "Recruit"))
  return !(paid.obj? token).any (·.exhausted) &&
    (paid.poolOf p).energy == 0 && paid.restrictedPowerNotes p .permanentMana == 0

end RiftboundTest
