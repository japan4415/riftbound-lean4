module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance Deploy and triggered costs -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Portal restricts both effects to its Battlefield and pays printed Power as well as Deflect.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field ← s.battlefields[0]?
  let away ← s.battlefields[1]?
  let (s, localUnit) ← putAt s p "RAD-011" field
  let (s, distantUnit) ← putAt s p "RAD-011" away
  let (s, foe) ← putAt s q "RAD-011" field
  let (s, portal) ← put s p "RAD-087" .hand
  let s := (addTempKw ⟨.deflect, .amount 1⟩ .never (s.control p field) foe).1
  let s := ((s.tire localUnit).tire distantUnit).tire foe
  let enter (fury body : Nat) := (step 100 (s.fund p 2 fury 0 body)
    ⟨.player p, .playCard portal ⟨2, []⟩ [field]⟩).toOption.map Prod.fst
  let onlyBody ← enter 0 1
  let onlyFury ← enter 2 0
  let enough ← enter 1 1
  let pay (target : ObjId) := Action.mk (.player p) (.putTrigger 0 [target] (.pay []))
  let (paid, _) ← (step 100 enough (pay foe)).toOption
  let ready := settleChain {} 12 paid
  return (step 100 onlyBody (pay foe)).toOption.isNone &&
    (step 100 onlyFury (pay localUnit)).toOption.isNone &&
    (step 100 enough (pay distantUnit)).toOption.isNone &&
    enough.hasKw localUnit .ganking && !enough.hasKw distantUnit .ganking &&
    !enough.hasKw foe .ganking && (paid.poolOf p).totalPower == 0 &&
    ready.tired foe == some false && ready.tired localUnit == some true

-- Exemplar finalizes with both costs. The Gear's departure cannot change the destination.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, legend) ← put s p "RAD-155" .legendZone
  let (s, movedUnit) ← put s p "RAD-011" .base
  let (s, dreamroot) ← put s p "RAD-024" .hand
  let s := s.control p field
  let enter (g : GameState) :=
    (step 100 g ⟨.player p, .playCard dreamroot ⟨2, []⟩ [field]⟩).toOption.map Prod.fst
  let paidWith := s.fund p 2 1
  let noPower ← enter (s.fund p 2)
  let exhausted ← enter (paidWith.tire legend)
  let choices ← enter paidWith
  let finish := Action.mk (.player p) (.putTrigger 0 [movedUnit] (.pay []))
  let (paid, _) ← (step 100 choices finish).toOption
  let (withRune, rune) ← put (s.fund p 2) p "OGN-007" .base
  let staged ← enter withRune
  let (locked, _) ← (step 100 staged
    ⟨.player p, .prepareTrigger 0 [movedUnit] (.pay [])⟩).toOption
  let (added, _) ← (step 100 locked ⟨.player p, .triggerAdd (.rune rune true)⟩).toOption
  let (committed, _) ← (step 100 added finish).toOption
  let gear ← paid.inPlay.find? (fun id => (paid.cardDef? id).any (·.id == ⟨"RAD-024"⟩))
  let resolved := settleChain {} 12 (killOrSave paid gear).1
  return (step 100 noPower finish).toOption.isNone &&
    (step 100 exhausted finish).toOption.isNone &&
    paid.tired legend == some true && (paid.poolOf p).totalPower == 0 &&
    added.tired legend == some false && added.locate rune == some (.player p .base) &&
    committed.tired legend == some true && committed.locate rune == none &&
    (committed.poolOf p).totalPower == 0 && (resolved.obj? movedUnit).any (·.loc == some field)

end RiftboundTest
