module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # The two-mode choices of Encore -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Two distinct modes are finalized together. The same Unit can be selected independently
-- for the damage and for the Might increase, and the increase can name a second Unit.
#guard radianceCase fun s => do
  let p := s.me
  let (s, encore) ← put s p "RAD-152" .hand
  let (s, a) ← put s p "RAD-060" .base
  let (s, b) ← put s p "RAD-067" .base
  let ready := s.fund p 3 (fury := 1) (mind := 1)
  let play (dom : Domain) (pick : SpellPick) : Action :=
    ⟨.player p, .playCard encore ⟨3, [dom]⟩ [a, a, b] none none pick⟩
  let (queued, _) ← (step 100 ready (play .mind (.mode 1))).toOption
  let done := settleChain {} 15 queued
  return (step 100 ready (play .fury (.mode 1))).toOption.isNone &&
    (step 100 ready (play .mind .plain)).toOption.isNone &&
    (step 100 ready (play .mind (.mode 6))).toOption.isNone &&
    (done.obj? a).any (·.damage == 2) && (done.obj? b).any (·.damage == 0) &&
    done.mightNow a == some 9 && done.mightNow b == some 9

-- This pair plays two Recruits to different legal destinations, then draws the selected
-- looked-at card and recycles the other original top card.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, _) ← putAt (s.control p field) p "RAD-060" field
  let (s, encore) ← put s p "RAD-152" .hand
  let (s, draw) ← put s p "RAD-011" .mainDeck
  let (s, recycle) ← put s p "RAD-047" .mainDeck
  let deck := Zone.player p .mainDeck
  let (queued, _) ← (step 100 (s.fund p 3 (order := 1))
    ⟨.player p, .playCard encore ⟨3, [.order]⟩ [] none none (.mode 4)⟩).toOption
  let (passed, _) ← (step 100 queued ⟨.player p, .pass⟩).toOption
  let (recruit, _) ← (step 100 passed ⟨.player q, .pass⟩).toOption
  let (nextRecruit, _) ← (step 100 recruit ⟨.player p, .decide true⟩).toOption
  let (looking, _) ← (step 100 nextRecruit ⟨.player p, .decide false⟩).toOption
  let (done, _) ← (step 100 looking ⟨.player p, .choose draw⟩).toOption
  let hasRecruit (ids : List ObjId) :=
    ids.any (fun id => (done.cardDef? id).any (·.name == "Recruit"))
  return hasRecruit (done.zone (.player p .base)) && hasRecruit (done.unitsAtOf field p) &&
    (done.zone (.player p .hand)).any (fun id => (done.obj? id).any (·.formerId == some draw)) &&
    done.zone deck == ((s.zone deck).erase draw).erase recycle ++ [recycle]

end RiftboundTest
