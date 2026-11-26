module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance movement payments -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- An opponent's Gravity Field adds a fee to Standard Move. Declining or lacking it never Exhausts.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, _) ← putAt s q "RAD-062" field
  let (s, unit) ← put s p "RAD-011" .base
  let move (pay : Cost := Cost.zero) : Action :=
    ⟨.player p, .standardMove unit (.battlefield field) pay⟩
  let funded := s.fund p 2 (calm := 1) (mind := 1)
  let (moved, _) ← (step 100 funded (move ⟨1, [.domain .mind]⟩)).toOption
  let flexible := funded.setPool p { funded.poolOf p with any := 1 }
  let (usedFlexible, _) ← (step 100 flexible (move ⟨1, [.any]⟩)).toOption
  let poor := s.fund p 1
  return !(legalFrameActions poor).contains (move ⟨1, [.domain .mind]⟩) &&
    (step 100 poor (move ⟨1, [.domain .mind]⟩)).toOption.isNone &&
    (step 100 funded move).toOption.isNone &&
    (legalFrameActions funded).contains (move ⟨1, [.domain .calm]⟩) &&
    (legalFrameActions funded).contains (move ⟨1, [.domain .mind]⟩) &&
    poor.tired unit == some false && (poor.obj? unit).any (·.loc.isNone) &&
    moved.tired unit == some true && (moved.obj? unit).any (·.loc == some field) &&
    (moved.poolOf p).energy == 1 && (moved.poolOf p).calm == 1 && (moved.poolOf p).mind == 0 &&
    (usedFlexible.poolOf p).any == 0 && (usedFlexible.poolOf p).mind == 1

-- A player who moves other players' Units pays once when they arrive together. Own fees are waived.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, source) ← put s p "RAD-011" .base
  let (s, gear) ← putAt s q "RAD-062" field
  let (s, first) ← put s q "RAD-011" .base
  let (s, second) ← put s q "RAD-011" .base
  let env : Env := { slots := [.obj field, .obj first, .obj second] }
  let body := EffectList.cons (.prim (.move (.slotsFrom 1) (.at_ (.slot 0)))) .nil
  let attempt (g : GameState) := (advance 100 {g with pending := [.run p source env body, .priority p] } []).toOption
  let g := (s.fund p 1 (calm := 1)).fund q 3 (chaos := 3)
  let (waiting, _) ← attempt g
  let answer (yes : Bool) : Action := ⟨.player p, .decide yes⟩
  let (paid, _) ← (step 100 waiting (answer true)).toOption
  let (declined, _) ← (step 100 waiting (answer false)).toOption
  let yours := (s.fund p 0).modObj gear (fun o => { o with controller := p })
  let (own, _) ← attempt yours
  let bothAt (t : GameState) (loc : Option ObjId) :=
    [first, second].all (fun id => (t.obj? id).any (·.loc == loc))
  return bothAt waiting none && bothAt paid (some field) && bothAt declined none && bothAt own (some field) &&
    (paid.poolOf p).energy == 0 && (paid.poolOf p).calm == 0 && paid.poolOf q == g.poolOf q &&
    declined.poolOf p == g.poolOf p && own.poolOf p == yours.poolOf p

-- Charm's caster pays the fee when moving an enemy Unit to the opponent's Gravity Field.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, _) ← putAt s q "RAD-062" field
  let (s, charm) ← put s p "OGN-043" .hand
  let (s, runner) ← put s q "RAD-011" .base
  let s := (s.fund p 2 (calm := 2)).fund q 0
  let (queued, _) ← (step 100 s ⟨.player p, .playCard charm ⟨1, [.calm]⟩ [runner]⟩).toOption
  let location := settleChain {} 2 queued
  let (pick, _) ← (step 100 location ⟨.player p, .decide false⟩).toOption
  let (waiting, _) ← (step 100 pick ⟨.player p, .choose field⟩).toOption
  let (paid, _) ← (step 100 waiting ⟨.player p, .decide true⟩).toOption
  return (waiting.obj? runner).any (·.loc.isNone) &&
    (paid.obj? runner).any (·.loc == some field) && (paid.poolOf p).energy == 0 &&
    (paid.poolOf p).calm == 0 && paid.poolOf q == s.poolOf q

-- Angler Wyrm mandates an eligible pick, but that player can decline the Gravity Field fee.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, _) ← putAt (s.control p field) p "RAD-062" field
  let (s, wyrm) ← putAt s p "RAD-113" field
  let (s, runner) ← put s q "RAD-011" .base
  let start (g : GameState) := do
    let (queued, _) ← (step 100 g ⟨.player p, .activate wyrm 0 ⟨0, []⟩ [] [] (some q)⟩).toOption
    return settleChain {} 2 queued
  let noPay := s.fund q 0
  let funded := (s.fund q 1 (chaos := 1)).fund p 3 (body := 3)
  let waiting ← start funded
  let unfunded ← start (noPay.fund p 3 (body := 3))
  let pay : Action := ⟨.player q, .decide true⟩
  let decline : Action := ⟨.player q, .decide false⟩
  let (paid, _) ← (step 100 waiting pay).toOption
  let (declined, _) ← (step 100 waiting decline).toOption
  let (stayed, _) ← (step 100 unfunded decline).toOption
  return !(legalFrameActions waiting).contains ⟨.player p, .decide true⟩ &&
    !(legalFrameActions unfunded).contains pay &&
    (paid.obj? runner).any (·.loc == some field) &&
    (declined.obj? runner).any (·.loc.isNone) && (stayed.obj? runner).any (·.loc.isNone) &&
    (paid.poolOf q).energy == 0 && (paid.poolOf q).chaos == 0 && paid.poolOf p == funded.poolOf p &&
    declined.poolOf q == funded.poolOf q

-- Deploy kills Gravity Field when an opponent holds that Battlefield, setting off Deathknell.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, card) ← put s q "RAD-062" .hand
  let open_ := { s with active := some q, pending := [.priority q] }.fund q 5 (mind := 1)
  let entered ← cast open_ q card ⟨5, [.mind]⟩ [field]
  let gear ← (entered.zone .battlefieldZone).find? (fun id =>
    (entered.cardDef? id).any (·.id == cid "RAD-062"))
  let resolved ← fire (entered.control p field) [.scored p field false]
  return (entered.obj? gear).any (·.loc == some field) && entered.movementFee p [field] == ⟨1, [.any]⟩ &&
    !resolved.inPlay.contains gear && resolved.countIn q .trash "RAD-062" == 1 &&
    resolved.handN q == entered.handN q + 1

end RiftboundTest
