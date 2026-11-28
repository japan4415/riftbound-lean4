module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Unit token replacement and Accelerate -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

private meta def playedTokens (s : GameState) (p : PlayerId) : List ObjId :=
  s.inPlay.filter (fun id => (s.obj? id).any (fun o => o.controller == p &&
    (match o.kind with | .token _ => true | _ => false)))

-- Heimerdinger can replace any subset of a simultaneous group, keeping placement and the
-- instruction to enter ready. His effect is inactive at a Base.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, heimer) ← putAt (s.control p field) p "RAD-132" field
  let env : Env := { slots := [.obj field] }
  let body := Effect.prim (.createAt "Recruit" (.const 2) (.slot 0) true)
  let pending := [.run p heimer env (.cons body .nil), .priority p]
  let before := { s with pending }
  let (asked, _) ← (advance 100 before []).toOption
  let replace : Action := ⟨.player p, .decide false⟩
  let keep : Action := ⟨.player p, .decide true⟩
  let (second, _) ← (step 100 asked replace).toOption
  let (formed, events) ← (step 100 second keep).toOption
  let home := before.modObj heimer (fun o => { o with loc := none })
  let (unmodified, _) ← (advance 100 home []).toOption
  let tokens := playedTokens formed p
  return body.observedWorkSupported && decisionRunAnswerWorkSupported asked replace &&
    decisionRunAnswerWorkSupported second keep &&
    (playedTokens asked p).isEmpty && (playedTokens second p).isEmpty && tokens.length == 2 &&
    (events.filter (fun | .tokenPlayed .. => true | _ => false)).length == 2 &&
    tokens.all (fun id => (formed.obj? id).any (fun o => o.loc == some field && !o.exhausted)) &&
    tokens.any (fun id => (formed.cardDef? id).any (·.name == "Mech")) &&
    tokens.any (fun id => (formed.cardDef? id).any (·.name == "Recruit")) &&
    (playedTokens unmodified p).all (fun id => (unmodified.cardDef? id).any (·.name == "Recruit"))

-- Zilean's decision is before entry. Declining leaves the use available, accepting uses it
-- for the rest of the turn, and the same object can use it again on a later turn.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, zilean) ← putAt (s.control p s.bf0) p "UNL-086" s.bf0
  let play (t : GameState) (who : PlayerId) :=
    let effect := Effect.prim (.create "Recruit" (.const 1) .atBase true)
    (advance 100 { t with pending := [.run who zilean {} (.cons effect .nil), .priority who] } []).toOption
  let (asked, firstEvents) ← play s p
  let (declined, declineEvents) ← (step 100 asked ⟨.player p, .decide false⟩).toOption
  let (again, _) ← play declined p
  let (accepted, playEvents) ← (step 100 again ⟨.player p, .decide true⟩).toOption
  let (used, usedEvents) ← play accepted p
  let (later, _) ← play { used with turn := used.turn + 1 } p
  let (outside, _) ← play s q
  let (atBase, _) ← play (s.modObj zilean fun o => { o with loc := none }) p
  let tokens (events : List Event) := events.filter (fun | .tokenPlayed .. => true | _ => false)
  return (playedTokens asked p).isEmpty && (tokens firstEvents).isEmpty &&
    (tokens declineEvents).length == 1 && (tokens playEvents).length == 2 &&
    (tokens usedEvents).length == 1 && (playedTokens used p).length == 4 &&
    (playedTokens used p).all (fun id => used.tired id == some false) &&
    (match later.pending with | .eitherDo .. :: _ => true | _ => false) &&
    (playedTokens outside q).length == 1 && (playedTokens atBase p).length == 1

-- Both orderings of Heimerdinger and Zilean are offered. A copy made after substitution is
-- a Mech, while substitution after duplication can change only one of the Recruit plays.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, heimer) ← putAt (s.control p field) p "RAD-132" field
  let (s, _) ← putAt s p "UNL-086" field
  let body := Effect.prim (.create "Recruit" (.const 1) .atBase true)
  let (offer, _) ← (advance 100 { s with pending := [.run p heimer {} (.cons body .nil), .priority p] } []).toOption
  let decide (t : GameState) (yes : Bool) := (step 100 t ⟨.player p, .decide yes⟩).toOption
  let (substituteFirst, _) ← decide offer true
  let (substituted, _) ← decide substituteFirst false
  let (bothMechs, _) ← decide substituted true
  let (duplicateFirst, _) ← decide offer false
  let (duplicated, _) ← decide duplicateFirst true
  let (firstKept, _) ← decide duplicated true
  let (mixed, _) ← decide firstKept false
  return (playedTokens substituted p).isEmpty && (playedTokens firstKept p).isEmpty &&
    bothMechs.countNamed p .base "Mech" == 2 && mixed.countNamed p .base "Mech" == 1 &&
    mixed.countNamed p .base "Recruit" == 1 &&
    (playedTokens mixed p).all (fun id => mixed.tired id == some false)

-- In 2v2 the teammate cannot use these replacements. Two Zileans controlled by the same
-- player each have their own use, and still produce a single simultaneous group.
#guard (do
  let p : PlayerId := ⟨0⟩
  let teammate : PlayerId := ⟨1⟩
  let s := GameState.empty { mode := Mode.teamDuel, ruleSet := .coreOnly } RiftboundCards.db
  let s := { s with phase := .main, turn := 1, active := some p }
  let (s, field) ← putBf s p "OGN-275"
  let (s, first) ← putAt (s.control p field) p "UNL-086" field
  let (s, second) ← putAt s p "UNL-086" field
  let play (who : PlayerId) :=
    let body := Effect.prim (.create "Recruit" (.const 1) .atBase false)
    (advance 100 { s with pending := [.run who first {} (.cons body .nil), .priority who] } []).toOption
  let (other, _) ← play teammate
  let (offered, _) ← play p
  let decide (t : GameState) := (step 100 t ⟨.player p, .decide true⟩).toOption
  let (ordered, _) ← decide offered
  let (firstUse, _) ← decide ordered
  let (both, events) ← decide firstUse
  return s.config.mode.sameSide p teammate && (playedTokens other teammate).length == 1 &&
    (playedTokens firstUse p).isEmpty && (playedTokens both p).length == 3 &&
    (events.filter (fun | .tokenPlayed .. => true | _ => false)).length == 3 &&
    [first, second].all (fun id => both.turnFx.any (·.appliesTo both.turn id (.duplicatedUnitToken none)))
  : Option Bool).getD false

-- The next token Unit can pay one Energy and any Power to enter ready. A second token in
-- the same group enters normally, and declining still uses the next-play effect.
#guard radianceCase fun s => do
  let p := s.me
  let (s, hideout) ← putBf s p "RAD-162"
  let triggered ← fire (s.control p hideout) [.scored p hideout true]
  let body := Effect.prim (.create "Recruit" (.const 2) .atBase false)
  let pending := [.run p hideout {} (.cons body .nil), .priority p]
  let before := ({ triggered with pending } : GameState).fund p 1 (fury := 1)
  let (offered, _) ← (advance 100 before []).toOption
  let buy : Action := ⟨.player p, .decide false⟩
  let decline : Action := ⟨.player p, .decide true⟩
  let (paid, _) ← (step 100 offered buy).toOption
  let (skipped, _) ← (step 100 offered decline).toOption
  let tokens := playedTokens paid p
  return body.observedWorkSupported && decisionRunAnswerWorkSupported offered buy &&
    decisionRunAnswerWorkSupported offered decline &&
    (playedTokens offered p).isEmpty && tokens.length == 2 &&
    (tokens.filter (fun id => paid.tired id == some false)).length == 1 &&
    (paid.poolOf p).energy == 0 && (paid.poolOf p).fury == 0 &&
    (playedTokens skipped p).all (fun id => skipped.tired id == some true) &&
    (skipped.poolOf p).energy == 1 && (skipped.poolOf p).fury == 1 &&
    !(paid.fxOf p).contains .nextUnitAccelerate && !(skipped.fxOf p).contains .nextUnitAccelerate

-- Accelerate can project a Sage Add and then either commit it or enter without paying.
#guard radianceCase fun s => do
  let p := s.me
  let (s, hideout) ← putBf s p "RAD-162"
  let triggered ← fire (s.control p hideout) [.scored p hideout true]
  let (before, sage) ← put (triggered.fund p 0 (fury := 1)) p "UNL-093" .base
  let body := Effect.prim (.create "Recruit" (.const 2) .atBase false)
  let (offer, _) ← (advance 100 { before with pending := [.run p hideout {} (.cons body .nil), .priority p] }
    []).toOption
  let accelerate : Action := ⟨.player p, .decide false⟩
  let select : Action := ⟨.player p, .decide true⟩
  let (funding, _) ← (step 100 offer accelerate).toOption
  let (confirmation, _) ← (step 100 funding select).toOption
  let (done, events) ← (step 100 confirmation select).toOption
  let (declined, _) ← (step 100 confirmation accelerate).toOption
  let ready := (playedTokens done p).filter (fun id => done.tired id == some false)
  let add ← events.findIdx? (fun
    | .activated actor source 0 _ => actor == p && source == sage
    | _ => false)
  let entry ← events.findIdx? (fun | .tokenPlayed .. => true | _ => false)
  return decisionRunAnswerWorkSupported offer accelerate && decisionRunAnswerWorkSupported funding select &&
    decisionRunAnswerWorkSupported confirmation select && decisionRunAnswerWorkSupported confirmation accelerate &&
    (playedTokens confirmation p).isEmpty && confirmation.tired sage == some false &&
    ready.length == 1 && (playedTokens done p).length == 2 && done.tired sage == some true && add < entry &&
    (done.poolOf p).energy == 0 && (done.poolOf p).fury == 0 &&
    declined.tired sage == some false && (declined.poolOf p).fury == 1 &&
    (playedTokens declined p).all (fun id => declined.tired id == some true)

end RiftboundTest
