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
  let (second, _) ← (step 100 asked ⟨.player p, .decide false⟩).toOption
  let (formed, events) ← (step 100 second ⟨.player p, .decide true⟩).toOption
  let home := before.modObj heimer (fun o => { o with loc := none })
  let (unmodified, _) ← (advance 100 home []).toOption
  let tokens := playedTokens formed p
  return (playedTokens asked p).isEmpty && (playedTokens second p).isEmpty && tokens.length == 2 &&
    (events.filter (fun | .tokenPlayed .. => true | _ => false)).length == 2 &&
    tokens.all (fun id => (formed.obj? id).any (fun o => o.loc == some field && !o.exhausted)) &&
    tokens.any (fun id => (formed.cardDef? id).any (·.name == "Mech")) &&
    tokens.any (fun id => (formed.cardDef? id).any (·.name == "Recruit")) &&
    (playedTokens unmodified p).all (fun id => (unmodified.cardDef? id).any (·.name == "Recruit"))

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
  let (paid, _) ← (step 100 offered ⟨.player p, .decide false⟩).toOption
  let (skipped, _) ← (step 100 offered ⟨.player p, .decide true⟩).toOption
  let tokens := playedTokens paid p
  return (playedTokens offered p).isEmpty && tokens.length == 2 &&
    (tokens.filter (fun id => paid.tired id == some false)).length == 1 &&
    (paid.poolOf p).energy == 0 && (paid.poolOf p).fury == 0 &&
    (playedTokens skipped p).all (fun id => skipped.tired id == some true) &&
    (skipped.poolOf p).energy == 1 && (skipped.poolOf p).fury == 1 &&
    !(paid.fxOf p).contains .nextUnitAccelerate && !(skipped.fxOf p).contains .nextUnitAccelerate

end RiftboundTest
