module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Last Caress -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- The next Unit can enter an opposing Battlefield. A second Unit cannot use that grant.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, caress) ← put s p "RAD-154" .hand
  let (s, first) ← put s p "RAD-011" .hand
  let (s, second) ← put s p "RAD-011" .hand
  let s := (s.control q field).rich p
  let atField (id : ObjId) : Action := ⟨.player p, .playCard id ⟨4, []⟩ [field]⟩
  let allowed ← play s p caress
  let (entered, _) ← (step 100 allowed (atField first)).toOption
  let unit ← (entered.unitsAtOf field p).head?
  let atHome ← play allowed p first
  let home ← atHome.firstOf p .base "RAD-011"
  return (step 100 s (atField first)).toOption.isNone &&
    (entered.obj? unit).any (·.buffed) && (atHome.obj? home).any (·.buffed) &&
    !(entered.playBfOptions p second).contains field && !(atHome.playBfOptions p second).contains field

-- A Unit can be revealed into a field other than where it was hidden and still enters buffed.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let home := s.bf0
  let away ← s.battlefields.find? (· != home)
  let (s, caress) ← put s p "RAD-154" .hand
  let (s, unit) ← put s p "RAD-095" .hidden
  let s := ((s.control p home).control q away).modObj unit
    (fun o => { o with hiddenAt := some home, hiddenTurn := some (s.turn - 1) })
  let allowed ← play s p caress
  let (queued, _) ← (step 100 allowed ⟨.player p, .activate unit 2 ⟨0, [], none⟩ []⟩).toOption
  let redirected := settleChain { fromEnd := some 0 } 18 queued
  let arrived ← (redirected.unitsAtOf away p).head?
  return (redirected.obj? arrived).any (fun o => o.buffed && o.fromHidden) &&
    (redirected.unitsAtOf home p).isEmpty

-- When a single instruction plays several Unit tokens, the grant buffs the first.
#guard radianceCase fun s => do
  let p := s.me
  let (s, caress) ← put s p "RAD-154" .hand
  let allowed ← play s p caress
  let body := Effect.prim (.create "Recruit" (.const 2) .atBase false)
  let (created, events) ← (advance 100 { allowed with
    pending := [.run p caress {} (.cons body .nil), .priority p] } []).toOption
  let newUnits := events.filterMap (fun
    | .tokenPlayed _ id => some id
    | _ => none)
  let [first, second] := newUnits | none
  return (created.obj? first).any (·.buffed) && !(created.obj? second).any (·.buffed) &&
    !(created.fxOf p).contains .nextUnitAnywhereBuffed

end RiftboundTest
