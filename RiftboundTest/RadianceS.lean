module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance delayed draws and Battlefield play history -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Each copy of Fanfare counts only later Unit plays by that player and stops after three.
#guard radianceCase fun s => do
  let p := s.me
  let (s, first) ← put s p "RAD-047" .hand
  let (s, second) ← put s p "RAD-047" .hand
  let (s, gear) ← put s p "RAD-089" .hand
  let (s, u1) ← put s p "RAD-088" .hand
  let (s, u2) ← put s p "RAD-088" .hand
  let (s, u3) ← put s p "RAD-088" .hand
  let (s, u4) ← put s p "RAD-088" .hand
  let (s, u5) ← put s p "RAD-088" .hand
  let (s, opponentUnit) ← put s s.you "RAD-088" .hand
  let s ← (List.range 6).foldlM (fun g _ => (put g p "RAD-011" .mainDeck).map Prod.fst) s
  let draws (t : GameState) := t.drawLog.count (p, t.turn)
  let waiting ← play s p first
  let afterGear ← play waiting p gear
  let afterOpponent ← play { afterGear with pending := [.priority s.you] } s.you opponentUnit
  let one ← play { afterOpponent with pending := [.priority p] } p u1
  let withBoth ← play one p second
  let two ← play withBoth p u2
  let three ← play two p u3
  let four ← play three p u4
  let five ← play four p u5
  let (expired, _) ← (advance 100 { withBoth with pending := [.expireTurn, .priority p] } []).toOption
  let later ← play expired p u2
  return waiting.countIn p .trash "RAD-047" == 1 &&
    draws afterGear == draws waiting && draws afterOpponent == draws waiting &&
    draws one == draws waiting + 1 && draws two == draws waiting + 3 &&
    draws three == draws waiting + 5 && draws four == draws waiting + 6 &&
    draws five == draws four && draws later == draws expired

-- A move or a Base play does not earn Hold 'Em's discount. Losing the played Gear does not undo it.
#guard radianceCase fun s => do
  let p := s.me
  let (s, holdEm) ← put s p "RAD-070" .hand
  let (s, unit) ← put s p "RAD-088" .hand
  let (s, root) ← put s p "RAD-024" .hand
  let field := s.bf0
  let based ← play (s.control p field) p unit
  let boardUnit ← based.firstOf p .base "RAD-088"
  let moved := (moveByEffect p (some field) based boardUnit).1
  let played ← play moved p root [field]
  let gear ← played.inPlay.find? (fun id => (played.cardDef? id).any (·.id == ⟨"RAD-024"⟩))
  let destroyed := (killOrSave played gear).1
  let boosted ← cast (destroyed.fund p 1) p holdEm ⟨1, []⟩ [boardUnit]
  let (destroyed, borrowed) ← put destroyed s.you "RAD-070" .banishment
  let effectDiscount := (limitedSpellOptions destroyed p borrowed (.reduceEnergy 0)).any (fun plan =>
    plan.targets == [boardUnit] && plan.cost == ⟨1, []⟩)
  return based.energyCost? p holdEm == some 3 && moved.energyCost? p holdEm == some 3 &&
    destroyed.energyCost? p holdEm == some 1 && effectDiscount &&
    boosted.mightEff boardUnit == moved.mightEff boardUnit + 3

-- Hunters' Circle discounts the destination in hand and effect plays, only on one's own turn.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s p "RAD-163"
  let (s, first) ← put s p "RAD-024" .hand
  let (s, second) ← put s p "RAD-024" .hand
  let (s, other) ← put s q "RAD-024" .hand
  let s := s.fund p 1
  let act (card : ObjId) := Action.mk (.player p) (.playCard card ⟨1, []⟩ [field])
  let effectHasPrice (state : GameState) (who : PlayerId) (card : ObjId) (price : Nat) :=
    (permanentPlayOptions state who card { price := .reduceEnergy 0 }).any (fun plan =>
      plan.battlefield == some field && plan.cost == ⟨price, []⟩)
  let (entered, _) ← (step 100 s (act first)).toOption
  let (expired, _) ← (advance 100 { entered with pending := [.expireTurn, .priority p] } []).toOption
  return (legalFrameActions s).contains (act first) &&
    !(legalFrameActions (entered.fund p 1)).contains (act second) &&
    (legalFrameActions (expired.fund p 1)).contains (act second) &&
    effectHasPrice s p first 1 && effectHasPrice entered p second 2 &&
    effectHasPrice entered q other 2 && effectHasPrice { entered with active := some q } q other 1

-- Rakelstake records the first play separately for each player. A Base play does not use it.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, field) ← putBf s p "RAD-165"
  let (s, a) ← put s p "RAD-024" .hand
  let (s, b) ← put s p "RAD-024" .hand
  let (s, c) ← put s q "RAD-024" .hand
  let (s, atBase) ← put s p "RAD-088" .hand
  let (s, _) ← put s q "RAD-011" .mainDeck
  let based ← play s p atBase
  let prediction (g : GameState) (who : PlayerId) :=
    match g.pending with | .predict player .. :: _ => player == who | _ => false
  let first ← play based p a [field]
  let .predict who _ top _ _ _ :: _ := first.pending | none
  let (continued, _) ← (step 100 first ⟨.player who, .predictPick top false⟩).toOption
  let repeatPlay ← play continued p b [field]
  let other ← play { repeatPlay with pending := [.priority q] } q c [field]
  let (newTurn, _) ← (advance 100 { continued with pending := [.expireTurn, .priority p] } []).toOption
  let reset ← play newTurn p b [field]
  return prediction first p && !prediction repeatPlay p && prediction other q && prediction reset p

end RiftboundTest
