module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance direct plays from Banishment and their expiry -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Both of the Anvil's triggers grant permission for their own card. The normal play action
-- still pays the unit's resources, and the permission expires as soon as Ending begins.
#guard radianceCase fun s => do
  let p := s.me
  let (s, anvil) ← put s p "RAD-012" .hand
  let (s, ordinary) ← put s p "RAD-088" .banishment
  let (s, _) ← put s p "RAD-047" .mainDeck
  let (s, _) ← put s p "RAD-088" .mainDeck
  let claims := Zone.player p .banishment
  let act (g : GameState) (kind : ActionKind) := (step 100 g ⟨.player p, kind⟩).toOption
  let (played, _) ← act (s.fund p 5 (body := 1) (chaos := 1)) (.playCard anvil ⟨1, []⟩ [])
  let first := settleChain {} 25 played
  let gear ← first.inPlay.find? (fun id => (first.cardDef? id).any (·.id == ⟨"RAD-012"⟩))
  let unit ← (first.zone claims).find? (fun id =>
    (first.cardDef? id).any (·.id == ⟨"RAD-088"⟩) && id != ordinary)
  let (used, _) ← act first (.activate gear 2 ⟨2, [.chaos], none⟩ [])
  let second := settleChain {} 25 used
  let spell ← (second.zone claims).find? (fun id => (second.cardDef? id).any (·.id == ⟨"RAD-047"⟩))
  let expired := { second with phase := .ending }
  let (arrived, _) ← act second (.playCard unit ⟨2, [.body]⟩ [])
  let direct := (arrived.fund p 3).playSources p
  let (casted, _) ← act (arrived.fund p 3) (.playCard spell ⟨3, []⟩ [])
  let done := settleChain {} 25 casted
  return (second.playSources p).contains unit && (second.playSources p).contains spell &&
    !(second.playSources p).contains ordinary && !(expired.playSources p).contains unit &&
    !(expired.playSources p).contains spell && arrived.countIn p .base "RAD-088" == 1 &&
    (arrived.poolOf p).body == 0 && (arrived.poolOf p).energy == 0 &&
    direct.contains spell && done.countIn p .trash "RAD-047" == 1

-- Leaving during another player's turn or during the owner's Ending Phase sets the deadline
-- at the start of the owner's following Ending Phase.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, gear) ← put s p "RAD-012" .base
  let (s, _) ← put s p "RAD-088" .mainDeck
  let leaves (g : GameState) := do
    let result := killOrSave g gear
    let (triggered, _) ← (advance 100 (result.1.withTriggers result.2) []).toOption
    return settleChain {} 25 triggered
  let next (g : GameState) (actor : PlayerId) :=
    { beginTurnStep g [] with phase := .main, pending := [.priority actor] }
  let onOppTurn := next s q
  let a ← leaves onOppTurn
  let b ← leaves { s with phase := .ending }
  let valid (g : GameState) :=
    (g.zone (.player p .banishment)).any (fun id => (g.playSources p).contains id)
  let aNext := next a p
  let bNext := next (next b q) p
  return onOppTurn.active == some q && aNext.active == some p && bNext.active == some p &&
    valid a && valid b && valid aNext && valid bNext &&
    !valid { aNext with phase := .ending } && !valid { bNext with phase := .ending }

end RiftboundTest
