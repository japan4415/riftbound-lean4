module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance triggered Add timing -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Sneaky Zeebles supplies Power to the interrupted instruction with no priority window.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, zeebles) ← putAt (s.control p field) p "RAD-076" field
  let s := s.fund p 0
  let payment := Frame.run p zeebles {} (.cons (.prim (.pay ⟨0, [.any]⟩)) .nil)
  let suspended := { s with pending := payment :: s.pending }
  let (unused, _) ← (advance 100 suspended []).toOption
  let scored := suspended.withTriggers [.scored p field true]
  let (paid, _) ← (advance 100 scored []).toOption
  let (unspent, _) ← (advance 100 (s.withTriggers [.scored p field true]) []).toOption
  return unused.pending == s.pending && paid.pending == s.pending && unspent.pending == s.pending &&
    paid.zone .chain == [] && unspent.zone .chain == [] &&
    (paid.poolOf p).any == 0 && (unspent.poolOf p).any == 1 &&
    (paid.obj? zeebles).any (fun obj => obj.abilityUses 0 none == 1)

-- The first move adds immediately, the second banishes on the Chain, and the third does neither.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let deck := Zone.player p .mainDeck
  let top ← (s.zone deck).head?
  let (s, _) ← putAt (s.control p field) p "RAD-011" field
  let (s, akali) ← put s p "RAD-SP2" .base
  let s := s.fund p 0
  let (first, _) ← (step 100 s ⟨.player p, .standardMove akali (.battlefield field)⟩).toOption
  let moved ← (first.unitsAtOf field p).find? (fun id =>
    (first.cardDef? id).any (fun d => d.id.code == "RAD-SP2"))
  let ready := first.modObj moved (fun obj => { obj with exhausted := false })
  let (second, _) ← (step 100 ready ⟨.player p, .standardMove moved .base⟩).toOption
  let resolved := settleChain {} 15 second
  let home ← (resolved.zone (.player p .base)).find? (fun id =>
    (resolved.cardDef? id).any (fun d => d.id.code == "RAD-SP2"))
  let readyAgain := resolved.modObj home (fun obj => { obj with exhausted := false })
  let (third, _) ← (step 100 readyAgain ⟨.player p, .standardMove home (.battlefield field)⟩).toOption
  let permission := (resolved.zone (.player p .banishment)).any (fun id =>
    (resolved.obj? id).any (fun obj => obj.formerId == some top && obj.playUntilEnding.isSome))
  return (first.poolOf p).energy == 1 && (first.poolOf p).any == 1 &&
    first.zone .chain == [] && first.pending == s.pending && second.zone deck == s.zone deck &&
    !((second.zone .chain).isEmpty) && (resolved.zone deck).length + 1 == (s.zone deck).length &&
    permission && third.pending == s.pending && third.zone deck == resolved.zone deck &&
    third.poolOf p == first.poolOf p

end RiftboundTest
