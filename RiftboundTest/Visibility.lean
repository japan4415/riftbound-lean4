module

import Riftbound.Spec.PlayerView
meta import Riftbound.Spec.PlayerView
import Riftbound.Engine.Observe
meta import Riftbound.Engine.Observe
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-! # Card faces visible during a resolution -/

namespace RiftboundTest

open Riftbound

private meta def initialViewBoard : Option GameState :=
  GameState.initial db { ruleSet := .coreOnly, mode := .duel } [goodDeck, goodDeck]

private meta def cardFace (s : GameState) (id : ObjId) : Option CardId :=
  (s.obj? id).bind (·.kind.cardId?)

private meta def startEffect (s : GameState) (p : PlayerId) (effect : Effect) :
    Option (GameState × List Event) :=
  let start := { s with
    active := some p
    phase := .main
    pending := [.run p ⟨0⟩ {} (.cons effect .nil), .priority p] }
  (advance 40 start []).toOption

-- Reveal exposes the selected hand cards while the instruction is resolving.
-- A card moved into that hand afterwards keeps its default privacy.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let deck := Zone.player p .mainDeck
  let hand := Zone.player p .hand
  let s ← initialViewBoard
  let first ← (s.zone deck).head?
  let (s, inHand) ← moveObj s first hand
  let newDraw ← (s.zone deck).head?
  let (shown, events) ← startEffect s p (.revealHand .you (.may .nop))
  let (drawn, _) ← moveObj shown newDraw hand
  let (done, _) ← (step 40 shown ⟨.player p, .decide false⟩).toOption
  return events.contains (.handRevealed p [inHand]) &&
    shown.resolutionZoneCardFaces q hand == some [cardFace shown inHand] &&
    drawn.resolutionZoneCardFaces q hand == some [none, cardFace shown inHand] &&
    done.resolutionZoneCardFaces q hand == some [none] : Option Bool) == some true

-- The player making a delegated choice cannot see the other player's inspected cards.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let deck := Zone.player p .mainDeck
  let s ← initialViewBoard
  let first ← (s.zone deck).head?
  let (seen, events) ← startEffect s p (.lookAtTop 1 (.eachPlayer .opponent (.may .nop)))
  let (done, _) ← (step 40 seen ⟨.player q, .decide false⟩).toOption
  return events.contains (.lookedAt p first) &&
    seen.pending.head?.any (fun | .mayDo chooser .. => chooser == q | _ => false) &&
    (seen.resolutionZoneCardFaces p deck).any (fun cards => cards.head? == some (cardFace s first)) &&
    seen.resolutionZoneCardFaces q deck == seen.zoneCardFaces q deck &&
    done.resolutionZoneCardFaces p deck == done.zoneCardFaces p deck : Option Bool) == some true

-- Predict exposes its cards privately and hides them again once the choice ends.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let deck := Zone.player p .mainDeck
  let s ← initialViewBoard
  let first ← (s.zone deck).head?
  let (predicting, events) ← startEffect s p (.prim (.predict (.const 1)))
  let (done, _) ← (step 40 predicting ⟨.player p, .predictPick first false⟩).toOption
  return events.contains (.lookedAt p first) &&
    (predicting.resolutionZoneCardFaces p deck).any (fun cards => cards.head? == some (cardFace s first)) &&
    predicting.resolutionZoneCardFaces q deck == predicting.zoneCardFaces q deck &&
    (predicting.zoneView p deck).any (fun cards => cards.head? == some (.plain (cardFace s first))) &&
    predicting.zoneView q deck == s.zoneView q deck &&
    done.resolutionZoneCardFaces p deck == done.zoneCardFaces p deck &&
    done.zoneView p deck == s.zoneView p deck : Option Bool) == some true

-- A shuffled deck retains only its size, and a hand has no observable order.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let deck := Zone.player p .mainDeck
  let hand := Zone.player p .hand
  let s ← initialViewBoard
  let cards := s.zone deck
  let (s, _) ← moveObj s (← cards.head?) hand
  let (s, _) ← moveObj s (← (s.zone deck).getLast?) hand
  let reordered := (s.setZone hand (s.zone hand).reverse).setZone deck (s.zone deck).reverse
  return s.zoneView p hand == reordered.zoneView p hand &&
    s.zoneView q hand == some [.plain none, .plain none] &&
    s.zoneView p deck == reordered.zoneView p deck : Option Bool) == some true

-- The public location and controller of a facedown card remain visible from both seats.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let deck := Zone.player p .mainDeck
  let hidden := Zone.player p .hidden
  let s ← initialViewBoard
  let battlefield ← (s.zone (.player p .outOfGame)).head?
  let (s, bf) ← moveObj s battlefield .battlefieldZone
  let (s, card) ← moveObj s (← (s.zone deck).head?) hidden
  let s := s.modObj card (fun o => { o with hiddenAt := some bf })
  let pos : Option ViewPosition := some ⟨.battlefieldZone, 0⟩
  return s.zoneView p hidden == some [.hidden (cardFace s card) p pos] &&
    (cardFace s card).isSome && s.zoneView q hidden == some [.hidden none p pos] &&
    s.publicPosition card == none && s.publicPosition bf == pos : Option Bool) == some true

-- A single answer looks at a card, reveals it, then moves it under a fresh object ID.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let deck := Zone.player p .mainDeck
  let hand := Zone.player p .hand
  let s ← initialViewBoard
  let id ← (s.zone deck).head?
  let face ← cardFace s id
  let effect := Effect.seqOf [
    .prim (.lookTop 1), .prim (.revealTop 1), .prim (.draw .you (.const 1))]
  let before := { s with
    active := some p
    phase := .main
    pending := [.mayDo p ⟨0⟩ {} effect .nil, .priority p] }
  let ((after, events), shown) ←
    (stepWithDisclosures 40 before ⟨.player p, .decide true⟩).toOption
  let drawn ← (after.zone hand).head?
  let [privateFace, publicFace] := shown | none
  return drawn != id && (after.obj? id).isNone && cardFace after drawn == some face &&
    privateFace.cards == [face] && events[privateFace.eventIndex]? == some (.lookedAt p id) &&
    publicFace.cards == [face] && events[publicFace.eventIndex]? == some (.revealed p id) &&
    privateFace.visibleTo p && !privateFace.visibleTo q &&
    publicFace.visibleTo p && publicFace.visibleTo q &&
    (after.resolutionDisclosedFaces p).isEmpty : Option Bool) == some true

end RiftboundTest
