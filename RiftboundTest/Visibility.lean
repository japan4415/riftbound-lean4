module

import Riftbound.Spec.Visibility
meta import Riftbound.Spec.Visibility
import Riftbound.Engine.Step
meta import Riftbound.Engine.Step
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
    done.resolutionZoneCardFaces p deck == done.zoneCardFaces p deck : Option Bool) == some true

end RiftboundTest
