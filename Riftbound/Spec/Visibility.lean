module

public import Riftbound.State.GameState

/-! # Default visibility of card faces (CR 128)

A zone's default privacy can be checked independently of the card's identifiers. Temporary
revelation, inspection and setup choices are additional information for a full player view.
-/

public section

namespace Riftbound

/-- A zone's card faces visible to a player under default privacy (CR 128.2). The outer `none`
means the zone is engine bookkeeping. A `none` within the list is a card back or an object without
a card face. The projection excludes temporary information from effects such as Reveal (CR 425). -/
def GameState.zoneCardFaces (s : GameState) (viewer : PlayerId) (z : Zone) :
    Option (List (Option CardId)) :=
  let ids := s.zone z
  let face (id : ObjId) := (s.obj? id).bind (·.kind.cardId?)
  let backs := List.replicate ids.length none
  match z with
  | .player _ .mainDeck | .player _ .runeDeck => some backs
  | .player owner .hand => some (if viewer == owner then ids.map face else backs)
  | .player _ .hidden => some (ids.map fun id => do
      let object ← s.obj? id
      if viewer == object.controller then object.kind.cardId? else none)
  | .player _ .setAside | .player _ .outOfGame | .player _ .reserveLegends => none
  | .battlefieldZone | .chain | .player _ .base | .player _ .legendZone | .player _ .championZone
  | .player _ .trash | .player _ .banishment => some (ids.map face)

/-- The default view of the Main Deck depends only on the number of cards (CR 108.4.d-108.4.e). -/
theorem GameState.zoneCardFaces_mainDeck (s : GameState) (viewer owner : PlayerId) :
    s.zoneCardFaces viewer (.player owner .mainDeck) =
      some (List.replicate (s.zone (.player owner .mainDeck)).length none) := by
  simp [GameState.zoneCardFaces]

/-- The default view of the Rune Deck has no information about its order (CR 108.5.d). -/
theorem GameState.zoneCardFaces_runeDeck (s : GameState) (viewer owner : PlayerId) :
    s.zoneCardFaces viewer (.player owner .runeDeck) =
      some (List.replicate (s.zone (.player owner .runeDeck)).length none) := by
  simp [GameState.zoneCardFaces]

/-- Another player's hand exposes its size while its faces remain private (CR 108.7.c, 108.7.e). -/
theorem GameState.zoneCardFaces_otherHand (s : GameState) {viewer owner : PlayerId}
    (different : viewer ≠ owner) : s.zoneCardFaces viewer (.player owner .hand) =
      some (List.replicate (s.zone (.player owner .hand)).length none) := by
  simp [GameState.zoneCardFaces, different]

/-- Facedown cards controlled by other players disclose no faces (CR 107.3.f, 128.4). -/
theorem GameState.zoneCardFaces_hidden_other (s : GameState) (viewer seat : PlayerId)
    (different : ∀ id ∈ s.zone (.player seat .hidden), ∀ obj,
      s.obj? id = some obj → viewer ≠ obj.controller) :
    s.zoneCardFaces viewer (.player seat .hidden) =
      some (List.replicate (s.zone (.player seat .hidden)).length none) := by
  simp only [GameState.zoneCardFaces, Option.some.injEq]
  calc
    _ = (s.zone (.player seat .hidden)).map (fun _ => none) := by
      apply List.map_congr_left
      intro id member
      cases found : s.obj? id with
      | none => rfl
      | some obj => simp [different id member obj found]
    _ = _ := List.map_const'

end Riftbound

end
