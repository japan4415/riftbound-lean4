module

public import Riftbound.Spec.Visibility
public import Riftbound.Rules.Passive

/-! # The board as seen from a seat (CR 107-109, 128) -/

@[expose] public section

namespace Riftbound

/-- Zones whose occupants can be referenced by a public position. -/
def Zone.hasPublicPositions : Zone → Bool
  | .battlefieldZone | .chain | .player _ .base | .player _ .legendZone
  | .player _ .championZone | .player _ .trash | .player _ .banishment => true
  | _ => false

/-- The position of an object in a single snapshot. It is not an engine object identifier. -/
structure ViewPosition where
  /-- The zone containing the object. -/
  zone : Zone
  /-- Its zero-based position in that zone. -/
  index : Nat
deriving DecidableEq, Repr

/-- Translate an engine identifier to a position only if its zone is public. -/
def GameState.publicPosition (s : GameState) (id : ObjId) : Option ViewPosition := do
  let zone ← s.locate id
  if !zone.hasPublicPositions then none else
    (s.zone zone).findIdx? (· == id) |>.map (ViewPosition.mk zone)

/-- References never point into a private deck, hand, or facedown zone. -/
theorem GameState.publicPosition_visible {s : GameState} {id : ObjId} {pos : ViewPosition}
    (h : s.publicPosition id = some pos) : pos.zone.hasPublicPositions = true := by
  unfold GameState.publicPosition at h
  cases whereAt : s.locate id with
  | none => simp [whereAt] at h
  | some zone =>
    cases hz : zone.hasPublicPositions with
    | false => simp [whereAt, hz] at h
    | true =>
      have found : ((s.zone zone).findIdx? (· == id)).map (ViewPosition.mk zone) = some pos := by
        simpa [whereAt, hz] using h
      obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp found
      exact hz

/-- Details that can be read from a face-up Board object (CR 109.2). -/
structure BoardObjectView where
  /-- The object's owner. -/
  owner : PlayerId
  /-- The object's current controller. -/
  controller : PlayerId
  /-- The Battlefield where it stands, or none when it is at Base or has no location. -/
  atBattlefield : Option ViewPosition
  /-- The public Unit an Equipment is attached to. -/
  attachedTo : Option ViewPosition
  /-- The controller of the Battlefield itself. -/
  control : Option PlayerId
  /-- The player contesting the Battlefield. -/
  contested : Option PlayerId
  /-- The object's effective card, after copy effects. -/
  effectiveCard : Option CardId
  /-- Its types, including effects that animate Gear. -/
  types : List CardType
  /-- The object's Might, if applicable. -/
  might : Option Int
  /-- Its effective keywords. -/
  keywords : List KeywordInst
  /-- Its Rune domain, if it is a Rune. -/
  rune : Option Domain
  /-- The damage marked on it. -/
  damage : Nat
  /-- Whether it is exhausted. -/
  exhausted : Bool
  /-- Whether it has a buff. -/
  buffed : Bool
  /-- Whether it is stunned. -/
  stunned : Bool
  /-- The number of times it is Empowered. -/
  empowerCount : Nat
  /-- The card named by a choice on the Board object. -/
  namedCard : Option CardId
deriving DecidableEq, Repr

/-- What the seat can see in a game zone. -/
inductive ViewCard where
  /-- A card back or a visible face without public Board attributes. -/
  | plain (face : Option CardId)
  /-- A card in a public Facedown Zone. Only an entitled viewer receives its face (CR 107.3.f). -/
  | hidden (face : Option CardId) (controller : PlayerId) (atBattlefield : Option ViewPosition)
  /-- A face-up card or token on the Board. -/
  | board (face : CardId) (details : BoardObjectView)
  /-- A Spell on the Chain with its public targets (CR 108.1.b). -/
  | spell (face : CardId) (controller : PlayerId) (targets : List (Option ViewPosition))
  /-- An ability on the Chain, named by its source card and ability index. -/
  | ability (sourceCard : CardId) (index : Nat) (controller : PlayerId)
      (source : Option ViewPosition) (targets : List (Option ViewPosition))
deriving DecidableEq, Repr

/-- Project the public attributes of a Board object. -/
def boardDetails (s : GameState) (id : ObjId) (obj : Object) : BoardObjectView :=
  let defn := s.cardDef? id
  { owner := obj.owner
    controller := obj.controller
    atBattlefield := obj.loc.bind s.publicPosition
    attachedTo := obj.attached.bind s.publicPosition
    control := obj.control
    contested := obj.contested
    effectiveCard := defn.map (·.id)
    types := defn.elim [] (·.types)
    might := s.mightNow id
    keywords := s.activeKeywords id
    rune := obj.runeDomain
    damage := obj.damage
    exhausted := obj.exhausted
    buffed := obj.buffed
    stunned := obj.stunned
    empowerCount := obj.empowerCount
    namedCard := obj.namedCard }

/-- Project the visible attributes of a card in a zone, given its visible face. -/
def viewObject (s : GameState) (zone : Zone) (id : ObjId) (face : Option CardId) :
    ViewCard :=
  match s.obj? id with
  | none => .plain face
  | some obj => match zone with
    | .player _ .hidden => .hidden face obj.controller (obj.hiddenAt.bind s.publicPosition)
    | .chain =>
      let targets := obj.targets.map s.publicPosition
      match obj.kind with
      | .chainAbility card index source =>
        .ability card index obj.controller (s.publicPosition source) targets
      | _ => face.elim (.plain none) (fun card => .spell card obj.controller targets)
    | _ => face.elim (.plain none) (fun card => .board (obj.originalToken.getD card) (boardDetails s id obj))

/-- Render known hand faces in card-code order, with an indistinguishable back for each unknown
card. The sequence of an untargeted hand has no rules meaning (CR 108.7.d). -/
def handView (faces : List (Option CardId)) : List ViewCard :=
  let shown := (faces.filterMap id).mergeSort (fun a b => a.code ≤ b.code)
  shown.map (fun face => .plain (some face)) ++ List.replicate (faces.length - shown.length) (.plain none)

/-- The board and card slots that this seat can see in a zone, including current disclosures.
Hidden decks expose neither object identifiers nor attributes of their unrevealed cards. -/
def GameState.zoneView (s : GameState) (viewer : PlayerId) (zone : Zone) :
    Option (List ViewCard) :=
  (s.resolutionZoneCardFaces viewer zone).map fun faces =>
    match zone with
    | .player _ .hand => handView faces
    | .battlefieldZone | .chain | .player _ .base | .player _ .legendZone | .player _ .hidden =>
      ((s.zone zone).zip faces).map (fun (id, face) => viewObject s zone id face)
    | _ => faces.map ViewCard.plain

/-- When none of its cards are disclosed, a Main Deck's view depends only on its size
(CR 108.4.d-108.4.e). -/
theorem GameState.zoneView_mainDeck_of_disjoint {s : GameState} {viewer : PlayerId}
    (owner : PlayerId) (h : ∀ id ∈ s.zone (.player owner .mainDeck), id ∉ s.resolutionDisclosedFaces viewer) :
    s.zoneView viewer (.player owner .mainDeck) =
      some (List.replicate (s.zone (.player owner .mainDeck)).length (.plain none)) := by
  simp [GameState.zoneView, GameState.resolutionZoneCardFaces_of_disjoint _ _ _ h,
    GameState.zoneCardFaces_mainDeck]

/-- When none of its cards are disclosed, a Rune Deck's view depends only on its size
(CR 108.5). -/
theorem GameState.zoneView_runeDeck_of_disjoint {s : GameState} {viewer : PlayerId}
    (owner : PlayerId) (h : ∀ id ∈ s.zone (.player owner .runeDeck), id ∉ s.resolutionDisclosedFaces viewer) :
    s.zoneView viewer (.player owner .runeDeck) =
      some (List.replicate (s.zone (.player owner .runeDeck)).length (.plain none)) := by
  simp [GameState.zoneView, GameState.resolutionZoneCardFaces_of_disjoint _ _ _ h,
    GameState.zoneCardFaces_runeDeck]

/-- Unless a card in it is disclosed, another player's hand exposes only its size (CR 108.7). -/
theorem GameState.zoneView_otherHand_of_disjoint {s : GameState} {viewer owner : PlayerId}
    (different : viewer ≠ owner) (h : ∀ id ∈ s.zone (.player owner .hand), id ∉ s.resolutionDisclosedFaces viewer) :
    s.zoneView viewer (.player owner .hand) =
      some (List.replicate (s.zone (.player owner .hand)).length (.plain none)) := by
  simp [GameState.zoneView, GameState.resolutionZoneCardFaces_of_disjoint _ _ _ h,
    GameState.zoneCardFaces_otherHand s different, handView]

/-- With no active disclosure, a Main Deck's view depends only on its size. -/
theorem GameState.zoneView_mainDeck {s : GameState} {viewer : PlayerId}
    (owner : PlayerId) (h : s.resolutionDisclosedFaces viewer = []) :
    s.zoneView viewer (.player owner .mainDeck) =
      some (List.replicate (s.zone (.player owner .mainDeck)).length (.plain none)) :=
  s.zoneView_mainDeck_of_disjoint owner (by simp [h])

/-- With no active disclosure, a Rune Deck's view depends only on its size. -/
theorem GameState.zoneView_runeDeck {s : GameState} {viewer : PlayerId}
    (owner : PlayerId) (h : s.resolutionDisclosedFaces viewer = []) :
    s.zoneView viewer (.player owner .runeDeck) =
      some (List.replicate (s.zone (.player owner .runeDeck)).length (.plain none)) :=
  s.zoneView_runeDeck_of_disjoint owner (by simp [h])

/-- With no active disclosure, another player's hand exposes only its size. -/
theorem GameState.zoneView_otherHand {s : GameState} {viewer owner : PlayerId}
    (different : viewer ≠ owner) (h : s.resolutionDisclosedFaces viewer = []) :
    s.zoneView viewer (.player owner .hand) =
      some (List.replicate (s.zone (.player owner .hand)).length (.plain none)) :=
  s.zoneView_otherHand_of_disjoint different (by simp [h])

/-- Hand sorting and suppression of unknown faces preserve the number of slots. -/
theorem handView_length (faces : List (Option CardId)) :
    (handView faces).length = faces.length := by
  simp only [handView, List.length_append, List.length_map, List.length_mergeSort,
    List.length_replicate]
  exact Nat.add_sub_of_le (List.length_filterMap_le _ _)

/-- The acting seat's hand view has one position for each card. -/
theorem GameState.zoneView_ownHand_length (s : GameState) (p : PlayerId) :
    (s.zoneView p (.player p .hand)).map List.length = some (s.zone (.player p .hand)).length := by
  have length := s.resolutionZoneCardFaces_ownHand_length p
  cases faces : s.resolutionZoneCardFaces p (.player p .hand) with
  | none => simp [faces] at length
  | some visible => simpa [GameState.zoneView, faces, handView_length] using length

end Riftbound

end
