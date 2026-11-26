module

public import Riftbound.State.GameState

/-! # Visibility of card faces (CR 128)

The zone provides the default privacy of each card face. A resolving instruction can reveal
particular faces or let a player inspect part of a deck.
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

/-- Every visible zone has one face or back for each of its slots. -/
theorem GameState.zoneCardFaces_length {s : GameState} {viewer : PlayerId} {z : Zone}
    {faces : List (Option CardId)} (h : s.zoneCardFaces viewer z = some faces) :
    faces.length = (s.zone z).length := by
  have lengths := congrArg (Option.map List.length) h
  cases z with
  | player owner kind =>
    by_cases eq : viewer = owner <;> cases kind <;>
      simp [GameState.zoneCardFaces, eq] at lengths <;> exact lengths.symm
  | battlefieldZone | chain =>
    simpa [GameState.zoneCardFaces] using congrArg (Option.map List.length) h.symm

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

/-- The environment carried forward while an effect is resolving. -/
private def Frame.resolutionEnv : Frame → Option Env
  | .run _ _ env _ | .mayDo _ _ env _ _ | .eitherDo _ _ env _ _ _
  | .pickDo _ _ env _ _ _ _ | .guessCardType _ _ _ env _ _ _ _
  | .nameCard _ _ env _ _ _ => some env
  | _ => none

/-- The card faces exposed by an environment to the player whose Main Deck is supplied
(CR 425.1, 128.3). -/
def Env.disclosedFaces (e : Env) (viewerDeck : List ObjId) : List ObjId :=
  e.revealedCards ++ e.lookedCards.filter viewerDeck.contains

/-- An inspection only discloses a card to the player whose deck contains it. -/
theorem Env.mem_disclosedFaces {e : Env} {deck : List ObjId} {card : ObjId} :
    card ∈ e.disclosedFaces deck ↔ card ∈ e.revealedCards ∨
      (card ∈ e.lookedCards ∧ card ∈ deck) := by
  simp [Env.disclosedFaces]

/-- Faces shown by a resolving instruction (CR 425, 437). Reveal is public. Private inspections
in an environment come from the inspecting player's Main Deck, even when another player is
making a choice. Predict records its player explicitly. -/
def Frame.disclosedFaces (viewer : PlayerId) (viewerDeck : List ObjId) :
    Frame → List ObjId
  | .predict p _ first more top bottom =>
    if viewer == p then first :: (more ++ top ++ bottom) else []
  | .chancePredict p _ top bottom =>
    if viewer == p then top ++ bottom else []
  | .chanceRecycleTrash .. => []
  | frame => match frame.resolutionEnv with
    | some env => env.disclosedFaces viewerDeck
    | none => []

/-- Cards whose faces the current resolution lets the viewer read. Frames preserve the
disclosures of a parent instruction while its child asks a question. -/
def GameState.resolutionDisclosedFaces (s : GameState) (viewer : PlayerId) : List ObjId :=
  s.pending.flatMap (Frame.disclosedFaces viewer (s.zone (.player viewer .mainDeck)))

/-- Zone card faces including the current resolution's Reveal and inspection permissions.
Only cards still present in the zone are shown, and bookkeeping zones remain outside the view. -/
def GameState.resolutionZoneCardFaces (s : GameState) (viewer : PlayerId) (z : Zone) :
    Option (List (Option CardId)) :=
  let shown := s.resolutionDisclosedFaces viewer
  let defaults := s.zoneCardFaces viewer z
  if shown.isEmpty then defaults else
    defaults.map (fun faces => ((s.zone z).zip faces).map (fun (id, face) =>
      if shown.contains id then (s.obj? id).bind (·.kind.cardId?) else face))

/-- With no active disclosure, the face view is the default privacy projection (CR 128). -/
theorem GameState.resolutionZoneCardFaces_default (s : GameState) (viewer : PlayerId)
    (z : Zone) (h : s.resolutionDisclosedFaces viewer = []) :
    s.resolutionZoneCardFaces viewer z = s.zoneCardFaces viewer z := by
  simp [resolutionZoneCardFaces, h]

/-- An active disclosure in another zone leaves this zone's face view unchanged. -/
theorem GameState.resolutionZoneCardFaces_of_disjoint (s : GameState) (viewer : PlayerId)
    (z : Zone) (hidden : ∀ id ∈ s.zone z, id ∉ s.resolutionDisclosedFaces viewer) :
    s.resolutionZoneCardFaces viewer z = s.zoneCardFaces viewer z := by
  unfold GameState.resolutionZoneCardFaces
  dsimp only
  split
  · rfl
  · cases h : s.zoneCardFaces viewer z with
    | none => rfl
    | some faces =>
      simp only [Option.map_some, Option.some.injEq]
      calc
        _ = ((s.zone z).zip faces).map Prod.snd := by
          apply List.map_congr_left
          rintro ⟨id, face⟩ member
          simp [hidden id (List.of_mem_zip member).1]
        _ = faces := List.map_snd_zip (Nat.le_of_eq (s.zoneCardFaces_length h))

/-- Only the predicting player sees the faces from the Predict decision (CR 437.1). -/
theorem Frame.disclosedFaces_predict_other {viewer p : PlayerId} (h : viewer ≠ p)
    (deck : List ObjId) (n : Nat) (first : ObjId) (more top bottom : List ObjId) :
    (Frame.predict p n first more top bottom).disclosedFaces viewer deck = [] := by
  simp [Frame.disclosedFaces, h]

/-- The same privacy applies to the cards awaiting the random order of recycling (CR 417.5). -/
theorem Frame.disclosedFaces_chancePredict_other {viewer p : PlayerId} (h : viewer ≠ p)
    (deck : List ObjId) (n : Nat) (top bottom : List ObjId) :
    (Frame.chancePredict p n top bottom).disclosedFaces viewer deck = [] := by
  simp [Frame.disclosedFaces, h]

/-- Randomizing selected Trash cards does not expose any Main Deck faces to either side. -/
theorem Frame.disclosedFaces_chanceRecycleTrash (viewer controller : PlayerId) (source : ObjId)
    (deck cards : List ObjId) :
    (Frame.chanceRecycleTrash controller source cards).disclosedFaces viewer deck = [] := by
  simp [Frame.disclosedFaces]

end Riftbound

end
