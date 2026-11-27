module

public import Riftbound.Engine.Step
public import Riftbound.Spec.PlayerView

/-! # Privacy of hand, deck and card-name decisions (I10) -/

@[expose] public section

namespace Riftbound

/-- Translate a hand choice when the same hand slots carry different engine identifiers. -/
def Action.renameHandPick (rename : ObjId → ObjId) (action : Action) : Action :=
  match action.kind with
  | .mulliganPick id => { action with kind := .mulliganPick (rename id) }
  | .discardPick id => { action with kind := .discardPick (rename id) }
  | _ => action

/-- A mulligan uses only its public pick count and the acting seat's own hand. With those
held fixed up to renaming and reordering, the same answers are legal in either state. -/
theorem legalFrameActions_mulligan_rename {s t : GameState} {p : PlayerId} {count : Nat}
    {tailS tailT : List Frame} (rename : ObjId → ObjId)
    (hs : s.pending = .mulligan p count :: tailS) (ht : t.pending = .mulligan p count :: tailT)
    (hand : (t.zone (.player p .hand)).Perm ((s.zone (.player p .hand)).map rename)) :
    (legalFrameActions t).Perm ((legalFrameActions s).map (Action.renameHandPick rename)) := by
  by_cases h : count < 2
  · have picks := hand.map (fun c => Action.mk (.player p) (.mulliganPick c))
    simpa [legalFrameActions, hs, ht, h, List.map_map, Function.comp_def, Action.renameHandPick]
      using picks.append_right [Action.mk (.player p) .mulliganDone]
  · simp [legalFrameActions, hs, ht, h, Action.renameHandPick]

/-- The ordinary discard decision also depends only on its count and the acting seat's hand. -/
theorem legalFrameActions_discard_rename {s t : GameState} {p : PlayerId} {count : Nat}
    {tailS tailT : List Frame} (rename : ObjId → ObjId)
    (hs : s.pending = .discard p count :: tailS) (ht : t.pending = .discard p count :: tailT)
    (hand : (t.zone (.player p .hand)).Perm ((s.zone (.player p .hand)).map rename)) :
    (legalFrameActions t).Perm ((legalFrameActions s).map (Action.renameHandPick rename)) := by
  have empty : t.zone (.player p .hand) = [] ↔ s.zone (.player p .hand) = [] := by
    simp [← List.length_eq_zero_iff, hand.length_eq]
  by_cases h : s.zone (.player p .hand) = [] ∨ count = 0
  · simp [legalFrameActions, hs, ht, empty, h, Action.renameHandPick]
  · have picks := hand.map (fun c => Action.mk (.player p) (.discardPick c))
    simpa [legalFrameActions, hs, ht, empty, h, List.map_map, Function.comp_def, Action.renameHandPick]
      using picks

private theorem sameOwnHandSize {s t : GameState} {p : PlayerId}
    (view : s.zoneView p (.player p .hand) = t.zoneView p (.player p .hand)) :
    (s.zone (.player p .hand)).length = (t.zone (.player p .hand)).length := by
  have size := congrArg (Option.map List.length) view
  rw [GameState.zoneView_ownHand_length, GameState.zoneView_ownHand_length] at size
  exact Option.some.inj size

/-- Equal own-hand views expose the same number of mulligan answers at the same pick count. -/
theorem legalFrameActions_mulligan_view_length {s t : GameState} {p : PlayerId} {count : Nat}
    {tailS tailT : List Frame}
    (hs : s.pending = .mulligan p count :: tailS) (ht : t.pending = .mulligan p count :: tailT)
    (view : s.zoneView p (.player p .hand) = t.zoneView p (.player p .hand)) :
    (legalFrameActions s).length = (legalFrameActions t).length := by
  have size := sameOwnHandSize view
  by_cases picks : count < 2 <;> simp [legalFrameActions, hs, ht, picks, size]

/-- Equal own-hand views expose the same number of ordinary discard answers at the same count. -/
theorem legalFrameActions_discard_view_length {s t : GameState} {p : PlayerId} {count : Nat}
    {tailS tailT : List Frame}
    (hs : s.pending = .discard p count :: tailS) (ht : t.pending = .discard p count :: tailT)
    (view : s.zoneView p (.player p .hand) = t.zoneView p (.player p .hand)) :
    (legalFrameActions s).length = (legalFrameActions t).length := by
  have size := sameOwnHandSize view
  have empty : s.zone (.player p .hand) = [] ↔ t.zone (.player p .hand) = [] := by
    simp [← List.length_eq_zero_iff, size]
  by_cases picks : t.zone (.player p .hand) = [] ∨ count = 0 <;>
    simp [legalFrameActions, hs, ht, empty, picks, size]

/-- The legal hand picks expressed as visible cards, retaining duplicate copies. A final
`none` marks an available finish answer. Unrelated actions have no hand-choice view. -/
def GameState.handActionView (s : GameState) (actions : List Action) : List (Option ViewCard) :=
  let faces := actions.filterMap (fun action =>
    match action.kind with
    | .mulliganPick id | .discardPick id => some ((s.obj? id).bind (·.kind.cardId?))
    | _ => none)
  let finishes := actions.countP (fun action =>
    match action.kind with
    | .mulliganDone | .discardDone => true
    | _ => false)
  (handView faces).map some ++ List.replicate finishes none

/-- At the same mulligan pick count, equal views yield equal choices by visible card,
including equal numbers of each duplicate and whether the player can finish. -/
theorem legalFrameActions_mulligan_view {s t : GameState} {p : PlayerId} {count : Nat}
    {tailS tailT : List Frame}
    (hs : s.pending = .mulligan p count :: tailS) (ht : t.pending = .mulligan p count :: tailT)
    (view : s.zoneView p (.player p .hand) = t.zoneView p (.player p .hand)) :
    s.handActionView (legalFrameActions s) = t.handActionView (legalFrameActions t) := by
  have faces := Option.some.inj (by
    simpa only [GameState.zoneView_ownHand_faces] using view)
  by_cases picks : count < 2
  · simpa [legalFrameActions, hs, ht, picks, GameState.handActionView, List.filterMap_map,
      Function.comp_def] using congrArg (List.map some) faces
  · simp [legalFrameActions, hs, ht, picks, GameState.handActionView]

/-- At the same discard count, equal views yield equal choices by visible card or the
same mandatory finish when there is nothing to discard. -/
theorem legalFrameActions_discard_view {s t : GameState} {p : PlayerId} {count : Nat}
    {tailS tailT : List Frame}
    (hs : s.pending = .discard p count :: tailS) (ht : t.pending = .discard p count :: tailT)
    (view : s.zoneView p (.player p .hand) = t.zoneView p (.player p .hand)) :
    s.handActionView (legalFrameActions s) = t.handActionView (legalFrameActions t) := by
  have faces := Option.some.inj (by
    simpa only [GameState.zoneView_ownHand_faces] using view)
  have size := sameOwnHandSize view
  have empty : s.zone (.player p .hand) = [] ↔ t.zone (.player p .hand) = [] := by
    simp [← List.length_eq_zero_iff, size]
  by_cases picks : t.zone (.player p .hand) = [] ∨ count = 0
  · simp [legalFrameActions, hs, ht, empty, picks, GameState.handActionView]
  · simpa [legalFrameActions, hs, ht, empty, picks, GameState.handActionView, List.filterMap_map,
      Function.comp_def] using congrArg (List.map some) faces

/-- Translate a Predict answer when the remaining candidates have different engine identifiers. -/
def Action.renamePredictPick (rename : ObjId → ObjId) (action : Action) : Action :=
  match action.kind with
  | .predictPick id recycle => { action with kind := .predictPick (rename id) recycle }
  | _ => action

/-- Predict offers top and recycle answers for the same candidates after renaming. Other
cards in the deck, and the orders in the earlier picks, do not enter this decision. -/
theorem legalFrameActions_predict_rename {s t : GameState} {p : PlayerId}
    {nS nT : Nat} {firstS firstT : ObjId} {moreS moreT topS topT bottomS bottomT : List ObjId}
    {tailS tailT : List Frame} (rename : ObjId → ObjId)
    (hs : s.pending = .predict p nS firstS moreS topS bottomS :: tailS)
    (ht : t.pending = .predict p nT firstT moreT topT bottomT :: tailT)
    (candidates : (firstT :: moreT).Perm ((firstS :: moreS).map rename)) :
    (legalFrameActions t).Perm ((legalFrameActions s).map (Action.renamePredictPick rename)) := by
  let picks (id : ObjId) := [Action.mk (.player p) (.predictPick id false),
    Action.mk (.player p) (.predictPick id true)]
  simpa [legalFrameActions, hs, ht, List.flatMap_map, List.map_flatMap, Function.comp_def,
    picks, Action.renamePredictPick] using candidates.flatMap_right picks

/-- The acting player receives no Predict answers referring to an undisclosed candidate. -/
theorem legalFrameActions_predict_disclosed {s : GameState} {p : PlayerId} {count : Nat}
    {first : ObjId} {more top bottom : List ObjId} {tail : List Frame} {answer : Action}
    (pending : s.pending = .predict p count first more top bottom :: tail)
    (legal : answer ∈ legalFrameActions s) :
    ∃ id recycle, answer = ⟨.player p, .predictPick id recycle⟩ ∧
      id ∈ s.resolutionDisclosedFaces p := by
  rw [legalFrameActions, pending] at legal
  obtain ⟨id, candidate, chosen⟩ := List.mem_flatMap.mp legal
  have disclosed := s.mem_resolutionDisclosedFaces_predict pending candidate
  simp only [List.mem_cons, List.not_mem_nil, or_false] at chosen
  rcases chosen with first | second
  · exact ⟨id, false, first, disclosed⟩
  · exact ⟨id, true, second, disclosed⟩

/-- A guesser has the same card-type choices even when the controller's private card and
everything remembered by the resolving instruction change. -/
theorem legalFrameActions_guessCardType_view {s t : GameState} {guesser p q : PlayerId}
    {srcS srcT : ObjId} {envS envT : Env} {unitS gearS spellS unitT gearT spellT : Effect}
    {restS restT : EffectList} {tailS tailT : List Frame}
    (hs : s.pending = .guessCardType guesser p srcS envS unitS gearS spellS restS :: tailS)
    (ht : t.pending = .guessCardType guesser q srcT envT unitT gearT spellT restT :: tailT) :
    legalFrameActions s = legalFrameActions t := by
  simp [legalFrameActions, hs, ht]

/-- Naming a card uses the names offered to the acting seat. Copies in hidden zones
and changes to the resolving instruction's internal references have no effect. -/
theorem legalFrameActions_nameCard_view {s t : GameState} {p : PlayerId} {first : CardId}
    {more : List CardId} {srcS srcT : ObjId} {envS envT : Env}
    {restS restT : EffectList} {tailS tailT : List Frame}
    (hs : s.pending = .nameCard p srcS envS first more restS :: tailS)
    (ht : t.pending = .nameCard p srcT envT first more restT :: tailT) :
    legalFrameActions s = legalFrameActions t := by
  simp [legalFrameActions, hs, ht]

/-- Concession eligibility is determined by the mode and the public roster of departed seats.
This applies to team games and to a free-for-all continuing after earlier concessions
(CR 649-652). -/
theorem GameState.canConcede_view {s t : GameState} (mode : s.config.mode = t.config.mode)
    (departed : s.departures.seats = t.departures.seats) (p : PlayerId) :
    s.canConcede p ↔ t.canConcede p := by
  have count : s.playerCount = t.playerCount := congrArg Mode.players mode
  have participation (q : PlayerId) : s.participates q = t.participates q := by
    simp only [GameState.participates, count, departed]
  have roster : s.participatingSeats = t.participatingSeats := by
    rw [GameState.participatingSeats, GameState.participatingSeats, count]
    exact List.filter_congr (fun q _ => participation q)
  simp only [GameState.canConcede, mode, GameState.withdrawSeat_participatingSeats,
    participation, roster, count]

/-- The answers to the pending decision, together with public participation and game status,
determine all listed player actions. -/
theorem legalActions_eq_of_frame_and_roster {s t : GameState}
    (mode : s.config.mode = t.config.mode) (departed : s.departures.seats = t.departures.seats)
    (result : s.result = t.result) (frame : legalFrameActions s = legalFrameActions t) :
    legalActions s = legalActions t := by
  have concede : concedeActions s = concedeActions t := by
    have count : s.playerCount = t.playerCount := congrArg Mode.players mode
    rw [concedeActions, concedeActions, count]
    congr 1
    apply List.filter_congr
    intro p _
    have eligible := GameState.canConcede_view mode departed p
    by_cases allowed : s.canConcede p
    · simp [allowed, eligible.mp allowed]
    · have other : ¬t.canConcede p := fun legal => allowed (eligible.mpr legal)
      simp [allowed, other]
  simp only [legalActions, result, frame, concede]

end Riftbound

end
