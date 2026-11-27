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

/-- An optional instruction offers Yes and No regardless of what its resolution remembers. -/
theorem legalFrameActions_mayDo_view {s t : GameState} {p : PlayerId}
    {srcS srcT : ObjId} {envS envT : Env} {x y : Effect}
    {restS restT : EffectList} {tailS tailT : List Frame}
    (hs : s.pending = .mayDo p srcS envS x restS :: tailS)
    (ht : t.pending = .mayDo p srcT envT y restT :: tailT) :
    legalFrameActions s = legalFrameActions t := by
  simp [legalFrameActions, hs, ht]

/-- Translate a choice of an object already offered to the player. -/
def Action.renameOfferedChoice (rename : ObjId → ObjId) (action : Action) : Action :=
  match action.kind with
  | .choose id => { action with kind := .choose (rename id) }
  | _ => action

/-- Once a resolving instruction has offered its candidates, only those references determine
the legal answers. Translating the offered candidates translates the answers. -/
theorem legalFrameActions_pickDo_rename {s t : GameState} {p : PlayerId}
    {srcS srcT firstS firstT : ObjId} {envS envT : Env} {x y : Effect}
    {restS restT : EffectList} {moreS moreT : List ObjId} {tailS tailT : List Frame}
    (rename : ObjId → ObjId)
    (hs : s.pending = .pickDo p srcS envS firstS moreS x restS :: tailS)
    (ht : t.pending = .pickDo p srcT envT firstT moreT y restT :: tailT)
    (offered : (firstT :: moreT).Perm ((firstS :: moreS).map rename)) :
    (legalFrameActions t).Perm ((legalFrameActions s).map (Action.renameOfferedChoice rename)) := by
  simpa [legalFrameActions, hs, ht, List.map_map, Function.comp_def, Action.renameOfferedChoice]
    using offered.map (fun id => Action.mk (.player p) (.choose id))

/-- A Showdown selection depends on the offered Battlefields. Which seat opened each
Showdown is used later and does not change the selection. -/
theorem legalFrameActions_chooseShowdown_rename {s t : GameState} {p : PlayerId}
    {firstS firstT : ObjId × PlayerId} {moreS moreT : List (ObjId × PlayerId)}
    {tailS tailT : List Frame} (rename : ObjId → ObjId)
    (hs : s.pending = .chooseShowdown p firstS moreS :: tailS)
    (ht : t.pending = .chooseShowdown p firstT moreT :: tailT)
    (offered : ((firstT :: moreT).map Prod.fst).Perm
      (((firstS :: moreS).map Prod.fst).map rename)) :
    (legalFrameActions t).Perm ((legalFrameActions s).map (Action.renameOfferedChoice rename)) := by
  simpa [legalFrameActions, hs, ht, List.map_map, Function.comp_def, Action.renameOfferedChoice]
    using offered.map (fun id => Action.mk (.player p) (.choose id))

/-- Burn Out targets depend on the public seat roster of the selected mode. -/
theorem legalFrameActions_chooseBurnOut_view {s t : GameState} {p : PlayerId}
    {tailS tailT : List Frame} (hs : s.pending = .chooseBurnOut p :: tailS)
    (ht : t.pending = .chooseBurnOut p :: tailT) (mode : s.config.mode = t.config.mode) :
    legalFrameActions s = legalFrameActions t := by
  have count : s.playerCount = t.playerCount := congrArg Mode.players mode
  simp [legalFrameActions, hs, ht, mode, count]

/-- An explicit Burn Out target list is offered as given. -/
theorem legalFrameActions_chooseBurnOutAmong_view {s t : GameState} {p first : PlayerId}
    {more : List PlayerId} {tailS tailT : List Frame}
    (hs : s.pending = .chooseBurnOutAmong p first more :: tailS)
    (ht : t.pending = .chooseBurnOutAmong p first more :: tailT) :
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

/-- Translate a Combat damage assignment when the Units have different engine identifiers. -/
def Action.renameAssignPick (rename : ObjId → ObjId) (action : Action) : Action :=
  match action.kind with
  | .assignPick id => { action with kind := .assignPick (rename id) }
  | _ => action

/-- Combat assignment uses the targets, their public controller and assignment priority,
and the targets already assigned. Changing internal references preserves those choices. -/
theorem legalAssigns_rename {s t : GameState} {before after : ObjId} {side : PlayerId}
    {assigned : List ObjId} (rename : ObjId → ObjId) (injective : Function.Injective rename)
    (targets : t.assignmentTargets after side = (s.assignmentTargets before side).map rename)
    (controller : ∀ id ∈ s.assignmentTargets before side,
      t.controllerOf (rename id) = s.controllerOf id)
    (priority : ∀ id ∈ s.assignmentTargets before side,
      t.assignmentRank after side (rename id) = s.assignmentRank before side id) :
    legalAssigns t after side (assigned.map rename) =
      (legalAssigns s before side assigned).map (Action.renameAssignPick rename) := by
  have mem_map (ids : List ObjId) (id : ObjId) : rename id ∈ ids.map rename ↔ id ∈ ids := by
    constructor
    · intro present
      obtain ⟨other, present, equal⟩ := List.mem_map.mp present
      exact (injective equal) ▸ present
    · intro present
      exact List.mem_map.mpr ⟨id, present, rfl⟩
  have pick (id : ObjId) (present : id ∈ s.assignmentTargets before side) :
      t.pickOk after side (assigned.map rename) (rename id) = s.pickOk before side assigned id := by
    simp only [GameState.pickOk, targets, List.all_map, mem_map, controller id present, priority id present]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, Function.comp_def]
    constructor
    · intro holds other member
      simpa only [mem_map, controller other member, priority other member] using holds other member
    · intro holds other member
      simpa only [mem_map, controller other member, priority other member] using holds other member
  have done : t.doneOk after side (assigned.map rename) = s.doneOk before side assigned := by
    unfold GameState.doneOk
    rw [targets, List.all_map]
    apply List.all_congr rfl
    intro id
    simp only [Function.comp_def, mem_map]
  have filtered : ((s.assignmentTargets before side).map rename).filter
        (t.pickOk after side (assigned.map rename)) =
      ((s.assignmentTargets before side).filter (s.pickOk before side assigned)).map rename := by
    rw [List.filter_map]
    exact congrArg (List.map rename) (List.filter_congr pick)
  unfold legalAssigns
  rw [targets, filtered, done, List.map_append]
  by_cases complete : s.doneOk before side assigned = true <;>
    simp [complete, List.map_map, Function.comp_def, Action.renameAssignPick]

/-- With those same public facts, the open assignment frame offers the same answers independently
of the earlier Combat assignments, which only become relevant on resolution. -/
theorem legalFrameActions_assign_rename {s t : GameState} {before after : ObjId}
    {attacker side : PlayerId} {assigned : List ObjId} {oldDamage newDamage : List (ObjId × Nat)}
    {tailS tailT : List Frame} (rename : ObjId → ObjId) (injective : Function.Injective rename)
    (hs : s.pending = .assign before attacker side assigned oldDamage :: tailS)
    (ht : t.pending = .assign after attacker side (assigned.map rename) newDamage :: tailT)
    (targets : t.assignmentTargets after side = (s.assignmentTargets before side).map rename)
    (controller : ∀ id ∈ s.assignmentTargets before side,
      t.controllerOf (rename id) = s.controllerOf id)
    (priority : ∀ id ∈ s.assignmentTargets before side,
      t.assignmentRank after side (rename id) = s.assignmentRank before side id) :
    legalFrameActions t = (legalFrameActions s).map (Action.renameAssignPick rename) := by
  simp only [legalFrameActions, hs, ht]
  exact legalAssigns_rename rename injective targets controller priority

/-- Excluding Units already selected for a Standard Move commutes with renaming the
public candidates and the selection. The fee is checked for the same group size. -/
theorem GameState.groupMoveRemaining_rename {s t : GameState} {p : PlayerId}
    {oldDest newDest : MoveDest} {pay : Cost} {units : List ObjId} (rename : ObjId → ObjId)
    (injective : Function.Injective rename)
    (candidates : (t.groupMoveChoices p newDest).Perm ((s.groupMoveChoices p oldDest).map rename))
    (fee : (t.standardMoveQuotes p newDest (max 2 (units.length + 1))
      (s.groupMoveChoices p oldDest).length).contains pay =
      (s.standardMoveQuotes p oldDest (max 2 (units.length + 1))
        (s.groupMoveChoices p oldDest).length).contains pay) :
    (t.groupMoveRemaining p newDest pay (units.map rename)).Perm
      ((s.groupMoveRemaining p oldDest pay units).map rename) := by
  have count : (t.groupMoveChoices p newDest).length = (s.groupMoveChoices p oldDest).length := by
    simpa only [List.length_map] using candidates.length_eq
  have selected (id : ObjId) : (units.map rename).contains (rename id) = units.contains id := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem, List.mem_map]
    constructor
    · rintro ⟨other, present, same⟩
      exact injective same ▸ present
    · intro present
      exact ⟨id, present, rfl⟩
  unfold GameState.groupMoveRemaining
  simp only [List.length_map, count, fee]
  split
  · have filtered := candidates.filter (fun id => !(units.map rename).contains id)
    simpa only [List.filter_map, Function.comp_def, selected] using filtered
  · simp

/-- The open group selection offers corresponding Units and the same accept or cancel
answers when the public candidates, quoted fee, and validity of the declaration agree. -/
theorem legalFrameActions_groupMove_rename {s t : GameState} {p : PlayerId}
    {oldDest newDest : MoveDest} {pay : Cost} {units : List ObjId} {tailS tailT : List Frame}
    (rename : ObjId → ObjId) (injective : Function.Injective rename)
    (hs : s.pending = .groupMove p oldDest pay units :: tailS)
    (ht : t.pending = .groupMove p newDest pay (units.map rename) :: tailT)
    (candidates : (t.groupMoveChoices p newDest).Perm ((s.groupMoveChoices p oldDest).map rename))
    (fee : (t.standardMoveQuotes p newDest (max 2 (units.length + 1))
      (s.groupMoveChoices p oldDest).length).contains pay =
      (s.standardMoveQuotes p oldDest (max 2 (units.length + 1))
        (s.groupMoveChoices p oldDest).length).contains pay)
    (ready : t.groupMoveReady p newDest pay (units.map rename) = s.groupMoveReady p oldDest pay units) :
    (legalFrameActions t).Perm ((legalFrameActions s).map (Action.renameOfferedChoice rename)) := by
  have remaining := (GameState.groupMoveRemaining_rename rename injective candidates fee).map
    (fun id => Action.mk (.player p) (.choose id))
  cases canAccept : s.groupMoveReady p oldDest pay units
  · simpa [legalFrameActions, hs, ht, ready, canAccept, List.map_map, Function.comp_def,
      Action.renameOfferedChoice] using remaining.cons (Action.mk (.player p) (.decide false))
  · simpa [legalFrameActions, hs, ht, ready, canAccept, List.map_map, Function.comp_def,
      Action.renameOfferedChoice] using
        (remaining.cons (Action.mk (.player p) (.decide true))).cons (Action.mk (.player p) (.decide false))

end Riftbound

end
