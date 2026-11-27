module

public import RiftboundDriver.ReplayCodec

/-! Independently transcribed observations of a replayed game. -/

public section

namespace RiftboundDriver

open Lean Riftbound

/-- The public place where a group of Units was observed. -/
inductive ReplayUnitPlace where
  /-- The Base of the controller named in the observation. -/
  | base
  /-- A Battlefield identified by its owner and printed card code. -/
  | battlefield (owner : PlayerId) (field : CardId)
deriving DecidableEq, Repr, ToJson, FromJson

/-- A Unit's visible condition, keyed by card code rather than internal object ID. -/
structure ReplayObservedUnit where
  /-- The visible card or token code. -/
  card : CardId
  /-- Whether the Unit is Exhausted. -/
  exhausted : Bool
  /-- The amount of damage currently marked on the Unit. -/
  damage : Nat
deriving DecidableEq, Repr, ToJson, FromJson

/-- The visible cards attached to one observed Unit. -/
structure ReplayObservedUnitAttachments where
  /-- The Unit's visible card or token code. -/
  unit : CardId
  /-- The visible codes of all attached objects, including duplicate copies. -/
  attached : List CardId
deriving DecidableEq, Repr, ToJson, FromJson

/-- A fact observed at a game checkpoint, expressed without engine-generated object IDs. -/
inductive ReplayObservationFact where
  /-- The turn number. -/
  | turn (number : Nat)
  /-- The current game phase. -/
  | phase (phase : Phase)
  /-- The active seat, or none during setup. -/
  | active (seat : Option PlayerId)
  /-- The points shown for a seat, including its shared score in team games. -/
  | score (seat : PlayerId) (points : Nat)
  /-- The size of a visible zone, including face-down cards or abilities on the Chain. -/
  | zoneCount (zone : Zone) (count : Nat)
  /-- All face-up card codes in a public zone, with duplicate copies and in any order. -/
  | zoneCards (zone : Zone) (cards : List CardId)
  /-- Observed copies in a public zone when the source did not show its entire contents. -/
  | zoneContains (zone : Zone) (cards : List CardId)
  /-- The controller of the indicated Battlefield, or none when it is neutral. -/
  | battlefieldControl (owner : PlayerId) (field : CardId) (controller : Option PlayerId)
  /-- The Units of one controller at the indicated Battlefield, in any order. -/
  | battlefieldUnits (owner : PlayerId) (field : CardId) (controller : PlayerId)
      (cards : List CardId)
  /-- All Units of the controller at the given public place, with exhaustion and marked damage. -/
  | unitStates (controller : PlayerId) (place : ReplayUnitPlace) (units : List ReplayObservedUnit)
  /-- Whether time has been called. -/
  | clockCalled (called : Bool)
  /-- The observed game result, or none while the game was ongoing. -/
  | result (result : Option GameResult)
  /-- The attachment groups on all Units of one controller at the given public place. -/
  | unitAttachments (controller : PlayerId) (place : ReplayUnitPlace)
      (units : List ReplayObservedUnitAttachments)
deriving DecidableEq, Repr, ToJson, FromJson

/-- Facts from a source such as a scoreboard, video frame or independent game log. -/
structure ReplayObservation where
  /-- The number of applied answers at the moment of observation. Zero is the initial state. -/
  checkpoint : Nat
  /-- An optional source label, such as a timestamp in the match video. -/
  source? : Option String := none
  /-- The facts visible at the selected checkpoint. -/
  facts : List ReplayObservationFact
deriving DecidableEq, Repr, ToJson, FromJson

private def checkFactValue {α : Type} [DecidableEq α] [ToJson α]
    (label : String) (expected actual : α) : Except String Unit :=
  unless expected == actual do
    throw s!"{label}: expected {(toJson expected).compress}, replayed {(toJson actual).compress}"

private def cardCodes (cards : List CardId) : List String := cards.map (·.code)

private def checkCardSet (label : String) (expected actual : List CardId)
    (allowOther : Bool := false) : Except String Unit := do
  if allowOther then
    let mut remaining := actual
    for card in expected do
      unless remaining.contains card do
        throw s!"{label}: expected at least {repr (cardCodes expected)}, replayed {repr (cardCodes actual)}"
      remaining := remaining.erase card
  else
    unless decide (expected.Perm actual) do
      throw s!"{label}: expected {repr (cardCodes expected)}, replayed {repr (cardCodes actual)}"

private def observeSeat (s : GameState) (seat : PlayerId) : Except String Unit :=
  unless s.players.contains seat do throw s!"seat {seat.n} is outside the game"

private def zoneLabel : Zone → String
  | .player seat kind => s!"seat {seat.n} {repr kind}"
  | .battlefieldZone => "Battlefield Zone"
  | .chain => "Chain"

private def observeZone (s : GameState) (zone : Zone) : Except String (List (Option CardId)) := do
  unless decide (zone.Valid s.playerCount) do throw s!"{zoneLabel zone} is outside the game"
  let some faces := s.zoneCardFaces ⟨0⟩ zone | throw s!"{zoneLabel zone} is an engine-only zone"
  return faces

private def publicCards (s : GameState) (zone : Zone) : Except String (List CardId) := do
  match zone with
  | .player _ .hand | .player _ .hidden | .player _ .mainDeck | .player _ .runeDeck =>
    throw s!"{zoneLabel zone}: only the count can be observed here"
  | _ => return (← observeZone s zone).filterMap id

private def observeBattlefield (s : GameState) (owner : PlayerId) (field : CardId) :
    Except String ObjId := do
  observeSeat s owner
  let ids := s.battlefields.filter fun id =>
    (s.obj? id).any (fun o => o.owner == owner && o.kind.cardId? == some field)
  let [id] := ids | throw s!"Battlefield {field.code} from seat {owner.n} must identify one active Battlefield"
  return id

private def observeUnitsAt (s : GameState) (controller : PlayerId) (place : ReplayUnitPlace) :
    Except String (String × List ObjId) := do
  observeSeat s controller
  match place with
  | .base =>
    let ids := (s.zone (.player controller .base)).filter
      (fun id => s.isUnit id && s.isControlledBy controller id)
    pure (s!"seat {controller.n} Units at Base", ids)
  | .battlefield owner field => do
    let id ← observeBattlefield s owner field
    pure (s!"seat {controller.n} Units at Battlefield {field.code} from seat {owner.n}",
      s.unitsOf controller id)

private def ReplayObservedUnitAttachments.sorted (group : ReplayObservedUnitAttachments) :
    ReplayObservedUnitAttachments :=
  { group with attached := group.attached.mergeSort (fun a b => a.code ≤ b.code) }

private def ReplayObservationFact.check (fact : ReplayObservationFact) (s : GameState) :
    Except String Unit := do
  match fact with
  | .turn number => checkFactValue "turn" number s.turn
  | .phase expectedPhase => checkFactValue "phase" expectedPhase s.phase
  | .active seat => checkFactValue "active seat" seat s.active
  | .score seat points =>
    observeSeat s seat
    checkFactValue s!"seat {seat.n} score" points (s.pointsOf seat)
  | .zoneCount zone count =>
    checkFactValue s!"{zoneLabel zone} count" count (← observeZone s zone).length
  | .zoneCards zone cards => checkCardSet (zoneLabel zone) cards (← publicCards s zone)
  | .zoneContains zone cards => checkCardSet (zoneLabel zone) cards (← publicCards s zone) true
  | .battlefieldControl owner field controller =>
    let id ← observeBattlefield s owner field
    checkFactValue s!"Battlefield {field.code} from seat {owner.n} controller" controller (s.controlOf id)
  | .battlefieldUnits owner field controller cards =>
    observeSeat s controller
    let id ← observeBattlefield s owner field
    let units := (s.unitsOf controller id).filterMap (fun unit => (s.obj? unit).bind (·.kind.cardId?))
    checkCardSet s!"seat {controller.n} Units at Battlefield {field.code} from seat {owner.n}" cards units
  | .unitStates controller place expected =>
    let (label, ids) ← observeUnitsAt s controller place
    let actual : List ReplayObservedUnit := ids.filterMap fun id => do
      let o ← s.obj? id
      let card ← o.kind.cardId?
      return ⟨card, o.exhausted, o.damage⟩
    unless decide (expected.Perm actual) do
      checkFactValue label expected actual
  | .unitAttachments controller place expected =>
    let (label, ids) ← observeUnitsAt s controller place
    let actual : List ReplayObservedUnitAttachments := ids.filterMap fun id => do
      let unit ← (s.obj? id).bind (·.kind.cardId?)
      let attached := s.inPlay.filterMap fun object => do
        let attached ← s.obj? object
        if attached.attached == some id then attached.kind.cardId? else none
      return ⟨unit, attached⟩
    unless decide ((expected.map ReplayObservedUnitAttachments.sorted).Perm
        (actual.map ReplayObservedUnitAttachments.sorted)) do
      checkFactValue s!"{label} attachments" expected actual
  | .clockCalled called => checkFactValue "clock called" called s.clock.isSome
  | .result expected =>
    match expected, s.result with
    | some (.won winners), some (.won actual) =>
      unless decide (winners.Perm actual) do
        checkFactValue "game result" expected s.result
    | _, _ => checkFactValue "game result" expected s.result

/-- Validate the observations at this position and advance an ordered observation schedule. -/
def ReplayObservation.checkAt (schedule : List ReplayObservation) (checkpoint : Nat)
    (s : GameState) : Except String (List ReplayObservation) := do
  let (observed, pending) := schedule.span (fun observation => observation.checkpoint == checkpoint)
  for observation in observed do
    let source := observation.source?.map (fun label => s!" ({(toJson label).compress})") |>.getD ""
    let check := observation.facts.forM (fun fact => fact.check s)
    check.mapError (fun error => s!"checkpoint {checkpoint}: observation{source}: {error}")
  return pending

end RiftboundDriver

end
