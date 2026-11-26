module

public import RiftboundDriver.Trace
public import Riftbound.Spec.PlayerView

/-! # JSON checkpoints for a single viewing seat -/

public section

namespace RiftboundDriver

open Riftbound

private def nullable {α : Type} (render : α → String) (value : Option α) : String :=
  value.elim "null" render

private def seatJson (p : PlayerId) : String := toString p.n

private def faceJson (c : CardId) : String := jstr c.code

private def positionJson (p : ViewPosition) : String :=
  jobj [("zone", jstr (zoneName p.zone)), ("index", toString p.index)]

private def cardViewJson : ViewCard → String
  | .plain none => "null"
  | .plain (some card) => jobj [("card", faceJson card)]
  | .hidden face controller battlefield =>
    jobj [("card", nullable faceJson face), ("controller", seatJson controller),
      ("atBattlefield", nullable positionJson battlefield)]
  | .board card d =>
    let keywords := d.keywords.map fun k =>
      jobj [("keyword", jstr (ctorName k.keyword)), ("arg", kwArgJson k.arg)]
    jobj [("card", faceJson card), ("owner", seatJson d.owner), ("controller", seatJson d.controller),
      ("atBattlefield", nullable positionJson d.atBattlefield),
      ("attachedTo", nullable positionJson d.attachedTo), ("control", nullable seatJson d.control),
      ("contested", nullable seatJson d.contested), ("effectiveCard", nullable faceJson d.effectiveCard),
      ("types", jarr (d.types.map (fun k => jstr (ctorName k)))),
      ("might", nullable toString d.might), ("keywords", jarr keywords),
      ("rune", nullable (fun k => jstr (ctorName k)) d.rune),
      ("damage", toString d.damage), ("exhausted", toString d.exhausted),
      ("buffed", toString d.buffed), ("stunned", toString d.stunned),
      ("empowerCount", toString d.empowerCount), ("namedCard", nullable faceJson d.namedCard)]
  | .spell card controller targets =>
    jobj [("card", faceJson card), ("controller", seatJson controller),
      ("targets", jarr (targets.map (nullable positionJson)))]
  | .ability card index controller source targets =>
    jobj [("card", faceJson card), ("ability", toString index), ("controller", seatJson controller),
      ("source", nullable positionJson source), ("targets", jarr (targets.map (nullable positionJson)))]

private def priorityView (s : GameState) : String :=
  match s.pending.head? with
  | some (.priority seat) | some (.chainPass seat _) => jobj [("seat", seatJson seat)]
  | some (.showdown bf focus _) =>
    jobj [("seat", seatJson focus), ("atBattlefield", nullable positionJson (s.publicPosition bf))]
  | _ => "null"

private def combatView (s : GameState) (combat : CombatParticipation) : String :=
  jobj [("atBattlefield", nullable positionJson (s.publicPosition combat.battlefield)),
    ("attacker", seatJson combat.attacker), ("defender", seatJson combat.defender),
    ("units", jarr ((combat.units.filterMap s.publicPosition).map positionJson))]

/-- A checkpoint containing the board, card faces, and game status observable by a seat. All
references to objects are local to this checkpoint. -/
def seatStateJson (s : GameState) (viewer : PlayerId) : String :=
  let players := allPlayers s.playerCount
  let zones := (shownZones s.playerCount).filterMap fun z =>
    (s.zoneView viewer z).map fun cards => (zoneName z, jarr (cards.map cardViewJson))
  let result := match s.result with
    | some (.won w) => jobj [("won", jarr (w.map seatJson))]
    | some .draw => jstr "draw"
    | none => "null"
  let clock := match s.clock with
    | some (.elimination deadline _) => [("eliminationDeadline", toString deadline)]
    | _ => []
  jobj ([("turn", toString s.turn), ("phase", jstr (ctorName s.phase)),
    ("active", nullable seatJson s.active), ("priority", priorityView s),
    ("turnOrder", jarr (s.turnOrder.map seatJson)), ("result", result),
    ("points", jarr (players.map (fun p => toString (s.pointsOf p)))),
    ("pools", jarr (players.map (fun p => poolJson (s.poolOf p)))),
    ("xp", jarr (players.map (fun p => toString (s.xpOf p)))),
    ("combat", nullable (combatView s) s.combat),
    ("departed", jarr (s.departures.seats.map seatJson)), ("zones", jobj zones)] ++ clock)

end RiftboundDriver
