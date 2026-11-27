module

import RiftboundDriver.Trace
meta import RiftboundDriver.Trace
import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests: the trace of a game (the viewer's input)
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

-- An unfinished Cleanup can never appear as available neutral priority in the observed engine.
#guard (do
  let initial ← lab
  let p := initial.me
  let (board, victim) ← put initial p "OGN-051" .base
  let damaged := board.modObj victim (fun o => { o with damage := 10 })
  let (next, events) ← (advance 10 damaged []).toOption
  let (observed, _) ← (advanceWithDisclosures 10 damaged [] []).toOption
  let inTrash ← next.firstOf p .trash "OGN-051"
  return (advance 0 damaged []).toOption.isNone &&
    damaged.pending.head? == some (.priority p) && next.pending.head? == some (.priority p) &&
    next.countIn p .trash "OGN-051" == 1 && (cleanupStep next).isNone &&
    inTrash != victim && events.contains (.died inTrash p) && observed == (next, events) : Option Bool).getD false

/-- The trace of the demo game, or the error text. -/
meta def traceOf (seed turns : Nat) : String :=
  match demoTrace seed turns with | .ok j => j | .error e => "ERROR " ++ e

-- the trace is written, and it is the same each time: a seed replays a game
#guard !(traceOf 1 2).startsWith "ERROR"
#guard traceOf 1 2 == traceOf 1 2
#guard traceOf 1 2 != traceOf 2 2

-- it names its parts, and a longer game is a longer trace
#guard (traceOf 1 2).startsWith "{\"seed\":1,\"players\":2,\"cards\":{"
#guard ((traceOf 1 2).splitOn "\"steps\":[").length == 2
#guard (traceOf 1 4).length > (traceOf 1 2).length

-- a demo game is played to the end: a player wins by points (CR 323.1)
#guard (traceOf 1 40).contains '{' && ((traceOf 1 40).splitOn "\"won\":[").length == 2

-- the trace shows the Battlefields and the Units at them
#guard ((traceOf 1 12).splitOn "\"battlefields\":[{").length > 2
#guard ((traceOf 1 12).splitOn "\"t\":\"moved_unit\"").length > 1
#guard ((traceOf 1 12).splitOn "\"t\":\"scored\"").length > 1

-- The full trace records public XP in seat order as it is gained and spent.
#guard (do
    let s ← lab
    let gained := gainXPOf 3 (gainXPOf 2 s ⟨1⟩) ⟨0⟩
    let (before, seen) := stateJson gained {}
    let (after, _) := stateJson (gained.spendXP ⟨0⟩ 1) seen
    return (before.splitOn "\"xp\":[3,2]").length == 2 &&
      (after.splitOn "\"xp\":[2,2]").length == 2 : Option Bool).getD false

-- A token already known to the viewer changes identity in `copies`, using its original ID.
#guard (do
    let s ← lab
    let (s, model) ← put s s.you "UNL-111" .base
    let id : ObjId := ⟨s.nextId⟩
    let placed := createOne (cid "UNL-T06") s.me none true s
    let (before, seen) := stateJson placed {}
    let copied := (becomeCopyOf model placed id).1
    let (after, _) := stateJson copied seen
    return (before.splitOn (s!"\"{id.n}\":" ++ "{\"card\":\"UNL-T06\"")).length == 2 &&
      (after.splitOn ("\"copies\":{" ++ s!"\"{id.n}\":\"UNL-111\"" ++ "}")).length == 2 &&
      (after.splitOn "\"new\":{}").length == 2 : Option Bool).getD false

-- A revised replacement still identifies the affected Unit and the actual Gear selected.
#guard
  let choose := Effect.recordDeathReselection [⟨3⟩, ⟨5⟩] [⟨3⟩] ⟨5⟩
  let frame := Frame.eitherDo ⟨1⟩ ⟨5⟩ {} (choose (.gear ⟨10⟩)) (choose (.gear ⟨11⟩)) .nil
  deathReplacementFields (some frame) false == [("deathGearUnit", "5"), ("deathGearSource", "11")]

-- The trace distinguishes the original Kill from a new Kill of the same Unit.
#guard
  let choose := Effect.recordNestedDeathDecision ⟨5⟩ [(⟨5⟩, false)] ⟨5⟩
  let frame := Frame.eitherDo ⟨1⟩ ⟨5⟩ {} (choose (.gear ⟨10⟩) none) (choose (.gear ⟨11⟩) none) .nil
  deathReplacementFields (some frame) true ==
    [("deathRootUnit", "5"), ("deathDepth", "1"), ("deathGearUnit", "5"), ("deathGearSource", "10")]

-- A combat priority choice identifies the Unit and the selected keyword.
#guard
  let record (priority : CombatAssignmentPriority) :=
    Effect.prim (.markOn .self (.combatAssignmentPriority priority))
  let frame := Frame.eitherDo ⟨0⟩ ⟨5⟩ {} (record .tank) (record .backline) .nil
  combatPriorityFields (some frame) true ==
      [("combatPriorityUnit", "5"), ("combatAssignmentPriority", jstr "tank")] &&
    combatPriorityFields (some frame) false ==
      [("combatPriorityUnit", "5"), ("combatAssignmentPriority", jstr "backline")]

-- quotes and backslashes in a name are escaped
#guard jstr "a\"b\\c" == "\"a\\\"b\\\\c\""
#guard jarr ["1", "2"] == "[1,2]"
#guard jobj [("k", "1")] == "{\"k\":1}"

end RiftboundTest
