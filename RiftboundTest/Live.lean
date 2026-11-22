module

import RiftboundDriver.Live
meta import RiftboundDriver.Live

/-!
# Tests: live play (the driver behind the viewer's buttons)

The game waits for a person at the decisions of the seats they control, answers the others, and
gives only legal answers to choose from.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def h0 : List PlayerId := [⟨0⟩]

-- a game for the person of seat 0: it waits for them (the mulligan), and offers only their answers
#guard match liveStart 1 h0 with
  | .ok (g, j) =>
    g.needsHuman && !g.legal.isEmpty &&
    g.legal.all (fun a => a.actor == .player ⟨0⟩) &&
    -- the answers are among the legal answers of the game
    g.legal.all (fun a => (legalActions g.s).contains a) &&
    -- the chance decisions were answered: the turn order is known
    g.s.turnOrder.length == 2 && (j.splitOn "\"legal\"").length == 2
  | .error _ => false

-- an answer number that is not in the list is refused, and a good one goes on
#guard match liveStart 1 h0 with
  | .ok (g, _) => (liveAct g 1000).toOption.isNone && (liveAct g 0).toOption.isSome
  | .error _ => false

-- the person finishes the mulligan; the game goes on to their next decision with more steps made
#guard match liveStart 1 h0 with
  | .ok (g, _) =>
    match g.legal.findIdx? (fun a => a.kind == .mulliganDone) with
    | some k =>
      match liveAct g k with
      | .ok (g', _) => g'.s.turn ≥ 1 && g'.i > g.i && (g'.needsHuman || g'.s.result.isSome)
      | .error _ => false
    | none => false
  | .error _ => false

-- when the person controls both seats, both seats' answers are offered (a concession each)
#guard match liveStart 1 [⟨0⟩, ⟨1⟩] with
  | .ok (g, _) =>
    (g.legal.filter (fun a => a.kind == .concede)).length == 2 && g.needsHuman
  | .error _ => false

-- a concession ends the game at once, and nothing is offered after it
#guard match liveStart 1 h0 with
  | .ok (g, _) =>
    match g.legal.findIdx? (fun a => a.kind == .concede) with
    | some k =>
      match liveAct g k with
      | .ok (g', _) => g'.s.result == some (.won [⟨1⟩]) && g'.legal.isEmpty && !g'.needsHuman
      | .error _ => false
    | none => false
  | .error _ => false

end RiftboundTest
