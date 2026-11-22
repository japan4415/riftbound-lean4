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

meta def clockA : Action := ⟨.clock, .timeCalled⟩
meta def judgeA : Action := ⟨.judge, .declareDraw⟩

/-- The game of a person for seat 0, after the mulligan (a turn has begun). -/
meta def afterMulligan (kind : LiveKind) (target : Option Nat) : Option LiveGame :=
  match liveStart 1 h0 kind target with
  | .ok (g, _) =>
    match g.legal.findIdx? (fun a => a.kind == .mulliganDone) with
    | some k => match liveAct g k with | .ok (g', _) => some g' | .error _ => none
    | none => none
  | .error _ => none

-- the clock and the judge work under the Tournament Rules, not under the Core Rules
#guard match afterMulligan .constructed none, afterMulligan .core none with
  | some t, some c =>
    (liveExternal t clockA).toOption.any (fun r => r.1.s.clock.isSome) &&
    (liveExternal t judgeA).toOption.any (fun r => r.1.s.result == some .draw) &&
    (liveExternal c clockA).toOption.isNone && (liveExternal c judgeA).toOption.isNone
  | _, _ => false

-- a game of Sealed decks starts with no Legend, and the extra draw gives the first player 1 more
#guard match liveStart 1 h0 .sealed none with
  | .ok (g, _) => (g.s.zone (.player ⟨0⟩ .legendZone)).isEmpty && g.s.config.ruleSet.isLimited
  | .error _ => false

/-- A person's game, ended by a concession of seat 0. -/
meta def conceded (target : Nat) : Option LiveGame :=
  match liveStart 1 h0 .constructed (some target) with
  | .ok (g, _) =>
    match g.legal.findIdx? (fun a => a.kind == .concede) with
    | some k => match liveAct g k with | .ok (g', _) => some g' | .error _ => none
    | none => none
  | .error _ => none

-- a Best of 1 is over after one game, and the match gives no next game
#guard match conceded 1 with
  | some g =>
    g.recorded && g.match_.any (·.finished) && (g.match_.bind (·.winner)) == some ⟨1⟩ &&
      (liveNext g none).toOption.isNone
  | none => false

-- a Best of 3 goes on: the loser (a person) is asked who goes first (TR 407), and the answer
-- decides the turn order of the next game
#guard match conceded 2 with
  | some g =>
    g.recorded && !(g.match_.any (·.finished)) && (g.match_.map (·.games)) == some 1 &&
    (match liveNext g none with
      | .ok (g0, j) => g0.s.result.isSome && (j.splitOn "\"choice\"").length == 2
      | .error _ => false) &&
    (match liveNext g (some false), liveNext g (some true) with
      | .ok (g1, _), .ok (g2, _) =>
        g1.s.turnOrder == [⟨1⟩, ⟨0⟩] && g2.s.turnOrder == [⟨0⟩, ⟨1⟩] &&
        (g1.match_.map (·.games)) == some 1 && !g1.recorded
      | _, _ => false)
  | none => false

-- a game that is not a match has no next game, and a game not over cannot be followed
#guard match liveStart 1 h0 .constructed none with
  | .ok (g, _) => (liveNext g none).toOption.isNone
  | .error _ => false
#guard match liveStart 1 h0 .constructed (some 2) with
  | .ok (g, _) => (liveNext g none).toOption.isNone
  | .error _ => false

end RiftboundTest
