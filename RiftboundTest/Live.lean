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

-- Legacy checkpoints decode without a damage witness. New ones record attribution separately
-- from the pre-existing state fingerprint.
#guard match liveStart 1 h0 with
  | .ok (g, _) =>
    let before := ReplayCheckpoint.capture g.s []
    let changed := { g.s with damageMarks := g.s.damageMarks.insert 19 [(some ⟨0⟩, 1)] }
    let after := ReplayCheckpoint.capture changed []
    let legacy := Lean.Json.mkObj [("state", .str before.state), ("events", .arr #[])]
    let restored := (Lean.fromJson? (α := ReplayCheckpoint) legacy).toOption
    before.state == after.state && after.damageMarks? == some [(19, [(some 0, 1)])] &&
      restored.any (fun item => item.state == before.state && item.damageMarks?.isNone)
  | .error _ => false

-- The spend witnesses extend the legacy state digest and survive lossless replay encoding.
#guard match liveStart 1 h0 with
  | .ok (g, _) =>
    let seat : PlayerId := ⟨0⟩
    let original := g.s.setPool seat .empty
    let paid := (g.s.setPool seat { deflectSpent := 1 }).addTurnFx seat (.powerSpentBeforeMain 2)
    let legacy := ReplayCheckpoint.capture original []
    let recorded := ReplayCheckpoint.capture paid []
    let restored := (Lean.fromJson? (α := ReplayCheckpoint) (Lean.toJson recorded)).toOption
    let observation (amount : Nat) : List ReplayObservation :=
      [{ checkpoint := 0, facts := [.spentPower seat amount] }]
    legacy.state == recorded.state && legacy.deflectSpent?.isNone && legacy.spentBeforeMain?.isNone &&
      restored.any (fun checkpoint => checkpoint.deflectSpent? == some [(0, 1)] &&
        checkpoint.spentBeforeMain? == some [(0, 2)]) &&
      (ReplayObservation.checkAt (observation 3) 0 paid).isOk &&
      !(ReplayObservation.checkAt (observation 2) 0 paid).isOk
  | .error _ => false

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

-- The viewer receives the two roles as separate lists.
#guard
  let a : Action := ⟨.player ⟨0⟩, .activate ⟨1⟩ 0 ⟨1, []⟩ [⟨2⟩] [⟨3⟩]⟩
  let json := actionJson a
  json.contains "\"targets\":[2]" && json.contains "\"discards\":[3]"

#guard
  let a : Action := ⟨.player ⟨0⟩, .playCard ⟨1⟩ ⟨3, []⟩ [⟨2⟩] none (some ⟨3⟩)⟩
  let json := actionJson a
  json.contains "\"targets\":[2]" && json.contains "\"discards\":[3]"

-- A token's Base choice and its Battlefield choice have distinct labels in live play.
#guard
  let p : PlayerId := ⟨0⟩
  let base := Effect.prim (.playUnitTokenAt "Tentacle" none)
  let field := Effect.prim (.playUnitTokenAt "Tentacle" (some ⟨9⟩))
  let question := some (.eitherDo p ⟨1⟩ {} base field .nil)
  let yes := actionJson ⟨.player p, .decide true⟩ question
  let no := actionJson ⟨.player p, .decide false⟩ question
  yes.contains "\"token\":\"Tentacle\",\"dest\":null" &&
    no.contains "\"token\":\"Tentacle\",\"dest\":9"

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

/-- How many cards with this identifier a player has, in any zone. -/
meta def countCard (s : GameState) (p : PlayerId) (code : String) : Nat :=
  (s.objects.toList.filter (fun (_, o) => o.owner == p &&
    (match o.kind with | .card _ c => c.code == code | _ => false))).length

/-- The number of cards with this identifier in a list. -/
meta def countIn (l : List CardId) (code : String) : Nat :=
  (l.filter (fun c => c.code == code)).length

-- sideboarding (TR 403.4): after a game that a player won, a card of the Main Deck is exchanged for
-- a card of the sideboard, one for one, and the next game is played with the new deck
#guard match conceded 2 with
  | some g =>
    match liveSwap g "S1" "S0" with
    | .ok (g1, _) =>
      match g1.decks[0]?, g1.sides[0]? with
      | some d, some side =>
        d.main.length == 40 && side.length == 10 && countIn d.main "S1" == 2 &&
        countIn d.main "S0" == 1 && countIn side "S0" == 2 && countIn side "S1" == 1 &&
        decide (ConstructedDeckValid demoDB demoEnv { deck := d, sideboard := side }) &&
        (match liveNext g1 (some true) with
          | .ok (g2, _) => countCard g2.s ⟨0⟩ "S0" == 1 && countCard g2.s ⟨0⟩ "S1" == 2 &&
              countCard g2.s ⟨1⟩ "S0" == 0
          | .error _ => false)
      | _, _ => false
    | .error _ => false
  | none => false

-- an exchange that is not allowed or not legal is refused: a card that is not there, the Chosen
-- Champion for a card that cannot take its place (TR 403.4.c), a game that is not over
#guard match conceded 2 with
  | some g =>
    (liveSwap g "Nope" "S0").toOption.isNone && (liveSwap g "S1" "Nope").toOption.isNone &&
    (liveSwap g "S0" "S1").toOption.isNone && (liveSwap g "C1" "S0").toOption.isNone
  | none => false
#guard match liveStart 1 h0 .constructed (some 2) with
  | .ok (g, _) => (liveSwap g "S1" "S0").toOption.isNone
  | .error _ => false

-- no exchange after a draw (TR 403.10), and not outside a Constructed match
#guard match afterMulligan .constructed (some 2) with
  | some g =>
    match liveExternal g judgeA with
    | .ok (g1, _) => g1.recorded && (liveSwap g1 "S1" "S0").toOption.isNone
    | .error _ => false
  | none => false
#guard match conceded 1 with
  | some g => (liveSwap g "S1" "S0").toOption.isNone
  | none => false
#guard match liveStart 1 h0 .sealed (some 2) with
  | .ok (g, _) => (liveSwap g "S1" "S0").toOption.isNone
  | .error _ => false

-- taking an answer back: the game before the answer is kept, so its reply says the same answers
-- again, tells the viewer how many steps to keep (the steps made until then), and has none new
#guard match liveStart 1 h0 with
  | .ok (g, _) =>
    match liveAct g 0 with
    | .ok (g', _) =>
      g.undoReply.contains "\"steps\":[]" &&
      g.undoReply.contains s!"\"truncate\":{g.i}" &&
      g.undoReply.contains g.legalJson &&
      -- the answer made steps, and the game before it is not changed by it
      g'.i > g.i
    | .error _ => false
  | .error _ => false

-- the steps the viewer keeps are the steps of the start: as many as the game has made
#guard match liveNew .core 1 h0 none none with
  | .ok (g, js) => js.length == g.i
  | .error _ => false

-- the same answer, given again to the game before it, makes the same reply: nothing is left over
#guard match liveStart 1 h0 with
  | .ok (g, _) =>
    match liveAct g 0, liveAct g 0 with
    | .ok (_, j1), .ok (_, j2) => j1 == j2
    | _, _ => false
  | .error _ => false

end RiftboundTest
