module

public import Riftbound

/-!
# Driver: seeded play

Answers the engine's questions so that a game can be run. Chance decisions are answered from a
seeded random number generator, so a seed and the list of answers replay a game (design.md §6.4).
Player decisions are answered by a fixed default: keep the hand, take the first opponent.
This library is not part of the verified core and may use any code (design.md §4).
-/

@[expose] public section

namespace RiftboundDriver

open Riftbound

/-- A small linear congruential generator. -/
structure Rng where
  /-- The state. -/
  state : Nat
deriving Repr

/-- A generator from a seed. -/
def Rng.ofSeed (seed : Nat) : Rng := ⟨seed % 2147483647⟩

/-- The next number below `n` (0 if `n` is 0), and the next generator. -/
def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let st := (r.state * 48271 + 11) % 2147483647
  (if n = 0 then 0 else (st / 7) % n, ⟨st⟩)

/-- Shuffle a list by picking members at random. -/
def shuffleList {α : Type} : Nat → Rng → List α → List α × Rng
  | 0, r, l => (l, r)
  | n + 1, r, l =>
    match l with
    | [] => ([], r)
    | _ :: _ =>
      let (i, r) := r.below l.length
      let (rest, r) := shuffleList n r (l.eraseIdx i)
      match l[i]? with
      | some x => (x :: rest, r)
      | none => (rest, r)

/-- Shuffle a list. -/
def shuffle {α : Type} (r : Rng) (l : List α) : List α × Rng :=
  shuffleList l.length r l

/-- The default answer to the current question, with the next generator. `none` when there is no
decision to answer. -/
def autoAnswer (r : Rng) (s : GameState) : Option (Action × Rng) :=
  match s.pending with
  | .chanceShuffle z :: _ =>
    let (l, r) := shuffle r (s.zone z)
    some (⟨.chance, .arrange l⟩, r)
  | .chanceBattlefield p :: _ =>
    let (i, r) := r.below (s.zone (.player p .outOfGame)).length
    some (⟨.chance, .pick i⟩, r)
  | .chanceTurnOrder :: _ =>
    let (l, r) := if s.config.mode.isTeamDuel then
      let (i, r) := r.below 2
      (Mode.teamTurnOrder (i == 0), r)
    else shuffle r (allPlayers s.playerCount)
    some (⟨.chance, .arrangePlayers l⟩, r)
  | .chanceRecycle p :: _ =>
    let (l, r) := shuffle r (s.zone (.player p .setAside))
    some (⟨.chance, .arrange l⟩, r)
  | .chanceBurnOut p :: _ =>
    let (l, r) := shuffle r (s.zone (.player p .trash))
    some (⟨.chance, .arrange l⟩, r)
  | .chancePredict _ _ _ bottom :: _ =>
    let (order, r) := shuffle r bottom
    some (⟨.chance, .arrange order⟩, r)
  | .mulligan p _ :: _ => some (⟨.player p, .mulliganDone⟩, r)
  | .chainPass p _ :: _ => some (⟨.player p, .pass⟩, r)
  | .showdown _ q _ :: _ => some (⟨.player q, .pass⟩, r)
  | .assign .. :: _ => (legalFrameActions s).head?.map (fun a => (a, r))
  | .triggerOrder .. :: _ => (legalFrameActions s).head?.map (fun a => (a, r))
  | .discard .. :: _ => (legalFrameActions s).head?.map (fun a => (a, r))
  | .mayDo .. :: _ => (legalFrameActions s).head?.map (fun a => (a, r))
  | .eitherDo .. :: _ => (legalFrameActions s).head?.map (fun a => (a, r))
  | .pickDo .. :: _ | .nameCard .. :: _ | .guessCardType .. :: _ | .predict .. :: _ =>
    (legalFrameActions s).head?.map (fun a => (a, r))
  | .chooseBurnOut p :: _ =>
    match (allPlayers s.playerCount).filter (fun q => !s.config.mode.sameSide p q) with
    | opp :: _ => some (⟨.player p, .burnOutTarget opp⟩, r)
    | [] => none
  | _ => none

/-- The default answer while playing turns: as `autoAnswer`, and pass when the turn player has
priority. -/
def playAnswer (r : Rng) (s : GameState) : Option (Action × Rng) :=
  match s.pending with
  | .priority p :: _ => some (⟨.player p, .pass⟩, r)
  | _ => autoAnswer r s

/-- Play until `turns` turns have begun and the turn player has priority in the Main Phase, or
`steps` answers were given. Every answer goes through `step`. -/
def runUntilTurn (fuel : Nat) (turns : Nat) :
    Nat → Rng → GameState → Except RuleError GameState
  | 0, _, s => .ok s
  | n + 1, r, s =>
    if turns ≤ s.turn && (match s.pending with | .priority _ :: _ => true | _ => false) then .ok s
    else
      match playAnswer r s with
      | none => .ok s
      | some (a, r') =>
        match step fuel s a with
        | .ok (s', _) => runUntilTurn fuel turns n r' s'
        | .error e => .error e

/-- Answer the questions with the defaults until none is left or `steps` answers were given.
Every answer goes through `step`. -/
def runAuto (fuel : Nat) : Nat → Rng → GameState → Except RuleError GameState
  | 0, _, s => .ok s
  | n + 1, r, s =>
    match autoAnswer r s with
    | none => .ok s
    | some (a, r') =>
      match step fuel s a with
      | .ok (s', _) => runAuto fuel n r' s'
      | .error e => .error e

end RiftboundDriver

end
