module

public import Riftbound.Spec.Legal

/-!
# The engine

`step` takes one answer, checks it with `Legal`, applies it, and works through the frames until
the next decision (design.md §6.1). `legalActions` lists the answers of the players, built
from the board, not by trying `step` (design.md §6.3).
-/

@[expose] public section

namespace Riftbound

/-- Why a step failed. -/
inductive RuleError where
  /-- The answer is not legal. -/
  | illegal
  /-- The automatic work did not reach the next decision within the fuel. -/
  | fuelExhausted
  /-- The engine's own bookkeeping failed. Under a well-formed state this does not happen
  (invariant I4, roadmap.md). -/
  | internal (msg : String)
deriving DecidableEq, Repr

/-- Work through the work frames until the next decision or the end, one `microStep` at a time.
`fuel` is the number of steps allowed. -/
def advance : Nat → GameState → List Event → Except RuleError (GameState × List Event)
  | 0, s, es =>
    match s.pending with
    | f :: _ => if f.isWork then .error .fuelExhausted else .ok (s, es)
    | [] => .ok (s, es)
  | n + 1, s, es =>
    match s.pending with
    | f :: _ =>
      if f.isWork then
        match microStep s with
        | some (s', es') => advance n s' (es ++ es')
        | none => .error (.internal "microStep")
      else .ok (s, es)
    | [] => .ok (s, es)

/-- Take one answer. -/
def step (fuel : Nat) (s : GameState) (a : Action) :
    Except RuleError (GameState × List Event) :=
  if Legal s a then
    match applyAction s a with
    | some (s1, es) => advance fuel s1 es
    | none => .error (.internal "applyAction")
  else .error .illegal

/-- The abilities of the player's Basic Runes that can be used (CR 164.2). -/
def legalRunes (s : GameState) (p : PlayerId) : List Action :=
  (s.zone (.player p .base)).flatMap (fun c =>
    ([RuneAbility.exhaust, .recycle].filter (fun ab => runeUsable s p c ab)).map
      (fun ab => ⟨.player p, .runeAbility c ab⟩))

/-- The answers of the players to the open question. Chance answers are not listed. -/
def legalFrameActions (s : GameState) : List Action :=
  match s.pending with
  | .mulligan p n :: _ =>
    (if n < 2 then
      (s.zone (.player p .hand)).map (fun c => ⟨.player p, .mulliganPick c⟩)
    else []) ++ [⟨.player p, .mulliganDone⟩]
  | .chooseBurnOut p :: _ =>
    ((allPlayers s.playerCount).filter (fun o => o ≠ p)).map
      (fun o => ⟨.player p, .burnOutTarget o⟩)
  | .priority p :: _ =>
    ⟨.player p, .pass⟩ :: (legalRunes s p ++ legalPlays s p ++ legalMoves s p ++
      legalActivates s p true)
  | .chainPass p _ :: _ =>
    ⟨.player p, .pass⟩ :: (legalRunes s p ++ legalReactions s p ++ legalActivates s p false)
  | .showdown _ q _ :: _ => [⟨.player q, .pass⟩]
  | .assign bf _ side acc _ :: _ => legalAssigns s bf side acc
  | _ => []

/-- The concessions: any player may concede at any time in a 1v1 game (CR 649-651). -/
def concedeActions (s : GameState) : List Action :=
  if s.playerCount = 2 then (allPlayers 2).map (fun p => ⟨.player p, .concede⟩) else []

/-- The answers of the players: to the open question, and the concessions. Nothing once the game
is over. -/
def legalActions (s : GameState) : List Action :=
  if s.result = none then legalFrameActions s ++ concedeActions s else []

end Riftbound

end
