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

/-- The answers of the players to the current question. Chance answers are not listed. -/
def legalActions (s : GameState) : List Action :=
  match s.pending with
  | .mulligan p n :: _ =>
    (if n < 2 then
      (s.zone (.player p .hand)).map (fun c => ⟨.player p, .mulliganPick c⟩)
    else []) ++ [⟨.player p, .mulliganDone⟩]
  | .chooseBurnOut p :: _ =>
    ((allPlayers s.playerCount).filter (fun o => o ≠ p)).map
      (fun o => ⟨.player p, .burnOutTarget o⟩)
  | _ => []

end Riftbound

end
