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

/-- Every way the player can put one of the abilities of the group on the Chain: each ability with
each legal pick of targets and costs, or a decision to pass it over (CR 383.3, 355). -/
def legalPuts (s : GameState) (p : PlayerId) (grp : List PendTrigger) : List Action :=
  (List.range grp.length).flatMap (fun (i : Nat) =>
    match grp[i]? with
    | some g => (trigOptions s g).map (fun (ts, payment) => ⟨.player p, .putTrigger i ts payment⟩)
    | none => [])

/-- The puts listed are exactly the legal ones. -/
theorem mem_legalPuts (s : GameState) (p : PlayerId) (grp : List PendTrigger) (a : Action) :
    a ∈ legalPuts s p grp ↔ ∃ i ts payment, a = ⟨.player p, .putTrigger i ts payment⟩ ∧
      (grp[i]?.any (fun g => trigLegal s g ts payment)) = true := by
  unfold legalPuts
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, ha⟩
    rcases hg : grp[i]? with _ | g
    · rw [hg] at ha
      simp at ha
    · rw [hg] at ha
      simp only [List.mem_map] at ha
      obtain ⟨⟨ts, payment⟩, hts, rfl⟩ := ha
      exact ⟨i, ts, payment, rfl, by rw [hg]; simp [(mem_trigOptions s g ts payment).mp hts]⟩
  · rintro ⟨i, ts, payment, rfl, h⟩
    rcases hg : grp[i]? with _ | g
    · rw [hg] at h
      simp at h
    · rw [hg] at h
      refine ⟨i, (List.getElem?_eq_some_iff.mp hg).1, ?_⟩
      rw [hg]
      simp only [Option.any_some] at h
      simp only [List.mem_map]
      exact ⟨(ts, payment), (mem_trigOptions s g ts payment).mpr h, rfl⟩

/-- The answers of the players to the open question. Chance answers are not listed. -/
def legalFrameActions (s : GameState) : List Action :=
  match s.pending with
  | .mulligan p n :: _ =>
    (if n < 2 then
      (s.zone (.player p .hand)).map (fun c => ⟨.player p, .mulliganPick c⟩)
    else []) ++ [⟨.player p, .mulliganDone⟩]
  | .discard p n :: _ =>
    if s.zone (.player p .hand) = [] ∨ n = 0 then [⟨.player p, .discardDone⟩]
    else (s.zone (.player p .hand)).map (fun c => ⟨.player p, .discardPick c⟩)
  | .mayDo p .. :: _ => [⟨.player p, .decide true⟩, ⟨.player p, .decide false⟩]
  | .eitherDo p src env x y _ :: _ =>
    ([⟨.player p, .decide true⟩, ⟨.player p, .decide false⟩] : List Action).filter (fun a =>
      match a.kind with
      | .decide yes => eitherOk s p src env x y yes
      | _ => true) ++
    (if x.isPayment then legalRunes s p ++ legalManas s p else [])
  | .pickDo p _ _ c more _ _ :: _ => (c :: more).map (fun o => ⟨.player p, .choose o⟩)
  | .nameCard p _ _ c more _ :: _ => (c :: more).map (fun id => ⟨.player p, .nameCard id⟩)
  | .chooseBurnOut p :: _ =>
    ((allPlayers s.playerCount).filter (fun o => o ≠ p)).map
      (fun o => ⟨.player p, .burnOutTarget o⟩)
  | .priority p :: _ =>
    ⟨.player p, .pass⟩ :: (legalRunes s p ++ legalManas s p ++ legalPlays s p ++
      legalMoves s p ++ legalActivates s p true)
  | .chainPass p _ :: _ =>
    ⟨.player p, .pass⟩ :: (legalRunes s p ++ legalManas s p ++ legalReactions s p ++
      legalActivates s p false)
  | .triggerOrder p t more _ :: _ => legalPuts s p (t :: more)
  | .showdown _ q _ :: _ =>
    ⟨.player q, .pass⟩ :: (legalRunes s q ++ legalManas s q ++ legalShowdownPlays s q ++
      legalShowdownActivates s q)
  | .assign bf _ side acc _ :: _ => legalAssigns s bf side acc
  | .predict p _ c cs _ _ :: _ =>
    (c :: cs).flatMap (fun id => [⟨.player p, .predictPick id false⟩, ⟨.player p, .predictPick id true⟩])
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
