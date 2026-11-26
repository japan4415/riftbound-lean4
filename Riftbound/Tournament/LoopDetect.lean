module

public import Riftbound.Invariant.Progress

/-! # Checking a forced loop (TR 505)

The checker accepts a recorded cycle only if each answer is the sole ordinary player action and
replaying the cycle returns to the same state. A judge can use this evidence to rule on the game (TR 505.6).
-/

public section

namespace Riftbound

/-- The only ordinary answer at a player decision, if it is forced. Tournament interventions,
concessions and chance answers are outside this test (TR 505.2.a, 505.6). -/
def forcedAnswer (s : GameState) : Option Action :=
  if s.result.isSome || s.pending.head?.any Frame.isChance then none
  else
    match (legalFrameActions s).eraseDups with
    | [action] => some action
    | _ => none

/-- When an answer is forced, every legal ordinary answer by a player is that answer. -/
theorem forcedAnswer_unique {s : GameState} {answer other : Action}
    (forced : forcedAnswer s = some answer) (legal : LegalFrame s other)
    (player : other.actor.isPlayer = true) : other = answer := by
  have listed := (legalFrameActions_iff s other).mpr ⟨legal, player⟩
  unfold forcedAnswer at forced
  split at forced
  · simp at forced
  · split at forced
    · rename_i only single
      simp only [Option.some.injEq] at forced
      have member := List.mem_eraseDups.mpr listed
      rw [single] at member
      simpa [forced] using member
    · simp at forced

/-- Play the recorded answers, stopping if one is optional or fails to advance. -/
def runForcedAnswers (fuel : Nat) (s : GameState) (answers : List Action) : Option GameState :=
  match answers with
  | [] => some s
  | answer :: rest => do
    if forcedAnswer s != some answer then none
    else
      let (next, _) ← (step fuel s answer).toOption
      runForcedAnswers fuel next rest

/-- Running two consecutive forced sequences is the same as running their concatenation. -/
theorem runForcedAnswers_append (fuel : Nat) (s : GameState) (left right : List Action) :
    runForcedAnswers fuel s (left ++ right) =
      (runForcedAnswers fuel s left).bind (fun next => runForcedAnswers fuel next right) := by
  induction left generalizing s with
  | nil => rfl
  | cons answer rest ih =>
    simp only [List.cons_append, runForcedAnswers]
    split
    · rfl
    · cases applied : (step fuel s answer).toOption with
      | none => rfl
      | some outcome =>
        obtain ⟨next, _⟩ := outcome
        exact ih next

/-- A nonempty cycle of forced answers that returns to an identical decision state. -/
def isExactForcedLoop (fuel : Nat) (s : GameState) (answers : List Action) : Bool :=
  !answers.isEmpty && decide (runForcedAnswers fuel s answers = some s)

/-- **I19**, identical-state case. Each positive number of iterations is a valid run of the
same forced answers, ending at the starting state (TR 505.6). -/
theorem isExactForcedLoop_repeats {fuel : Nat} {s : GameState} {answers : List Action}
    (loop : isExactForcedLoop fuel s answers = true) (rounds : Nat) :
    answers ≠ [] ∧ runForcedAnswers fuel s (List.replicate rounds answers).flatten = some s := by
  obtain ⟨nonempty, same⟩ := Bool.and_eq_true_iff.mp loop
  refine ⟨by simpa using nonempty, ?_⟩
  have cycle := of_decide_eq_true same
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    rw [List.replicate_succ, List.flatten_cons, runForcedAnswers_append, cycle]
    exact ih

private def findExactForcedLoop (fuel : Nat) (current : GameState) :
    List (GameState × Action) → List Action → Option (List Action)
  | [], _ => none
  | (before, answer) :: earlier, later =>
    let answers := answer :: later
    if before.turn == current.turn && before.nextId == current.nextId &&
        before.nextTimestamp == current.nextTimestamp && before == current &&
        isExactForcedLoop fuel current answers then some answers
    else findExactForcedLoop fuel current earlier answers

/-- Search decision history, most recent first, for a certified forced cycle ending here. Each
entry gives the state immediately before the answer. -/
def detectExactForcedLoop (fuel : Nat) (current : GameState)
    (history : List (GameState × Action)) : Option (List Action) :=
  findExactForcedLoop fuel current history []

private theorem findExactForcedLoop_sound {fuel : Nat} {current : GameState}
    {history : List (GameState × Action)} {later answers : List Action}
    (found : findExactForcedLoop fuel current history later = some answers) :
    isExactForcedLoop fuel current answers = true := by
  induction history generalizing later with
  | nil => simp [findExactForcedLoop] at found
  | cons entry earlier ih =>
    obtain ⟨before, answer⟩ := entry
    simp only [findExactForcedLoop] at found
    split at found
    · rename_i accepted
      obtain rfl := Option.some.inj found
      exact (Bool.and_eq_true_iff.mp accepted).2
    · exact ih found

/-- A detected cycle can be repeated any number of times using only forced answers. -/
theorem detectExactForcedLoop_sound {fuel : Nat} {current : GameState}
    {history : List (GameState × Action)} {answers : List Action}
    (found : detectExactForcedLoop fuel current history = some answers) (rounds : Nat) :
    answers ≠ [] ∧ runForcedAnswers fuel current (List.replicate rounds answers).flatten =
      some current :=
  isExactForcedLoop_repeats (findExactForcedLoop_sound found) rounds

end Riftbound

end
