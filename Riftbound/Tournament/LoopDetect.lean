module

public import Riftbound.Invariant.Progress
public import Riftbound.Invariant.PrivateChoices

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

private theorem eraseDups_eq_single_answer {actions : List Action} {answer : Action} :
    actions.eraseDups = [answer] ↔ answer ∈ actions ∧ ∀ other ∈ actions, other = answer := by
  constructor
  · intro one
    refine ⟨List.mem_eraseDups.mp (by simp [one]), ?_⟩
    intro other member
    have preserved := List.mem_eraseDups.mpr member
    simpa only [one, List.mem_singleton] using preserved
  · rintro ⟨present, unique⟩
    cases actions with
    | nil => cases present
    | cons first rest =>
      have same := unique first (by simp)
      subst first
      have empty : (rest.filter (fun other => !(other == answer))) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro other member
        have ⟨inside, different⟩ := List.mem_filter.mp member
        simp [unique other (List.mem_cons_of_mem _ inside)] at different
      rw [List.eraseDups_cons, empty, List.eraseDups_nil]

/-- A player answer is forced exactly when it is listed and every listed answer equals it.
Finished games and chance decisions have no forced answer. -/
theorem forcedAnswer_eq_some_iff {s : GameState} {answer : Action} :
    forcedAnswer s = some answer ↔
      s.result.isSome = false ∧ s.pending.head?.any Frame.isChance = false ∧
      answer ∈ legalFrameActions s ∧ ∀ other ∈ legalFrameActions s, other = answer := by
  have shape :
      (match (legalFrameActions s).eraseDups with
       | [action] => some action
       | _ => none) = some answer ↔ (legalFrameActions s).eraseDups = [answer] := by
    cases (legalFrameActions s).eraseDups with
    | nil => simp
    | cons first rest => cases rest <;> simp
  unfold forcedAnswer
  cases s.result.isSome <;> cases s.pending.head?.any Frame.isChance <;>
    simp [shape, eraseDups_eq_single_answer]

/-- The order of the answer list is immaterial. An action renaming only needs to be injective on
the answers actually offered at the source decision. -/
theorem forcedAnswer_rename_perm {s t : GameState} (rename : Action → Action)
    (injective : ∀ ⦃a b⦄, a ∈ legalFrameActions s → b ∈ legalFrameActions s →
      rename a = rename b → a = b)
    (finished : s.result.isSome = t.result.isSome)
    (chance : s.pending.head?.any Frame.isChance = t.pending.head?.any Frame.isChance)
    (answers : (legalFrameActions t).Perm ((legalFrameActions s).map rename)) :
    forcedAnswer t = (forcedAnswer s).map rename := by
  have offered (a : Action) : a ∈ legalFrameActions t ↔
      ∃ original ∈ legalFrameActions s, rename original = a :=
    answers.mem_iff.trans List.mem_map
  cases source : forcedAnswer s with
  | none =>
    cases target : forcedAnswer t with
    | none => rfl
    | some mapped =>
      obtain ⟨ongoing, ordinary, listed, unique⟩ := forcedAnswer_eq_some_iff.mp target
      obtain ⟨original, eligible, rfl⟩ := (offered mapped).mp listed
      have prior : forcedAnswer s = some original := forcedAnswer_eq_some_iff.mpr
        ⟨finished.trans ongoing, chance.trans ordinary, eligible, fun a member =>
          injective member eligible (unique _ ((offered _).mpr ⟨a, member, rfl⟩))⟩
      simp [source] at prior
  | some answer =>
    obtain ⟨ongoing, ordinary, eligible, unique⟩ := forcedAnswer_eq_some_iff.mp source
    apply forcedAnswer_eq_some_iff.mpr
    refine ⟨finished.symm.trans ongoing, chance.symm.trans ordinary,
      (offered _).mpr ⟨answer, eligible, rfl⟩, ?_⟩
    intro other member
    obtain ⟨original, present, rfl⟩ := (offered other).mp member
    exact congrArg rename (unique original present)

/-- Translating all ordinary answers injectively preserves whether one answer is forced at a
player decision. The forced answer, if there is one, is translated with the same map. -/
theorem forcedAnswer_rename {s t : GameState} (rename : Action → Action)
    (injective : Function.Injective rename)
    (finished : s.result.isSome = t.result.isSome)
    (chance : s.pending.head?.any Frame.isChance = t.pending.head?.any Frame.isChance)
    (answers : legalFrameActions t = (legalFrameActions s).map rename) :
    forcedAnswer t = (forcedAnswer s).map rename := by
  apply forcedAnswer_rename_perm rename (fun {_ _} _ _ eq => injective eq) finished chance
  rw [answers]

/-- For an offered object choice, forcedness and its answer survive renaming the offered objects.
The renaming can be undefined outside the candidates in this decision. -/
theorem forcedAnswer_pickDo_rename {s t : GameState} {p : PlayerId}
    {srcS srcT firstS firstT : ObjId} {envS envT : Env} {x y : Effect}
    {restS restT : EffectList} {moreS moreT : List ObjId} {tailS tailT : List Frame}
    (rename : ObjId → ObjId)
    (hs : s.pending = .pickDo p srcS envS firstS moreS x restS :: tailS)
    (ht : t.pending = .pickDo p srcT envT firstT moreT y restT :: tailT)
    (finished : s.result.isSome = t.result.isSome)
    (injective : ∀ ⦃a b⦄, a ∈ firstS :: moreS → b ∈ firstS :: moreS →
      rename a = rename b → a = b)
    (offered : (firstT :: moreT).Perm ((firstS :: moreS).map rename)) :
    forcedAnswer t = (forcedAnswer s).map (Action.renameOfferedChoice rename) := by
  have chance : s.pending.head?.any Frame.isChance = t.pending.head?.any Frame.isChance := by
    simp [hs, ht, Frame.isChance]
  refine forcedAnswer_rename_perm (Action.renameOfferedChoice rename) ?_ finished chance
    (legalFrameActions_pickDo_rename rename hs ht offered)
  intro a b first second equal
  simp only [legalFrameActions, hs, List.mem_map] at first second
  obtain ⟨id, member, rfl⟩ := first
  obtain ⟨other, otherMember, rfl⟩ := second
  have renamed : rename id = rename other := by
    simpa only [Action.renameOfferedChoice, Action.mk.injEq, ActionKind.choose.injEq, true_and]
      using equal
  rw [injective member otherMember renamed]

/-- An open Predict is never forced because its first offered card can be kept or recycled. -/
theorem forcedAnswer_predict_none {s : GameState} {p : PlayerId} {count : Nat} {first : ObjId}
    {more top bottom : List ObjId} {rest : List Frame}
    (pending : s.pending = .predict p count first more top bottom :: rest) :
    forcedAnswer s = none := by
  cases forced : forcedAnswer s with
  | none => rfl
  | some answer =>
    obtain ⟨_, _, _, unique⟩ := forcedAnswer_eq_some_iff.mp forced
    have keep := unique ⟨.player p, .predictPick first false⟩ (by simp [legalFrameActions, pending])
    have recycle := unique ⟨.player p, .predictPick first true⟩ (by simp [legalFrameActions, pending])
    have cannot := keep.trans recycle.symm
    cases cannot

/-- A forced Combat assignment depends on the corresponding targets and their public facts.
Renaming the targets preserves both a forced pick and the decision to finish assigning. -/
theorem forcedAnswer_assign_rename {s t : GameState} {before after : ObjId}
    {attacker side : PlayerId} {assigned : List ObjId} {oldDamage newDamage : List (ObjId × Nat)}
    {tailS tailT : List Frame} (rename : ObjId → ObjId) (injective : Function.Injective rename)
    (hs : s.pending = .assign before attacker side assigned oldDamage :: tailS)
    (ht : t.pending = .assign after attacker side (assigned.map rename) newDamage :: tailT)
    (finished : s.result.isSome = t.result.isSome)
    (targets : t.assignmentTargets after side = (s.assignmentTargets before side).map rename)
    (controller : ∀ id ∈ s.assignmentTargets before side,
      t.controllerOf (rename id) = s.controllerOf id)
    (priority : ∀ id ∈ s.assignmentTargets before side,
      t.assignmentRank after side (rename id) = s.assignmentRank before side id) :
    forcedAnswer t = (forcedAnswer s).map (Action.renameAssignPick rename) := by
  have chance : s.pending.head?.any Frame.isChance = t.pending.head?.any Frame.isChance := by
    simp [hs, ht, Frame.isChance]
  refine forcedAnswer_rename_perm (Action.renameAssignPick rename) ?_ finished chance ?_
  · intro a b ha hb eq
    simp only [legalFrameActions, hs] at ha hb
    rcases mem_legalAssigns.mp ha with ⟨first, rfl, _⟩ | ⟨rfl, _⟩ <;>
      rcases mem_legalAssigns.mp hb with ⟨second, rfl, _⟩ | ⟨rfl, _⟩
    · simp only [Action.renameAssignPick, Action.mk.injEq, true_and, ActionKind.assignPick.injEq] at eq
      rw [injective eq]
    · cases eq
    · cases eq
    · rfl
  · rw [legalFrameActions_assign_rename rename injective hs ht targets controller priority]

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

/-- A state relation transports each checked forced answer to a forced answer at a related state. -/
def TransportsForcedAnswers (fuel : Nat) (related : GameState → GameState → Prop) : Prop :=
  ∀ ⦃s t next : GameState⦄ ⦃answer : Action⦄ ⦃events : List Event⦄,
    related s t → forcedAnswer s = some answer → step fuel s answer = .ok (next, events) →
    ∃ other next' events', forcedAnswer t = some other ∧
      step fuel t other = .ok (next', events') ∧ related next next'

/-- A checked sequence can be replayed from a related state with the same number of
answers, preserving the relation at its endpoint. -/
theorem runForcedAnswers_transport {fuel : Nat} {related : GameState → GameState → Prop}
    (transport : TransportsForcedAnswers fuel related) {s t next : GameState}
    {answers : List Action} (view : related s t)
    (run : runForcedAnswers fuel s answers = some next) :
    ∃ others next', others.length = answers.length ∧
      runForcedAnswers fuel t others = some next' ∧ related next next' := by
  induction answers generalizing s t with
  | nil =>
    change some s = some next at run
    obtain rfl := Option.some.inj run
    exact ⟨[], _, rfl, rfl, view⟩
  | cons answer rest ih =>
    simp only [runForcedAnswers] at run
    split at run
    · contradiction
    next canPlay =>
      have forced : forcedAnswer s = some answer := by simpa using canPlay
      cases act : step fuel s answer with
      | error error => simp [act, Except.toOption] at run
      | ok outcome =>
        obtain ⟨middle, events⟩ := outcome
        simp only [act, Except.toOption] at run
        obtain ⟨other, middle', events', forced', act', related'⟩ := transport view forced act
        obtain ⟨others, next', length, replay, relatedNext⟩ := ih related' run
        exact ⟨other :: others, next', by simp [length],
          by simp [runForcedAnswers, forced', act', Except.toOption, replay], relatedNext⟩

/-- Once a relation preserves forced transitions, a checked cycle closing under that
relation can be replayed arbitrarily many times, with potentially different action identifiers. -/
theorem runForcedAnswers_equivalentCycle_repeats {fuel : Nat} {related : GameState → GameState → Prop}
    (transport : TransportsForcedAnswers fuel related) (transitive : ∀ ⦃a b c⦄, related a b → related b c → related a c)
    {start finish current : GameState} {cycle : List Action}
    (run : runForcedAnswers fuel start cycle = some finish) (returns : related start finish)
    (currentRelated : related start current) (rounds : Nat) :
    ∃ answers final, answers.length = rounds * cycle.length ∧
      runForcedAnswers fuel current answers = some final ∧ related start final := by
  induction rounds generalizing current with
  | zero => exact ⟨[], current, by simp, rfl, currentRelated⟩
  | succ rounds ih =>
    obtain ⟨one, next, oneLength, first, nextRelated⟩ :=
      runForcedAnswers_transport transport currentRelated run
    obtain ⟨rest, final, restLength, remaining, finalRelated⟩ :=
      ih (current := next) (transitive returns nextRelated)
    refine ⟨one ++ rest, final, ?_, ?_, finalRelated⟩
    · rw [List.length_append, oneLength, restLength, Nat.succ_mul, Nat.add_comm]
    · simp [runForcedAnswers_append, first, remaining]

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

/-- Ordinary priority cannot be part of a forced loop while a Basic Rune can be used. -/
theorem forcedAnswer_priority_none_of_rune {s : GameState} {p : PlayerId} {rune : ObjId}
    {ability : RuneAbility} {rest : List Frame} (pending : s.pending = .priority p :: rest)
    (board : rune ∈ s.zone (.player p .base)) (usable : runeUsable s p rune ability = true) :
    forcedAnswer s = none := by
  let use : Action := ⟨.player p, .runeAbility rune ability⟩
  have offered : use ∈ legalRunes s p := by
    apply List.mem_flatMap.mpr
    refine ⟨rune, board, List.mem_map.mpr ⟨ability, ?_, rfl⟩⟩
    apply List.mem_filter.mpr
    exact ⟨by cases ability <;> simp, usable⟩
  cases step : forcedAnswer s with
  | none => rfl
  | some answer =>
    obtain ⟨_, _, _, unique⟩ := forcedAnswer_eq_some_iff.mp step
    have pass := unique ⟨.player p, .pass⟩ (by simp [legalFrameActions, pending])
    have rune := unique use (by simp [legalFrameActions, pending, offered])
    have distinct : (⟨.player p, .pass⟩ : Action) ≠ use := by simp [use]
    exact (distinct (pass.trans rune.symm)).elim

end Riftbound

end
