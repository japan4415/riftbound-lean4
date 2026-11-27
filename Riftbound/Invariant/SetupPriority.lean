module

public import Riftbound.Invariant.Priority
public import Riftbound.Invariant.Progress
public import Riftbound.Invariant.Setup

/-! # Neutral priority during setup (I17) -/

@[expose] public section

namespace Riftbound

/-- None of the given frames can offer ordinary priority. -/
def noNeutralPriority (frames : List Frame) : Prop := ∀ p, Frame.priority p ∉ frames

/-- The first turn queues priority behind Awaken, which ends the setup before it can be offered. -/
def SetupPriority (s : GameState) : Prop :=
  s.phase = .setup → noNeutralPriority s.pending ∨ s.pending.head? = some (.phase .awaken)

/-- Neutral priority at the front of an opening stack implies setup has already ended. -/
theorem SetupPriority.not_setup {s : GameState} (known : SetupPriority s) {p : PlayerId}
    {rest : List Frame} (pending : s.pending = .priority p :: rest) : s.phase ≠ .setup := by
  intro setup
  rcases known setup with closed | awakening
  · exact closed p (pending ▸ List.mem_cons_self)
  · simp [pending] at awakening

private theorem noNeutralPriority.tail {frame : Frame} {rest : List Frame}
    (before : noNeutralPriority (frame :: rest)) : noNeutralPriority rest :=
  fun p present => before p (List.mem_cons_of_mem _ present)

private theorem noNeutralPriority.cons {frame : Frame} {rest : List Frame}
    (before : noNeutralPriority rest) (neutral : ∀ p, Frame.priority p ≠ frame) :
    noNeutralPriority (frame :: rest) := by
  intro p present
  exact (List.mem_cons.mp present).elim (neutral p) (before p)

private theorem setupPriority_beginTurn (s : GameState) (rest : List Frame) :
    SetupPriority (beginTurnStep s rest) := by
  intro _
  rcases beginTurnStep_cases s rest with ordinary | ⟨_, finished⟩
  · right
    simp [ordinary, turnFrames]
  · left
    simp [finished, noNeutralPriority]

private theorem microStep0_setupPriority {s t : GameState} {events : List Event}
    (phase : s.phase = .setup) (hands : HandInv s) (known : SetupPriority s)
    (worked : microStep0 s = some (t, events)) : SetupPriority t := by
  intro setup
  have without : noNeutralPriority s.pending := by
    rcases known phase with closed | awakening
    · exact closed
    · obtain ⟨rest, pending⟩ := List.head?_eq_some_iff.mp awakening
      have next := microStep_phase0 pending (by decide) worked
      simp [setup] at next
  cases pending : s.pending with
  | nil => simp [microStep0, pending] at worked
  | cons frame rest =>
    have tail := noNeutralPriority.tail (pending ▸ without)
    have notPlay : frame.isPlay ≠ true :=
      fun play => hands.play frame (pending ▸ List.mem_cons_self) play phase
    cases frame <;> simp [Frame.isPlay] at notPlay <;> simp [microStep0, pending] at worked
    case setupHands =>
      obtain ⟨rfl, _⟩ := worked
      left
      intro p present
      simp only [List.mem_append, List.mem_map, List.mem_cons] at present
      rcases present with ⟨_, _, equal⟩ | ⟨_, _, equal⟩ | equal | old
      · cases equal
      · cases equal
      · cases equal
      · exact tail p old
    case beginTurn =>
      obtain ⟨rfl, _⟩ := worked
      exact setupPriority_beginTurn s rest setup
    case phase ph =>
      cases ph <;> simp at worked
      case setup =>
        obtain ⟨rfl, _⟩ := worked
        exact Or.inl tail
      case draw =>
        obtain ⟨rfl, _⟩ := worked
        by_cases skip : s.hasControlledMod (s.active.getD ⟨0⟩) .skipDrawPhase
        · simpa only [skip, ite_true] using Or.inl tail
        · simp only [skip] at setup
          cases setup
      all_goals obtain ⟨rfl, _⟩ := worked; cases setup
    case scoreHolds =>
      obtain ⟨rfl, _⟩ := worked
      cases setup
    case draw p count start =>
      cases count with
      | zero =>
        simp at worked
        obtain ⟨rfl, _⟩ := worked
        exact Or.inl tail
      | succ count =>
        cases draw : drawOne s p with
        | none =>
          simp [draw] at worked
          obtain ⟨rfl, _⟩ := worked
          exact Or.inl <| noNeutralPriority.cons (frame := .chanceBurnOut p)
            (noNeutralPriority.cons (frame := .draw p (count + 1) start) tail
              (fun _ equal => by cases equal))
            (fun _ equal => by cases equal)
        | some drawn =>
          simp [draw] at worked
          obtain ⟨rfl, _⟩ := worked
          exact Or.inl (noNeutralPriority.cons (frame := .draw p count _) tail
            (fun _ equal => by cases equal))

private theorem withTriggers_eq_in_setup (s : GameState) (events : List Event)
    (phase : s.phase = .setup) : s.withTriggers events = s := by
  rcases withTriggers_cases s events with ⟨_, _, playing⟩ | recorded | ⟨_, _, playing, _⟩
  · exact (playing phase).elim
  · rw [recorded]
    cases s
    simp_all [GameState.recordTurnEvents]
  · exact (playing phase).elim

private theorem microStep_setupPriority {s t : GameState} {events : List Event}
    (phase : s.phase = .setup) (hands : HandInv s) (known : SetupPriority s)
    (worked : microStep s = some (t, events)) : SetupPriority t := by
  intro setup
  obtain ⟨raw, result, rfl⟩ := microStep_cases worked
  obtain ⟨_, _, updated⟩ := withTriggers_pending raw (events ++ s.workTransitionEvents raw)
  have rawPhase : raw.phase = .setup := by rw [updated] at setup; exact setup
  rw [withTriggers_eq_in_setup _ _ rawPhase]
  exact microStep0_setupPriority phase hands known result rawPhase

private theorem removePlayer_setupPriority {s after : GameState} {frame : Frame}
    (noPlay : frame.isPlay = false) (ordinary : ∀ p, Frame.priority p ≠ frame)
    (departing : PlayerId) : noNeutralPriority (frame.afterPlayerRemoval s after departing) := by
  intro p appears
  cases frame <;> simp [Frame.isPlay] at noPlay
  case priority owner => exact ordinary owner rfl
  case' chanceShuffle zone => cases zone
  case' phase phase => cases phase
  all_goals simp only [Frame.afterPlayerRemoval] at appears
  all_goals try (simp at appears)
  all_goals try (split at appears <;> try simp at appears)
  all_goals try (split at appears <;> try simp at appears)
  all_goals try (unfold GameState.survivingBurnOutDecision at appears <;> split at appears <;> simp at appears)

private theorem applyFrame0_setupPriority {s t : GameState} {a : Action} {events : List Event}
    (phase : s.phase = .setup) (hands : HandInv s) (known : noNeutralPriority s.pending)
    (applied : applyFrame0 s a = some (t, events)) : noNeutralPriority t.pending := by
  have forbidden {frame rest} (pending : s.pending = frame :: rest) (play : frame.isPlay = true) :
      False := hands.play frame (pending ▸ List.mem_cons_self) play phase
  have noPriority {p rest} (pending : s.pending = .priority p :: rest) : False :=
    known p (pending ▸ List.mem_cons_self)
  have suffix {frame rest} (pending : s.pending = frame :: rest) : noNeutralPriority rest :=
    noNeutralPriority.tail (pending ▸ known)
  unfold applyFrame0 at applied
  split at applied
  all_goals first
    | exact (forbidden (by assumption) rfl).elim
    | exact (noPriority (by assumption)).elim
    | skip
  all_goals try contradiction
  all_goals try (solve
    | simp only [Option.some.injEq, Prod.mk.injEq] at applied
      obtain ⟨rfl, _⟩ := applied
      first
      | exact known
      | exact suffix (by assumption)
      | intro p member
        simp only [List.mem_cons, reduceCtorEq, false_or] at member
        exact suffix (by assumption) p member
      | simp [noNeutralPriority])
  case h_25 =>
    split at applied
    · obtain ⟨⟨_, _⟩, _, resolved⟩ := Option.map_eq_some_iff.mp applied
      obtain ⟨rfl, _⟩ := Prod.mk.inj resolved
      exact suffix (by assumption)
    · contradiction
  case h_27 =>
    obtain ⟨⟨_, _⟩, _, resolved⟩ := Option.map_eq_some_iff.mp applied
    obtain ⟨rfl, _⟩ := Prod.mk.inj resolved
    intro p member
    simp only [List.mem_cons, reduceCtorEq, false_or] at member
    exact suffix (by assumption) p member
  case h_28 =>
    split at applied <;> simp only [Option.some.injEq, Prod.mk.injEq] at applied <;>
      obtain ⟨rfl, _⟩ := applied
    · exact suffix (by assumption)
    · intro p member
      simp only [List.mem_cons, reduceCtorEq, false_or] at member
      exact suffix (by assumption) p member
  case h_29 =>
    obtain ⟨_, _, resolved⟩ := Option.map_eq_some_iff.mp applied
    obtain ⟨rfl, _⟩ := Prod.mk.inj resolved
    exact suffix (by assumption)
  case h_30 =>
    rename_i player rest _ pending _
    obtain ⟨_, _, resolved⟩ := Option.map_eq_some_iff.mp applied
    obtain ⟨rfl, _⟩ := Prod.mk.inj resolved
    intro p member
    rcases List.mem_append.mp member with choice | old
    · rcases s.burnOutDecision_cases player with ordinary | empty | ⟨_, _, refreshed⟩
      · simp [ordinary] at choice
      · simp [empty] at choice
      · simp [refreshed] at choice
    · exact suffix pending p old

private theorem concession_setupPriority {s t : GameState} {seat : PlayerId} {blank : CardId}
    {events : List Event} (phase : s.phase = .setup) (hands : HandInv s)
    (known : noNeutralPriority s.pending)
    (removed : applyFreeForAllConcession s seat blank = some (t, events)) :
    noNeutralPriority t.pending := by
  rcases applyFreeForAllConcession_cases removed with ⟨_, rfl⟩ | ⟨board, _, rfl⟩
  · simp [noNeutralPriority]
  · have remaining : noNeutralPriority (s.pending.flatMap (fun f => f.afterPlayerRemoval s board seat)) := by
      intro p present
      obtain ⟨frame, old, current⟩ := List.mem_flatMap.mp present
      have noPlay : frame.isPlay = false := by
        cases yes : frame.isPlay
        · rfl
        · exact (hands.play frame old yes phase).elim
      exact removePlayer_setupPriority noPlay
        (fun q equal => known q (equal ▸ old)) seat p current
    change noNeutralPriority (s.pendingAfterConcession board seat)
    unfold GameState.pendingAfterConcession
    split
    · exact remaining
    · exact noNeutralPriority.cons (frame := .cleanup) remaining (fun _ equal => by cases equal)

private theorem applyAction_setupPriority {s t : GameState} {a : Action} {events : List Event}
    (phase : s.phase = .setup) (hands : HandInv s) (known : noNeutralPriority s.pending)
    (applied : applyAction s a = some (t, events)) : SetupPriority t := by
  intro setup
  left
  by_cases concession : a.kind = .concede
  · cases actor : a.actor with
    | player seat =>
      cases mode : s.config.mode.isFreeForAll with
      | false =>
        rw [applyAction_concede concession actor mode] at applied
        obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
        simp [noNeutralPriority]
      | true =>
        obtain ⟨board, _, removed, next⟩ := applyAction_concede_ffa_cases concession actor mode applied
        subst t
        have retained : ({ board with cards := board.cards.withConcessionBattlefield } : GameState).phase = .setup :=
          (applyFreeForAllConcession_meta removed).2.1.trans phase
        rw [withTriggers_eq_in_setup _ _ retained]
        have retainedPending : noNeutralPriority board.pending := concession_setupPriority phase hands known removed
        exact retainedPending
    | chance => simp [applyAction, concession, actor] at applied
    | judge => simp [applyAction, concession, actor] at applied
    | clock => simp [applyAction, concession, actor] at applied
  · rw [applyAction_of_ne concession] at applied
    obtain ⟨raw, seen, paid, rawAction, pool, rfl, _⟩ := applyFrame_cases applied
    obtain ⟨_, _, updated⟩ := withTriggers_pending paid (seen ++ extraEvents a seen ++ s.actionTransitionEvents paid a)
    have paidPhase : paid.phase = .setup := by rw [updated] at setup; exact setup
    rw [withTriggers_eq_in_setup _ _ paidPhase, pool.pending_eq]
    exact applyFrame0_setupPriority phase hands known rawAction

private theorem applyDeclaredAction_setupPriority {s t : GameState} {a : Action} {events : List Event}
    (phase : s.phase = .setup) (hands : HandInv s) (known : noNeutralPriority s.pending)
    (applied : applyDeclaredAction s a = some (t, events)) : SetupPriority t := by
  rcases applyDeclaredAction_cases applied with ordinary | ⟨_, _, _, _, choice, _, _⟩
  · exact applyAction_setupPriority phase hands known ordinary
  · exact ((GameState.actionDeathCostChoice_context choice).1 phase).elim

private theorem phase_of_safeP {s t : GameState} (safe : SafeP s t) : t.phase = s.phase := by
  obtain ⟨_, metadata, rfl | ⟨_, _, rfl⟩⟩ := safe <;> exact metadata.same.phase

private theorem showdownEnd_phase_eq (s : GameState) (field : ObjId) (rest : List Frame) :
    (showdownEnd s field rest).1.phase = s.phase := by
  rcases showdownEnd_cases s field rest with ⟨_, next⟩ | next <;> rw [next]
  change (endShowdown s field).1.phase = s.phase
  exact phase_of_safeP (endShowdown_safeP s field)

private theorem microStep0_phase_was_setup {s t : GameState} {events : List Event}
    (worked : microStep0 s = some (t, events)) (setup : t.phase = .setup) : s.phase = .setup := by
  unfold microStep0 at worked
  split at worked
  all_goals try contradiction
  all_goals try (solve
    | obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
      exact setup
    | obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
      exfalso
      cases setup)
  case h_2 =>
    rename_i rest _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
    rcases beginTurnStep_cases s rest with next | ⟨_, next⟩ <;> rw [next] at setup <;> exact setup
  case h_5 =>
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
    cases skip : s.hasControlledMod (s.active.getD ⟨0⟩) .skipDrawPhase
    · simp [skip] at setup
    · simpa [skip] using setup
  case h_13 =>
    split at worked
    · rename_i _ _ drawn
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
      exact (drawOne_meta drawn).phase.symm.trans setup
    · obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
      exact setup
  case h_16 =>
    rename_i p src env effect effects _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
    exact (runEffect_safe s p src (env.withMight s.mightTable) effect effects effectAddPolicy).same.phase.symm.trans setup
  case h_17 =>
    rename_i card _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
    exact (finishItem_sameMeta s card).phase.symm.trans setup
  case h_18 =>
    rename_i rest _
    have target : (cleanupFrame s rest).1 = t := congrArg Prod.fst (Option.some.inj worked)
    rw [← target] at setup
    rcases cleanupFrame_cases s rest with ⟨_, next⟩ | ⟨_, _, _, _, next⟩ |
      ⟨_, safe, next⟩ | ⟨_, _, next⟩ | ⟨_, _, _, next⟩ | next <;> rw [next] at setup
    all_goals first | exact setup | exact safe.same.phase.symm.trans setup
  case h_20 =>
    rename_i field attacker _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
    exact (combatCleanup_safe s field attacker).same.phase.symm.trans setup
  case h_22 =>
    rename_i field _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
    exact (phase_of_safeP (combatControl_safeP s field)).symm.trans setup
  case h_24 =>
    rename_i pending rest _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj worked)
    exact (triggersStep_spec s pending rest).1.same.phase.symm.trans setup
  case h_25 =>
    rename_i field rest _
    have target : (showdownEnd s field rest).1 = t := congrArg Prod.fst (Option.some.inj worked)
    rw [← target] at setup
    exact (showdownEnd_phase_eq s field rest).symm.trans setup

private theorem applyFrame0_phase_eq {s t : GameState} {a : Action} {events : List Event}
    (applied : applyFrame0 s a = some (t, events)) : t.phase = s.phase := by
  unfold applyFrame0 at applied
  split at applied
  all_goals try (solve
    | contradiction
    | exact (applyRune_meta applied).2.2.1
    | exact (applyPlayCard_meta applied).2.2.1
    | exact (reactStep_meta applied).2.2.1
    | exact (activateStep_meta applied).2.2.1
    | exact (applyMana_meta applied).2.2.1
    | obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
      rfl)
  case h_4 =>
    obtain ⟨⟨_, _⟩, moved, finished⟩ := Option.map_eq_some_iff.mp applied
    obtain ⟨rfl, _⟩ := Prod.mk.inj finished
    exact (applyMove_safe moved).same.phase
  case h_5 =>
    rename_i field _ _ rest _ _
    split at applied <;> obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
    · rfl
    · exact showdownEnd_phase_eq s field rest
  case h_7 =>
    rename_i field attacker side choices done rest _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
    change (assignDoneStep s field attacker side choices done rest).1.phase = s.phase
    rcases assignDoneStep_cases s field attacker side choices done rest with
      ⟨_, _, _, _, next⟩ | ⟨_, next⟩ | ⟨_, safe, next⟩ <;> rw [next]
    exact safe.same.phase
  case h_8 =>
    split at applied <;> obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied) <;> rfl
  case h_13 =>
    rename_i _ first more _ funding _ index targets payment _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
    exact (finishTrigger_safe s (first :: more) funding index targets payment).same.phase
  case h_17 =>
    obtain ⟨⟨_, _⟩, funded, finished⟩ := Option.map_eq_some_iff.mp applied
    obtain ⟨rfl, _⟩ := Prod.mk.inj finished
    exact (applyMana_meta funded).2.2.1
  case h_19 =>
    rename_i _ _ _ card _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
    exact (discardObj_safe s card).same.phase
  case h_25 =>
    split at applied
    · obtain ⟨⟨_, _⟩, moved, finished⟩ := Option.map_eq_some_iff.mp applied
      obtain ⟨rfl, _⟩ := Prod.mk.inj finished
      exact (Safe.moveObj moved).same.phase
    · contradiction
  case h_27 =>
    obtain ⟨⟨_, _⟩, moved, finished⟩ := Option.map_eq_some_iff.mp applied
    obtain ⟨rfl, _⟩ := Prod.mk.inj finished
    exact (Safe.moveObj moved).same.phase
  case h_28 =>
    split at applied <;> obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied) <;> rfl
  case h_29 =>
    obtain ⟨_, recycled, finished⟩ := Option.map_eq_some_iff.mp applied
    obtain ⟨rfl, _⟩ := Prod.mk.inj finished
    exact (recycleAll_meta _ _ recycled).phase
  case h_30 =>
    obtain ⟨_, recycled, finished⟩ := Option.map_eq_some_iff.mp applied
    obtain ⟨rfl, _⟩ := Prod.mk.inj finished
    exact (recycleAll_meta _ _ recycled).phase
  case h_39 =>
    rename_i player count first more top bottom _ chosen recycle _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
    exact (continuePrediction_safe s player count ((first :: more).erase chosen)
      (if recycle then top else top ++ [chosen]) (if recycle then chosen :: bottom else bottom)).same.phase
  case h_40 =>
    rename_i player count top _ _ bottom _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
    exact (completePrediction_safe s player count top bottom).same.phase
  case h_41 =>
    rename_i _ _ _ _ order _ _
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
    exact (recycleTrashCards_safe s order).same.phase
  case h_52 =>
    obtain ⟨_, _, finished⟩ := Option.map_eq_some_iff.mp applied
    obtain ⟨rfl, _⟩ := Prod.mk.inj finished
    rfl
  case h_56 =>
    obtain ⟨result, moved, finished⟩ := Option.map_eq_some_iff.mp applied
    have next : _ = t := congrArg Prod.fst finished
    rw [← next]
    exact (applyGroupMove_safe moved).same.phase

private theorem withTriggers_phase_eq (s : GameState) (events : List Event) :
    (s.withTriggers events).phase = s.phase := by
  obtain ⟨_, _, updated⟩ := withTriggers_pending s events
  rw [updated]
  rfl

private theorem applyAction_phase_eq {s t : GameState} {a : Action} {events : List Event}
    (applied : applyAction s a = some (t, events)) : t.phase = s.phase := by
  by_cases concession : a.kind = .concede
  · cases actor : a.actor with
    | player seat =>
      cases mode : s.config.mode.isFreeForAll with
      | false =>
        rw [applyAction_concede concession actor mode] at applied
        obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj applied)
        rfl
      | true =>
        obtain ⟨board, _, removed, rfl⟩ := applyAction_concede_ffa_cases concession actor mode applied
        rw [withTriggers_phase_eq]
        exact (applyFreeForAllConcession_meta removed).2.1
    | chance => simp [applyAction, concession, actor] at applied
    | judge => simp [applyAction, concession, actor] at applied
    | clock => simp [applyAction, concession, actor] at applied
  · rw [applyAction_of_ne concession] at applied
    obtain ⟨raw, _, paid, rawAction, pool, rfl, _⟩ := applyFrame_cases applied
    rw [withTriggers_phase_eq]
    have retained := applyFrame0_phase_eq rawAction
    rcases pool with rfl | ⟨_, _, rfl⟩ <;> exact retained

private theorem applyDeclaredAction_phase_eq {s t : GameState} {a : Action} {events : List Event}
    (applied : applyDeclaredAction s a = some (t, events)) : t.phase = s.phase := by
  rcases applyDeclaredAction_cases applied with ordinary | ⟨_, _, _, _, _, rfl, _⟩
  · exact applyAction_phase_eq ordinary
  · rfl

private theorem workStep_setupPriority {s t : GameState} {events : List Event} (hands : HandInv s)
    (known : SetupPriority s) (worked : workStep s = some (t, events)) : SetupPriority t := by
  intro setup
  rcases workStep_cases worked with ordinary | ⟨a, rest, pending, resumed⟩
  · obtain ⟨raw, core, same⟩ := microStep_cases ordinary
    have rawPhase : raw.phase = .setup := by rwa [same, withTriggers_phase_eq] at setup
    exact microStep_setupPriority (microStep0_phase_was_setup core rawPhase) hands known ordinary setup
  · have sourcePhase : s.phase = .setup := by
      rcases resumed with ⟨_, _, applied⟩ | ⟨same, _⟩
      · exact (applyDeclaredAction_phase_eq applied).symm.trans setup
      · rw [same] at setup
        exact setup
    exact (hands.play (.resumeCost a) (pending ▸ List.mem_cons_self) rfl sourcePhase).elim

private theorem SetupPriority.prepare {s : GameState} (known : SetupPriority s) :
    SetupPriority s.preparePriority := by
  intro setup
  have samePhase : s.phase = .setup := s.preparePriority_phase ▸ setup
  rw [GameState.preparePriority_of_setup samePhase]
  exact known samePhase

private theorem advance_setupPriority {s t : GameState} {fuel : Nat} {seen events : List Event}
    (wf : s.WF) (owner : s.OwnerOk) (hands : HandInv s) (guarded : SetupPriority s)
    (advanced : advance fuel s seen = .ok (t, events)) : SetupPriority t := by
  have invariant := advance_preserves (fun x => x.WF ∧ x.OwnerOk ∧ HandInv x ∧ SetupPriority x)
    (fun _ ⟨valid, owned, hand, setup⟩ =>
      ⟨valid.preparePriority, owned.preparePriority, hand.preparePriority, setup.prepare⟩)
    (fun ⟨valid, owned, hand, setup⟩ work =>
      ⟨workStep_wf valid work, workStep_ownerOk valid owned work, workStep_handInv valid owned hand work,
        workStep_setupPriority hand setup work⟩)
    ⟨wf, owner, hands, guarded⟩ advanced
  exact invariant.2.2.2

private theorem TopIdle.no_setup_priority {s : GameState} (idle : TopIdle s) (known : SetupPriority s)
    (phase : s.phase = .setup) : noNeutralPriority s.pending := by
  rcases known phase with closed | awakening
  · exact closed
  · obtain ⟨rest, pending⟩ := List.head?_eq_some_iff.mp awakening
    have : (Frame.phase .awaken).isWork = false := idle _ rest pending
    contradiction

private theorem Start.openingFrames {s : GameState} (start : Start s) :
    s.pending = startFrames s.playerCount := by
  cases start with
  | core built => exact GameState.initial_pending built
  | limited built => exact GameState.initialLimited_pending built

private theorem Start.topIdle {s : GameState} (start : Start s) : TopIdle s := by
  intro frame rest pending
  apply (startFrames_spec s.playerCount).1 frame
  rw [← start.openingFrames, pending]
  exact List.mem_cons_self

private theorem Start.noNeutralPriority {s : GameState} (start : Start s) : noNeutralPriority s.pending := by
  intro p present
  have := startFrames_isSetup _ _ (start.openingFrames ▸ present)
  contradiction

private theorem Reachable.setupPriorityIdle {s : GameState} (reachable : Reachable s) :
    SetupPriority s ∧ TopIdle s := by
  induction reachable with
  | init start => exact ⟨fun _ => Or.inl start.noNeutralPriority, start.topIdle⟩
  | next prior stepped ih =>
    refine ⟨?_, step_idle stepped⟩
    have wf := prior.inv.1
    have owner := prior.inv.2
    have hands := prior.handInv
    unfold step at stepped
    split at stepped
    · rename_i legal
      split at stepped
      · rename_i after declaredEvents declared
        have afterGuard : SetupPriority after := by
          intro phase
          have before := (applyDeclaredAction_phase_eq declared).symm.trans phase
          have closed := ih.2.no_setup_priority ih.1 before
          exact applyDeclaredAction_setupPriority before hands closed declared phase
        exact advance_setupPriority (applyDeclaredAction_wf wf legal declared)
          (applyDeclaredAction_ownerOk wf owner legal declared)
          (applyDeclaredAction_handInv wf owner hands legal declared) afterGuard stepped
      · contradiction
    · contradiction

/-- In any reachable game, neutral priority is offered only after Cleanup has settled the board. -/
theorem Reachable.priority_settled {s : GameState} (reachable : Reachable s) {p : PlayerId} {rest}
    (pending : s.pending = .priority p :: rest) : s.Settled := by
  have playing := reachable.setupPriorityIdle.1.not_setup pending
  cases reachable with
  | init start => exact (start.noNeutralPriority p (pending ▸ List.mem_cons_self)).elim
  | next _ applied => exact step_priority_settled applied pending playing

end Riftbound

end
