module

public import Riftbound.Invariant.RunWorkCore

/-!
# Work that reads card faces or asks for a name or type (I12)

Follow actual event observation and the nested resolution when a disclosure supplies cards to a body.
-/

@[expose] public section

namespace Riftbound

/-- Predict either waits for the first choice and emits the actual inspected cards,
or leaves an empty look to the rest of the program. -/
theorem Effect.ObservedFinite.predict (amount : Amount) :
    (Effect.prim (.predict amount)).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  have skip (frames : (runEffect s p src live (.prim (.predict amount)) more effectAddPolicy).2.1 =
      [.run p src live more]) : AdvanceTo s (RunContinuation p src more keeps) := by
    apply advance_run_rule wf reads pending ?_ (fun _ keep q ne => keep.insert inserted q ne)
    dsimp only
    rw [frames]
    exact ⟨_, rest, rfl, base⟩
  cases evaluated : amount.evalS s p src live with
  | none =>
    apply skip
    simp only [runEffect, Effect.pickSel?, runEffect1, Prim.pickSel?, runPrimEffect, evaluated]
  | some count =>
    cases cards : (s.zone (.player p .mainDeck)).take count with
    | nil =>
      apply skip
      simp only [runEffect, Effect.pickSel?, runEffect1, Prim.pickSel?, runPrimEffect, evaluated, cards]
    | cons first remaining =>
      apply advance_run_decision wf reads pending
      simp only [runEffect, Effect.pickSel?, runEffect1, Prim.pickSel?, runPrimEffect,
        ← show live = env.withMight s.mightTable from rfl, evaluated, cards]
      rfl

/-- Vision's look emits the actual private observations before the rest of the effect. -/
theorem Effect.SingleRun.lookTop (count : Nat) : (Effect.prim (.lookTop count)).SingleRun := by
  intro s p src env more
  let inspected := (s.zone (.player p .mainDeck)).take count
  let events := inspected.map (Event.lookedAt p)
  have noReplacement : attachmentReplacementFrames s events = [] := by
    simp only [attachmentReplacementFrames, events, List.flatMap_map]
    apply List.flatMap_eq_nil_iff.mpr
    intro id _
    rfl
  refine ⟨s, events, ?_⟩
  simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect, effectDamageBatch?,
    permanentPlayEffects]
  by_cases small : s.turnFx.length < 2
  all_goals
    simp only [small, ite_true, ite_false, applyPrim]
    change (s, attachmentReplacementFrames s events ++ [Frame.run p src env more], events) =
      (s, [Frame.run p src env more], events)
    rw [noReplacement, List.nil_append]

/-- A top-card Recycle rotates the affected decks and records the Recycle events. -/
theorem Effect.SingleRun.recycleTop (who : PlayerSel) : (Effect.prim (.recycleTop who)).SingleRun := by
  intro s p src env more
  let result : GameState × List Event :=
    match who.resolve s p env with
    | none => (s, [Event.skipped src])
    | some seats => (recycleTopAll s seats, seats.filterMap (fun q =>
        if (s.zone (.player q .mainDeck)).isEmpty then none else some (Event.recycled q)))
  refine ⟨result.1, result.2, ?_⟩
  simp only [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect,
    effectDamageBatch?, permanentPlayEffects]
  by_cases small : s.turnFx.length < 2
  all_goals
    simp only [small, ite_true, ite_false, applyPrim, result]
    cases resolved : who.resolve s p env with
    | none => rfl
    | some seats =>
      have noReplacement :
          attachmentReplacementFrames (recycleTopAll s seats)
            (seats.filterMap (fun q =>
              if (s.zone (.player q .mainDeck)).isEmpty then none else some (Event.recycled q))) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro event present
        obtain ⟨q, _, eq⟩ := List.mem_filterMap.mp present
        split at eq
        · contradiction
        · obtain rfl := Option.some.inj eq
          rfl
      simp only [Option.map_some, noReplacement, List.nil_append] <;> rfl

/-- The name-card choice hands control to its decision, or continues if no candidate exists. -/
theorem Effect.ObservedFinite.nameCard (kind : CardType) : (Effect.nameCard kind).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  cases listed : s.nameableCards kind with
  | nil =>
    apply advance_run_rule wf reads pending ?_ (fun _ kept q ne => kept.insert inserted q ne)
    refine ⟨env.withMight s.mightTable, rest, ?_, base⟩
    simp [runEffect, Effect.pickSel?, runEffect1, listed]
  | cons first others =>
    apply advance_run_decision wf reads pending
    simp [runEffect, Effect.pickSel?, runEffect1, listed, Frame.isWork]

/-- A selected name is recorded on the source and emits the corresponding event. -/
theorem Effect.ObservedFinite.rememberNamedCard (card : CardId) :
    (Effect.rememberNamedCard card).ObservedFinite :=
  Effect.SingleRun.observed (fun s p src _ _ =>
    ⟨s.modObj src (fun obj => { obj with namedCard := some card }), [.namedCard p src card], rfl⟩)

/-- A guess prompts the one selected player. If there is no single player, work continues. -/
theorem Effect.ObservedFinite.guessCardType (who : PlayerSel) (unit gear spell : Effect) :
    (Effect.guessCardType who unit gear spell).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  have skip (frames : (runEffect s p src live (.guessCardType who unit gear spell) more effectAddPolicy).2.1 =
      [.run p src live more]) : AdvanceTo s (RunContinuation p src more keeps) := by
    apply advance_run_rule wf reads pending ?_ (fun _ kept q ne => kept.insert inserted q ne)
    refine ⟨live, rest, ?_, base⟩
    rw [frames]
    rfl
  cases resolved : who.resolve s p live with
  | none =>
    exact skip (by simp [runEffect, Effect.pickSel?, runEffect1, resolved])
  | some seats =>
    cases seats with
    | nil => exact skip (by simp [runEffect, Effect.pickSel?, runEffect1, resolved])
    | cons seat rest =>
      cases rest with
      | nil =>
        apply advance_run_decision wf reads pending
        simp [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl,
          resolved, Frame.isWork]
      | cons another others =>
        exact skip (by simp [runEffect, Effect.pickSel?, runEffect1, resolved])

private theorem advance_scoped_run {s : GameState} {p : PlayerId} {src : ObjId} {env inside : Env}
    {effect body : Effect} {more : EffectList} {rest : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards) (finite : body.ObservedFinite)
    (pending : s.pending = .run p src env (.cons effect more) :: rest)
    (frames : (runEffect s p src (env.withMight s.mightTable) effect more effectAddPolicy).2.1 =
      [.run p src inside (.cons body .nil), .run p src (env.withMight s.mightTable) more])
    (base : keeps rest) (inserted : ∀ tail, keeps tail → ∀ queue, queue ≠ [] → keeps (insertTriggers queue tail)) :
    AdvanceTo s (RunContinuation p src more keeps) := by
  let insideFrames := [Frame.run p src inside (.cons body .nil)]
  let tail := RunContinuation p src more keeps
  have keepTail (stack : List Frame) (kept : tail stack) (queue : List PendTrigger) (ne : queue ≠ []) :
      tail (insertTriggers queue stack) := kept.insert inserted queue ne
  have entered : AdvanceTo s (ResolutionPrefix insideFrames tail) := by
    apply advance_run_rule wf reads pending ?_ ?_
    · dsimp only
      rw [frames]
      exact ⟨.run p src (env.withMight s.mightTable) more :: rest, rfl, _, rest, rfl, base⟩
    · intro stack kept queue ne
      exact kept.insert (fun _ member => (List.mem_singleton.mp member).symm ▸ rfl) keepTail queue ne
  apply entered.then reads
  intro t safe checked keep
  apply advance_run_frames safe checked keep ?_ keepTail
  intro f member
  obtain rfl := List.mem_singleton.mp member
  exact ⟨p, src, inside, .cons body .nil, rfl, .cons finite .nil⟩

/-- Looking at a private prefix uses the inspected cards in the nested body, then restores
the outer environment. Its actual observation can open a decision earlier. -/
theorem Effect.ObservedFinite.lookAtTop (count : Nat) {body : Effect} (finite : body.ObservedFinite) :
    (Effect.lookAtTop count body).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let inside := { env.withMight s.mightTable with lookedCards := (s.zone (.player p .mainDeck)).take count }
  exact advance_scoped_run (inside := inside) wf reads finite pending rfl base inserted

/-- A hand reveal scopes the disclosed cards to the body before returning to the original program. -/
theorem Effect.ObservedFinite.revealHand (who : PlayerSel) {body : Effect} (finite : body.ObservedFinite) :
    (Effect.revealHand who body).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  cases resolved : who.resolve s p live with
  | none =>
    apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
    refine ⟨live, rest, ?_, base⟩
    simp [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl, resolved]
  | some players =>
    let cards := players.flatMap (fun q => s.zone (.player q .hand))
    let inside := { live with revealedCards := cards ++ live.revealedCards }
    apply advance_scoped_run (inside := inside) wf reads finite pending ?_ base inserted
    simp [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl, resolved,
      inside, cards, List.flatMap_map]

/-- Revealing several deck tops makes the revealed cards available within its body. -/
theorem Effect.ObservedFinite.revealDeckTops (who : PlayerSel) {body : Effect} (finite : body.ObservedFinite) :
    (Effect.revealDeckTops who body).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  cases resolved : who.resolve s p live with
  | none =>
    apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
    refine ⟨live, rest, ?_, base⟩
    simp [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl, resolved]
  | some players =>
    let tops := players.filterMap (fun q =>
      (s.zone (.player q .mainDeck)).head?.map (fun card => (q, card)))
    let cards := tops.map Prod.snd
    let inside := { live with lookedCards := cards, revealedCards := cards }
    apply advance_scoped_run (inside := inside) wf reads finite pending ?_ base inserted
    simp [runEffect, Effect.pickSel?, runEffect1, ← show live = env.withMight s.mightTable from rfl,
      resolved, inside, cards, tops]

end Riftbound

end
