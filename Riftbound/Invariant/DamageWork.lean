module

public import Riftbound.Invariant.RunWorkCore

/-!
# Damage instructions in the observed dispatcher (I12)

An effect damage batch decreases by the number of pending hits and then by the replacements
remaining for the current hit. An order choice or a death replacement yields to the player.
The immediate damage route preserves the same Run continuation through event observation.
-/

@[expose] public section

namespace Riftbound

/-- Record the final excess damage for a Combat before resuming its Run program. -/
theorem Effect.ObservedFinite.endCombatDamage (excess : Nat × Nat) :
    (Effect.endCombatDamage excess).ObservedFinite :=
  Effect.SingleRun.observed (fun s _ src _ _ => ⟨recordCombatDamage s src excess, [], rfl⟩)

private def damageRank (batch : EffectDamageBatch) (hit : Option EffectDamageHit) : Nat × Nat :=
  (batch.incoming.length, (hit.map fun h => h.replacements.length + 1).getD 0)

private theorem applyDamageAmount_incoming (choice : DamageReplacement) (batch : EffectDamageBatch) (amount : Nat) :
    (choice.applyAmount batch amount).1.incoming = batch.incoming := by
  unfold DamageReplacement.applyAmount
  split
  · rfl
  · cases choice <;> rfl

private theorem advance_run_via {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {effect next : Effect} {more : EffectList} {rest : List Frame} {keeps : List Frame → Prop}
    (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons effect more) :: rest)
    (known : let live := env.withMight s.mightTable
      (runEffect s p src live effect more effectAddPolicy).2.1 = [.run p src live (.cons next more)])
    (finite : next.ObservedFinite) (base : keeps rest)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s (RunContinuation p src more keeps) := by
  have entered : AdvanceTo s (RunContinuation p src (.cons next more) keeps) := by
    apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
    dsimp only
    rw [known]
    exact ⟨_, rest, rfl, base⟩
  apply entered.then reads
  intro t safe checked tracks
  obtain ⟨live, nextTail, stack, tracked⟩ := tracks
  exact finite t p src live more nextTail keeps safe checked stack tracked inserted

private theorem advance_damage_offer {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {effect choice : Effect} {controller : PlayerId} {more : EffectList} {rest : List Frame}
    {keeps : List Frame → Prop} (wf : s.WF) (reads : MightRead.database s.cards)
    (pending : s.pending = .run p src env (.cons effect more) :: rest)
    (known : let live := env.withMight s.mightTable
      (runEffect s p src live effect more effectAddPolicy).2.1 =
        [.run controller src live (.cons choice .nil), .run p src live more])
    (finite : choice.ObservedFinite) (base : keeps rest)
    (inserted : ∀ tail, keeps tail → ∀ q, q ≠ [] → keeps (insertTriggers q tail)) :
    AdvanceTo s (RunContinuation p src more keeps) := by
  let resume := RunContinuation p src more keeps
  let offer := RunContinuation controller src (.cons choice .nil) resume
  have enter : AdvanceTo s offer := by
    apply advance_run_rule wf reads pending ?_ ?_
    · dsimp only
      rw [known]
      exact ⟨_, _, rfl, ⟨_, _, rfl, base⟩⟩
    · exact fun _ tracks q ne => tracks.insert
        (fun _ prior r nonempty => prior.insert inserted r nonempty) q ne
  refine enter.then reads ?_
  intro t safe checked track
  obtain ⟨live, tail, ready, queued⟩ := track
  exact advance_run_program safe checked ready (.cons finite .nil) resume queued
    (fun _ kept q ne => kept.insert inserted q ne)

/-- Runtime damage resolution consumes pending hits and each successive replacement, or
yields when a player must decide how to order replacements or replace a death. -/
theorem Effect.ObservedFinite.resolveDamage (batch : EffectDamageBatch) (hit : Option EffectDamageHit) :
    (Effect.resolveEffectDamage batch hit).ObservedFinite := by
  cases hitEq : hit with
  | none =>
    intro s p src env more rest keeps wf reads pending base inserted
    cases incoming : batch.incoming with
    | nil =>
      cases choice : batch.resolved.reverse.findSome? (damageDeathChoice s batch) with
      | none =>
        apply advance_run_rule wf reads pending ?_ (fun _ route q ne => route.insert inserted q ne)
        simp only [runEffect, Effect.pickSel?, runEffect1, resolveEffectDamageStep, incoming, choice]
        exact ⟨_, rest, rfl, base⟩
      | some data =>
        obtain ⟨u, controller, first, other⟩ := data
        apply advance_run_decision wf reads pending
        simp only [runEffect, Effect.pickSel?, runEffect1, resolveEffectDamageStep, incoming, choice]
        rfl
    | cons first later =>
      obtain ⟨id, amount⟩ := first
      let next := { batch with incoming := later }
      have lower : Prod.Lex (· < ·) (· < ·) (damageRank next none) (damageRank batch none) := by
        apply Prod.Lex.left
        simp [next, incoming]
      cases target : s.obj? id with
      | none =>
        refine advance_run_via wf reads pending ?_ (resolveDamage next none) base inserted
        simp only [runEffect, Effect.pickSel?, runEffect1, resolveEffectDamageStep, incoming, target, next]
      | some targetObj =>
        by_cases immune : damageImmune s id targetObj batch.controller = true
        · refine advance_run_via wf reads pending ?_ (resolveDamage next none) base inserted
          simp only [runEffect, Effect.pickSel?, runEffect1, resolveEffectDamageStep, incoming,
            target, next, immune, ite_true]
        · by_cases zero : (amount == 0) = true
          · let reduced := { next with resolved := (id, 0) :: next.resolved }
            have lower : Prod.Lex (· < ·) (· < ·) (damageRank reduced none) (damageRank batch none) := lower
            refine advance_run_via wf reads pending ?_ (resolveDamage reduced none) base inserted
            simp only [runEffect, Effect.pickSel?, runEffect1, resolveEffectDamageStep, incoming,
              target, next, reduced, ite_eq_right immune, zero, ite_true]
          · let current : EffectDamageHit := ⟨id, amount, damageReplacements s batch id⟩
            have lower : Prod.Lex (· < ·) (· < ·) (damageRank next (some current)) (damageRank batch none) := by
              apply Prod.Lex.left
              simp [next, incoming]
            refine advance_run_via wf reads pending ?_ (resolveDamage next (some current)) base inserted
            simp only [runEffect, Effect.pickSel?, runEffect1, resolveEffectDamageStep, incoming,
              target, next, current, ite_eq_right immune, ite_eq_right zero]
  | some current =>
    intro s p src env more rest keeps wf reads pending base inserted
    by_cases zero : (current.amount == 0) = true
    · have lower : Prod.Lex (· < ·) (· < ·) (damageRank batch none) (damageRank batch (some current)) := by
        apply Prod.Lex.right
        simp
      refine advance_run_via wf reads pending ?_ (resolveDamage batch none) base inserted
      simp only [runEffect, Effect.pickSel?, runEffect1, resolveEffectDamageStep, zero, ite_true]
    · cases remaining : current.replacements with
      | nil =>
        let next := { batch with resolved := (current.target, current.amount) :: batch.resolved }
        have lower : Prod.Lex (· < ·) (· < ·) (damageRank next none) (damageRank batch (some current)) := by
          apply Prod.Lex.right
          simp
        refine advance_run_via wf reads pending ?_ (resolveDamage next none) base inserted
        simp only [runEffect, Effect.pickSel?, runEffect1, resolveEffectDamageStep,
          ite_eq_right zero, remaining, List.isEmpty_nil, ite_true, next]
      | cons first restChoices =>
        let controller := ((s.obj? current.target).map (·.controller)).getD p
        let further := (restChoices.filter (fun other => DamageReplacement.sameChoice other first = false)).eraseDupsBy
          DamageReplacement.sameChoice
        let offered := EffectList.ofList
          ((first :: further).map (Effect.chooseDamageReplacement batch current))
        have shape :
            (runEffect s p src (env.withMight s.mightTable)
              (.resolveEffectDamage batch (some current)) more effectAddPolicy).2.1 =
              [.run controller src (env.withMight s.mightTable) (.cons (.eitherOf offered) .nil),
                .run p src (env.withMight s.mightTable) more] := by
          simp only [runEffect, Effect.pickSel?, runEffect1, resolveEffectDamageStep,
            ite_eq_right zero, controller, offered, remaining, List.isEmpty_cons, Bool.false_eq_true, ite_false,
            List.eraseDupsBy_cons, further]
        have choiceFinite : (Effect.eitherOf offered).ObservedFinite := by
          cases extra : further with
          | nil =>
            let next := chooseEffectDamage batch current first
            have member : first ∈ current.replacements := by simp [remaining]
            have shorter : (current.replacements.erase first).length < current.replacements.length := by
              have ne : 0 < current.replacements.length := by simp [remaining]
              rw [List.length_erase_of_mem member]
              omega
            have unchanged : next.1.incoming = batch.incoming :=
              applyDamageAmount_incoming first batch current.amount
            have lower : Prod.Lex (· < ·) (· < ·)
                (damageRank next.1 (some next.2)) (damageRank batch (some current)) := by
              unfold damageRank
              rw [unchanged]
              apply Prod.Lex.right
              change (current.replacements.erase first).length + 1 < current.replacements.length + 1
              omega
            have chosen : (Effect.chooseDamageReplacement batch current first).ObservedFinite := by
              intro t who source context tail suffix continuation safe checked start suffixTracked inserted'
              refine advance_run_via safe checked start ?_ (resolveDamage next.1 (some next.2))
                suffixTracked inserted'
              simp only [runEffect, Effect.pickSel?, runEffect1, next]
            rw [show offered = .cons (.chooseDamageReplacement batch current first) .nil by simp [offered, extra, EffectList.ofList]]
            exact .eitherOf (.cons chosen .nil)
          | cons second others =>
            intro t who source context tail suffix continuation safe checked start _ _
            apply advance_run_decision safe checked start
            simp only [offered, extra, List.map_cons, EffectList.ofList, runEffect, Effect.pickSel?, runEffect1]
            cases others <;> rfl
        exact advance_damage_offer wf reads pending shape choiceFinite base inserted
termination_by damageRank batch hit
decreasing_by all_goals simpa only [hitEq] using lower

/-- The explicit replacement instruction resumes with the chosen replacement applied. -/
theorem Effect.ObservedFinite.chooseDamage (batch : EffectDamageBatch) (hit : EffectDamageHit)
    (replacement : DamageReplacement) :
    (Effect.chooseDamageReplacement batch hit replacement).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let next := chooseEffectDamage batch hit replacement
  exact advance_run_via wf reads pending rfl (.resolveDamage next.1 (some next.2)) base inserted

/-- A distribution selected by the player runs as an effect damage batch. -/
theorem Effect.ObservedFinite.applySplitDamage (hits : List (ObjId × Nat)) :
    (Effect.applySplitDamage hits).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  by_cases disabled : s.damageOff = true
  · apply advance_run_rule wf reads pending ?_ (fun _ route q ne => route.insert inserted q ne)
    simp only [runEffect, Effect.pickSel?, runEffect1, disabled, ite_true]
    exact ⟨_, rest, rfl, base⟩
  · let batch : EffectDamageBatch := {
      controller := some ((env.withMight s.mightTable).effectController.getD p), incoming := hits }
    refine advance_run_via wf reads pending ?_ (.resolveDamage batch none) base inserted
    simp only [runEffect, Effect.pickSel?, runEffect1, ite_eq_right disabled, batch]

/-- A Unit's distributed damage also records the corresponding Kill linkage. -/
theorem Effect.ObservedFinite.applyUnitSplitDamage (hits : List (ObjId × Nat)) (link : DamageKillLink) :
    (Effect.applyUnitSplitDamage hits link).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  by_cases disabled : s.damageOff = true
  · apply advance_run_rule wf reads pending ?_ (fun _ route q ne => route.insert inserted q ne)
    simp only [runEffect, Effect.pickSel?, runEffect1, disabled, ite_true]
    exact ⟨_, rest, rfl, base⟩
  · let batch := unitSplitDamageBatch s hits link
    refine advance_run_via wf reads pending ?_ (.resolveDamage batch none) base inserted
    simp only [runEffect, Effect.pickSel?, runEffect1, ite_eq_right disabled, batch]

private theorem EffectList.ObservedFinite.ofList {effects : List Effect}
    (finite : ∀ effect ∈ effects, effect.ObservedFinite) : (EffectList.ofList effects).ObservedFinite := by
  induction effects with
  | nil => exact .nil
  | cons first later ih =>
    exact .cons (finite first List.mem_cons_self) (ih fun e mem => finite e (List.mem_cons_of_mem _ mem))

/-- A split prompts if there are several distributions, or applies the unique one. -/
theorem Effect.ObservedFinite.splitDamage (targets : Selector) (total : Nat) :
    (Effect.splitDamage targets total).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  have skip (h : (runEffect s p src live (.splitDamage targets total) more effectAddPolicy).2.1 =
      [.run p src live more]) : AdvanceTo s (RunContinuation p src more keeps) := by
    apply advance_run_rule wf reads pending ?_ (fun _ route q ne => route.insert inserted q ne)
    dsimp only
    rw [h]
    exact ⟨live, rest, rfl, base⟩
  cases targetsEq : targets.eval s p src live with
  | none =>
    apply skip
    simp only [runEffect, Effect.pickSel?, runEffect1, targetsEq]
  | some ids =>
    cases ids with
    | nil =>
      apply skip
      simp only [runEffect, Effect.pickSel?, runEffect1, targetsEq]
    | cons first others =>
      let total := total + s.bonusOn p src first live.sourceCard
      let choices := (damageDivisions (first :: others) total).map Effect.applySplitDamage
      have finite : (Effect.eitherOf (EffectList.ofList choices)).ObservedFinite := by
        apply Effect.ObservedFinite.eitherOf
        apply EffectList.ObservedFinite.ofList
        intro e member
        obtain ⟨hits, _, rfl⟩ := List.mem_map.mp member
        exact .applySplitDamage hits
      apply advance_run_via wf reads pending ?_ finite base inserted
      simp only [runEffect, Effect.pickSel?, runEffect1, choices, total, ← show live = env.withMight s.mightTable from rfl, targetsEq]

/-- A Unit's split uses its current Might and retains the link to any Kill it causes. -/
theorem Effect.ObservedFinite.splitUnitDamage (dealer targets : Selector) (index : Nat) :
    (Effect.splitUnitDamage dealer targets index).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  let frames := (runEffect s p src live (.splitUnitDamage dealer targets index) more effectAddPolicy).2.1
  have routes : frames = [.run p src live more] ∨
      ∃ hits : List (List (ObjId × Nat)), ∃ link : DamageKillLink,
        frames = [.run p src live
          (.cons (.eitherOf (EffectList.ofList (hits.map (fun h => .applyUnitSplitDamage h link)))) more)] := by
    simp only [frames, runEffect, Effect.pickSel?, runEffect1]
    split
    · rename_i unit ids card _ _ _
      split
      · exact Or.inr ⟨_, ⟨src, unit, p, card, index⟩, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  rcases routes with skip | ⟨hits, link, choices⟩
  · apply advance_run_rule wf reads pending ?_ (fun _ route q ne => route.insert inserted q ne)
    change RunContinuation p src more keeps (frames ++ rest)
    rw [skip]
    exact ⟨_, rest, rfl, base⟩
  · have finite : (Effect.eitherOf (EffectList.ofList
        (hits.map (fun h => .applyUnitSplitDamage h link)))).ObservedFinite := by
      apply Effect.ObservedFinite.eitherOf
      apply EffectList.ObservedFinite.ofList
      intro e member
      obtain ⟨h, _, rfl⟩ := List.mem_map.mp member
      exact .applyUnitSplitDamage h link
    exact advance_run_via wf reads pending choices finite base inserted

private theorem killObj_noAttach (s : GameState) (id : ObjId) :
    NoAttach (killObj s id).2 := by
  unfold killObj
  generalize (if s.banishedOnDeath id = true then ZoneKind.banishment else .trash) = dest
  split
  · dsimp only
    split
    · apply NoAttach.append (sendObj_noAttach _ s id)
      intro gear unit member
      obtain ⟨p, _, attached⟩ := List.mem_flatMap.mp member
      exact banishCardEvents_noAttach p s id _ gear unit attached
    · apply NoAttach.append (sendObj_noAttach _ s id)
      intro gear unit member
      obtain ⟨e, _, h⟩ := List.mem_filterMap.mp member
      cases e <;> cases h
  · exact sendObj_noAttach _ s id

private theorem sendHome_silent (s : GameState) (id : ObjId) : (sendHome s id).2 = [] := by
  unfold sendHome
  split
  · split <;> rfl
  · rfl

private theorem recallFx_noAttach (ex : Bool) (s : GameState) (id : ObjId) :
    NoAttach (recallFx ex s id).2 := by
  have moved : NoAttach (sendHome s id).2 := sendHome_silent s id ▸ NoAttach.nil
  let recalled := if (s.obj? id).any (·.loc.isSome) && ((sendHome s id).1.obj? id).any (·.loc.isNone) then
    [Event.recalled id] else []
  have note : NoAttach recalled := by
    intro gear unit
    unfold recalled
    split <;> simp
  cases ex
  · exact moved.append note
  · exact (moved.append note).append (setExhausted_noAttach true _ _)

private theorem completeDeathSave_noAttach (s : GameState) (id : ObjId) (mark : Option TurnEffect)
    (p : PlayerId) (clear : Bool) : NoAttach (completeDeathSave s id mark p clear).2 := by
  have healed : NoAttach (healAllOn s id).2 := by
    intro gear unit
    unfold healAllOn
    dsimp only
    split <;> simp
  let recalled := recallFx false (healAllOn s id).1 id
  exact ((NoAttach.nil.append healed).append (setExhausted_noAttach true recalled.1 id)).append
    (recallFx_noAttach false _ _)

private theorem killOrSaveFrom_noAttach (root : ObjId) (fuel : Nat) (s : GameState) (id : ObjId)
    (used : List (ObjId × Bool)) : NoAttach (killOrSaveFrom root fuel s id used).2 := by
  induction fuel generalizing s id used with
  | zero => exact killObj_noAttach _ _
  | succ fuel ih =>
    unfold killOrSaveFrom
    dsimp only
    split
    · exact killObj_noAttach _ _
    · rename_i save _
      have prior : NoAttach (save.cost.elim (s, []) (fun cost =>
          killOrSaveFrom root fuel s cost (save.useKey id :: used))).2 := by
        cases cost : save.cost with
        | none => exact .nil
        | some _ => exact ih _ _ _
      exact prior.append (completeDeathSave_noAttach _ _ _ _ _)

private theorem dealObj_noAttach (n : Nat) (s : GameState) (id : ObjId)
    (controller responsible : Option PlayerId) : NoAttach (dealObj n s id controller responsible).2 := by
  unfold dealObj
  split
  · split
    · exact .nil
    · split
      · exact .nil
      · unfold dealThroughPrevent
        split
        split
        · exact .nil
        · unfold dealRemaining
          dsimp only
          have prepend {t : GameState} {amount : Nat} : NoAttach (Event.damaged id amount :: (killOrSave t id).2) := by
            intro gear unit member
            rcases List.mem_cons.mp member with eq | member
            · contradiction
            · exact killOrSaveFrom_noAttach id _ t id [] gear unit member
          split
          · exact prepend
          · split
            · exact prepend
            · intro gear unit
              simp
  · exact .nil

private theorem exchangeDamage_noAttach (s : GameState) (a b : ObjId) :
    NoAttach (exchangeDamage s a b).2 := by
  unfold exchangeDamage
  split
  · exact (dealObj_noAttach _ _ _ _ _).append (dealObj_noAttach _ _ _ _ _)
  · exact .nil

private inductive PrimitiveDamage : Prim → Prop where
  | deal (target : Selector) (amount : Amount) : PrimitiveDamage (.deal target amount)
  | exchange (a b : Selector) : PrimitiveDamage (.exchangeDamage a b)

private theorem PrimitiveDamage.noAttach {pr : Prim} (damage : PrimitiveDamage pr)
    {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {result : GameState × List Event}
    (rule : applyPrim s p src env pr = some result) : NoAttach result.2 := by
  cases damage with
  | deal target amount =>
    simp only [applyPrim] at rule
    split at rule
    · obtain rfl := (Option.some.inj rule).symm
      exact .nil
    · obtain ⟨n, _, body⟩ := Option.bind_eq_some_iff.mp rule
      obtain ⟨ids, _, done⟩ := Option.map_eq_some_iff.mp body
      rw [← done]
      exact applyEach_noAttach _ (fun _ _ => dealObj_noAttach _ _ _ _ _) s ids
  | exchange a b =>
    simp only [applyPrim] at rule
    split at rule
    · obtain rfl := (Option.some.inj rule).symm
      exact exchangeDamage_noAttach _ _ _
    · obtain rfl := (Option.some.inj rule).symm
      exact .nil

private def primitiveDamageFrames (s : GameState) (p : PlayerId) (src : ObjId)
    (env : Env) (pr : Prim) (more : EffectList) : List Frame :=
  match effectDamageBatch? s p src env pr with
  | some batch => [.run p src env (.cons (.resolveEffectDamage batch none) more)]
  | none =>
    match applyPrim s p src env pr with
    | some r => attachmentReplacementFrames r.1 r.2 ++ [.run p src env more]
    | none => [.run p src env more]

private theorem PrimitiveDamage.runForm {pr : Prim} (damage : PrimitiveDamage pr)
    (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (more : EffectList) :
    (runPrimEffect s p src env pr more effectAddPolicy).2.1 =
      primitiveDamageFrames s p src env pr more := by
  cases batch : effectDamageBatch? s p src env pr with
  | some batch => cases damage <;> simp only [runPrimEffect, primitiveDamageFrames, batch]
  | none =>
    cases result : applyPrim s p src env pr <;> cases damage <;>
      simp only [runPrimEffect, primitiveDamageFrames, batch, permanentPlayEffects, result]

private theorem PrimitiveDamage.finiteWithoutPick {pr : Prim} (damage : PrimitiveDamage pr)
    (noPick : (Effect.prim pr).pickSel? = none) : (Effect.prim pr).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  have form : (runEffect s p src live (.prim pr) more effectAddPolicy).2.1 =
      primitiveDamageFrames s p src live pr more := by
    simp only [runEffect, noPick, runEffect1]
    exact damage.runForm s p src live more
  cases batch : effectDamageBatch? s p src live pr with
  | some ready =>
    apply advance_run_via wf reads pending ?_ (.resolveDamage ready none) base inserted
    dsimp only
    exact form.trans (by simp only [primitiveDamageFrames, batch]; rfl)
  | none =>
    apply advance_run_rule wf reads pending ?_ (fun _ tracked q ne => tracked.insert inserted q ne)
    change RunContinuation p src more keeps
      ((runEffect s p src live (.prim pr) more effectAddPolicy).2.1 ++ rest)
    rw [form]
    simp only [primitiveDamageFrames, batch]
    cases checked : applyPrim s p src live pr with
    | none => exact ⟨live, rest, rfl, base⟩
    | some next =>
      change RunContinuation p src more keeps ((attachmentReplacementFrames next.1 next.2 ++ [.run p src live more]) ++ rest)
      rw [(damage.noAttach checked).replacementFrames next.1]
      exact ⟨live, rest, rfl, base⟩

private theorem Effect.ObservedFinite.withTargetPick {effect : Effect}
    {side : Side} {place : Place} {filters : FilterList}
    (pick : effect.pickSel? = some (.pick .one side place filters))
    (separate : ∀ qs qp qf body, effect ≠ .chooseObject qs qp qf body)
    (finite : effect.withPick.ObservedFinite) :
    effect.ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let live := env.withMight s.mightTable
  let options := requiredPlayCandidates s p src live effect effectAddPolicy <|>
    s.pickCandidates p src live side place filters (!effect.isLinkedCost)
  let result := runEffect s p src live effect more effectAddPolicy
  have frames : result.2.1 = match options with
      | some [o] => [.run p src (live.bindPick o (effect.pickIsTarget s o)) (.cons effect.withPick more)]
      | some (o :: other :: tail) => [.pickDo p src live o (other :: tail) effect.withPick more]
      | _ => [.run p src live more] := by
    unfold result runEffect
    rw [pick]
    change (match options with
      | some [o] => match effect with
        | .chooseObject .. => (s, [Frame.pickDo p src live o [] effect.withPick more], [])
        | _ => (s, [.run p src (live.bindPick o (effect.pickIsTarget s o))
            (.cons effect.withPick more)], effect.pickEvents s p src o)
      | some (o :: other :: tail) => (s, [.pickDo p src live o (other :: tail) effect.withPick more], [])
      | _ => (s, [.run p src live more], [Event.skipped src])).2.1 = _
    cases options with
    | none => rfl
    | some candidates => cases candidates with
      | nil => rfl
      | cons first others =>
        cases others with
        | cons => rfl
        | nil =>
          dsimp only
          split
          · exfalso
            exact separate _ _ _ _ rfl
          · rfl
  have skip (h : result.2.1 = [.run p src live more]) : AdvanceTo s (RunContinuation p src more keeps) := by
    apply advance_run_rule wf reads pending ?_ (fun _ kept q ne => kept.insert inserted q ne)
    change RunContinuation p src more keeps (result.2.1 ++ rest)
    rw [h]
    exact ⟨_, rest, rfl, base⟩
  cases chosen : options with
  | none => exact skip (by simpa only [chosen] using frames)
  | some candidates =>
    cases candidates with
    | nil => exact skip (by simpa only [chosen] using frames)
    | cons first others =>
      cases others with
      | cons second remaining =>
        apply advance_run_decision wf reads pending
        change NonNeutralDecision (result.2.1 ++ rest)
        rw [frames, chosen]
        rfl
      | nil =>
        let resume := RunContinuation p src (.cons effect.withPick more) keeps
        have entered : AdvanceTo s resume := by
          apply advance_run_rule wf reads pending ?_ (fun _ kept q ne => kept.insert inserted q ne)
          change resume (result.2.1 ++ rest)
          rw [frames, chosen]
          exact ⟨_, rest, rfl, base⟩
        refine entered.then reads ?_
        intro t safe checked track
        obtain ⟨context, tail, ready, kept⟩ := track
        exact finite t p src context more tail keeps safe checked ready kept inserted

/-- Damage follows the ordinary or ordered batch path, including an in-resolution target pick. -/
theorem Effect.ObservedFinite.deal (target : Selector) (amount : Amount) :
    (Effect.prim (.deal target amount)).ObservedFinite := by
  cases target <;> try exact (PrimitiveDamage.deal _ _).finiteWithoutPick rfl
  case pick quantity side place filters =>
    cases quantity <;> try exact (PrimitiveDamage.deal _ _).finiteWithoutPick rfl
    exact .withTargetPick rfl (by intro _ _ _ _ h; cases h)
      ((PrimitiveDamage.deal (.var pickVar) amount).finiteWithoutPick rfl)

private theorem grant_withoutPick (target : Selector) (modification : StaticMod) (duration : Duration)
    (noPick : (Effect.grant target modification duration).pickSel? = none) :
    (Effect.grant target modification duration).ObservedFinite := by
  apply Effect.SingleRun.observed
  intro s p src env more
  simp only [runEffect, noPick, runEffect1]
  split <;> exact ⟨_, _, rfl⟩

/-- Temporary modifiers and keywords resume after applying to the selected objects. -/
theorem Effect.ObservedFinite.grant (target : Selector) (modification : StaticMod) (duration : Duration) :
    (Effect.grant target modification duration).ObservedFinite := by
  cases target <;> try exact grant_withoutPick _ _ _ rfl
  case pick quantity side place filters =>
    cases quantity <;> try exact grant_withoutPick _ _ _ rfl
    exact .withTargetPick rfl (by intro _ _ _ _ h; cases h)
      (grant_withoutPick (.var pickVar) modification duration rfl)

private theorem markOn_withoutPick (target : Selector) (note : TurnEffect)
    (noPick : (Effect.prim (.markOn target note)).pickSel? = none) :
    (Effect.prim (.markOn target note)).ObservedFinite := by
  apply Effect.SingleRun.observed
  intro s p src env more
  have noBatch : effectDamageBatch? s p src env (.markOn target note) = none := by
    unfold effectDamageBatch?
    split <;> rfl
  simp only [runEffect, noPick, runEffect1, runPrimEffect, noBatch, permanentPlayEffects]
  cases applied : applyPrim s p src env (.markOn target note) with
  | none => exact ⟨_, _, rfl⟩
  | some r =>
    have noAttach : NoAttach r.2 := by
      simp only [applyPrim, onSelected] at applied
      obtain ⟨ids, _, result⟩ := Option.map_eq_some_iff.mp applied
      rw [← result]
      exact applyEach_noAttach _ (fun _ _ => .nil) s ids
    dsimp only
    rw [noAttach.replacementFrames r.1, List.nil_append]
    exact ⟨_, _, rfl⟩

/-- Marking objects records turn effects before running the next instruction. -/
theorem Effect.ObservedFinite.markOn (target : Selector) (note : TurnEffect) :
    (Effect.prim (.markOn target note)).ObservedFinite := by
  cases target <;> try exact markOn_withoutPick _ _ rfl
  case pick quantity side place filters =>
    cases quantity <;> try exact markOn_withoutPick _ _ rfl
    exact .withTargetPick rfl (by intro _ _ _ _ h; cases h)
      (markOn_withoutPick (.var pickVar) note rfl)

/-- Exchanging damage snapshots the two Mights and then uses the damage rules. -/
theorem Effect.ObservedFinite.exchangeDamage (a b : Selector) :
    (Effect.prim (.exchangeDamage a b)).ObservedFinite :=
  (PrimitiveDamage.exchange a b).finiteWithoutPick rfl

/-- A combat damage order is recorded immediately or, if more than one distinct replacement
remains, asks its controller to pick the next replacement. -/
theorem Effect.ObservedFinite.orderCombatDamage (target : ObjId)
    (chosen remaining : List DamageReplacement) :
    (Effect.orderCombatDamage target chosen remaining).ObservedFinite := by
  intro s p src env more rest keeps wf reads pending base inserted
  let options := remaining.eraseDupsBy DamageReplacement.sameChoice
  let choose := fun r => Effect.orderCombatDamage target (r :: chosen) (remaining.erase r)
  by_cases multiple : 1 < options.length
  · have optionsShape : ∃ a b tail, options = a :: b :: tail := by
      cases shape : options with
      | nil => simp [shape] at multiple
      | cons a tail =>
        cases tail with
        | nil => simp [shape] at multiple
        | cons b tail => exact ⟨a, b, tail, rfl⟩
    obtain ⟨a, b, tail, offered⟩ := optionsShape
    let choices := EffectList.ofList (options.map choose)
    let live := env.withMight s.mightTable
    have begin : AdvanceTo s (RunContinuation p src (.cons (.eitherOf choices) more) keeps) := by
      apply advance_run_rule wf reads pending ?_ (fun _ threaded q ne => threaded.insert inserted q ne)
      simp only [runEffect, Effect.pickSel?, runEffect1, orderCombatDamageStep, ← show
        options = remaining.eraseDupsBy DamageReplacement.sameChoice from rfl, multiple, ite_true]
      exact ⟨live, rest, rfl, base⟩
    apply begin.then reads
    intro next safe checked reached
    obtain ⟨newEnv, tailStack, stack, _⟩ := reached
    apply advance_run_decision safe checked stack
    simp only [choices, offered, List.map_cons, EffectList.ofList, runEffect, Effect.pickSel?, runEffect1]
    cases tail <;> rfl
  · apply advance_run_rule wf reads pending ?_ (fun _ threaded q ne => threaded.insert inserted q ne)
    simp only [runEffect, Effect.pickSel?, runEffect1, orderCombatDamageStep, ← show
      options = remaining.eraseDupsBy DamageReplacement.sameChoice from rfl, ite_eq_right multiple]
    exact ⟨_, rest, rfl, base⟩

end Riftbound

end
