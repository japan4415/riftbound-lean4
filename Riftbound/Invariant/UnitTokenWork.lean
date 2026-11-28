module

public import Riftbound.Invariant.RunWorkCore

/-!
# Unit token replacements and funding (I12)
-/

@[expose] public section

namespace Riftbound

private theorem Effect.ObservedFinite.eitherList (options : List Effect)
    (single : ∀ effect, options = [effect] → effect.ObservedFinite) :
    (Effect.eitherOf (EffectList.ofList options)).ObservedFinite := by
  cases options with
  | nil => exact .eitherOf .nil
  | cons first rest =>
    cases rest with
    | nil => exact .eitherOf (.cons (single first rfl) .nil)
    | cons second later => exact .eitherChoice first second (EffectList.ofList later)

private theorem Effect.ObservedFinite.eitherWithLast (choices : List Effect) {last : Effect}
    (finite : last.ObservedFinite) : (Effect.eitherOf (EffectList.ofList (choices ++ [last]))).ObservedFinite := by
  apply Effect.ObservedFinite.eitherList
  intro only offered
  have size := congrArg List.length offered
  have empty : choices = [] := by
    apply List.length_eq_zero_iff.mp
    simpa using size
  simp only [empty, List.nil_append, List.cons.injEq] at offered
  exact offered.1 ▸ finite

/-- Committing a token payment places the planned batch or skips if the payment is unavailable. -/
theorem Effect.ObservedFinite.finishUnitTokens (batch : UnitTokenBatch) (payment : Option (Nat × List Domain))
    (adds : List EffectAdd) : (Effect.finishUnitTokens batch payment adds).ObservedFinite := by
  apply Effect.SingleRun.observed
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, runEffect1]
  split <;> exact ⟨_, _, rfl⟩

/-- Funding a projected Accelerate preserves the option to enter without paying.
Additional funding is requested only via a new decision. -/
theorem Effect.ObservedFinite.fundTokenAccelerate (batch : UnitTokenBatch) (payment : Nat × List Domain)
    (adds : List EffectAdd) : (Effect.fundTokenAccelerate batch payment adds).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  let opts := fundUnitTokenOptions s p batch ⟨payment.1, payment.2⟩ adds effectAddPolicy
  refine ⟨.cons (.eitherOf (EffectList.ofList opts)) .nil, ?_, rfl⟩
  have decline : ∃ choices, opts = choices ++ [.finishUnitTokens batch none []] := by
    unfold opts fundUnitTokenOptions
    split
    · exact ⟨[], rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨choices, offered⟩ := decline
  rw [offered]
  exact .cons (.eitherWithLast choices (.finishUnitTokens batch none [])) .nil

private theorem priceUnitToken_finite (s : GameState) (p : PlayerId) (batch : UnitTokenBatch)
    (funding : EffectAddPolicy) : (s.priceUnitToken p batch funding).ObservedFinite := by
  unfold GameState.priceUnitToken
  dsimp only
  split
  · exact .finishUnitTokens batch none []
  · apply Effect.ObservedFinite.eitherList
    intro only offered
    exact (List.cons.inj offered).1 ▸ Effect.ObservedFinite.finishUnitTokens batch none []

/-- Number of future replacements, the current replacement's phase, and its unhandled entries. -/
private def unitTokenPlanMeasure : UnitTokenPlan → Nat × Nat × Nat
  | .apply _ after => (after.length, 1, 0)
  | .substitute _ remaining _ after => (after.length, 0, remaining.length)
  | .duplicate _ _ _ after => (after.length, 0, 0)

private theorem unitTokenReplacementOrder_finite (batch : UnitTokenBatch)
    (first second : UnitTokenReplacement) (later : List UnitTokenReplacement) :
    (beginUnitTokenEntries batch (first :: second :: later)).ObservedFinite := by
  exact .eitherChoice _ _ _

/-- Each automatic planning step proceeds to the next replacement, processes one entry, or
opens a choice. The remaining replacements may include duplication on a larger batch. -/
theorem Effect.ObservedFinite.planUnitTokenEntries (batch : UnitTokenBatch) (plan : UnitTokenPlan) :
    (Effect.planUnitTokenEntries batch plan).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  let next := nextUnitTokenPlan s p batch effectAddPolicy plan
  refine ⟨.cons next .nil, .cons ?_ .nil, rfl⟩
  change (nextUnitTokenPlan s p batch effectAddPolicy plan).ObservedFinite
  cases plan with
  | apply replacement after =>
    cases replacement with
    | substitute cards =>
      exact planUnitTokenEntries batch (.substitute cards batch.entries [] after)
    | duplicate source copy =>
      simp only [nextUnitTokenPlan, applyUnitTokenReplacement]
      cases entries : batch.entries with
      | nil =>
        simpa [entries, EffectList.ofList] using
          (Effect.ObservedFinite.eitherOf (.cons (planUnitTokenEntries batch (.duplicate source copy none after)) .nil))
      | cons first later =>
        apply Effect.ObservedFinite.eitherList
        intro only offered
        have size := congrArg List.length offered
        simp at size
  | duplicate source copy entry after =>
    let planned := duplicateUnitTokenEntry batch source copy entry
    cases after with
    | nil => exact priceUnitToken_finite s p planned _
    | cons first later =>
      cases later with
      | nil => exact planUnitTokenEntries planned (.apply first [])
      | cons second more => exact unitTokenReplacementOrder_finite planned first second more
  | substitute substitutes remaining chosen after =>
    cases remaining with
    | nil =>
      let original := batch.entries.head?.map Prod.fst
      let entries := if substitutes.isEmpty then chosen.reverse else
        let (replaced, ordinary) := chosen.reverse.partition (fun entry => some entry.1 != original)
        replaced ++ ordinary
      let planned := { batch with entries }
      cases after with
      | nil => exact priceUnitToken_finite s p planned _
      | cons first later =>
        cases later with
        | nil => exact planUnitTokenEntries planned (.apply first [])
        | cons second more => exact unitTokenReplacementOrder_finite planned first second more
    | cons entry later =>
      cases available : substitutes.filter (· != entry.1) with
      | nil =>
        have finite := planUnitTokenEntries batch (.substitute substitutes later (entry :: chosen) after)
        simpa only [nextUnitTokenPlan, unitTokenEntryPlan, available, List.isEmpty_nil, ite_true] using finite
      | cons first rest =>
        simp only [nextUnitTokenPlan, unitTokenEntryPlan, available, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.map_cons, EffectList.ofList]
        exact .eitherChoice _ _ _
termination_by unitTokenPlanMeasure plan
decreasing_by
  all_goals simp_wf
  all_goals simp [unitTokenPlanMeasure]
  all_goals first | exact Prod.Lex.left _ _ (by omega) |
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega)) |
    exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

private theorem beginUnitTokenEntries_finite (batch : UnitTokenBatch) (replacements : List UnitTokenReplacement) :
    (beginUnitTokenEntries batch replacements).ObservedFinite := by
  cases replacements with
  | nil => exact .planUnitTokenEntries _ _
  | cons first rest =>
    cases rest with
    | nil => exact .planUnitTokenEntries _ _
    | cons second later => exact unitTokenReplacementOrder_finite batch first second later

private theorem unitTokenPrimitive_finite (pr : Prim)
    (dispatch : ∀ s p src env more, runEffect s p src env (.prim pr) more effectAddPolicy =
      unitTokenPrimStep s p src env pr more) :
    (Effect.prim pr).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  rw [dispatch]
  unfold unitTokenPrimStep
  dsimp only
  split
  · rename_i batch _
    exact ⟨.cons (beginUnitTokenEntries batch (s.unitTokenReplacements p)) .nil,
      .cons (beginUnitTokenEntries_finite batch _) .nil, rfl⟩
  · split <;> exact ⟨.nil, .nil, rfl⟩

/-- Token creation at a named place processes replacements and any optional payment. -/
theorem Effect.ObservedFinite.create (name : String) (count : Amount) (place : Place) (ready : Bool) :
    (Effect.prim (.create name count place ready)).ObservedFinite :=
  unitTokenPrimitive_finite _ (fun _ _ _ _ _ => rfl)

private theorem Effect.ObservedFinite.createAtDirect (name : String) (count : Amount)
    (dest : Selector) (ready : Bool) (direct : (Effect.prim (.createAt name count dest ready)).pickSel? = none) :
    (Effect.prim (.createAt name count dest ready)).ObservedFinite := by
  apply unitTokenPrimitive_finite
  intro s p src env more
  simp only [runEffect, direct, runEffect1, runPrimEffect]

/-- Creating a batch at a selected Battlefield can first ask where it may enter. -/
theorem Effect.ObservedFinite.createAt (name : String) (count : Amount) (dest : Selector) (ready : Bool) :
    (Effect.prim (.createAt name count dest ready)).ObservedFinite :=
  .withResolutionPick _ (.createAtDirect name count dest ready)
    (.createAtDirect name count (.var pickVar) ready rfl) (fun _ _ _ _ impossible => by cases impossible)

/-- A previously selected location uses the same replacement and payment planning. -/
theorem Effect.ObservedFinite.createAtPrev (name : String) (count : Amount) (ready : Bool) :
    (Effect.prim (.createAtPrev name count ready)).ObservedFinite :=
  unitTokenPrimitive_finite _ (fun _ _ _ _ _ => rfl)

/-- A cloned token uses the same replacement and payment planning. -/
theorem Effect.ObservedFinite.cloneToken (target : Selector) :
    (Effect.prim (.cloneToken target)).ObservedFinite :=
  unitTokenPrimitive_finite _ (fun _ _ _ _ _ => rfl)

/-- A token at a known location retains its ready instruction during entry planning. -/
theorem Effect.ObservedFinite.playUnitTokenAt (name : String) (dest : Option ObjId) (ready : Bool) :
    (Effect.prim (if ready then .playReadyUnitTokenAt name dest else .playUnitTokenAt name dest)).ObservedFinite := by
  cases ready <;> exact unitTokenPrimitive_finite _ (fun _ _ _ _ _ => rfl)

private theorem tokenDestinationChoice_finite (name : String) (destinations : List (Option ObjId)) (ready : Bool) :
    (Effect.eitherOf (EffectList.ofList (destinations.map (fun dest =>
      Effect.prim (if ready then .playReadyUnitTokenAt name dest else .playUnitTokenAt name dest))))).ObservedFinite := by
  apply Effect.ObservedFinite.eitherOf
  apply EffectList.ObservedFinite.ofList
  intro effect member
  obtain ⟨dest, _, rfl⟩ := List.mem_map.mp member
  exact .playUnitTokenAt name dest ready

/-- Offer the legal destinations and carry the original ready instruction into the chosen play. -/
theorem Effect.ObservedFinite.playUnitToken (name : String) (ready : Bool) :
    (Effect.prim (if ready then .playReadyUnitToken name else .playUnitToken name)).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  cases card : s.tokenCard name with
  | none =>
    refine ⟨.nil, .nil, ?_⟩
    cases ready <;> simp [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect, card,
      EffectList.append]
  | some definition =>
    let destinations := s.unitTokenDestinations p definition
    let offer := Effect.eitherOf (EffectList.ofList (destinations.map (fun dest =>
      Effect.prim (if ready then .playReadyUnitTokenAt name dest else .playUnitTokenAt name dest))))
    refine ⟨.cons offer .nil, .cons (tokenDestinationChoice_finite name destinations ready) .nil, ?_⟩
    cases ready <;> simp [runEffect, Effect.pickSel?, Prim.pickSel?, runEffect1, runPrimEffect, card,
      offer, destinations, EffectList.append]

/-- Linked token entry preserves the follow-up while it plans the actual batch. -/
theorem Effect.ObservedFinite.playUnitTokensThen (name : String) (count : Nat) (place : Place)
    (ready : Bool) (index : Nat) (target : Option Selector) :
    (Effect.playUnitTokensThen name count place ready index target).ObservedFinite := by
  apply Effect.ObservedFinite.ofPrograms
  intro s p src env more
  simp only [runEffect, Effect.pickSel?, runEffect1]
  split
  · rename_i batch _
    exact ⟨.cons (beginUnitTokenEntries batch (s.unitTokenReplacements p)) .nil,
      .cons (beginUnitTokenEntries_finite batch _) .nil, rfl⟩
  · exact ⟨.nil, .nil, rfl⟩


end Riftbound

end
