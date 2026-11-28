module

public import Riftbound.Invariant.DamageWork

/-!
# Kill instructions and their linked continuations (I12)
-/

@[expose] public section

namespace Riftbound

private theorem banishObj_noAttach (p : PlayerId) (s : GameState) (id : ObjId) :
    NoAttach (banishObj p s id).2 :=
  (sendObj_noAttach .banishment s id).append (banishCardEvents_noAttach p s id _)

private theorem killOrSaveInGroup_noAttach (before s : GameState) (id : ObjId) :
    NoAttach (killOrSaveInGroup before s id).2 := by
  unfold killOrSaveInGroup
  split
  · split
    · exact banishObj_noAttach _ _ _
    · exact killOrSave_noAttach s id
  · exact killOrSave_noAttach s id

private theorem killSpellTarget_noAttach (p : PlayerId) (before s : GameState) (id : ObjId) :
    NoAttach (killSpellTarget p before s id).2 := by
  unfold killSpellTarget
  dsimp only
  split
  · intro gear unit member
    rcases List.mem_cons.mp member with impossible | prior
    · contradiction
    · exact killOrSaveInGroup_noAttach before s id gear unit prior
  · exact killOrSaveInGroup_noAttach before s id

private theorem resolveDeathGroup_noAttach (s : GameState) (group : List ObjId)
    (g : GameState → ObjId → GameState × List Event) (safe : ∀ board id, NoAttach (g board id).2) :
    NoAttach (resolveDeathGroupWith s group g).2 := by
  unfold resolveDeathGroupWith
  apply applyEach_noAttach
  intro board entry
  exact safe (entry.prepare group board) entry.unit

private theorem applyKill_noAttach {s t : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {targets : Selector} {events : List Event}
    (done : applyPrim s p src env (.kill targets) = some (t, events)) : NoAttach events := by
  simp only [applyPrim] at done
  obtain ⟨group, _, applied⟩ := Option.map_eq_some_iff.mp done
  by_cases spell : ((s.cardDef? src) <|> env.sourceCard.bind s.cards.find?).any (·.hasType .spell) = true
  · rw [ite_eq_left spell] at applied
    rw [← (Prod.mk.inj applied).2]
    have safe := resolveDeathGroup_noAttach s group (killSpellTarget p s) (killSpellTarget_noAttach p s)
    apply NoAttach.append
    · intro gear unit member
      exact safe gear unit (List.mem_filter.mp member).1
    · split <;> simp [NoAttach]
  · rw [ite_eq_right spell] at applied
    rw [← (Prod.mk.inj applied).2]
    exact resolveDeathGroup_noAttach s group (killOrSaveInGroup s) (killOrSaveInGroup_noAttach s)

private theorem linkedKillFrames_finite (before s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (events : List Event) (linked : Option KillFollowup)
    (finite : ∀ link, linked = some link → link.body.ObservedFinite) :
    ∀ frame ∈ linkedKillFrames before s p src env events linked, frame.FiniteRun := by
  intro frame member
  cases linked with
  | none => simp [linkedKillFrames] at member
  | some link =>
    unfold linkedKillFrames at member
    dsimp only at member
    split at member
    · split at member
      · obtain rfl := List.mem_singleton.mp member
        exact ⟨_, _, _, _, rfl, .cons (finite link rfl) .nil⟩
      · simp at member
    · simp at member

private theorem killEffect_finite {effect : Effect} (targets : Selector) (delay : Option Nat)
    (linked : Option KillFollowup)
    (dispatch : ∀ s p src env more, runEffect s p src env effect more effectAddPolicy =
      killEffectStep s p src env targets delay more linked)
    (finite : ∀ link, linked = some link → link.body.ObservedFinite) : effect.ObservedFinite := by
  apply Effect.ObservedFinite.ofDecisionOrForks
  intro s p src env more
  dsimp only
  rw [dispatch]
  cases offered : s.deathGroupChoice ((targets.eval s p src env).getD []) with
  | some choice =>
    obtain ⟨unit, controller, first, other⟩ := choice
    simp only [killEffectStep, offered]
    exact Or.inr ⟨_, _, rfl, rfl⟩
  | none =>
    cases applied : applyPrim s p src env (.kill targets) with
    | none =>
      simp only [killEffectStep, offered, applied]
      exact Or.inl ⟨[], rfl, by simp⟩
    | some result =>
      obtain ⟨killed, events⟩ := result
      simp only [killEffectStep, offered, applied, (applyKill_noAttach applied).replacementFrames, List.nil_append]
      exact Or.inl ⟨_, rfl, linkedKillFrames_finite s _ p src env events linked finite⟩

private theorem Effect.ObservedFinite.killDirect (targets : Selector)
    (direct : (Effect.prim (.kill targets)).pickSel? = none) : (Effect.prim (.kill targets)).ObservedFinite := by
  apply killEffect_finite targets none none _ (fun _ impossible => by contradiction)
  intro s p src env more
  simp only [runEffect, direct, runEffect1, runPrimEffect]

/-- A Kill processes its selected group, waits for a target or death-replacement decision,
or resumes the effect with the observed events. -/
theorem Effect.ObservedFinite.kill (targets : Selector) : (Effect.prim (.kill targets)).ObservedFinite :=
  .withResolutionPick _ (.killDirect targets) (.killDirect (.var pickVar) rfl)
    (fun _ _ _ _ impossible => by cases impossible)

/-- A Kill can record the count for an end-of-turn trigger before resuming. -/
theorem Effect.ObservedFinite.killThenAtEnd (targets : Selector) (index : Nat) :
    (Effect.killThenAtEnd targets index).ObservedFinite :=
  killEffect_finite targets (some index) none (fun _ _ _ _ _ => rfl) (fun _ impossible => by contradiction)

/-- Follow a Kill with a certified instruction for the affected Unit's controller. -/
theorem Effect.ObservedFinite.killThenForController (slot : Nat) {body : Effect} (finite : body.ObservedFinite) :
    (Effect.killThenForController slot body).ObservedFinite := by
  apply killEffect_finite (.slot slot) none (some ⟨slot, body, .forController⟩) (fun _ _ _ _ _ => rfl)
  intro link eq
  obtain rfl := Option.some.inj eq
  exact finite

/-- Run a certified follow-up only when this Kill caused the target's death. -/
theorem Effect.ObservedFinite.killThenIfKilled (slot : Nat) {body : Effect} (finite : body.ObservedFinite) :
    (Effect.killThenIfKilled slot body).ObservedFinite := by
  apply killEffect_finite (.slot slot) none (some ⟨slot, body, .ifKilled⟩) (fun _ _ _ _ _ => rfl)
  intro link eq
  obtain rfl := Option.some.inj eq
  exact finite

end Riftbound

end
