module

public import Riftbound.Engine.Step

/-!
# Properties of the engine

Well-formedness (I3), conservation of physical cards (I1), completeness of `step` against `Legal`
and monotonicity in the fuel (I15) (roadmap.md).

Not yet proved, and tracked in roadmap.md: that a legal answer is never refused for any reason but
the fuel (soundness, with I4). It needs an invariant on the frames, which come in milestone M3.
-/

@[expose] public section

namespace Riftbound

/-- Applying a legal answer keeps the game well formed. -/
theorem applyFrame_wf0 {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : LegalFrame s a) (h : applyFrame0 s a = some (s', es)) : s'.WF := by
  unfold applyFrame0 at h
  unfold LegalFrame at hl
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · exact applyRune_wf hwf h
  · exact applyPlayCard_wf hwf h
  · rename_i p rest u d hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact GameState.WF.congr ((applyMove_safe (es := es2) hm).wf hwf) rfl rfl rfl rfl
  · rename_i bf q n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr hwf rfl rfl rfl rfl
    · have hs' : s' = (showdownEnd s bf rest).1 := by
        rw [Option.some.inj h]
      subst hs'
      rcases showdownEnd_cases s bf rest with ⟨a, e⟩ | e <;> rw [e]
      · exact hwf.congr rfl rfl rfl rfl
      · exact ((endShowdown_safeP s bf).wf hwf).congr rfl rfl rfl rfl
  · rename_i bf att side acc done rest u hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · rename_i bf att side acc done rest hp hk
    have hs' : s' = (assignDoneStep s bf att side acc done rest).1 := by
      rw [Option.some.inj h]
    subst hs'
    rcases assignDoneStep_cases s bf att side acc done rest with
        ⟨b, a, q, d, e⟩ | ⟨r, hr, e⟩ <;>
      rw [e]
    · exact hwf.congr rfl rfl rfl rfl
    · exact (hr.wf hwf).congr rfl rfl rfl rfl
  · rename_i p n rest hp hk
    split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       exact GameState.WF.congr hwf rfl rfl rfl rfl)
  · rename_i p rest c pay ts hp hk
    exact castStep_wf hwf h
  · rename_i p rest src idx pay ts hp hk
    exact activateStep_wf hwf h
  · rename_i p n rest c ab hp hk
    exact applyRune_wf hwf h
  · rename_i p rest src idx pay ts hp hk
    exact activateStep_wf hwf h
  · rename_i p t more others rest i ts hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((putPick_safe s _ i ts).wf hwf).congr rfl rfl rfl rfl
  · rename_i p tail src idx hp hk
    exact applyMana_wf hwf h
  · rename_i p n tail src idx hp hk
    exact applyMana_wf hwf h
  · rename_i p n rest c hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((sendObj_safe .trash s c).wf hwf).congr rfl rfl rfl rfl
  · rename_i p n rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · rename_i z rest l hp hk
    rw [hp, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr (GameState.wf_reorder hwf hl.2.1 hl.2.2) rfl rfl rfl rfl
  · rename_i p rest i hp hk
    split at h
    · rename_i id hid
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact GameState.WF.congr (moveObj_wf hwf hm) rfl rfl rfl rfl
    · exact absurd h (by simp)
  · rename_i rest l hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · rename_i p n rest c hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact GameState.WF.congr (moveObj_wf hwf hm) rfl rfl rfl rfl
  · rename_i p n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr hwf rfl rfl rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr hwf rfl rfl rfl rfl
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact GameState.WF.congr (recycleAll_wf p _ hwf hm) rfl rfl rfl rfl
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact GameState.WF.congr (recycleAll_wf p _ hwf hm) rfl rfl rfl rfl
  · rename_i p rest opp hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr (GameState.wf_gainPoints hwf opp 1) rfl rfl rfl rfl
  · exact absurd h (by simp)

/-- Applying a legal answer keeps the game well formed. -/
theorem applyFrame_wf {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : LegalFrame s a) (h : applyFrame s a = some (s', es)) : s'.WF := by
  obtain ⟨s2, es2, h0, rfl, -⟩ := applyFrame_cases h
  exact withTriggers_wf _ (applyFrame_wf0 hwf hl h0)

/-- Applying a legal answer keeps the game well formed. -/
theorem applyAction_wf {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : Legal s a) (h : applyAction s a = some (s', es)) : s'.WF := by
  by_cases hk : a.kind = .concede
  · obtain ⟨p, hp, -⟩ := (hl.of_concede hk).actor
    rw [applyAction_concede hk hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · rw [applyAction_of_ne hk] at h
    exact applyFrame_wf hwf (hl.frame hk) h

/-- The automatic work keeps the game well formed. -/
theorem advance_wf :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event}, s.WF →
      advance n s es = .ok (s', es') → s'.WF
  | 0, s, s', es, es', hwf, h => by
    unfold advance at h
    split at h
    · rename_i f rest hp
      split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hwf
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hwf
  | n + 1, s, s', es, es', hwf, h => by
    unfold advance at h
    split at h
    · rename_i f rest hp
      split at h
      · split at h
        · rename_i s1 es1 hm
          exact advance_wf n (microStep_wf hwf hm) h
        · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hwf
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hwf

/-- **I3** (engine). A step keeps the game well formed. -/
theorem step_wf {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (h : step fuel s a = .ok (s', es)) : s'.WF := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      exact advance_wf fuel (applyAction_wf hwf hl ha) h
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A step is accepted only for a legal answer: `step` is complete against `Legal`
(design.md §6.3, I6). -/
theorem legal_of_step_ok {fuel : Nat} {s : GameState} {a : Action} {r : GameState × List Event}
    (h : step fuel s a = .ok r) : Legal s a := by
  unfold step at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- An answer that is not legal is refused as illegal. -/
theorem step_illegal {fuel : Nat} {s : GameState} {a : Action} (h : ¬ Legal s a) :
    step fuel s a = .error .illegal := by
  simp [step, h]

/-- **I15** (work). More fuel gives the same result: if the work reaches the next decision with
`n` steps, it does with any number of steps from `n` up. -/
theorem advance_mono :
    ∀ (n : Nat) {m : Nat} {s : GameState} {es : List Event} {r : GameState × List Event},
      advance n s es = .ok r → n ≤ m → advance m s es = .ok r
  | 0, m, s, es, r, h, _ => by
    cases m with
    | zero => exact h
    | succ k =>
      unfold advance at h ⊢
      split at h
      · split at h
        · exact absurd h (by simp)
        · rename_i hf
          simpa [hf] using h
      · exact h
  | n + 1, m, s, es, r, h, hnm => by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    unfold advance at h ⊢
    split at h
    · split at h
      · rename_i hf
        simp only [hf, ite_true] at h ⊢
        split at h
        · exact advance_mono n h (by omega)
        · exact absurd h (by simp)
      · rename_i hf
        simpa [hf] using h
    · exact h

/-- **I15.** More fuel gives the same result for a whole step. -/
theorem step_mono {n m : Nat} {s : GameState} {a : Action} {r : GameState × List Event}
    (h : step n s a = .ok r) (hnm : n ≤ m) : step m s a = .ok r := by
  by_cases hl : Legal s a
  · cases ha : applyAction s a with
    | none => simp [step, hl, ha] at h
    | some r1 =>
      simp only [step, hl, ha, ite_true] at h ⊢
      exact advance_mono n h hnm
  · simp [step, hl] at h

/-- Applying a legal answer keeps the physical cards. -/
theorem applyFrame_physIds0 {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : LegalFrame s a) (h : applyFrame0 s a = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  unfold applyFrame0 at h
  unfold LegalFrame at hl
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · exact applyRune_physIds hwf h
  · exact applyPlayCard_physIds hwf h
  · rename_i p rest u d hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (applyMove_safe (es := es2) hm).phys hwf
  · rename_i bf q n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
    · have hs' : s' = (showdownEnd s bf rest).1 := by
        rw [Option.some.inj h]
      subst hs'
      rcases showdownEnd_cases s bf rest with ⟨a, e⟩ | e <;> rw [e]
      · exact List.Perm.refl _
      · exact (endShowdown_safeP s bf).phys hwf
  · rename_i bf att side acc done rest u hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · rename_i bf att side acc done rest hp hk
    have hs' : s' = (assignDoneStep s bf att side acc done rest).1 := by
      rw [Option.some.inj h]
    subst hs'
    rcases assignDoneStep_cases s bf att side acc done rest with
        ⟨b, a, q, d, e⟩ | ⟨r, hr, e⟩ <;>
      rw [e]
    · exact List.Perm.refl _
    · exact hr.phys hwf
  · rename_i p n rest hp hk
    split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       exact List.Perm.refl _)
  · rename_i p n rest c pay ts hp hk
    exact castStep_physIds hwf h
  · rename_i p n rest src idx pay ts hp hk
    exact activateStep_physIds hwf h
  · rename_i p n tail c ab hp hk
    exact applyRune_physIds hwf h
  · rename_i p rest src idx pay ts hp hk
    exact activateStep_physIds hwf h
  · rename_i p t more others rest i ts hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (putPick_safe s _ i ts).phys hwf
  · rename_i p tail src idx hp hk
    exact applyMana_physIds hwf h
  · rename_i p n tail src idx hp hk
    exact applyMana_physIds hwf h
  · rename_i p n rest c hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (sendObj_safe .trash s c).phys hwf
  · rename_i p n rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · rename_i z rest l hp hk
    rw [hp, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.physIds_reorder hl.2.1 hl.2.2
  · rename_i p rest i hp hk
    split at h
    · rename_i id hid
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      have hp' := moveObj_physIds hwf hm
      exact hp'
    · exact absurd h (by simp)
  · rename_i rest l hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · rename_i p n rest c hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hp' := moveObj_physIds hwf hm
    exact hp'
  · rename_i p n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hp' := recycleAll_physIds p _ hwf hm
    exact hp'
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hp' := recycleAll_physIds p _ hwf hm
    exact hp'
  · rename_i p rest opp hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · exact absurd h (by simp)

/-- Applying a legal answer keeps the physical cards. -/
theorem applyFrame_physIds {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : LegalFrame s a) (h : applyFrame s a = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨s2, es2, h0, rfl, -⟩ := applyFrame_cases h
  rw [withTriggers_physIds]
  exact applyFrame_physIds0 hwf hl h0

/-- Applying a legal answer keeps the physical cards. -/
theorem applyAction_physIds {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : Legal s a) (h : applyAction s a = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  by_cases hk : a.kind = .concede
  · obtain ⟨p, hp, -⟩ := (hl.of_concede hk).actor
    rw [applyAction_concede hk hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · rw [applyAction_of_ne hk] at h
    exact applyFrame_physIds hwf (hl.frame hk) h

/-- The automatic work keeps the physical cards. -/
theorem advance_physIds :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event}, s.WF →
      advance n s es = .ok (s', es') → s'.physIds.Perm s.physIds
  | 0, s, s', es, es', hwf, h => by
    unfold advance at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact List.Perm.refl _
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
  | n + 1, s, s', es, es', hwf, h => by
    unfold advance at h
    split at h
    · split at h
      · split at h
        · rename_i s1 es1 hm
          exact (advance_physIds n (microStep_wf hwf hm) h).trans (microStep_physIds hwf hm)
        · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact List.Perm.refl _
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _

/-- **I1** (engine). A step keeps the physical cards: the list of physical cards in the zones is
rearranged, nothing is lost or made. -/
theorem step_physIds {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (h : step fuel s a = .ok (s', es)) : s'.physIds.Perm s.physIds := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      exact (advance_physIds fuel (applyAction_wf hwf hl ha) h).trans
        (applyAction_physIds hwf hl ha)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The answers of the players to the open question that `legalFrameActions` lists are exactly
the legal ones by a player. -/
theorem legalFrameActions_iff (s : GameState) (a : Action) :
    a ∈ legalFrameActions s ↔ LegalFrame s a ∧ a.actor.isPlayer = true := by
  obtain ⟨actor, kind⟩ := a
  unfold legalFrameActions LegalFrame
  rcases hp : s.pending with _ | ⟨f, rest⟩
  · simp
  · cases f <;> cases kind <;> cases actor <;>
      simp [legalRunes, Actor.isPlayer, mem_legalPlays, mem_legalMoves, mem_legalAssigns,
        mem_legalActivates, mem_legalReactions, mem_legalPuts, mem_legalManas]
    all_goals try grind
    all_goals (rename_i _ _ ab _; cases ab <;> grind)

/-- The concessions listed are exactly the legal concessions. -/
theorem concedeActions_iff (s : GameState) (a : Action) :
    a ∈ concedeActions s ↔ LegalConcede s a ∧ a.actor.isPlayer = true := by
  obtain ⟨actor, kind⟩ := a
  unfold concedeActions LegalConcede
  cases kind <;> cases actor <;> by_cases h : s.playerCount = 2 <;>
    simp [Actor.isPlayer, h, allPlayers]
  all_goals grind

/-- **I6** (enumeration). The answers of the players that `legalActions` lists are exactly the legal
answers by a player: nothing legal is missing and nothing illegal is listed (design.md §6.3).
Chance answers are not listed. -/
theorem legalActions_iff (s : GameState) (a : Action) :
    a ∈ legalActions s ↔ Legal s a ∧ a.actor.isPlayer = true := by
  unfold legalActions Legal
  by_cases h : s.result = none
  · simp only [h, ite_true, true_and, List.mem_append]
    rw [legalFrameActions_iff, concedeActions_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
  · simp [h]

end Riftbound

end
