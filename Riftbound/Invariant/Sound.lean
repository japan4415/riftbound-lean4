module

public import Riftbound.Invariant.Step
public import Riftbound.Rules.Owner

/-!
# Soundness of the engine

A legal answer is never refused for any reason but the fuel (invariant I4 and the soundness half of
I6, roadmap.md). This needs, besides `WF`, the ownership invariant `OwnerOk` (CR 056): it is what
makes a card in a player's Non-Board zone go to that player's zones. Both are kept by `step`, so
they hold in every state reached from a set-up game.
-/

@[expose] public section

namespace Riftbound

/-- The work frames always have a step to take. -/
theorem microStep_isSome0 {s : GameState} {f : Frame} {rest : List Frame}
    (hp : s.pending = f :: rest) (hf : f.isWork = true) : ∃ r, microStep0 s = some r := by
  unfold microStep0
  rw [hp]
  cases f with
  | setupHands => exact ⟨_, rfl⟩
  | beginTurn => exact ⟨_, rfl⟩
  | phase ph => cases ph <;> exact ⟨_, rfl⟩
  | scoreHolds => exact ⟨_, rfl⟩
  | expireTurn => exact ⟨_, rfl⟩
  | draw p n =>
    cases n with
    | zero => exact ⟨_, rfl⟩
    | succ n =>
      simp only
      split <;> exact ⟨_, rfl⟩
  | resolveChain => exact ⟨_, rfl⟩
  | run p src env todo => cases todo <;> exact ⟨_, rfl⟩
  | finishSpell item => exact ⟨_, rfl⟩
  | cleanup => exact ⟨_, rfl⟩
  | combatDamage bf att => exact ⟨_, rfl⟩
  | combatResolve bf att => exact ⟨_, rfl⟩
  | combatResult _ => exact ⟨_, rfl⟩
  | combatControl _ => exact ⟨_, rfl⟩
  | combatFinish _ => exact ⟨_, rfl⟩
  | triggers pend => exact ⟨_, rfl⟩
  | _ => simp [Frame.isWork] at hf

/-- A work frame can be advanced: `microStep` does not fail on it. -/
theorem microStep_isSome {s : GameState} {f : Frame} {rest : List Frame}
    (hp : s.pending = f :: rest) (hf : f.isWork = true) : ∃ r, microStep s = some r := by
  obtain ⟨r, hr⟩ := microStep_isSome0 hp hf
  exact ⟨_, by unfold microStep; rw [hr]; rfl⟩

/-- The automatic work fails for no reason but the fuel. -/
theorem advance_error :
    ∀ (n : Nat) {s : GameState} {es : List Event} {e : RuleError},
      advance n s es = .error e → e = .fuelExhausted
  | 0, s, es, e, h => by
    unfold advance at h
    split at h
    · split at h
      · simpa using h.symm
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | n + 1, s, es, e, h => by
    unfold advance at h
    split at h
    · rename_i f rest hp
      split at h
      · rename_i hf
        obtain ⟨r, hr⟩ := microStep_isSome hp hf
        obtain ⟨s1, es1⟩ := r
        simp only [hr] at h
        exact advance_error n h
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- A legal answer to the open question can be applied: `applyFrame` does not fail on it. -/
theorem applyFrame_isSome0 {s : GameState} {a : Action} (hwf : s.WF) (hown : s.OwnerOk)
    (hl : LegalFrame s a) : ∃ r, applyFrame0 s a = some r := by
  unfold applyFrame0
  unfold LegalFrame at hl
  split
  · exact ⟨_, rfl⟩
  · rename_i p _ c ab hp hk
    rw [hp, hk] at hl
    exact applyRune_isSome hwf hl.2.1 hl.2.2
  · rename_i p rest c pay ts flow discard pick hp hk
    rw [hp, hk] at hl
    obtain ⟨r, hr⟩ := applyPlayCard_isSome (rest := rest) hwf hl.2.1 hl.2.2.1
    exact ⟨_, Option.map_eq_some_iff.mpr ⟨r, hr, rfl⟩⟩
  · rename_i p rest u d _ hp hk
    rw [hp, hk] at hl
    obtain ⟨r, hr⟩ := applyMove_isSome hwf hl.2.1
    rw [hr]
    exact ⟨_, rfl⟩
  · rename_i bf q n rest hp hk
    split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rename_i p n rest hp hk
    split <;> exact ⟨_, rfl⟩
  · rename_i p n rest c pay ts flow discard pick hp hk
    rw [hp, hk] at hl
    have hplay : castable s p c pay ts flow pick = true ∨ ∃ d xs choice, playable s p c pay d xs choice = true := by
      rcases reactable_spec.mp hl.2.2.1 with ⟨(h | h) | h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨none, ts, pick, h.2.2.2⟩
      · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h.2
        exact Or.inr ⟨some b, ts, pick, hb⟩
      · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h.2
        exact Or.inr ⟨some b, ts, pick, hb⟩
    obtain ⟨r, hr⟩ := reactStep_isSome (new := .chainPass p 0 :: rest) hwf hl.2.1 hplay
    exact ⟨_, Option.map_eq_some_iff.mpr ⟨r, hr, rfl⟩⟩
  · rename_i p n rest src idx pay ts discards targetPlayer _costBanisher hp hk
    rw [hp, hk] at hl
    exact activateStep_isSome hl.2.1
  · rename_i p n tail c ab hp hk
    rw [hp, hk] at hl
    exact applyRune_isSome hwf hl.2.1 hl.2.2
  · rename_i p rest src idx pay ts discards targetPlayer _costBanisher hp hk
    rw [hp, hk] at hl
    exact activateStep_isSome hl.2.1
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rename_i p tail src idx pay hp hk
    rw [hp, hk] at hl
    exact applyMana_isSome hl.2
  · rename_i p n tail src idx pay hp hk
    rw [hp, hk] at hl
    exact applyMana_isSome hl.2
  · rename_i p n rest c hp hk
    exact ⟨_, rfl⟩
  · rename_i p n rest hp hk
    exact ⟨_, rfl⟩
  · rename_i p src env e es rest yes hp hk
    exact ⟨_, rfl⟩
  · rename_i p src env a b es rest yes hp hk
    exact ⟨_, rfl⟩
  · rename_i p src env c more e es rest o hp hk
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rename_i p rest i hp hk
    rw [hp, hk] at hl
    have hi : i < (s.zone (.player p .outOfGame)).length := hl.2
    have hget : (s.zone (.player p .outOfGame))[i]? = some ((s.zone (.player p .outOfGame))[i]) :=
      List.getElem?_eq_getElem hi
    rw [hget]
    simp only
    obtain ⟨r, hr⟩ := moveObj_isSome hwf (List.getElem_mem hi) .battlefieldZone .top
      (fun o _ => ⟨by simp [Zone.normalize, Zone.valid_battlefieldZone],
        by simp [Zone.normalize]⟩)
    rw [hr]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rename_i p n rest c hp hk
    rw [hp, hk] at hl
    have hc : c ∈ s.zone (.player p .hand) := hl.2.1
    obtain ⟨o, ho⟩ := GameState.obj_of_mem hwf hc
    have howner : o.owner = p := hown.owner p .hand rfl c hc o ho
    have hpn : p.n < s.playerCount :=
      Zone.lt_of_valid_player (GameState.zone_valid_of_mem hwf hc)
    obtain ⟨r, hr⟩ := moveObj_isSome hwf hc (.player p .setAside) .top (fun o' ho' => by
      have : o' = o := Option.some.inj (ho'.symm.trans ho)
      subst this
      rw [howner]
      simp only [Zone.normalize, Zone.isBoard, Bool.false_eq_true, ite_false]
      exact ⟨Zone.valid_player hpn _, by simp⟩)
    rw [hr]
    exact ⟨_, rfl⟩
  · rename_i p n rest hp hk
    split <;> exact ⟨_, rfl⟩
  · rename_i p rest l hp hk
    rw [hp, hk] at hl
    have hperm : l.Perm (s.zone (.player p .setAside)) := hl.2
    have hnd : l.Nodup := hperm.nodup_iff.mpr (GameState.zone_nodup_any hwf _)
    obtain ⟨s2, hs2, -⟩ := recycleAll_some (p := p) (q := p) (k := .setAside) rfl (by simp)
      (by simp) l hwf hown hnd (fun id hid => hperm.mem_iff.mp hid)
    simp only [hs2]
    exact ⟨_, rfl⟩
  · rename_i p rest l hp hk
    rw [hp, hk] at hl
    have hperm : l.Perm (s.zone (.player p .trash)) := hl.2
    have hnd : l.Nodup := hperm.nodup_iff.mpr (GameState.zone_nodup_any hwf _)
    obtain ⟨s2, hs2, -⟩ := recycleAll_some (p := p) (q := p) (k := .trash) rfl (by simp)
      (by simp) l hwf hown hnd (fun id hid => hperm.mem_iff.mp hid)
    simp only [hs2]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rename_i bf q n rest c pay ts flow discard pick hp hk
    rw [hp, hk] at hl
    obtain ⟨r, hr⟩ := reactStep_isSome (new := .chainPass q 0 :: .showdown bf q 0 :: rest)
      hwf hl.2.1 (showdownable_spec hl.2.2.1)
    exact ⟨_, Option.map_eq_some_iff.mpr ⟨r, hr, rfl⟩⟩
  · rename_i bf q rest src idx pay ts discards targetPlayer _costBanisher hp hk
    rw [hp, hk] at hl
    simp only [activatableSD, Bool.and_eq_true] at hl
    exact activateStep_isSome hl.2.1.1
  · rename_i q c ab hp hk
    rw [hp, hk] at hl
    exact applyRune_isSome hwf hl.2.1 hl.2.2
  · rename_i q src idx pay hp hk
    rw [hp, hk] at hl
    exact applyMana_isSome hl.2
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rename_i c ab hp hk
    rw [hp, hk] at hl
    exact applyRune_isSome hwf hl.2.1 hl.2.2.1
  · rename_i src idx pay hp hk
    rw [hp, hk] at hl
    exact applyMana_isSome hl.2.1
  · exact absurd hl (by simp)

/-- A legal answer to the open question can be applied: `applyFrame` does not fail on it. -/
theorem applyFrame_isSome {s : GameState} {a : Action} (hwf : s.WF) (hown : s.OwnerOk)
    (hl : LegalFrame s a) : ∃ r, applyFrame s a = some r := by
  obtain ⟨r, hr⟩ := applyFrame_isSome0 hwf hown hl
  exact ⟨_, by unfold applyFrame; rw [hr]; rfl⟩

/-- A legal answer can be applied: `applyAction` does not fail on it. -/
theorem applyAction_isSome {s : GameState} {a : Action} (hwf : s.WF) (hown : s.OwnerOk)
    (hl : Legal s a) : ∃ r, applyAction s a = some r := by
  by_cases hk : a.kind = .concede
  · obtain ⟨p, hp, -⟩ := (hl.of_concede hk).actor
    exact ⟨_, applyAction_concede hk hp⟩
  · rw [applyAction_of_ne hk]
    exact applyFrame_isSome hwf hown (hl.frame hk)

/-- Applying a legal answer to the open question keeps `OwnerOk`. -/
theorem applyFrame_ownerOk0 {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (hl : LegalFrame s a) (h : applyFrame0 s a = some (s', es)) :
    s'.OwnerOk := by
  unfold applyFrame0 at h
  unfold LegalFrame at hl
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · exact applyRune_ownerOk hwf hown h
  · obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    have hout : _ = s' := congrArg Prod.fst he
    rw [← hout]
    exact (payPlayDiscard_safe _ _ _ _).own (applyPlayCard_wf hwf hr)
      (applyPlayCard_ownerOk hwf hown hr)
  · rename_i p rest u d _ hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact ((applyMove_safe (es := es2) hm).own hwf hown).congr rfl rfl
  · rename_i bf q n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hown.congr rfl rfl
    · have hs' : s' = (showdownEnd s bf rest).1 := by
        rw [Option.some.inj h]
      subst hs'
      rcases showdownEnd_cases s bf rest with ⟨a, e⟩ | e <;> rw [e]
      · exact hown.congr rfl rfl
      · exact ((endShowdown_safeP s bf).own hwf hown).congr rfl rfl
  · rename_i bf att side acc done rest u hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i bf att side acc done rest hp hk
    have hs' : s' = (assignDoneStep s bf att side acc done rest).1 := by
      rw [Option.some.inj h]
    subst hs'
    rcases assignDoneStep_cases s bf att side acc done rest with
        ⟨b, a, q, d, e⟩ | ⟨_, e⟩ | ⟨r, hr, e⟩ <;>
      rw [e]
    · exact hown.congr rfl rfl
    · exact hown.congr rfl rfl
    · exact (hr.own hwf hown).congr rfl rfl
  · rename_i p n rest hp hk
    split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       exact hown.congr rfl rfl)
  · rename_i p n rest c pay ts flow hp hk
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    have hout : _ = s' := congrArg Prod.fst he
    rw [← hout]
    exact (payPlayDiscard_safe _ _ _ _).own (reactStep_wf hwf hr) (reactStep_ownerOk hwf hown hr)
  · rename_i p n rest src idx pay ts discards targetPlayer _costBanisher hp hk
    exact activateStep_ownerOk hwf hown h
  · rename_i p n tail c ab hp hk
    exact applyRune_ownerOk hwf hown h
  · rename_i p rest src idx pay ts discards targetPlayer _costBanisher hp hk
    exact activateStep_ownerOk hwf hown h
  · rename_i p t more others funding rest i ts payment hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((finishTrigger_safe s _ funding i ts payment).own hwf hown).congr rfl rfl
  · rename_i p t more others rest i ts payment hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i p t more others previous rest add hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i p t more others previous rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i p tail src idx pay hp hk
    exact applyMana_ownerOk hwf hown h
  · rename_i p n tail src idx pay hp hk
    exact applyMana_ownerOk hwf hown h
  · rename_i p n rest c hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((discardObj_safe s c).own hwf hown).congr rfl rfl
  · rename_i p n rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i p src env e es rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i p src env a b es rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i p src env c more e es rest o hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i z rest l hp hk
    rw [hp, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.ownerOk_reorder hown hl.2.2).congr rfl rfl
  · rename_i p rest i hp hk
    split at h
    · rename_i id hid
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact (moveObj_ownerOk hwf hown hm).congr rfl rfl
    · exact absurd h (by simp)
  · rename_i rest l hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i p n rest c hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (moveObj_ownerOk hwf hown hm).congr rfl rfl
  · rename_i p n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hown.congr rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hown.congr rfl rfl
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (recycleAll_ownerOk p _ hwf hown hm).congr rfl rfl
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (recycleAll_ownerOk p _ hwf hown hm).congr rfl rfl
  · rename_i p rest opp hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.ownerOk_gainPoints hown opp 1).congr rfl rfl
  · rename_i bf q rest c pay ts flow hp hk
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    have hout : _ = s' := congrArg Prod.fst he
    rw [← hout]
    exact (payPlayDiscard_safe _ _ _ _).own (reactStep_wf hwf hr) (reactStep_ownerOk hwf hown hr)
  · rename_i bf q rest src idx pay ts discards targetPlayer _costBanisher hp hk
    exact activateStep_ownerOk hwf hown h
  · rename_i q c ab hp hk
    exact applyRune_ownerOk hwf hown h
  · rename_i q src idx pay hp hk
    exact applyMana_ownerOk hwf hown h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((continuePrediction_safe _ _ _ _ _ _).own hwf hown).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((completePrediction_safe _ _ _ _ _).own hwf hown).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · exact applyRune_ownerOk hwf hown h
  · exact applyMana_ownerOk hwf hown h
  · exact absurd h (by simp)

/-- Applying a legal answer to the open question keeps `OwnerOk`. -/
theorem applyFrame_ownerOk {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (hl : LegalFrame s a) (h : applyFrame s a = some (s', es)) :
    s'.OwnerOk := by
  obtain ⟨s2, es2, s3, h0, h3, rfl, -⟩ := applyFrame_cases h
  exact withTriggers_ownerOk _ (h3.ownerOk (applyFrame_ownerOk0 hwf hown hl h0))

/-- Applying a legal answer keeps `OwnerOk`. -/
theorem applyAction_ownerOk {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (hl : Legal s a) (h : applyAction s a = some (s', es)) :
    s'.OwnerOk := by
  by_cases hk : a.kind = .concede
  · obtain ⟨p, hp, -⟩ := (hl.of_concede hk).actor
    rw [applyAction_concede hk hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rw [applyAction_of_ne hk] at h
    exact applyFrame_ownerOk hwf hown (hl.frame hk) h

/-- A step of work keeps `OwnerOk`. -/
theorem microStep_ownerOk0 {s s' : GameState} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : microStep0 s = some (s', es)) : s'.OwnerOk := by
  unfold microStep0 at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases beginTurnStep_cases s _ with e | ⟨r, e⟩
    · rw [e]
      exact (GameState.ownerOk_mapObjects hown (f := clearScored) (fun o => rfl)).congr rfl rfl
    · rw [e]; exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.ownerOk_mapObjectsAt hown (awakenReady_owner _)).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((channelEx_safe _ _ _ _).own hwf hown).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.ownerOk_mapObjects hown (fun o => endTurnObj_owner o)).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((beginStep_safe s _).own hwf hown).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((hold_safeP s _).own hwf hown).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i p n rest hp
    split at h
    · rename_i s1 es1 hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact (drawOne_ownerOk hwf hown hd).congr rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((runEffect_safe _ _ _ _ _ _ effectAddPolicy).own hwf hown).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (finishItem_ownerOk hwf hown _).congr rfl rfl
  · rename_i rest hp
    have hs' : s' = (cleanupFrame s rest).1 := by
      have := Option.some.inj h
      rw [this]
    subst hs'
    rcases cleanupFrame_cases s rest with ⟨w, e⟩ | ⟨_, _, _, _, e⟩ | ⟨r, hr, e⟩ | ⟨bf, q, e⟩ | e <;>
      rw [e]
    · exact hown.congr rfl rfl
    · exact hown.congr rfl rfl
    · exact (hr.own hwf hown).congr rfl rfl
    · exact hown.congr rfl rfl
    · exact hown.congr rfl rfl
  · rename_i bf att rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · rename_i bf att rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((combatCleanup_safe s _ _).own hwf hown).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hown.congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((combatControl_safeP s _).own hwf hown).congr rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.ownerOk_mapObjects hown endShowdownObj_owner).congr rfl rfl
  · rename_i pend rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (((triggersStep_spec s pend rest).1).own hwf hown).congr rfl rfl
  · exact absurd h (by simp)

/-- A step of work keeps `OwnerOk`. -/
theorem microStep_ownerOk {s s' : GameState} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : microStep s = some (s', es)) : s'.OwnerOk := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  exact withTriggers_ownerOk _ (microStep_ownerOk0 hwf hown h0)

/-- The automatic work keeps `OwnerOk`. -/
theorem advance_ownerOk :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event}, s.WF → s.OwnerOk →
      advance n s es = .ok (s', es') → s'.OwnerOk
  | 0, s, s', es, es', hwf, hown, h => by
    unfold advance at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hown
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hown
  | n + 1, s, s', es, es', hwf, hown, h => by
    unfold advance at h
    split at h
    · split at h
      · split at h
        · rename_i s1 es1 hm
          exact advance_ownerOk n (microStep_wf hwf hm) (microStep_ownerOk hwf hown hm) h
        · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hown
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hown

/-- A step keeps `OwnerOk`. -/
theorem step_ownerOk {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (h : step fuel s a = .ok (s', es)) : s'.OwnerOk := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      exact advance_ownerOk fuel (applyAction_wf hwf hl ha) (applyAction_ownerOk hwf hown hl ha) h
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Soundness of `step`** (I6, design.md §6.3): a legal answer is refused for no reason but the
fuel. With `step_illegal` and `legal_of_step_ok`, `step` accepts exactly the legal answers, except
that it may run out of fuel. -/
theorem step_sound {fuel : Nat} {s : GameState} {a : Action} (hwf : s.WF) (hown : s.OwnerOk)
    (hl : Legal s a) {e : RuleError} (h : step fuel s a = .error e) : e = .fuelExhausted := by
  obtain ⟨⟨s1, es1⟩, ha⟩ := applyAction_isSome hwf hown hl
  simp only [step, hl, ha, ite_true] at h
  exact advance_error fuel h

/-- **I4.** A step never fails by the engine's own bookkeeping: in a well-formed game, whatever the
answer, the error is `illegal` or `fuelExhausted`, never `internal`. -/
theorem step_not_internal {fuel : Nat} {s : GameState} {a : Action} (hwf : s.WF)
    (hown : s.OwnerOk) {msg : String} : step fuel s a ≠ .error (.internal msg) := by
  intro h
  by_cases hl : Legal s a
  · have := step_sound hwf hown hl h
    simp at this
  · rw [step_illegal hl] at h
    simp at h

/-- The states a game starts from: set up from decks under the Core Rules or a tournament format,
or from Limited decks (TR 602.4). -/
inductive Start : GameState → Prop where
  /-- Set up from decks (CR 101-103). -/
  | core {db : CardDB} {config : GameConfig} {decks : List Deck} {s : GameState}
      (h : GameState.initial db config decks = some s) : Start s
  /-- Set up from Limited decks (TR 602.4). -/
  | limited {db : CardDB} {env : LegalityEnv} {config : GameConfig}
      {decks : List LimitedDeck} {s : GameState}
      (h : GameState.initialLimited db env config decks = some s) : Start s

/-- The states a game can reach: the set-up game, and whatever `step` makes of a reachable state
(design.md §8). -/
inductive Reachable : GameState → Prop where
  /-- The state a game starts from. -/
  | init {s : GameState} (h : Start s) : Reachable s
  /-- A step from a reachable state. -/
  | next {s s' : GameState} {fuel : Nat} {a : Action} {es : List Event} (hs : Reachable s)
      (h : Riftbound.step fuel s a = .ok (s', es)) : Reachable s'

/-- Every reachable state is well formed and keeps cards in their owners' zones. -/
theorem Reachable.inv {s : GameState} (h : Reachable s) : s.WF ∧ s.OwnerOk := by
  induction h with
  | init h =>
    cases h with
    | core h => exact ⟨GameState.initial_wf h, GameState.initial_ownerOk h⟩
    | limited h => exact ⟨GameState.initialLimited_wf h, GameState.initialLimited_ownerOk h⟩
  | next hs h ih => exact ⟨step_wf ih.1 h, step_ownerOk ih.1 ih.2 h⟩

/-- **I4**, for the reachable states: `step` never returns an internal error. -/
theorem Reachable.not_internal {s : GameState} (h : Reachable s) {fuel : Nat} {a : Action}
    {msg : String} : Riftbound.step fuel s a ≠ .error (.internal msg) :=
  Riftbound.step_not_internal h.inv.1 h.inv.2

end Riftbound

end
