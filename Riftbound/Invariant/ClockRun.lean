module

public import Riftbound.Invariant.Sound
public import Riftbound.Invariant.Clock

/-!
# The clock in every run (I14)

The local facts of the clock are in `Clock.lean`: what calling time does, and what the beginning of
a turn does when the clock has or has not run out. This file adds the rest of I14: **no other step
changes the turn counter or the clock**, so in every game that can be played the turn counter stays
within the clock (`Reachable.clockOk`), a clock that is set never moves, and, once time is called
in the turn `t`, no later state has a turn past `t + 3` (`time_called_bound`). With
`beginTurn_ends`, the game is over after finitely many turns.

The proof walks the arms of `applyFrame0` and `microStep0` the way the other invariants do, with the
existing `SameMeta` and `Safe` facts of the helpers. The turn counter and the clock are written in
two places only: the call of time and the beginning of a turn.
-/

@[expose] public section

namespace Riftbound

/-- The turn counter and the clock are as they were. -/
def TC (s s' : GameState) : Prop := s'.turn = s.turn ∧ s'.clock = s.clock

namespace TC
theorem refl (s : GameState) : TC s s := ⟨rfl, rfl⟩
theorem trans {s s' s'' : GameState} (h1 : TC s s') (h2 : TC s' s'') : TC s s'' :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
theorem of_sameMeta {s s' : GameState} (h : SameMeta s s') : TC s s' := by
  unfold SameMeta at h
  have h1 := congrArg GameState.turn h
  have h2 := congrArg GameState.clock h
  exact ⟨h1, h2⟩
theorem of_safe {s s' : GameState} (h : Safe s s') : TC s s' := of_sameMeta h.same
theorem of_safeP {s s' : GameState} (h : SafeP s s') : TC s s' := by
  obtain ⟨s1, hs, h1⟩ := h
  rcases h1 with rfl | ⟨p, n, rfl⟩
  · exact of_safe hs
  · exact (of_safe hs).trans ⟨rfl, rfl⟩
end TC

theorem tc_applyMana {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {es : List Event}
    (h : applyMana s p src idx pay = some (s', es)) : TC s s' := by
  obtain ⟨s1, pool, hs, rfl⟩ := applyMana_cases h
  exact (TC.of_safe hs).trans ⟨rfl, rfl⟩

theorem tc_applyRune {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (h : applyRune s p c ab = some (s', es)) : TC s s' := by
  unfold applyRune at h
  split at h
  · rename_i o ho
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, rfl⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      obtain ⟨src, d, hs⟩ := moveObj_spec hm
      have h1 : TC s s2 := TC.of_sameMeta hs.other
      exact h1.trans ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem tc_applyPlay {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {pick : SpellPick} {es : List Event} (h : applyPlay s p c pay pick = some (s', es)) : TC s s' := by
  obtain ⟨d, pool, s2, id', m, exhaust, -, -, hm, rfl⟩ := applyPlay_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have h1 : TC s s2 := TC.of_sameMeta hs.other
  split
  · exact h1.trans ⟨rfl, rfl⟩
  · exact h1.trans ⟨rfl, rfl⟩

theorem tc_applyCast {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {targets : List ObjId} {es : List Event} (h : applyCast s p c pay targets flow pick = some (s', es)) :
    TC s s' := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have h1 : TC s s2 := TC.of_sameMeta hs.other
  exact h1.trans ⟨rfl, rfl⟩

theorem tc_applyPlayCard {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {flow : Option Cost} {pick : SpellPick} {targets : List ObjId} {rest : List Frame} {es : List Event}
    (h : applyPlayCard s p c pay targets rest flow pick = some (s', es)) : TC s s' := by
  unfold applyPlayCard at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact ((tc_applyCast hm).trans (TC.of_sameMeta (castPay_safe s c targets (s2, es2)).same)).trans
      ⟨rfl, rfl⟩
  · obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (tc_applyPlay hr).trans (TC.of_sameMeta (payExtra_safe h2).same)

theorem tc_applyActivate {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {targetPlayer : Option PlayerId} {es : List Event}
    (h : applyActivate s p src idx pay ts discards targetPlayer = some (s', es)) : TC s s' := by
  exact TC.of_sameMeta (applyActivate_safe h).same

theorem tc_activateStep {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts discards : List ObjId} {new : List Frame} {targetPlayer : Option PlayerId} {es : List Event}
    (h : activateStep s p src idx pay ts new discards targetPlayer = some (s', es)) : TC s s' := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  exact (tc_applyActivate hm).trans ⟨rfl, rfl⟩

theorem tc_castStep {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : castStep s p c pay ts new flow pick = some (s', es)) : TC s s' := by
  obtain ⟨s2, es2, hm, rfl⟩ := castStep_cases h
  exact ((tc_applyCast hm).trans (TC.of_sameMeta (castPay_safe s c ts (s2, es2)).same)).trans
    ⟨rfl, rfl⟩

theorem tc_reactStep {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {flow : Option Cost} {pick : SpellPick} {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : reactStep s p c pay ts new flow pick = some (s', es)) : TC s s' := by
  rcases reactStep_cases h with ⟨s2, es2, hm, rfl⟩ | ⟨s1, es1, s2, es2, hm, hx, rfl⟩
  · exact ((tc_applyCast hm).trans (TC.of_sameMeta (castPay_safe s c ts (s2, es2)).same)).trans
      ⟨rfl, rfl⟩
  · exact ((tc_applyPlay hm).trans (TC.of_sameMeta (payExtra_safe hx).same)).trans ⟨rfl, rfl⟩

theorem tc_showdownEnd (s : GameState) (bf : ObjId) (rest : List Frame) :
    TC s (showdownEnd s bf rest).1 := by
  rcases showdownEnd_cases s bf rest with ⟨a, e⟩ | e <;> rw [e]
  · exact ⟨rfl, rfl⟩
  · exact (TC.of_safeP (endShowdown_safeP s bf)).trans ⟨rfl, rfl⟩

theorem tc_assignDoneStep (s : GameState) (bf : ObjId) (att side : PlayerId) (acc : List ObjId)
    (done : List (ObjId × Nat)) (rest : List Frame) :
    TC s (assignDoneStep s bf att side acc done rest).1 := by
  rcases assignDoneStep_cases s bf att side acc done rest with
    ⟨b, a, q, d, e⟩ | ⟨r, hr, e⟩ <;> rw [e]
  · exact ⟨rfl, rfl⟩
  · exact (TC.of_safe hr).trans ⟨rfl, rfl⟩

theorem tc_withTriggers (s : GameState) (es : List Event) : TC s (s.withTriggers es) := by
  rcases withTriggers_cases s es with h | ⟨pend, h, -, -⟩ <;> rw [h]
  · exact TC.refl s
  · exact ⟨rfl, rfl⟩

theorem tc_paySurcharge (s : GameState) (a : Action) (s2 : GameState) :
    TC s2 (s.paySurcharge a s2) := by
  rcases GameState.paySurcharge_cases s a s2 with h | ⟨p, pool, h⟩ <;> rw [h]
  · exact TC.refl s2
  · exact ⟨rfl, rfl⟩

theorem tc_cleanupFrame (s : GameState) (rest : List Frame) :
    TC s (cleanupFrame s rest).1 := by
  rcases cleanupFrame_cases s rest with ⟨w, e⟩ | ⟨r, hr, e⟩ | ⟨bf, q, e⟩ | e <;> rw [e]
  · exact ⟨rfl, rfl⟩
  · exact (TC.of_safe hr).trans ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- **The clock is kept** (I14): when time has been called, the turn counter is not past the turn
the clock named. -/
def ClockOk (s : GameState) : Prop := ∀ lim, s.clock = some lim → s.turn ≤ lim

theorem ClockOk.of_tc {s s' : GameState} (hc : ClockOk s) (h : TC s s') : ClockOk s' := by
  intro lim hl
  rw [h.2] at hl
  rw [h.1]
  exact hc lim hl

/-- An answer to a decision frame changes neither the turn nor the clock, except that calling time
sets the clock to 3 turns past the turn that is going on. -/
theorem applyFrame0_tc {s s' : GameState} {a : Action} {es : List Event}
    (h : applyFrame0 s a = some (s', es)) :
    TC s s' ∨ (a.kind = .timeCalled ∧ s'.turn = s.turn ∧ s'.clock = some (s.turn + 3)) := by
  unfold applyFrame0 at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl (tc_applyRune h)
  · obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    have hout : _ = s' := congrArg Prod.fst he
    rw [← hout]
    exact Or.inl ((tc_applyPlayCard hr).trans (TC.of_safe (payPlayDiscard_safe _ _ _ _)))
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have h1 : TC s s2 := TC.of_safe (applyMove_safe (es := es2) hm)
    exact Or.inl (h1.trans ⟨rfl, rfl⟩)
  · rename_i bf q n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl ⟨rfl, rfl⟩
    · have hs' : s' = (showdownEnd s bf rest).1 := by
        rw [Option.some.inj h]
      subst hs'
      exact Or.inl (tc_showdownEnd _ _ _)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · rename_i bf att side acc done rest hp hk
    have hs' : s' = (assignDoneStep s bf att side acc done rest).1 := by
      rw [Option.some.inj h]
    subst hs'
    exact Or.inl (tc_assignDoneStep _ _ _ _ _ _ _)
  · split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       exact Or.inl ⟨rfl, rfl⟩)
  · obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    have hout : _ = s' := congrArg Prod.fst he
    rw [← hout]
    exact Or.inl ((tc_reactStep hr).trans (TC.of_safe (payPlayDiscard_safe _ _ _ _)))
  · exact Or.inl (tc_activateStep h)
  · exact Or.inl (tc_applyRune h)
  · exact Or.inl (tc_activateStep h)
  · rename_i p t more others rest i ts payment hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s ((finalizePick s (t :: more) i ts payment).1) := TC.of_safe (finalizePick_safe s _ i ts payment)
    exact Or.inl (h1.trans ⟨rfl, rfl⟩)
  · exact Or.inl (tc_applyMana h)
  · exact Or.inl (tc_applyMana h)
  · rename_i p n rest c hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (discardObj s c).1 := TC.of_safe (discardObj_safe s c)
    exact Or.inl (h1.trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      obtain ⟨src, d, hs⟩ := moveObj_spec hm
      have h1 : TC s s2 := TC.of_sameMeta hs.other
      exact Or.inl (h1.trans ⟨rfl, rfl⟩)
    · exact absurd h (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨src, d, hs⟩ := moveObj_spec hm
    have h1 : TC s s2 := TC.of_sameMeta hs.other
    exact Or.inl (h1.trans ⟨rfl, rfl⟩)
  · split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       exact Or.inl ⟨rfl, rfl⟩)
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have h1 : TC s s2 := TC.of_sameMeta (recycleAll_meta _ _ hm)
    exact Or.inl (h1.trans ⟨rfl, rfl⟩)
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have h1 : TC s s2 := TC.of_sameMeta (recycleAll_meta _ _ hm)
    exact Or.inl (h1.trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    have hout : _ = s' := congrArg Prod.fst he
    rw [← hout]
    exact Or.inl ((tc_reactStep hr).trans (TC.of_safe (payPlayDiscard_safe _ _ _ _)))
  · exact Or.inl (tc_activateStep h)
  · exact Or.inl (tc_applyRune h)
  · exact Or.inl (tc_applyMana h)
  · rename_i l hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inr ⟨hk, rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · rename_i p n c cs top bottom rest id recycle hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have tc := TC.of_safe (continuePrediction_safe s p n ((c :: cs).erase id)
      (if recycle then top else top ++ [id]) (if recycle then id :: bottom else bottom))
    exact Or.inl (tc.trans ⟨rfl, rfl⟩)
  · rename_i p n top old rest bottom hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have tc := TC.of_safe (completePrediction_safe s p n top bottom)
    exact Or.inl (tc.trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl (tc_applyRune h)
  · exact Or.inl (tc_applyMana h)
  · exact absurd h (by simp)

/-- A step of work leaves the clock, and leaves the turn counter, or begins the next turn when the
clock has not run out. -/
def Tick (s s' : GameState) : Prop :=
  s'.clock = s.clock ∧ (s'.turn = s.turn ∨ (s'.turn = s.turn + 1 ∧ s.clockDue = false))

theorem Tick.of_tc {s s' : GameState} (h : TC s s') : Tick s s' := ⟨h.2, Or.inl h.1⟩

/-- The next turn begins when the clock has not run out; otherwise the game ends. -/
theorem beginTurnStep_tick (s : GameState) (rest : List Frame) : Tick s (beginTurnStep s rest) := by
  unfold beginTurnStep
  split
  · exact Tick.of_tc ⟨rfl, rfl⟩
  · rename_i hd
    exact ⟨rfl, Or.inr ⟨rfl, by simpa using hd⟩⟩

/-- A step of work: only the beginning of a turn changes the turn counter, and only when the clock
has not run out. -/
theorem microStep0_tick {s s' : GameState} {es : List Event}
    (h : microStep0 s = some (s', es)) : Tick s s' := by
  unfold microStep0 at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact beginTurnStep_tick _ _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (s.mapObjects (readyOf (s.active.getD ⟨0⟩))) :=
      TC.of_sameMeta (GameState.sameMeta_mapObjects s _)
    exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (channel (s.active.getD ⟨0⟩) s.channelCount s).1 :=
      TC.of_sameMeta (channel_sameMeta _ _ s)
    exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (s.mapObjects endTurnObj) :=
      TC.of_sameMeta (GameState.sameMeta_mapObjects s _)
    exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (beginStep s (s.active.getD ⟨0⟩)).1 := TC.of_safe (beginStep_safe s _)
    exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (hold s (s.active.getD ⟨0⟩)).1 := TC.of_safeP (hold_safeP s _)
    exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · rename_i p n rest hp
    split at h
    · rename_i s1 es1 hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have h1 : TC s s1 := TC.of_sameMeta (drawOne_meta hd)
      exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Tick.of_tc ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · rename_i p src env e es' rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (runEffect s p src (env.withMight s.mightTable) e es').1 :=
      TC.of_safe (runEffect_safe s p src (env.withMight s.mightTable) e es')
    exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
  · rename_i item rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (finishItem s item).1 := TC.of_sameMeta (finishItem_sameMeta s item)
    exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
  · rename_i rest hp
    have hs' : s' = (cleanupFrame s rest).1 := by
      have := Option.some.inj h
      rw [this]
    subst hs'
    exact Tick.of_tc (tc_cleanupFrame s rest)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · rename_i bf att rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (combatCleanup s bf att).1 := TC.of_safe (combatCleanup_safe s bf att)
    exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · rename_i bf rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ((TC.of_safeP (combatControl_safeP s bf)).trans ⟨rfl, rfl⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Tick.of_tc ⟨rfl, rfl⟩
  · rename_i pend rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have h1 : TC s (triggersStep s pend rest).1 :=
      TC.of_safe (triggersStep_spec s pend rest).1
    exact Tick.of_tc (h1.trans ⟨rfl, rfl⟩)
  · exact absurd h (by simp)


/-- The turn counter and the clock are the same through a chain of steps that leave them. -/
theorem tc_addCards {db : CardDB} (owner : PlayerId) (z : Zone) :
    ∀ (cs : List CardId) {s s' : GameState}, addCards db owner z s cs = some s' → TC s s'
  | [], s, s', h => by
    rw [show addCards db owner z s [] = some s from rfl] at h
    cases h
    exact TC.refl _
  | c :: cs, s, s', h => by
    cases hr : addObject s (newCard db s owner c) z .bottom with
    | none => simp [addCards, hr] at h
    | some r =>
      have h' : addCards db owner z r.1 cs = some s' := by simpa [addCards, hr] using h
      exact (TC.of_sameMeta (addObject_sameMeta hr)).trans (tc_addCards owner z cs h')

theorem tc_addDeck {db : CardDB} {s s' : GameState} {p : PlayerId} {d : Deck}
    (h : s.addDeck db p d = some s') : TC s s' := by
  unfold GameState.addDeck at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s1, h1, s2, h2, s3, h3, s4, h4, h5⟩ := h
  exact (tc_addCards _ _ _ h1).trans ((tc_addCards _ _ _ h2).trans ((tc_addCards _ _ _ h3).trans
    ((tc_addCards _ _ _ h4).trans (tc_addCards _ _ _ h5))))

theorem tc_addDecks {db : CardDB} :
    ∀ (ds : List Deck) {s s' : GameState} {i : Nat}, s.addDecks db i ds = some s' → TC s s'
  | [], s, s', i, h => by
    rw [show s.addDecks db i [] = some s from rfl] at h
    cases h
    exact TC.refl _
  | d :: ds, s, s', i, h => by
    cases hr : s.addDeck db ⟨i⟩ d with
    | none => simp [GameState.addDecks, hr] at h
    | some s1 =>
      have h' : s1.addDecks db (i + 1) ds = some s' := by simpa [GameState.addDecks, hr] using h
      exact (tc_addDeck hr).trans (tc_addDecks ds h')

theorem tc_addLimitedDeck {db : CardDB} {s s' : GameState} {p : PlayerId} {d : LimitedDeck}
    (h : s.addLimitedDeck db p d = some s') : TC s s' := by
  unfold GameState.addLimitedDeck at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s1, h1, s2, h2, s3, h3, s4, h4, h5⟩ := h
  exact (tc_addCards _ _ _ h1).trans ((tc_addCards _ _ _ h2).trans ((tc_addCards _ _ _ h3).trans
    ((tc_addCards _ _ _ h4).trans (tc_addCards _ _ _ h5))))

theorem tc_addLimitedDecks {db : CardDB} :
    ∀ (ds : List LimitedDeck) {s s' : GameState} {i : Nat},
      s.addLimitedDecks db i ds = some s' → TC s s'
  | [], s, s', i, h => by
    rw [show s.addLimitedDecks db i [] = some s from rfl] at h
    cases h
    exact TC.refl _
  | d :: ds, s, s', i, h => by
    cases hr : s.addLimitedDeck db ⟨i⟩ d with
    | none => simp [GameState.addLimitedDecks, hr] at h
    | some s1 =>
      have h' : s1.addLimitedDecks db (i + 1) ds = some s' := by
        simpa [GameState.addLimitedDecks, hr] using h
      exact (tc_addLimitedDeck hr).trans (tc_addLimitedDecks ds h')

/-- A game that has just been set up has not called time, and no turn has begun. -/
theorem Start.clockOk {s : GameState} (h : Start s) : ClockOk s := by
  have key : ∀ (c : GameConfig) (db : CardDB) (s1 : GameState),
      TC (GameState.empty c db) s1 → ClockOk s1 := by
    intro c db s1 ht lim hl
    rw [ht.2] at hl
    exact absurd hl (by simp [GameState.empty])
  cases h with
  | core h =>
    unfold GameState.initial at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨s1, h1, rfl⟩ := h
      exact key _ _ _ ((tc_addDecks _ h1).trans ⟨rfl, rfl⟩)
    · exact absurd h (by simp)
  | limited h =>
    unfold GameState.initialLimited at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨s1, h1, rfl⟩ := h
      exact key _ _ _ ((tc_addLimitedDecks _ h1).trans ⟨rfl, rfl⟩)
    · exact absurd h (by simp)


theorem Tick.keep {s s' : GameState} (hc : ClockOk s) (ht : Tick s s') :
    ClockOk s' ∧ s'.clock = s.clock := by
  refine ⟨fun lim hl => ?_, ht.1⟩
  rw [ht.1] at hl
  rcases ht.2 with h | ⟨h, hd⟩
  · rw [h]; exact hc lim hl
  · rw [h]
    simp only [GameState.clockDue, hl, decide_eq_false_iff_not, Nat.not_le] at hd
    omega

/-- Calling time, through `paySurcharge`, `withTriggers` and the rest of `applyFrame`. -/
theorem applyFrame_called {s s' : GameState} {a : Action} {es : List Event}
    (hk : a.kind = .timeCalled) (h : applyFrame s a = some (s', es)) :
    s'.turn = s.turn ∧ s'.clock = some (s.turn + 3) := by
  obtain ⟨s2, es2, s3, h0, h3, rfl, -⟩ := applyFrame_cases h
  have h2 : TC s2 s3 := by
    rcases h3 with rfl | ⟨q, pool, rfl⟩
    · exact TC.refl _
    · exact ⟨rfl, rfl⟩
  have h4 : TC s3 (s3.withTriggers (es2 ++ extraEvents a es2 ++ s.actionMightEvents s3 a)) :=
    tc_withTriggers _ _
  obtain ⟨actor, kind⟩ := a
  simp only at hk
  subst hk
  rw [applyFrame0_timeCalled] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, -⟩ := h0
  exact ⟨h4.1.trans h2.1, h4.2.trans (h2.2.trans rfl)⟩

theorem tc_applyFrame {s s' : GameState} {a : Action} {es : List Event}
    (h : applyFrame s a = some (s', es)) :
    TC s s' ∨ (a.kind = .timeCalled ∧ s'.turn = s.turn ∧ s'.clock = some (s.turn + 3)) := by
  obtain ⟨s2, es2, s3, h0, h3, rfl, -⟩ := applyFrame_cases h
  have h2 : TC s2 s3 := by
    rcases h3 with rfl | ⟨q, pool, rfl⟩
    · exact TC.refl _
    · exact ⟨rfl, rfl⟩
  have h4 : TC s3 (s3.withTriggers (es2 ++ extraEvents a es2 ++ s.actionMightEvents s3 a)) :=
    tc_withTriggers _ _
  rcases applyFrame0_tc h0 with h1 | ⟨hk, ht, hcl⟩
  · exact Or.inl ((h1.trans h2).trans h4)
  · exact Or.inr ⟨hk, h4.1.trans (h2.1.trans ht), h4.2.trans (h2.2.trans hcl)⟩

/-- An answer changes neither the turn nor the clock, except that the call of time sets the clock
to 3 turns past the turn that is going on. -/
theorem tc_applyAction {s s' : GameState} {a : Action} {es : List Event}
    (h : applyAction s a = some (s', es)) :
    TC s s' ∨ (a.kind = .timeCalled ∧ s'.turn = s.turn ∧ s'.clock = some (s.turn + 3)) := by
  by_cases hk : a.kind = .concede
  · unfold applyAction at h
    simp only [hk] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · rw [applyAction_of_ne hk] at h
    exact tc_applyFrame h

theorem applyAction_called {s s' : GameState} {a : Action} {es : List Event}
    (hk : a.kind = .timeCalled) (h : applyAction s a = some (s', es)) :
    s'.turn = s.turn ∧ s'.clock = some (s.turn + 3) := by
  have hne : a.kind ≠ .concede := by rw [hk]; decide
  rw [applyAction_of_ne hne] at h
  exact applyFrame_called hk h

theorem microStep_tick {s s' : GameState} {es : List Event}
    (h : microStep s = some (s', es)) : Tick s s' := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  have h1 := microStep0_tick h0
  have h2 := tc_withTriggers s2 (es ++ s.mightyEvents s2)
  refine ⟨h2.2.trans h1.1, ?_⟩
  rcases h1.2 with h | h
  · exact Or.inl (h2.1.trans h)
  · exact Or.inr ⟨h2.1.trans h.1, h.2⟩

/-- The work after an answer keeps the clock and does not take the turn counter past it. -/
theorem advance_keep :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event},
      ClockOk s → advance n s es = .ok (s', es') → ClockOk s' ∧ s'.clock = s.clock
  | 0, s, s', es, es', hc, h => by
    unfold advance at h
    split at h
    · rename_i f rest hp
      split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨hc, rfl⟩
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨hc, rfl⟩
  | n + 1, s, s', es, es', hc, h => by
    unfold advance at h
    split at h
    · rename_i f rest hp
      split at h
      · split at h
        · rename_i s1 es1 hm
          obtain ⟨hc1, hcl1⟩ := (microStep_tick hm).keep hc
          obtain ⟨hc2, hcl2⟩ := advance_keep n hc1 h
          exact ⟨hc2, hcl2.trans hcl1⟩
        · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨hc, rfl⟩
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨hc, rfl⟩

/-- **I14, one step.** A step keeps the turn counter within the clock. A clock that is set stays
as it is, because the only answer that sets it, the call of time, is legal once (TR 408.2). The
call sets the clock to 3 turns past the turn that is going on. -/
theorem step_keep {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hc : ClockOk s) (h : step fuel s a = .ok (s', es)) :
    ClockOk s' ∧ (s.clock ≠ none → s'.clock = s.clock) ∧
      (a.kind = .timeCalled → s'.clock = some (s.turn + 3)) := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 hm
      have hc1 : ClockOk s1 := by
        rcases tc_applyAction hm with ht | ⟨-, ht, hcl⟩
        · exact hc.of_tc ht
        · intro lim hl'
          rw [hcl] at hl'
          rw [ht]
          have := Option.some.inj hl'
          omega
      obtain ⟨hc2, hcl2⟩ := advance_keep fuel hc1 h
      refine ⟨hc2, fun hne => ?_, fun hk => ?_⟩
      · by_cases hk : a.kind = .timeCalled
        · exact absurd (legal_timeCalled hk (hl.frame (by rw [hk]; decide))).2.2.2.1 hne
        · rcases tc_applyAction hm with ht | ⟨hk', -, -⟩
          · exact hcl2.trans ht.2
          · exact absurd hk' hk
      · exact hcl2.trans (applyAction_called hk hm).2
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **I14.** In every game that can be played, once time has been called, the turn counter never
goes past the turn the clock named. -/
theorem Reachable.clockOk {s : GameState} (h : Reachable s) : ClockOk s := by
  induction h with
  | init h => exact h.clockOk
  | next hs h ih => exact (step_keep ih h).1

/-- Several steps of play, one after another. -/
inductive Steps : GameState → GameState → Prop where
  /-- No step. -/
  | refl (s : GameState) : Steps s s
  /-- One more step. -/
  | next {s s1 s2 : GameState} {fuel : Nat} {a : Action} {es : List Event}
      (h : Steps s s1) (hs : step fuel s1 a = .ok (s2, es)) : Steps s s2

/-- However the play goes on, a clock that is set stays as it is, and the turn counter stays within
it. -/
theorem Steps.keep {s s2 : GameState} (h : Steps s s2) {lim : Nat} (hc : ClockOk s)
    (hl : s.clock = some lim) : ClockOk s2 ∧ s2.clock = some lim := by
  induction h with
  | refl => exact ⟨hc, hl⟩
  | next h hs ih =>
    obtain ⟨hc1, hl1⟩ := ih
    obtain ⟨hc2, hst, -⟩ := step_keep hc1 hs
    exact ⟨hc2, (hst (by rw [hl1]; simp)).trans hl1⟩

/-- **I14.** After time is called, the game ends in finitely many turns (TR 408.2). When time is
called in the turn `t`, the turn counter is never past `t + 3` in any later state of the game:
the turn that is going on and 3 turns more are played, and the beginning of the next turn ends the
game (`beginTurn_ends`). -/
theorem time_called_bound {s s1 s2 : GameState} {fuel : Nat} {a : Action} {es : List Event}
    (hs : Reachable s) (hk : a.kind = .timeCalled) (h : step fuel s a = .ok (s1, es))
    (hr : Steps s1 s2) : s2.turn ≤ s.turn + 3 := by
  obtain ⟨hc1, -, hcl⟩ := step_keep hs.clockOk h
  exact (hr.keep hc1 (hcl hk)).1 (s.turn + 3) (hr.keep hc1 (hcl hk)).2

end Riftbound

end
