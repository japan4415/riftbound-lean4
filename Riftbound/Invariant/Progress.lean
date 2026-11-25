module

public import Riftbound.Invariant.Hands

/-!
# Progress

**I5** (roadmap.md): while the game is not over, there is an answer other than a concession, or a
chance decision is asked for; and a decision that is split into steps never reaches a dead end.

The proof tracks the bottom of the stack. The frames at the bottom are the ones that never go
away without another frame taking their place: the turn player's `priority`, the `beginTurn` that
follows `Ending`, and the two frames of the setup. So the stack is never empty while the game is on.
-/

@[expose] public section

namespace Riftbound

/-- The frames that can be at the bottom of the stack: each one is replaced by a frame that is
itself at the bottom, never by nothing. -/
def Frame.isBottom : Frame → Bool
  | .priority _ => true
  | .beginTurn => true
  | .setupHands => true
  | .chanceTurnOrder => true
  | _ => false

/-- The bottom of the stack is one of those frames. -/
def BottomOk (l : List Frame) : Prop := ∃ f, l.getLast? = some f ∧ f.isBottom = true

/-- A stack with a bottom frame is not empty. -/
theorem BottomOk.ne_nil {l : List Frame} (h : BottomOk l) : l ≠ [] := by
  obtain ⟨f, hf, -⟩ := h
  intro e
  rw [e] at hf
  simp at hf

/-- Replacing the top frame keeps a bottom frame: if the top frame was the only one, what replaces
it must have a bottom frame itself. -/
theorem BottomOk.replace {f : Frame} {rest new : List Frame} (h : BottomOk (f :: rest))
    (hnew : rest = [] → BottomOk new) : BottomOk (new ++ rest) := by
  cases rest with
  | nil => simpa using hnew rfl
  | cons x xs =>
    obtain ⟨g, hg, hb⟩ := h
    refine ⟨g, ?_, hb⟩
    rw [List.getLast?_append]
    simpa [List.getLast?_cons_cons] using hg

/-- A frame that is not a bottom frame is never alone: popping it leaves a bottom frame. -/
theorem BottomOk.pop {f : Frame} {rest : List Frame} (h : BottomOk (f :: rest))
    (hf : f.isBottom = false) : BottomOk rest := by
  have := h.replace (new := []) (fun hr => by
    obtain ⟨g, hg, hb⟩ := h
    subst hr
    simp at hg
    subst hg
    rw [hf] at hb
    exact absurd hb (by simp))
  simpa using this

/-- A frame that is not a bottom frame can be replaced by any frames. -/
theorem BottomOk.swap {f : Frame} {rest : List Frame} (h : BottomOk (f :: rest))
    (hf : f.isBottom = false) (new : List Frame) : BottomOk (new ++ rest) := by
  have hr := h.pop hf
  have hne := hr.ne_nil
  exact h.replace (fun e => absurd e hne)

/-- **The stack invariant.** While the game is on, the stack has a bottom frame. -/
def StackInv (s : GameState) : Prop := s.result = none → BottomOk s.pending

/-- A step that keeps the result and keeps a bottom frame in the new stack keeps the invariant. -/
theorem StackInv.of_next {s s2 : GameState} (hinv : StackInv s) (hres : s2.result = s.result)
    (hb : BottomOk s.pending → BottomOk s2.pending) : StackInv s2 :=
  fun h => hb (hinv (hres ▸ h))

/-- Applying a legal answer to the open question keeps the stack invariant. -/
theorem applyFrame_stack0 {s s' : GameState} {a : Action} {es : List Event}
    (hinv : StackInv s) (h : applyFrame0 s a = some (s', es)) : StackInv s' := by
  unfold applyFrame0 at h
  split at h
  · rename_i rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.replace (new := [Frame.phase .ending, Frame.beginTurn])
      (fun _ => ⟨Frame.beginTurn, by simp, rfl⟩)
  · rename_i p rest c ab hp hk
    have hmeta := applyRune_meta h
    exact hinv.of_next hmeta.2.2.2.1 (fun hb => by rw [hmeta.2.2.2.2]; exact hb)
  · rename_i p rest c pay ts flow discard pick hp hk
    obtain ⟨-, -, -, hres, -, hpend⟩ := applyPlayCard_discard_meta h
    refine hinv.of_next hres (fun hb => ?_)
    rw [hp] at hb
    rcases hpend with e | e
    · rw [e, hp]; exact hb
    · rw [e]
      exact hb.replace (new := [Frame.chainPass p 0, Frame.priority p])
        (fun _ => ⟨Frame.priority p, by simp, rfl⟩)
  · rename_i p rest u d hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    refine hinv.of_next (applyMove_safe (es := es2) hm).same.result (fun hb => ?_)
    rw [hp] at hb
    exact hb.replace (new := [Frame.cleanup, Frame.priority p])
      (fun _ => ⟨Frame.priority p, by simp, rfl⟩)
  · rename_i bf q n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_next rfl (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.showdown bf (s.nextPlayer q) (n + 1)]
    · have hs' : s' = (showdownEnd s bf rest).1 := by
        rw [Option.some.inj h]
      subst hs'
      rcases showdownEnd_cases s bf rest with ⟨a, e⟩ | e <;> rw [e]
      · refine hinv.of_next rfl (fun hb => ?_)
        rw [hp] at hb
        exact hb.swap rfl [Frame.combatDamage bf a]
      · refine hinv.of_next (endShowdown_safeP s bf).result (fun hb => ?_)
        rw [hp] at hb
        exact hb.swap rfl _
  · rename_i bf att side acc done rest u hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.assign bf att side (acc ++ [u]) done]
  · rename_i bf att side acc done rest hp hk
    have hs' : s' = (assignDoneStep s bf att side acc done rest).1 := by
      rw [Option.some.inj h]
    subst hs'
    rcases assignDoneStep_cases s bf att side acc done rest with
        ⟨b, a, q, d, e⟩ | ⟨r, hr, e⟩ <;>
      rw [e]
    · refine hinv.of_next rfl (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.assign b a q [] d]
    · refine hinv.of_next hr.same.result (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.cleanup, Frame.combatResolve bf att]
  · rename_i p n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_next rfl (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.chainPass (s.nextPlayer p) (n + 1)]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_next rfl (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.resolveChain]
  · rename_i p n rest c pay ts flow discard pick hp hk
    obtain ⟨-, -, -, hres, -, hpend⟩ := reactStep_discard_meta h
    refine hinv.of_next hres (fun hb => ?_)
    rw [hp] at hb
    rw [hpend]
    exact hb.swap rfl [Frame.chainPass p 0]
  · rename_i p n rest src idx pay ts discards targetPlayer hp hk
    obtain ⟨-, -, -, hres, -, hpend⟩ := activateStep_meta h
    refine hinv.of_next hres (fun hb => ?_)
    rw [hp] at hb
    rw [hpend]
    exact hb.swap rfl [Frame.chainPass p 0]
  · rename_i p n tail c ab hp hk
    have hmeta := applyRune_meta h
    exact hinv.of_next hmeta.2.2.2.1 (fun hb => by rw [hmeta.2.2.2.2]; exact hb)
  · rename_i p rest src idx pay ts discards targetPlayer hp hk
    obtain ⟨-, -, -, hres, -, hpend⟩ := activateStep_meta h
    refine hinv.of_next hres (fun hb => ?_)
    rw [hp] at hb
    rw [hpend]
    exact hb.replace (new := [Frame.chainPass p 0, Frame.priority p])
      (fun _ => ⟨Frame.priority p, by simp, rfl⟩)
  · rename_i p t more others rest i ts payment hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (finalizePick_safe s (t :: more) i ts payment).same.result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.triggers ((t :: more).eraseIdx i ++ others)]
  · rename_i p tail src idx pay hp hk
    have hmeta := applyMana_meta h
    exact hinv.of_next hmeta.2.2.2.1 (fun hb => by rw [hmeta.2.2.2.2]; exact hb)
  · rename_i p n tail src idx pay hp hk
    have hmeta := applyMana_meta h
    exact hinv.of_next hmeta.2.2.2.1 (fun hb => by rw [hmeta.2.2.2.2]; exact hb)
  · rename_i p n rest c hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (discardObj_safe s c).same.result (fun hb => ?_)
    rw [hp] at hb
    dsimp only
    split
    · exact hb.pop rfl
    · exact hb.swap rfl [Frame.discard p (n - 1)]
  · rename_i p n rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i p src env e es rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.run p src env (if yes = true then EffectList.cons e es else es)]
  · rename_i p src env a b es rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.run p src env (EffectList.cons (if yes = true then a else b) es)]
  · rename_i p src env c more e es rest o hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.run p src (env.bindPick o (e.pickIsTarget s o)) (EffectList.cons e es)]
  · rename_i z rest l hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i p rest i hp hk
    split at h
    · rename_i id hid
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      obtain ⟨src, d, hs⟩ := moveObj_spec hm
      refine hinv.of_next hs.other.result (fun hb => ?_)
      rw [hp] at hb
      exact hb.pop rfl
    · exact absurd h (by simp)
  · rename_i rest l hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.replace (new := [Frame.setupHands]) (fun _ => ⟨Frame.setupHands, by simp, rfl⟩)
  · rename_i p n rest c hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨src, d, hs⟩ := moveObj_spec hm
    refine hinv.of_next hs.other.result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.mulligan p (n + 1)]
  · rename_i p n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_next rfl (fun hb => ?_)
      rw [hp] at hb
      exact hb.pop rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_next rfl (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.draw p (_ + 1), Frame.chanceRecycle p]
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    refine hinv.of_next (recycleAll_meta p _ hm).result (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    refine hinv.of_next (recycleAll_meta p _ hm).result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.chooseBurnOut p]
  · rename_i p rest opp hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i bf q n rest c pay ts flow discard pick hp hk
    obtain ⟨-, -, -, hres, -, hpend⟩ := reactStep_discard_meta h
    refine hinv.of_next hres (fun hb => ?_)
    rw [hp] at hb
    rw [hpend]
    exact hb.swap rfl [Frame.chainPass q 0, Frame.showdown bf q 0]
  · rename_i bf q n rest src idx pay ts discards targetPlayer hp hk
    obtain ⟨-, -, -, hres, -, hpend⟩ := activateStep_meta h
    refine hinv.of_next hres (fun hb => ?_)
    rw [hp] at hb
    rw [hpend]
    exact hb.swap rfl [Frame.chainPass q 0, Frame.showdown bf q 0]
  · rename_i q c ab hp hk
    have hmeta := applyRune_meta h
    exact hinv.of_next hmeta.2.2.2.1 (fun hb => by rw [hmeta.2.2.2.2]; exact hb)
  · rename_i q src idx pay hp hk
    have hmeta := applyMana_meta h
    exact hinv.of_next hmeta.2.2.2.1 (fun hb => by rw [hmeta.2.2.2.2]; exact hb)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_next rfl (fun hb => hb)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact fun hres => by simp at hres
  · rename_i p n c cs top bottom rest id recycle hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    let r := continuePrediction s p n ((c :: cs).erase id)
      (if recycle then top else top ++ [id]) (if recycle then id :: bottom else bottom)
    have hm := (continuePrediction_safe s p n ((c :: cs).erase id)
      (if recycle then top else top ++ [id]) (if recycle then id :: bottom else bottom)).same
    refine hinv.of_next hm.result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl r.2
  · rename_i p n top old rest bottom hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (completePrediction_safe s p n top bottom).same.result (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i p src env first more es rest card hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.run p src env (.cons (.rememberNamedCard card) es)]
  · have hmeta := applyRune_meta h
    exact hinv.of_next hmeta.2.2.2.1 (fun hb => by rw [hmeta.2.2.2.2]; exact hb)
  · have hmeta := applyMana_meta h
    exact hinv.of_next hmeta.2.2.2.1 (fun hb => by rw [hmeta.2.2.2.2]; exact hb)
  · exact absurd h (by simp)

/-- Finding the triggers a step set off keeps the stack invariant: `triggers` frames go beneath the
work, above a frame that decides, so the bottom of the stack stays. -/
theorem StackInv.withTriggers {s : GameState} (hinv : StackInv s) (es : List Event) :
    StackInv (s.withTriggers es) := by
  rcases withTriggers_cases s es with h | ⟨pend, h, -⟩
  · rw [h]; exact hinv
  · rw [h]
    intro hres
    obtain ⟨g, hg, hb⟩ := hinv hres
    refine ⟨g, insertTriggers_getLast pend _ hg ?_ ?_, hb⟩
    · cases g <;> simp [Frame.isBottom, Frame.isResolution] at hb ⊢
    · intro x hx
      subst hx
      simp [Frame.isBottom] at hb

/-- Applying a legal answer to the open question keeps the stack invariant. -/
theorem applyFrame_stack {s s' : GameState} {a : Action} {es : List Event}
    (hinv : StackInv s) (h : applyFrame s a = some (s', es)) : StackInv s' := by
  obtain ⟨s2, es2, s3, h0, h3, rfl, -⟩ := applyFrame_cases h
  have h5 : StackInv s2 := applyFrame_stack0 hinv h0
  have h4 : StackInv s3 := by
    rcases h3 with rfl | ⟨q, pool, rfl⟩ <;> exact h5
  exact h4.withTriggers _

/-- Applying an answer keeps the stack invariant. A concession ends the game, and the stack is then
no longer asked for a bottom frame. -/
theorem applyAction_stack {s s' : GameState} {a : Action} {es : List Event}
    (hinv : StackInv s) (hl : Legal s a) (h : applyAction s a = some (s', es)) : StackInv s' := by
  by_cases hk : a.kind = .concede
  · obtain ⟨p, hp, -⟩ := (hl.of_concede hk).actor
    rw [applyAction_concede hk hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro hres
    simp at hres
  · rw [applyAction_of_ne hk] at h
    exact applyFrame_stack hinv h

/-- A step of work keeps the stack invariant. -/
theorem microStep_stack0 {s s' : GameState} {es : List Event} (hinv : StackInv s)
    (h : microStep0 s = some (s', es)) : StackInv s' := by
  unfold microStep0 at h
  split at h
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.replace (new := s.turnOrder.map (fun p => Frame.draw p 4) ++
        s.turnOrder.map (fun p => Frame.mulligan p 0) ++ [Frame.beginTurn])
      (fun _ => ⟨Frame.beginTurn, by simp, rfl⟩)
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases beginTurnStep_cases s rest with e | ⟨r, e⟩
    rotate_left
    · rw [e]
      exact fun hres => by simp at hres
    rw [e]
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.replace (new := turnFrames s.nextTurnPlayer)
      (fun _ => ⟨Frame.priority s.nextTurnPlayer, by simp [turnFrames], rfl⟩)
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (channel_sameMeta (s.active.getD ⟨0⟩) s.channelCount s).result
      (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    dsimp only
    split
    · exact hb.pop rfl
    · exact hb.swap rfl [Frame.draw (s.active.getD ⟨0⟩) 1]
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.cleanup, Frame.expireTurn]
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl (expirationFrames s)
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (beginStep_safe s (s.active.getD ⟨0⟩)).same.result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.cleanup, Frame.draw _ _, Frame.scoreHolds]
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (hold_safeP s (s.active.getD ⟨0⟩)).result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.cleanup]
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.cleanup]
  · rename_i q rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i q n rest hp
    split at h
    · rename_i s1 es1 hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_next (drawOne_meta hd).result (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.draw q n]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_next rfl (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.chanceBurnOut q, Frame.draw q (n + 1)]
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    obtain ⟨pre, hpre, -⟩ := resolveFrames_eq s rest
    show BottomOk (resolveFrames s rest)
    rw [hpre]
    exact hb.swap rfl pre
  · rename_i p src env rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i p src env e es rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (runEffect_safe s p src (env.withMight s.mightTable) e es).same.result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl (runEffect s p src (env.withMight s.mightTable) e es).2.1
  · rename_i item rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (finishItem_sameMeta s item).result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl (Frame.cleanup :: afterItem (finishItem s item).1)
  · rename_i rest hp
    have hs' : s' = (cleanupFrame s rest).1 := by
      have := Option.some.inj h
      rw [this]
    subst hs'
    rcases cleanupFrame_cases s rest with ⟨w, e⟩ | ⟨r, hr, e⟩ | ⟨bf, q, e⟩ | e <;>
      rw [e]
    · intro hres
      exact absurd hres (by simp)
    · refine hinv.of_next hr.same.result (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.cleanup]
    · refine hinv.of_next rfl (fun hb => ?_)
      rw [hp] at hb
      exact hb.swap rfl [Frame.showdown bf q 0, Frame.cleanup]
    · refine hinv.of_next rfl (fun hb => ?_)
      rw [hp] at hb
      exact hb.pop rfl
  · rename_i bf att rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    have := hb.swap rfl (s.startCombat bf att ++ combatSteps bf)
    simpa [List.append_assoc] using this
  · rename_i bf att rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (combatCleanup_safe s bf att).same.result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.cleanup]
  · rename_i bf rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.pop rfl
  · rename_i bf rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (combatControl_safeP s bf).result (fun hb => ?_)
    rw [hp] at hb
    have := hb.swap rfl ((combatControl s bf).2.1 ++ [Frame.cleanup])
    simpa using this
  · rename_i bf rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next rfl (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl [Frame.cleanup]
  · rename_i pend rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_next (triggersStep_spec s pend rest).1.same.result (fun hb => ?_)
    rw [hp] at hb
    exact hb.swap rfl (triggersStep s pend rest).2
  · exact absurd h (by simp)

/-- A step of work keeps the stack invariant. -/
theorem microStep_stack {s s' : GameState} {es : List Event} (hinv : StackInv s)
    (h : microStep s = some (s', es)) : StackInv s' := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  exact (microStep_stack0 hinv h0).withTriggers _

/-- The automatic work keeps the stack invariant. -/
theorem advance_stack :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event}, StackInv s →
      advance n s es = .ok (s', es') → StackInv s'
  | 0, s, s', es, es', hinv, h => by
    unfold advance at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hinv
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv
  | n + 1, s, s', es, es', hinv, h => by
    unfold advance at h
    split at h
    · split at h
      · split at h
        · rename_i s1 es1 hm
          exact advance_stack n (microStep_stack hinv hm) h
        · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hinv
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv

/-- A step keeps the stack invariant. -/
theorem step_stack {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hinv : StackInv s) (h : step fuel s a = .ok (s', es)) : StackInv s' := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      exact advance_stack fuel (applyAction_stack hinv hl ha) h
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The frame on top of the stack is not work: the engine has worked through all of it. -/
def TopIdle (s : GameState) : Prop := ∀ f rest, s.pending = f :: rest → f.isWork = false

/-- The automatic work stops at a frame that is not work. -/
theorem advance_idle :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event},
      advance n s es = .ok (s', es') → TopIdle s'
  | 0, s, s', es, es', h => by
    unfold advance at h
    split at h
    · rename_i f rest hp
      split at h
      · exact absurd h (by simp)
      · rename_i hw
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro g r hg
        rw [hp] at hg
        simp only [List.cons.injEq] at hg
        obtain ⟨rfl, -⟩ := hg
        simpa using hw
    · rename_i hp
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      intro g r hg
      rw [hp] at hg
      exact absurd hg (by simp)
  | n + 1, s, s', es, es', h => by
    unfold advance at h
    split at h
    · rename_i f rest hp
      split at h
      · split at h
        · exact advance_idle n h
        · exact absurd h (by simp)
      · rename_i hw
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro g r hg
        rw [hp] at hg
        simp only [List.cons.injEq] at hg
        obtain ⟨rfl, -⟩ := hg
        simpa using hw
    · rename_i hp
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      intro g r hg
      rw [hp] at hg
      exact absurd hg (by simp)

/-- After a step, the frame on top of the stack is not work. -/
theorem step_idle {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (h : step fuel s a = .ok (s', es)) : TopIdle s' := by
  unfold step at h
  split at h
  · split at h
    · exact advance_idle fuel h
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The frames of the setup are all decisions, and the last one is the turn order. -/
theorem startFrames_spec (n : Nat) :
    (∀ f ∈ startFrames n, f.isWork = false) ∧
      (startFrames n).getLast? = some Frame.chanceTurnOrder := by
  refine ⟨fun f hf => ?_, ?_⟩
  · simp only [startFrames, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hf
    rcases hf with (⟨i, -, rfl | rfl⟩ | ⟨i, -, rfl⟩) | rfl <;> rfl
  · simp [startFrames, List.getLast?_append]

/-- **The stack invariant and the idle top hold at the start.** -/
theorem GameState.initial_stack {db : CardDB} {config : GameConfig} {decks : List Deck}
    {s : GameState} (h : GameState.initial db config decks = some s) :
    StackInv s ∧ TopIdle s := by
  unfold GameState.initial at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    obtain ⟨hw, hl⟩ := startFrames_spec config.mode.players
    refine ⟨fun _ => ⟨Frame.chanceTurnOrder, hl, rfl⟩, fun f rest hp => ?_⟩
    exact hw f (by
      change startFrames config.mode.players = f :: rest at hp
      rw [hp]; exact List.mem_cons_self)
  · exact absurd h (by simp)

/-- **The stack invariant and the idle top hold at the start of a Limited game.** -/
theorem GameState.initialLimited_stack {db : CardDB} {env : LegalityEnv} {config : GameConfig}
    {decks : List LimitedDeck} {s : GameState}
    (h : GameState.initialLimited db env config decks = some s) :
    StackInv s ∧ TopIdle s := by
  unfold GameState.initialLimited at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    obtain ⟨hw, hl⟩ := startFrames_spec config.mode.players
    refine ⟨fun _ => ⟨Frame.chanceTurnOrder, hl, rfl⟩, fun f rest hp => ?_⟩
    exact hw f (by
      change startFrames config.mode.players = f :: rest at hp
      rw [hp]; exact List.mem_cons_self)
  · exact absurd h (by simp)

/-- Every reachable state satisfies the stack invariant and has an idle top. -/
theorem Reachable.stack {s : GameState} (h : Reachable s) : StackInv s ∧ TopIdle s := by
  induction h with
  | init h =>
    cases h with
    | core h => exact GameState.initial_stack h
    | limited h => exact GameState.initialLimited_stack h
  | next hs h ih => exact ⟨step_stack ih.1 h, step_idle h⟩

/-- Frames whose answer is a chance decision: they are not listed in `legalActions` (design.md
§6.4). -/
def Frame.isChance : Frame → Bool
  | .chanceShuffle _ => true
  | .chanceBattlefield _ => true
  | .chanceTurnOrder => true
  | .chanceRecycle _ => true
  | .chanceBurnOut _ => true
  | .chancePredict .. => true
  | _ => false

/-- In a game of at least two players, there is a player other than `p`. -/
theorem exists_other_player {n : Nat} (hn : 2 ≤ n) (p : PlayerId) :
    ∃ o, o ∈ (allPlayers n).filter (fun o => o ≠ p) := by
  by_cases hp : p = ⟨0⟩
  · refine ⟨⟨1⟩, ?_⟩
    simp only [List.mem_filter, mem_allPlayers, decide_eq_true_eq]
    refine ⟨by omega, fun e => ?_⟩
    rw [hp] at e
    cases e
  · refine ⟨⟨0⟩, ?_⟩
    simp only [List.mem_filter, mem_allPlayers, decide_eq_true_eq]
    exact ⟨by omega, fun e => hp e.symm⟩

/-- **I5, progress, for a game of at least two players.** In a reachable game of at least two
players that is not over, either there is an answer other than a concession in `legalActions`, or
the top frame asks for a chance decision. The decisions that are split into steps (the mulligan, the
choice of the opponent of a Burn Out, the Main Phase) always have such an answer, so no choice leads
into a dead end. `Reachable.progress` in `Invariant/Setup.lean` drops the assumption on the players.
-/
theorem Reachable.progress_of_players {s : GameState} (h : Reachable s)
    (hres : s.result = none) (hv : 2 ≤ s.playerCount) :
    (∃ a ∈ legalActions s, a.kind ≠ .concede) ∨
      ∃ f rest, s.pending = f :: rest ∧ f.isChance = true := by
  obtain ⟨hs, ht⟩ := h.stack
  have hb := hs hres
  obtain ⟨f, rest, hp⟩ : ∃ f rest, s.pending = f :: rest := by
    cases hq : s.pending with
    | nil => exact absurd hq hb.ne_nil
    | cons f rest => exact ⟨f, rest, rfl⟩
  have hw := ht f rest hp
  have hla : legalActions s = legalFrameActions s ++ concedeActions s := by
    simp [legalActions, hres]
  cases f with
  | priority p =>
    left
    refine ⟨⟨.player p, .pass⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp [legalFrameActions, hp]
  | mulligan p n =>
    left
    refine ⟨⟨.player p, .mulliganDone⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp [legalFrameActions, hp]
  | discard p n =>
    left
    by_cases hz : s.zone (.player p .hand) = [] ∨ n = 0
    · refine ⟨⟨.player p, .discardDone⟩, ?_, by simp⟩
      rw [hla]
      apply List.mem_append_left
      simp [legalFrameActions, hp, hz]
    · obtain ⟨c, hc⟩ : ∃ c, c ∈ s.zone (.player p .hand) := by
        cases hh : s.zone (.player p .hand) with
        | nil => exact absurd (Or.inl hh) hz
        | cons c cs => exact ⟨c, by simp⟩
      refine ⟨⟨.player p, .discardPick c⟩, ?_, by simp⟩
      rw [hla]
      apply List.mem_append_left
      simp only [legalFrameActions, hp, hz, ↓reduceIte]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
  | mayDo p src env e es =>
    left
    refine ⟨⟨.player p, .decide true⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp [legalFrameActions, hp]
  | eitherDo p src env a b es =>
    left
    by_cases hy : eitherOk s p src env a b true = true
    · refine ⟨⟨.player p, .decide true⟩, ?_, by simp⟩
      rw [hla]
      apply List.mem_append_left
      simp [legalFrameActions, hp, hy]
    · have hn : eitherOk s p src env a b false = true := by
        unfold eitherOk at hy ⊢
        cases hva : a.viable s p src env <;> cases hvb : b.viable s p src env <;>
          simp_all
      refine ⟨⟨.player p, .decide false⟩, ?_, by simp⟩
      rw [hla]
      apply List.mem_append_left
      simp [legalFrameActions, hp, hn]
  | pickDo p src env c more e es =>
    left
    refine ⟨⟨.player p, .choose c⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp [legalFrameActions, hp]
  | nameCard p src env card more es =>
    left
    refine ⟨⟨.player p, .nameCard card⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp [legalFrameActions, hp]
  | predict p n c cs top bottom =>
    left
    refine ⟨⟨.player p, .predictPick c false⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp [legalFrameActions, hp]
  | chooseBurnOut p =>
    left
    obtain ⟨o, ho⟩ := exists_other_player hv p
    refine ⟨⟨.player p, .burnOutTarget o⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp only [legalFrameActions, hp, List.mem_map]
    exact ⟨o, ho, rfl⟩
  | chanceShuffle z => right; exact ⟨_, rest, hp, rfl⟩
  | chanceBattlefield p => right; exact ⟨_, rest, hp, rfl⟩
  | chanceTurnOrder => right; exact ⟨_, rest, hp, rfl⟩
  | chanceRecycle p => right; exact ⟨_, rest, hp, rfl⟩
  | chanceBurnOut p => right; exact ⟨_, rest, hp, rfl⟩
  | chancePredict p n top bottom => right; exact ⟨_, rest, hp, rfl⟩
  | setupHands => exact absurd hw (by simp [Frame.isWork])
  | draw p n => exact absurd hw (by simp [Frame.isWork])
  | beginTurn => exact absurd hw (by simp [Frame.isWork])
  | phase ph => exact absurd hw (by simp [Frame.isWork])
  | scoreHolds => exact absurd hw (by simp [Frame.isWork])
  | expireTurn => exact absurd hw (by simp [Frame.isWork])
  | chainPass p n =>
    left
    refine ⟨⟨.player p, .pass⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp [legalFrameActions, hp]
  | resolveChain => exact absurd hw (by simp [Frame.isWork])
  | run p src env todo => exact absurd hw (by simp [Frame.isWork])
  | finishSpell item => exact absurd hw (by simp [Frame.isWork])
  | triggers pend => exact absurd hw (by simp [Frame.isWork])
  | cleanup => exact absurd hw (by simp [Frame.isWork])
  | combatDamage bf att => exact absurd hw (by simp [Frame.isWork])
  | combatResolve bf att => exact absurd hw (by simp [Frame.isWork])
  | combatResult bf => exact absurd hw (by simp [Frame.isWork])
  | combatControl bf => exact absurd hw (by simp [Frame.isWork])
  | combatFinish bf => exact absurd hw (by simp [Frame.isWork])
  | assign bf att side acc done =>
    left
    obtain ⟨a, ha, hk⟩ := assign_exists s bf side acc
    refine ⟨a, ?_, hk⟩
    rw [hla]
    apply List.mem_append_left
    simp only [legalFrameActions, hp]
    exact ha
  | showdown bf q n =>
    left
    refine ⟨⟨.player q, .pass⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp [legalFrameActions, hp]
  | triggerOrder p t more others =>
    left
    obtain ⟨ts, payment, hts⟩ := trigLegal_exists s t
    refine ⟨⟨.player p, .putTrigger 0 ts payment⟩, ?_, by simp⟩
    rw [hla]
    apply List.mem_append_left
    simp only [legalFrameActions, hp, mem_legalPuts]
    exact ⟨0, ts, payment, rfl, by simpa using hts⟩

/-- What a chance frame needs for a chance answer to exist: the zone to shuffle is a zone of the
game, and a player has a Battlefield to pick. The other chance frames need nothing. -/
def Frame.chanceReady (s : GameState) : Frame → Prop
  | .chanceShuffle z => z.Valid s.playerCount
  | .chanceBattlefield p => 0 < (s.zone (.player p .outOfGame)).length
  | _ => True

/-- **A chance decision has a legal answer** when the frame has what it needs: an arrangement of
what is there, or the first Battlefield. That the two needs are met in every reachable game is
proved in `Invariant/Setup.lean` (`Reachable.exists_legal`). -/
theorem chance_answer_exists {s : GameState} {f : Frame} {rest : List Frame}
    (hres : s.result = none) (hp : s.pending = f :: rest) (hc : f.isChance = true)
    (hr : f.chanceReady s) : ∃ a, a.actor = .chance ∧ Legal s a := by
  cases f with
  | chanceShuffle z =>
    refine ⟨⟨.chance, .arrange (s.zone z)⟩, rfl, hres, Or.inl ?_⟩
    unfold LegalFrame
    rw [hp]
    exact ⟨rfl, hr, List.Perm.refl _⟩
  | chanceBattlefield p =>
    refine ⟨⟨.chance, .pick 0⟩, rfl, hres, Or.inl ?_⟩
    unfold LegalFrame
    rw [hp]
    exact ⟨rfl, hr⟩
  | chanceTurnOrder =>
    refine ⟨⟨.chance, .arrangePlayers (allPlayers s.playerCount)⟩, rfl, hres, Or.inl ?_⟩
    unfold LegalFrame
    rw [hp]
    exact ⟨rfl, List.Perm.refl _⟩
  | chanceRecycle p =>
    refine ⟨⟨.chance, .arrange (s.zone (.player p .setAside))⟩, rfl, hres, Or.inl ?_⟩
    unfold LegalFrame
    rw [hp]
    exact ⟨rfl, List.Perm.refl _⟩
  | chanceBurnOut p =>
    refine ⟨⟨.chance, .arrange (s.zone (.player p .trash))⟩, rfl, hres, Or.inl ?_⟩
    unfold LegalFrame
    rw [hp]
    exact ⟨rfl, List.Perm.refl _⟩
  | chancePredict p n top bottom =>
    refine ⟨⟨.chance, .arrange bottom⟩, rfl, hres, Or.inl ?_⟩
    unfold LegalFrame
    rw [hp]
    exact ⟨rfl, List.Perm.refl _⟩
  | mulligan p n => exact absurd hc (by simp [Frame.isChance])
  | discard p n => exact absurd hc (by simp [Frame.isChance])
  | mayDo p src env e es => exact absurd hc (by simp [Frame.isChance])
  | eitherDo p src env a b es => exact absurd hc (by simp [Frame.isChance])
  | pickDo p src env c more e es => exact absurd hc (by simp [Frame.isChance])
  | nameCard p src env card more es => exact absurd hc (by simp [Frame.isChance])
  | predict p n c cs top bottom => exact absurd hc (by simp [Frame.isChance])
  | chooseBurnOut p => exact absurd hc (by simp [Frame.isChance])
  | setupHands => exact absurd hc (by simp [Frame.isChance])
  | draw p n => exact absurd hc (by simp [Frame.isChance])
  | beginTurn => exact absurd hc (by simp [Frame.isChance])
  | phase ph => exact absurd hc (by simp [Frame.isChance])
  | scoreHolds => exact absurd hc (by simp [Frame.isChance])
  | expireTurn => exact absurd hc (by simp [Frame.isChance])
  | priority p => exact absurd hc (by simp [Frame.isChance])
  | chainPass p n => exact absurd hc (by simp [Frame.isChance])
  | resolveChain => exact absurd hc (by simp [Frame.isChance])
  | run p src env todo => exact absurd hc (by simp [Frame.isChance])
  | finishSpell item => exact absurd hc (by simp [Frame.isChance])
  | triggers pend => exact absurd hc (by simp [Frame.isChance])
  | cleanup => exact absurd hc (by simp [Frame.isChance])
  | combatDamage bf att => exact absurd hc (by simp [Frame.isChance])
  | combatResolve bf att => exact absurd hc (by simp [Frame.isChance])
  | combatResult bf => exact absurd hc (by simp [Frame.isChance])
  | combatControl bf => exact absurd hc (by simp [Frame.isChance])
  | combatFinish bf => exact absurd hc (by simp [Frame.isChance])
  | assign bf att side acc done => exact absurd hc (by simp [Frame.isChance])
  | showdown bf q n => exact absurd hc (by simp [Frame.isChance])
  | triggerOrder p t more others => exact absurd hc (by simp [Frame.isChance])

end Riftbound

end
