module

public import Riftbound.Rules.Actions.Recycle

/-!
# Burn Out

Trying to draw from an empty Main Deck makes the player burn out (CR 432): the Trash is put into the
Main Deck in a random order, and one opponent of the player's choice gains 1 point. Both
decisions come from outside, as arguments: the order is a chance decision (CR 432.2.b) and the
opponent a choice (CR 432.2.c). Burn Out is a replacement of the draw (CR 432.5); that stage
arrives with the engine (milestone M2b) and the ability system (M6).
-/

@[expose] public section

namespace Riftbound

/-- Give a player points. -/
def GameState.gainPoints (s : GameState) (p : PlayerId) (n : Nat) : GameState :=
  { s with points := s.points.insert (s.config.mode.scoringSeat p).n (s.pointsOf p + n) }

/-- Burn Out of player `p`: recycle the Trash in the order `order`, which must be an
arrangement of the Trash, then `opp`, an opponent of `p`, gains 1 point (CR 432.2). `none` when the
order is not an arrangement of the Trash or `opp` is not an opponent. -/
def burnOut (s : GameState) (p : PlayerId) (order : List ObjId) (opp : PlayerId) :
    Option (GameState × List Event) :=
  if order.Perm (s.zone (.player p .trash)) ∧ s.config.mode.sameSide p opp = false ∧
      opp.n < s.playerCount then
    (recycleAll p s order).map
      (fun s1 => (s1.gainPoints opp 1, [Event.burnedOut p, Event.pointsGained opp 1]))
  else none

/-- A player has the points they had, plus the gain. -/
theorem GameState.pointsOf_gainPoints_self (s : GameState) (p : PlayerId) (n : Nat) :
    (s.gainPoints p n).pointsOf p = s.pointsOf p + n := by
  simp [gainPoints, pointsOf]

/-- A teammate sees the same gain. -/
theorem GameState.pointsOf_gainPoints_side (s : GameState) {p q : PlayerId}
    (h : s.config.mode.sameSide p q = true) (n : Nat) :
    (s.gainPoints p n).pointsOf q = s.pointsOf p + n := by
  have hs := of_decide_eq_true h
  simp [gainPoints, pointsOf, hs]

/-- A player on another side keeps their points. -/
theorem GameState.pointsOf_gainPoints_ne (s : GameState) {p q : PlayerId}
    (h : s.config.mode.sameSide p q = false) (n : Nat) :
    (s.gainPoints p n).pointsOf q = s.pointsOf q := by
  have hs := of_decide_eq_false h
  have h' : (s.config.mode.scoringSeat p).n ≠ (s.config.mode.scoringSeat q).n := by
    intro e
    have seatEq (a b : PlayerId) (hn : a.n = b.n) : a = b := by
      cases a
      cases b
      exact congrArg PlayerId.mk hn
    exact hs (seatEq _ _ e)
  simp [gainPoints, pointsOf, Std.ExtTreeMap.getD_insert, h']

/-- Gaining points keeps the game well formed: points are not part of `WF`. -/
theorem GameState.wf_gainPoints {s : GameState} (h : s.WF) (p : PlayerId) (n : Nat) :
    (s.gainPoints p n).WF := by
  exact ⟨h.nodup, h.table_of_zone, h.zone_of_table, h.lt_nextId, h.zones_valid⟩

/-- Burn Out keeps the game well formed. -/
theorem burnOut_wf {s s' : GameState} {p : PlayerId} {order : List ObjId} {opp : PlayerId}
    {es : List Event} (hwf : s.WF) (h : burnOut s p order opp = some (s', es)) : s'.WF := by
  unfold burnOut at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, hs1, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact GameState.wf_gainPoints (recycleAll_wf p order hwf hs1) opp 1
  · exact absurd h (by simp)

/-- **I1** (Burn Out). Burn Out keeps the physical cards. -/
theorem burnOut_physIds {s s' : GameState} {p : PlayerId} {order : List ObjId} {opp : PlayerId}
    {es : List Event} (hwf : s.WF) (h : burnOut s p order opp = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  unfold burnOut at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, hs1, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    rw [show (s1.gainPoints opp 1).physIds = s1.physIds from rfl]
    exact recycleAll_physIds p order hwf hs1
  · exact absurd h (by simp)

/-- Burn Out gives one point to the chosen opposing side (CR 432.2.c, 491.8.d). -/
theorem burnOut_points {s s' : GameState} {p : PlayerId} {order : List ObjId} {opp : PlayerId}
    {es : List Event} (h : burnOut s p order opp = some (s', es)) :
    s.config.mode.sameSide p opp = false ∧ s'.pointsOf opp = s.pointsOf opp + 1 ∧
      ∀ q, s.config.mode.sameSide opp q = false → s'.pointsOf q = s.pointsOf q := by
  unfold burnOut at h
  split at h
  · rename_i hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, hs1, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hp := recycleAll_points p order hs1
    have hcfg := (recycleAll_meta p order hs1).config
    have hpo : ∀ q, s1.pointsOf q = s.pointsOf q := fun q => by simp [GameState.pointsOf, hp, hcfg]
    refine ⟨hc.2.1, ?_, fun q hq => ?_⟩
    · rw [GameState.pointsOf_gainPoints_self, hpo]
    · rw [GameState.pointsOf_gainPoints_ne s1 (q := q) (p := opp) (by simpa [hcfg] using hq), hpo]
  · exact absurd h (by simp)

end Riftbound

end
