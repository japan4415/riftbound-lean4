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

/-- Build a Burn Out decision from the remaining opponents. The frame is nonempty by construction
and a later departure refreshes it before the next answer (CR 432.2.c, 651.3). -/
def GameState.survivingBurnOutDecision (s : GameState) (p : PlayerId) : List Frame :=
  match s.participatingSeats.filter (fun q => !s.config.mode.sameSide p q) with
  | [] => []
  | first :: more => [.chooseBurnOutAmong p first more]

/-- Every candidate in a refreshed Burn Out decision is a participating opponent. -/
theorem GameState.survivingBurnOutDecision_target {s : GameState} {p first opp : PlayerId}
    {more : List PlayerId}
    (decision : .chooseBurnOutAmong p first more ∈ s.survivingBurnOutDecision p)
    (target : opp ∈ first :: more) : s.participates opp = true ∧
      s.config.mode.sameSide p opp = false := by
  unfold GameState.survivingBurnOutDecision at decision
  split at decision
  · simp at decision
  · rename_i first' more' candidates
    simp only [List.mem_singleton, Frame.chooseBurnOutAmong.injEq, true_and] at decision
    obtain ⟨head, tail⟩ := decision
    rw [head, tail, ← candidates] at target
    obtain ⟨live, opposing⟩ := List.mem_filter.mp target
    exact ⟨(List.mem_filter.mp live).2, by simpa only [Bool.not_eq_true'] using opposing⟩

/-- Preserve the ordinary Burn Out decision when every registered seat is still playing. -/
def GameState.burnOutDecision (s : GameState) (p : PlayerId) : List Frame :=
  if s.departures.seats.isEmpty then [.chooseBurnOut p] else s.survivingBurnOutDecision p

/-- The Burn Out instruction queues either the ordinary prompt, a prompt with remaining
opponents, or no prompt if there is nobody to choose. -/
theorem GameState.burnOutDecision_cases (s : GameState) (p : PlayerId) :
    s.burnOutDecision p = [.chooseBurnOut p] ∨ s.burnOutDecision p = [] ∨
      ∃ first more, s.burnOutDecision p = [.chooseBurnOutAmong p first more] := by
  unfold GameState.burnOutDecision
  split
  · exact Or.inl rfl
  · unfold GameState.survivingBurnOutDecision
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- Burn Out of player `p`: recycle the Trash in the order `order`, which must be an
arrangement of the Trash, then `opp`, a participating opponent of `p`, gains 1 point (CR 432.2). -/
def burnOut (s : GameState) (p : PlayerId) (order : List ObjId) (opp : PlayerId) :
    Option (GameState × List Event) :=
  if order.Perm (s.zone (.player p .trash)) ∧ s.config.mode.sameSide p opp = false ∧
      s.participates opp = true then
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
