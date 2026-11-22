module

public import Riftbound.Rules.Objects
public import Riftbound.Rules.Owner
public import Riftbound.Rules.Actions.Channel
public import Riftbound.State.Pool

/-!
# Rune abilities

Every Basic Rune has two abilities, both of which add to the Rune Pool (CR 164.2): exhaust it for
one Energy, or recycle it for one Power of its domain. An ability that adds a resource resolves at
once (CR 430.2); the Chain it should go through arrives with the playing of cards (milestone M4).
-/

@[expose] public section

namespace Riftbound

namespace GameState

/-- Reading a Pool just written gives what was written. -/
theorem poolOf_setPool_self (s : GameState) (p : PlayerId) (pool : RunePool) :
    (s.setPool p pool).poolOf p = pool := by
  simp [poolOf, setPool]

/-- Writing a Pool leaves the other players' Pools alone. -/
theorem poolOf_setPool_ne (s : GameState) {p q : PlayerId} (h : q ≠ p) (pool : RunePool) :
    (s.setPool p pool).poolOf q = s.poolOf q := by
  have hn : p.n ≠ q.n := fun e => h (by cases p; cases q; simp_all)
  simp [poolOf, setPool, Std.ExtTreeMap.getD_insert, hn]

end GameState

/-- The player can use the ability of the Rune: it is a Rune of theirs, and an Exhaust needs it
ready (CR 164.2, 415). -/
def runeUsable (s : GameState) (p : PlayerId) (c : ObjId) (ab : RuneAbility) : Bool :=
  match s.obj? c with
  | some o => o.owner == p && o.runeDomain.isSome && (ab == .recycle || !o.exhausted)
  | none => false

/-- Use a Basic Rune's ability (CR 164.2): exhaust it for one Energy, or recycle it to the Rune
Deck for one Power of its domain. The resource is added at once (CR 430.2). -/
def applyRune (s : GameState) (p : PlayerId) (c : ObjId) (ab : RuneAbility) :
    Option (GameState × List Event) :=
  match s.obj? c with
  | some o =>
    match o.runeDomain, ab with
    | some _, .exhaust => some ((s.exhaustObj c).setPool p ((s.poolOf p).addEnergy 1), [])
    | some d, .recycle =>
      (moveObj s c (.player p .runeDeck) .bottom).map
        (fun r => (r.1.setPool p ((r.1.poolOf p).addPower d 1),
          [Event.moved c r.2 (.player p .runeDeck)]))
    | none, _ => none
  | none => none

/-- A rune that can be used is an object of the player with a domain. -/
theorem runeUsable_spec {s : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    (h : runeUsable s p c ab = true) :
    ∃ o d, s.obj? c = some o ∧ o.owner = p ∧ o.runeDomain = some d ∧
      (ab = .exhaust → o.exhausted = false) := by
  unfold runeUsable at h
  cases ho : s.obj? c with
  | none => rw [ho] at h; simp at h
  | some o =>
    rw [ho] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
    obtain ⟨⟨h1, d, h2⟩, h3⟩ := h
    refine ⟨o, d, rfl, h1, h2, fun hab => ?_⟩
    subst hab
    simpa using h3

/-- Using a Rune keeps the game well formed. -/
theorem applyRune_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (hwf : s.WF) (h : applyRune s p c ab = some (s', es)) : s'.WF := by
  unfold applyRune at h
  split at h
  · rename_i o ho
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact (GameState.wf_exhaustObj hwf c).congr rfl rfl rfl rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact (moveObj_wf hwf hm).congr rfl rfl rfl rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Using a Rune keeps the physical cards. -/
theorem applyRune_physIds {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (hwf : s.WF) (h : applyRune s p c ab = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  unfold applyRune at h
  split at h
  · rename_i o ho
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      rw [← h1]
      have := GameState.physIds_exhaustObj s c
      exact this ▸ List.Perm.refl _
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      have hp := moveObj_physIds hwf hm
      exact hp
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Using a Rune keeps `OwnerOk`. -/
theorem applyRune_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (hwf : s.WF) (hown : s.OwnerOk) (h : applyRune s p c ab = some (s', es)) :
    s'.OwnerOk := by
  unfold applyRune at h
  split at h
  · rename_i o ho
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact (GameState.ownerOk_exhaustObj hown c).congr rfl rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact (moveObj_ownerOk hwf hown hm).congr rfl rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Using a Rune changes nothing of the stack, the turn order, the phase, the result or the
rules. -/
theorem applyRune_meta {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (h : applyRune s p c ab = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending := by
  unfold applyRune at h
  split at h
  · rename_i o ho
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      obtain ⟨src, d, hs⟩ := moveObj_spec hm
      exact ⟨hs.other.config, hs.other.turnOrder, hs.other.phase, hs.other.result,
        hs.other.pending⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A Rune on the Base that the player can use can be used. -/
theorem applyRune_isSome {s : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    (hwf : s.WF) (hc : c ∈ s.zone (.player p .base)) (hu : runeUsable s p c ab = true) :
    ∃ r, applyRune s p c ab = some r := by
  obtain ⟨o, d, ho, howner, hd, -⟩ := runeUsable_spec hu
  unfold applyRune
  rw [ho]
  simp only [hd]
  cases ab with
  | exhaust => exact ⟨_, rfl⟩
  | recycle =>
    have hpn : p.n < s.playerCount :=
      Zone.lt_of_valid_player (GameState.zone_valid_of_mem hwf hc)
    obtain ⟨r, hr⟩ := moveObj_isSome hwf hc (.player p .runeDeck) .bottom (fun o' ho' => by
      have : o' = o := Option.some.inj (ho'.symm.trans ho)
      subst this
      rw [howner]
      simp only [Zone.normalize, Zone.isBoard, Bool.false_eq_true, ite_false]
      exact ⟨Zone.valid_player hpn _, by simp⟩)
    simp only [hr, Option.map_some]
    exact ⟨_, rfl⟩

/-- **Exhausting a Rune adds exactly one Energy** (CR 164.2, 430). -/
theorem applyRune_exhaust_pool {s s' : GameState} {p : PlayerId} {c : ObjId} {es : List Event}
    (h : applyRune s p c .exhaust = some (s', es)) :
    s'.poolOf p = (s.poolOf p).addEnergy 1 ∧ ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  unfold applyRune at h
  cases ho : s.obj? c with
  | none => simp [ho] at h
  | some o =>
    cases hd : o.runeDomain with
    | none => simp [ho, hd] at h
    | some d =>
      simp only [ho, hd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨GameState.poolOf_setPool_self _ _ _,
        fun q hq => GameState.poolOf_setPool_ne _ hq _⟩

/-- **Recycling a Rune adds exactly one Power of its domain** (CR 164.2, 430). -/
theorem applyRune_recycle_pool {s s' : GameState} {p : PlayerId} {c : ObjId} {es : List Event}
    (h : applyRune s p c .recycle = some (s', es)) :
    ∃ d, s'.poolOf p = (s.poolOf p).addPower d 1 ∧
      ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  unfold applyRune at h
  cases ho : s.obj? c with
  | none => simp [ho] at h
  | some o =>
    cases hd : o.runeDomain with
    | none => simp [ho, hd] at h
    | some d =>
      simp only [ho, hd, Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      obtain ⟨src, dd, hs⟩ := moveObj_spec hm
      have hpools : s2.pools = s.pools := hs.pools
      refine ⟨d, ?_, fun q hq => ?_⟩
      · rw [GameState.poolOf_setPool_self]
        simp [GameState.poolOf, hpools]
      · rw [GameState.poolOf_setPool_ne _ hq]
        simp [GameState.poolOf, hpools]

/-- Using a Rune leaves every hand alone. -/
theorem applyRune_hand {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (hwf : s.WF) (hc : c ∈ s.zone (.player p .base))
    (hu : runeUsable s p c ab = true) (h : applyRune s p c ab = some (s', es)) (r : PlayerId) :
    s'.zone (.player r .hand) = s.zone (.player r .hand) := by
  obtain ⟨o, d, ho, howner, hd, -⟩ := runeUsable_spec hu
  unfold applyRune at h
  rw [ho] at h
  simp only [hd] at h
  cases ab with
  | exhaust =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | recycle =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have := moveObj_zone_unchanged hwf hc hm (z := .player r .hand) (by simp)
      (fun o' ho' => by
        have : o' = o := Option.some.inj (ho'.symm.trans ho)
        subst this
        rw [howner]
        simp [Zone.normalize, Zone.isBoard])
    exact this

/-- **Recycling a Rune keeps the number of Runes on the Base and in the Rune Deck** (I8) (CR 164.2):
one leaves the Base and one enters the Rune Deck. -/
theorem applyRune_recycle_zones {s s' : GameState} {p : PlayerId} {c : ObjId} {es : List Event}
    (hwf : s.WF) (hc : c ∈ s.zone (.player p .base)) (hu : runeUsable s p c .recycle = true)
    (h : applyRune s p c .recycle = some (s', es)) :
    (s'.zone (.player p .base)).length + 1 = (s.zone (.player p .base)).length ∧
      (s'.zone (.player p .runeDeck)).length = (s.zone (.player p .runeDeck)).length + 1 := by
  obtain ⟨o, d, ho, howner, hd, -⟩ := runeUsable_spec hu
  unfold applyRune at h
  rw [ho] at h
  simp only [hd, Option.map_eq_some_iff] at h
  obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, -⟩ := hr
  obtain ⟨src, dd, hs, o', ho', hdd⟩ := moveObj_spec_dst hm
  have hsrc : src = .player p .base :=
    Option.some.inj (hs.locate.symm.trans
      (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hc) hc))
  have hoo : o' = o := Option.some.inj (ho'.symm.trans ho)
  have hd2 : dd = .player p .runeDeck := by
    rw [hdd, hoo, howner]
    simp [Zone.normalize, Zone.isBoard]
  have h1 := hs.zone_src
  have h2 := hs.zone_dst
  rw [hsrc] at h1
  rw [hd2] at h2
  refine ⟨?_, ?_⟩
  · show (s2.zone (.player p .base)).length + 1 = _
    rw [h1, List.length_erase_of_mem hc]
    have : 0 < (s.zone (.player p .base)).length := List.length_pos_of_mem hc
    omega
  · show (s2.zone (.player p .runeDeck)).length = _
    rw [h2, (Pos.insert_perm _ _ _).length_eq]
    simp

/-- **Channeling a Rune keeps the number of Runes on the Base and in the Rune Deck** (I8) (CR 431):
one leaves the Rune Deck and one enters the Base. -/
theorem channelOne_zones {s s' : GameState} {p : PlayerId} {es : List Event} (hwf : s.WF)
    (h : channelOne s p = some (s', es)) :
    (s'.zone (.player p .runeDeck)).length + 1 = (s.zone (.player p .runeDeck)).length ∧
      (s'.zone (.player p .base)).length = (s.zone (.player p .base)).length + 1 := by
  unfold channelOne at h
  split at h
  · exact absurd h (by simp)
  · rename_i top rest hz
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have htop : top ∈ s.zone (.player p .runeDeck) := by rw [hz]; exact List.mem_cons_self
    obtain ⟨src, d, hs, o, ho, hd⟩ := moveObj_spec_dst hm
    have hsrc : src = .player p .runeDeck :=
      Option.some.inj (hs.locate.symm.trans
        (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf htop) htop))
    have hd2 : d = .player p .base := by
      rw [hd]
      simp [Zone.normalize, Zone.isBoard]
    have h1 := hs.zone_src
    have h2 := hs.zone_dst
    rw [hsrc] at h1
    rw [hd2] at h2
    refine ⟨?_, ?_⟩
    · show (s2.zone (.player p .runeDeck)).length + 1 = _
      rw [h1, List.length_erase_of_mem htop]
      have : 0 < (s.zone (.player p .runeDeck)).length := List.length_pos_of_mem htop
      omega
    · show (s2.zone (.player p .base)).length = _
      rw [h2, (Pos.insert_perm _ _ _).length_eq]
      simp

end Riftbound

end
