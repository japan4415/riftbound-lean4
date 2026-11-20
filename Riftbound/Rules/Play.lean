module

public import Riftbound.Rules.Resources
public import Riftbound.Rules.Pay

/-!
# Playing a card

A player with priority in their Main Phase can play a Unit or a Gear from their hand: the cost is
paid from the Rune Pool, and the card goes to the Base (CR 349-359). A Unit enters exhausted
(CR 359). Units and Gear resolve at once when they are finalized (CR 337.2), so for them the Chain
holds the card for no time at all and nothing can be played in answer; the Chain itself comes with
Spells (milestone M4).

The definition of the card is read from `GameState.cards`. The game's cards are fixed, so the
engine does not know any card by name (design.md §3, P3).
-/

@[expose] public section

namespace Riftbound

namespace GameState

/-- The definition of the card an object is. -/
def cardDef? (s : GameState) (c : ObjId) : Option CardDef :=
  match s.obj? c with
  | some o =>
    match o.kind with
    | .card _ id => s.cards.find? id
    | .token id => s.cards.find? id
    | .chainAbility _ => none
  | none => none

end GameState

/-- The player can play the object with the payment: it is the player's card, a Unit or a Gear, in
the Main Phase, and the payment pays its cost and the Rune Pool holds it (CR 349, 356, 357). The
card must also be in the hand, which `Legal` states apart. -/
def playable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment) : Bool :=
  s.phase == .main &&
    match s.obj? c, s.cardDef? c with
    | some o, some d =>
      o.owner == p && (d.hasType .unit || d.hasType .gear) &&
        (match d.cost with
          | some cost => cost.paidBy d.domains pay
          | none => false) &&
        ((s.poolOf p).spend pay).isSome
    | _, _ => false

/-- Play a card (CR 349-359): pay, and put it on the Base, exhausted if it is a Unit (CR 359). -/
def applyPlay (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment) :
    Option (GameState × List Event) :=
  match s.cardDef? c, (s.poolOf p).spend pay with
  | some d, some pool =>
    (moveObj s c (.player p .base)).map (fun r =>
      let s1 := r.1.setPool p pool
      ((if d.hasType .unit then s1.exhaustObj r.2 else s1),
        [Event.moved c r.2 (.player p .base)]))
  | _, _ => none

/-- What a playable card is: the game is in the Main Phase, and the card is the player's, a Unit or
a Gear, with a cost that the payment pays and the Pool covers (CR 349, 356, 357). -/
theorem playable_spec {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    (h : playable s p c pay = true) :
    ∃ o d cost pool, s.phase = .main ∧ s.obj? c = some o ∧ s.cardDef? c = some d ∧
      o.owner = p ∧ (d.hasType .unit = true ∨ d.hasType .gear = true) ∧ d.cost = some cost ∧
      cost.paidBy d.domains pay = true ∧ (s.poolOf p).spend pay = some pool := by
  unfold playable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hph, hrest⟩ := h
  cases ho : s.obj? c with
  | none => rw [ho] at hrest; simp at hrest
  | some o =>
    cases hd : s.cardDef? c with
    | none => rw [ho, hd] at hrest; simp at hrest
    | some d =>
      rw [ho, hd] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hrest
      obtain ⟨⟨⟨howner, hty⟩, hcost⟩, hspend⟩ := hrest
      cases hc : d.cost with
      | none => rw [hc] at hcost; simp at hcost
      | some cost =>
        rw [hc] at hcost
        obtain ⟨pool, hpool⟩ := Option.isSome_iff_exists.mp hspend
        exact ⟨o, d, cost, pool, hph, rfl, rfl, howner, hty, hc, hcost, hpool⟩

/-- The shape of a card being played: its definition, the Pool after paying, and the move to the
Base. -/
theorem applyPlay_cases {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    ∃ d pool s2 id', s.cardDef? c = some d ∧ (s.poolOf p).spend pay = some pool ∧
      moveObj s c (.player p .base) = some (s2, id') ∧
      s' = (if d.hasType .unit = true then (s2.setPool p pool).exhaustObj id'
        else s2.setPool p pool) := by
  unfold applyPlay at h
  cases hd : s.cardDef? c with
  | none => simp [hd] at h
  | some d =>
    cases hs : (s.poolOf p).spend pay with
    | none => simp [hd, hs] at h
    | some pool =>
      simp only [hd, hs, Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      exact ⟨d, pool, s2, id', rfl, rfl, hm, hr.1.symm⟩

/-- Playing a card keeps the game well formed. -/
theorem applyPlay_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (h : applyPlay s p c pay = some (s', es)) : s'.WF := by
  obtain ⟨d, pool, s2, id', -, -, hm, rfl⟩ := applyPlay_cases h
  have h2 : (s2.setPool p pool).WF := (moveObj_wf hwf hm).congr rfl rfl rfl rfl
  split
  · exact GameState.wf_exhaustObj h2 id'
  · exact h2

/-- Playing a card keeps the physical cards. -/
theorem applyPlay_physIds {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (h : applyPlay s p c pay = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨d, pool, s2, id', -, -, hm, rfl⟩ := applyPlay_cases h
  have hp := moveObj_physIds hwf hm
  split
  · rw [GameState.physIds_exhaustObj]
    exact hp
  · exact hp

/-- Playing a card keeps `OwnerOk`. -/
theorem applyPlay_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (hown : s.OwnerOk) (h : applyPlay s p c pay = some (s', es)) :
    s'.OwnerOk := by
  obtain ⟨d, pool, s2, id', -, -, hm, rfl⟩ := applyPlay_cases h
  have h2 : (s2.setPool p pool).OwnerOk := (moveObj_ownerOk hwf hown hm).congr rfl rfl
  split
  · exact GameState.ownerOk_exhaustObj h2 id'
  · exact h2

/-- Playing a card changes nothing of the stack, the turn order, the phase, the result, the rules
or the cards. -/
theorem applyPlay_meta {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending ∧ s'.cards = s.cards := by
  obtain ⟨d, pool, s2, id', -, -, hm, rfl⟩ := applyPlay_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have hc := hs.other.config
  have ht := hs.other.turnOrder
  have hph := hs.other.phase
  have hr := hs.other.result
  have hpe := hs.other.pending
  have hcd : s2.cards = s.cards := by
    have := congrArg GameState.cards hs.other
    exact this
  split
  · exact ⟨hc, ht, hph, hr, hpe, hcd⟩
  · exact ⟨hc, ht, hph, hr, hpe, hcd⟩

/-- A playable card of the hand can be played. -/
theorem applyPlay_isSome {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    (hwf : s.WF) (hc : c ∈ s.zone (.player p .hand)) (hp : playable s p c pay = true) :
    ∃ r, applyPlay s p c pay = some r := by
  obtain ⟨o, d, cost, pool, -, ho, hd, howner, -, -, -, hpool⟩ := playable_spec hp
  have hpn : p.n < s.playerCount :=
    Zone.lt_of_valid_player (GameState.zone_valid_of_mem hwf hc)
  obtain ⟨r, hr⟩ := moveObj_isSome hwf hc (.player p .base) .top (fun o' ho' => by
    have : o' = o := Option.some.inj (ho'.symm.trans ho)
    subst this
    rw [howner]
    simp only [Zone.normalize, Zone.isBoard, ite_true]
    exact ⟨Zone.valid_player hpn _, by simp⟩)
  unfold applyPlay
  rw [hd, hpool]
  simp only [hr, Option.map_some]
  exact ⟨_, rfl⟩

/-- **Playing a card takes exactly the payment out of the Pool** (I8) (CR 357, 445): the player's
Pool is what the Pool is left with after paying, and no other Pool changes. -/
theorem applyPlay_pool {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    ∃ pool, (s.poolOf p).spend pay = some pool ∧ s'.poolOf p = pool ∧
      ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  obtain ⟨d, pool, s2, id', -, hspend, hm, rfl⟩ := applyPlay_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have hpools : s2.pools = s.pools := hs.other.pools
  refine ⟨pool, hspend, ?_, fun q hq => ?_⟩
  · split
    · exact GameState.poolOf_setPool_self s2 p pool
    · exact GameState.poolOf_setPool_self s2 p pool
  · split
    · rw [show ((s2.setPool p pool).exhaustObj id').poolOf q = (s2.setPool p pool).poolOf q
        from rfl, GameState.poolOf_setPool_ne _ hq]
      simp [GameState.poolOf, hpools]
    · rw [GameState.poolOf_setPool_ne _ hq]
      simp [GameState.poolOf, hpools]

/-- **Playing a card moves it from the hand to the Base** (CR 359): the hand is one card shorter,
the Base one card longer. -/
theorem applyPlay_zones {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (hc : c ∈ s.zone (.player p .hand))
    (hp : playable s p c pay = true) (h : applyPlay s p c pay = some (s', es)) :
    (s'.zone (.player p .hand)).length + 1 = (s.zone (.player p .hand)).length ∧
      (s'.zone (.player p .base)).length = (s.zone (.player p .base)).length + 1 := by
  obtain ⟨o, d0, cost, pool0, -, ho, -, howner, -, -, -, -⟩ := playable_spec hp
  obtain ⟨d, pool, s2, id', -, -, hm, rfl⟩ := applyPlay_cases h
  obtain ⟨src, dd, hs, o', ho', hdd⟩ := moveObj_spec_dst hm
  have hsrc : src = .player p .hand :=
    Option.some.inj (hs.locate.symm.trans
      (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hc) hc))
  have hoo : o' = o := Option.some.inj (ho'.symm.trans ho)
  have hd2 : dd = .player p .base := by
    rw [hdd, hoo, howner]
    simp [Zone.normalize, Zone.isBoard]
  have h1 := hs.zone_src
  have h2 := hs.zone_dst
  rw [hsrc] at h1
  rw [hd2] at h2
  have hne : (Zone.player p .hand) ≠ .player p .base := by simp
  have hlen1 : (s2.zone (.player p .hand)).length + 1 = (s.zone (.player p .hand)).length := by
    rw [h1, List.length_erase_of_mem hc]
    have : 0 < (s.zone (.player p .hand)).length := List.length_pos_of_mem hc
    omega
  have hlen2 : (s2.zone (.player p .base)).length = (s.zone (.player p .base)).length + 1 := by
    rw [h2, (Pos.insert_perm _ _ _).length_eq]
    simp
  split
  · exact ⟨hlen1, hlen2⟩
  · exact ⟨hlen1, hlen2⟩

/-- Every way the player can play a card of the hand: each card with each payment that pays its
cost and that the Pool covers. -/
def legalPlays (s : GameState) (p : PlayerId) : List Action :=
  (s.zone (.player p .hand)).flatMap (fun c =>
    match s.cardDef? c with
    | some d =>
      match d.cost with
      | some cost =>
        ((cost.payments d.domains).filter (fun pay => playable s p c pay)).map
          (fun pay => ⟨.player p, .playCard c pay⟩)
      | none => []
    | none => [])

/-- The plays listed are exactly the card-and-payment pairs that are playable. -/
theorem mem_legalPlays (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalPlays s p ↔ ∃ c pay, a = ⟨.player p, .playCard c pay⟩ ∧
      c ∈ s.zone (.player p .hand) ∧ playable s p c pay = true := by
  unfold legalPlays
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, ha⟩
    cases hd : s.cardDef? c with
    | none => simp [hd] at ha
    | some d =>
      cases hcost : d.cost with
      | none => simp [hd, hcost] at ha
      | some cost =>
        simp only [hd, hcost, List.mem_map, List.mem_filter] at ha
        obtain ⟨pay, ⟨-, hpl⟩, rfl⟩ := ha
        exact ⟨c, pay, rfl, hc, hpl⟩
  · rintro ⟨c, pay, rfl, hc, hpl⟩
    obtain ⟨o, d, cost, pool, -, -, hd, -, -, hcost, hpaid, -⟩ := playable_spec hpl
    refine ⟨c, hc, ?_⟩
    simp only [hd, hcost, List.mem_map, List.mem_filter]
    exact ⟨pay, ⟨(Cost.mem_payments _ _ _).mpr hpaid, hpl⟩, rfl⟩

/-- Playing a card tells that it moved to the Base, under its new identifier. -/
theorem applyPlay_events {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    ∃ id', es = [Event.moved c id' (.player p .base)] ∧
      ∀ d, s.cardDef? c = some d → d.hasType .unit = true →
        ∀ o, s'.obj? id' = some o → o.exhausted = true := by
  unfold applyPlay at h
  cases hd : s.cardDef? c with
  | none => simp [hd] at h
  | some d =>
    cases hs : (s.poolOf p).spend pay with
    | none => simp [hd, hs] at h
    | some pool =>
      simp only [hd, hs, Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨hs', hes⟩ := hr
      refine ⟨id', hes.symm, fun d' hd' hu o ho => ?_⟩
      cases hd'
      rw [← hs'] at ho
      simp only [hu, ite_true, GameState.obj?_exhaustObj] at ho
      cases hx : (s2.setPool p pool).obj? id' with
      | none => rw [hx] at ho; simp at ho
      | some o0 =>
        rw [hx] at ho
        simp only [Option.map_some, Option.some.injEq] at ho
        subst ho
        rfl

end Riftbound

end
