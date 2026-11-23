module

public import Riftbound.Rules.Resources
public import Riftbound.Rules.Pay
public import Riftbound.Rules.Select
public import Riftbound.Rules.Passive
public import Riftbound.Rules.Deflect

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

/-- The additional costs a card may pay when it is played, one at a time (CR 357.2): a Unit with
Accelerate may pay 1 Energy and a Power of its domain, to enter ready (CR 805); a Spell with Repeat
may pay the cost the keyword names, to repeat its effect (CR 820). -/
def CardDef.extraCosts (d : CardDef) : List Cost :=
  d.additionalCost.toList ++ d.keywords.filterMap (fun i =>
    match i.keyword, i.arg with
    | .accelerate, _ => if d.hasType .unit then some ⟨1, [.own]⟩ else none
    | .repeat_, .cost c => if d.hasType .spell then some c else none
    | _, _ => none)

/-- The costs a card may be played for: its cost, or its cost with one additional cost. -/
def CardDef.playCosts (d : CardDef) (cost : Cost) : List Cost :=
  cost :: d.extraCosts.map cost.plus

/-- The payment pays the cost of the card, or the cost with an additional cost. -/
def CardDef.paysFor (d : CardDef) (cost : Cost) (pay : RunePool.Payment) : Bool :=
  (d.playCosts cost).any (fun c => c.paidBy d.domains pay)

/-- Every payment that pays the cost of the card, with or without an additional cost. -/
def CardDef.playPayments (d : CardDef) (cost : Cost) : List RunePool.Payment :=
  (d.playCosts cost).flatMap (fun c => c.payments d.domains)

/-- The payments listed are exactly the payments that pay. -/
theorem CardDef.mem_playPayments (d : CardDef) (cost : Cost) (pay : RunePool.Payment) :
    pay ∈ d.playPayments cost ↔ d.paysFor cost pay = true := by
  simp only [playPayments, paysFor, List.mem_flatMap, List.any_eq_true, Cost.mem_payments]

/-- A payment that pays takes out as much as one of the costs it can pay. -/
theorem CardDef.paysFor_total {d : CardDef} {cost : Cost} {pay : RunePool.Payment}
    (h : d.paysFor cost pay = true) :
    ∃ c ∈ d.playCosts cost, pay.energy + pay.power.length = c.total := by
  unfold paysFor at h
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, hp⟩ := h
  exact ⟨c, hc, Cost.total_of_paidBy hp⟩

/-- The player has played a card in the turn that is going on, Legion (CR 812). -/
def GameState.playedBefore (s : GameState) (p : PlayerId) : Bool :=
  s.objects.toList.any (fun (_, o) => o.owner == p && o.playedTurn == some s.turn)

/-- Whether the card `c` is one of the objects the selector of a passive ability of `src`, which
the player `p` controls, stands for, as a cost change reads it (the card is not in play): the card
itself, or a card on a side (seen by `p`) with the properties. -/
def GameState.costSelects (s : GameState) (p : PlayerId) (src c : ObjId) : Selector → Bool
  | .self => src == c
  | .pick .all side _ fs =>
    (s.obj? c).any (fun o => side.admits p o) && (fs.holds s src {} c == some true)
  | _ => false

/-- The card `c` enters ready: by itself, by a passive ability of its own whose condition holds,
by the passive ability of an object the player controls, or by an effect of the turn. -/
def GameState.readyNow (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) : Bool :=
  d.entersReady || s.readyByFx p ||
    (d.fullAbilities.any (fun ab =>
      match ab with
      | Ability.passive cond mods =>
        mods.contains (.entersReady .self) && cond.eval s p c {} == some true
      | _ => false)) ||
    (s.passiveSources.any (fun src =>
      match s.obj? src, s.cardDef? src with
      | some o, some d2 =>
        d2.fullAbilities.any (fun ab =>
          match ab with
          | Ability.passive cond mods =>
            cond.eval s o.controller src {} == some true &&
              mods.any (fun m => match m with
                | .entersReady sel => src != c && s.costSelects o.controller src c sel
                | _ => false)
          | _ => false)
      | _, _ => false))

/-- The cuts of the Energy cost of the card `c` of the player: each is an amount and the floor the
cost does not go below (CR 356). They come from the passive abilities of the objects in play and of
the card itself, whose condition holds: Legion is the player having played a card (CR 812). -/
def GameState.costCuts (s : GameState) (p : PlayerId) (c : ObjId) : List (Nat × Nat) :=
  (s.passiveSources ++ [c]).flatMap (fun src =>
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      d.fullAbilities.flatMap (fun ab =>
        match ab with
        | Ability.passive cond mods =>
          let holds := match cond with
            | .legion =>
              -- another card of the player was played this turn, not the card itself
              some (s.objects.toList.any (fun (k, x) =>
                x.owner == p && x.playedTurn == some s.turn && k != c.n))
            | k => k.eval s o.controller src {}
          if holds == some true then
            mods.filterMap (fun m =>
              match m with
              | .costMinus sel a =>
                if s.costSelects o.controller src c sel then
                  some ((a.evalS s o.controller src {}).getD 0, 0) else none
              | .costMinusMin sel a fl =>
                if s.costSelects o.controller src c sel then
                  some ((a.evalS s o.controller src {}).getD 0, fl) else none
              | _ => none)
          else []
        | _ => [])
    | _, _ => []) ++
  (if (s.cardDef? c).any (·.hasType .spell) then (s.spellCutFx p).map (fun n => (n, 0)) else [])

/-- The Energy that the passive abilities add to the cost of the card `c` of the player (CR 356):
the cost of the spells of the opponents of Vex, Cheerless goes up. -/
def GameState.costRaise (s : GameState) (c : ObjId) : Nat :=
  (s.passiveSources ++ [c]).foldl (fun acc src =>
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      d.fullAbilities.foldl (fun acc ab =>
        match ab with
        | Ability.passive cond mods =>
          if cond.eval s o.controller src {} == some true then
            mods.foldl (fun acc m =>
              match m with
              | .costPlus sel a =>
                if s.costSelects o.controller src c sel then
                  acc + ((a.evalS s o.controller src {}).getD 0) else acc
              | _ => acc) acc
          else acc
        | _ => acc) acc
    | _, _ => acc) 0

/-- The cost the card `c` of the player is played for: its cost, less the cuts, and more by what the
passive abilities add (CR 356). -/
def GameState.effCost (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) : Option Cost :=
  d.cost.map (fun k =>
    -- the cost goes up first, then down (to its floor)
    let e := (s.costCuts p c).foldl
      (fun e (cut : Nat × Nat) => if e ≤ cut.2 then e else Nat.max cut.2 (e - cut.1))
      (k.energy + s.costRaise c)
    { k with energy := e })

/-- The payment pays more than the cost of the card: an additional cost is paid. -/
def GameState.paidExtra (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (pay : RunePool.Payment) : Bool :=
  match s.effCost p c d with
  | some cost => !(cost.paidBy d.domains pay)
  | none => false

/-- The player can play the object with the payment: it is the player's card, a Unit or a Gear, in
the Main Phase, and the payment pays its cost and the Rune Pool holds it (CR 349, 356, 357). The
card must also be in the hand, which `Legal` states apart. -/
def playable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment) : Bool :=
  s.phase == .main && !s.cantPlay p &&
    match s.obj? c, s.cardDef? c with
    | some o, some d =>
      o.owner == p && (d.hasType .unit || d.hasType .gear) &&
        (match s.effCost p c d with
          | some cost => d.paysFor cost pay
          | none => false) &&
        ((s.poolOf p).spend pay).isSome &&
        -- a card that is played only to a Battlefield is not played to the Base
        !(d.abilities.any (fun ab =>
          match ab with | Ability.passive _ mods => mods.contains .noPlayToBase | _ => false))
    | _, _ => false

/-- What is true when a card is played: whether an additional cost was paid, whether another card
had been played in the turn (Legion), and the turn. -/
structure PlayMark where
  /-- An additional cost was paid. -/
  paid : Bool
  /-- Another card of the player had been played in the turn. -/
  legion : Bool
  /-- The turn. -/
  turn : Nat
  /-- The timestamp counter. -/
  stamp : Nat
  /-- The Energy paid. -/
  energy : Nat
  /-- The Unit is buffed as it is played, by an effect of the turn. -/
  buff : Bool := false

/-- The object after it is played: the objects chosen (for a Spell on the Chain), and the facts of
the play. -/
def Object.withPlay (ts : List ObjId) (m : PlayMark) (o : Object) : Object :=
  let o1 : Object :=
    { o with targets := ts, paid := m.paid, legion := m.legion, playedTurn := some m.turn,
             buffed := o.buffed || m.buff }
  { o1 with playedStamp := some m.stamp, energyPaid := m.energy }

/-- The facts of playing the card now with the payment. -/
def GameState.playMark (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment) :
    PlayMark :=
  { paid := (s.cardDef? c).any (fun d => s.paidExtra p c d pay), legion := s.playedBefore p,
    turn := s.turn, stamp := s.nextTimestamp, energy := pay.energy,
    buff := (s.cardDef? c).any (·.hasType .unit) && (s.fxOf p).any (· == .unitsBuffed) }

/-- Play a card (CR 349-359): pay, and put it on the Base, exhausted if it is a Unit (CR 359),
unless it enters ready or the cost of Accelerate was paid (CR 805). -/
def applyPlay (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment) :
    Option (GameState × List Event) :=
  match s.cardDef? c, (s.poolOf p).spend pay with
  | some d, some pool =>
    (moveObj s c (.player p .base)).map (fun r =>
      let s1 := (r.1.modObj r.2 (Object.withPlay [] (s.playMark p c pay))).setPool p pool
      ((if d.hasType .unit && !s.readyNow p c d && !s.paidExtra p c d pay then s1.exhaustObj r.2
        else s1),
        [Event.moved c r.2 (.player p .base)]))
  | _, _ => none

/-- The player can cast the object with the payment and the targets: it is the player's Spell, the
objects chosen are a legal pick for its choices, and the payment pays its cost and the Pool covers
it, in the Main Phase (CR 349, 355, 356, 357). The card must also be in the hand, which `Legal`
states apart. -/
def castable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) : Bool :=
  s.phase == .main && !s.cantPlay p &&
    match s.obj? c, s.cardDef? c with
    | some o, some d =>
      o.owner == p && d.hasType .spell &&
        (match d.spellEffect with
          | some e => targetsOk s p c e.choices targets
          | none => false) &&
        (match s.effCost p c d with
          | some cost => d.paysFor cost pay
          | none => false) &&
        ((s.poolOf p).spend pay).any (fun pool => s.deflectOk p pool targets)
    | _, _ => false

/-- Cast a Spell (CR 354, 357): pay, and put it on the Chain with the objects chosen. -/
def applyCast (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) : Option (GameState × List Event) :=
  match (s.poolOf p).spend pay with
  | some pool =>
    (moveObj s c .chain).map (fun r =>
      (((r.1.setPool p pool).modObj r.2 (Object.withPlay targets (s.playMark p c pay))),
        [Event.moved c r.2 .chain]))
  | none => none

/-- What a playable card is: the game is in the Main Phase, and the card is the player's, a Unit or
a Gear, with a cost that the payment pays and the Pool covers (CR 349, 356, 357). -/
theorem playable_spec {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    (h : playable s p c pay = true) :
    ∃ o d cost pool, s.phase = .main ∧ s.obj? c = some o ∧ s.cardDef? c = some d ∧
      o.owner = p ∧ (d.hasType .unit = true ∨ d.hasType .gear = true) ∧
        s.effCost p c d = some cost ∧
      d.paysFor cost pay = true ∧ (s.poolOf p).spend pay = some pool := by
  unfold playable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hph, -⟩, hrest⟩ := h
  cases ho : s.obj? c with
  | none => rw [ho] at hrest; simp at hrest
  | some o =>
    cases hd : s.cardDef? c with
    | none => rw [ho, hd] at hrest; simp at hrest
    | some d =>
      rw [ho, hd] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hrest
      obtain ⟨⟨⟨⟨howner, hty⟩, hcost⟩, hspend⟩, -⟩ := hrest
      cases hc : s.effCost p c d with
      | none => rw [hc] at hcost; simp at hcost
      | some cost =>
        rw [hc] at hcost
        obtain ⟨pool, hpool⟩ := Option.isSome_iff_exists.mp hspend
        exact ⟨o, d, cost, pool, hph, rfl, rfl, howner, hty, hc, hcost, hpool⟩

/-- The shape of a card being played: its definition, the Pool after paying, and the move to the
Base. -/
theorem applyPlay_cases {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    ∃ d pool s2 id' m, s.cardDef? c = some d ∧ (s.poolOf p).spend pay = some pool ∧
      moveObj s c (.player p .base) = some (s2, id') ∧
      s' = (if (d.hasType .unit && !s.readyNow p c d && !s.paidExtra p c d pay) = true
        then ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).exhaustObj id'
        else (s2.modObj id' (Object.withPlay [] m)).setPool p pool) := by
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
      exact ⟨d, pool, s2, id', _, rfl, rfl, hm, hr.1.symm⟩

/-- Playing a card keeps the game well formed. -/
theorem applyPlay_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (h : applyPlay s p c pay = some (s', es)) : s'.WF := by
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
  have h2 : ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).WF :=
    (GameState.wf_modObj (moveObj_wf hwf hm) id' _).congr rfl rfl rfl rfl
  split
  · exact GameState.wf_exhaustObj h2 id'
  · exact h2

/-- Playing a card keeps the physical cards. -/
theorem applyPlay_physIds {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (h : applyPlay s p c pay = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
  have hp0 := moveObj_physIds hwf hm
  have hp : ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).physIds.Perm s.physIds := by
    have e : (s2.modObj id' (Object.withPlay [] m)).physIds = s2.physIds :=
      GameState.physIds_modObj s2 id' (f := Object.withPlay [] m) (fun _ => rfl)
    exact e ▸ hp0
  split
  · rw [GameState.physIds_exhaustObj]
    exact hp
  · exact hp

/-- Playing a card keeps `OwnerOk`. -/
theorem applyPlay_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (hwf : s.WF) (hown : s.OwnerOk) (h : applyPlay s p c pay = some (s', es)) :
    s'.OwnerOk := by
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
  have h2 : ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).OwnerOk :=
    (GameState.ownerOk_modObj (moveObj_ownerOk hwf hown hm) id'
      (f := Object.withPlay [] m) (fun _ => rfl)).congr rfl rfl
  split
  · exact GameState.ownerOk_exhaustObj h2 id'
  · exact h2

/-- Playing a card changes nothing of the stack, the turn order, the phase, the result, the rules
or the cards. -/
theorem applyPlay_meta {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending ∧ s'.cards = s.cards := by
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
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
  obtain ⟨d, pool, s2, id', m, -, hspend, hm, rfl⟩ := applyPlay_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have hpools : (s2.modObj id' (Object.withPlay [] m)).pools = s.pools := hs.pools
  refine ⟨pool, hspend, ?_, fun q hq => ?_⟩
  · split
    · exact GameState.poolOf_setPool_self (s2.modObj id' (Object.withPlay [] m)) p pool
    · exact GameState.poolOf_setPool_self (s2.modObj id' (Object.withPlay [] m)) p pool
  · split
    · rw [show (((s2.modObj id' (Object.withPlay [] m)).setPool p pool).exhaustObj id').poolOf q =
          ((s2.modObj id' (Object.withPlay [] m)).setPool p pool).poolOf q from rfl,
        GameState.poolOf_setPool_ne _ hq]
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
  obtain ⟨d, pool, s2, id', m, -, -, hm, rfl⟩ := applyPlay_cases h
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

/-- Playing a card tells that it moved to the Base, under its new identifier. -/
theorem applyPlay_events {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {es : List Event} (h : applyPlay s p c pay = some (s', es)) :
    ∃ id', es = [Event.moved c id' (.player p .base)] ∧
      ∀ d, s.cardDef? c = some d → d.hasType .unit = true → s.readyNow p c d = false →
        s.paidExtra p c d pay = false → ∀ o, s'.obj? id' = some o → o.exhausted = true := by
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
      refine ⟨id', hes.symm, fun d' hd' hu hr hx0 o ho => ?_⟩
      cases hd'
      rw [← hs'] at ho
      simp only [hu, hr, hx0, Bool.not_false, Bool.and_self, ite_true,
        GameState.obj?_exhaustObj] at ho
      cases hx : ((s2.modObj id' (Object.withPlay [] (s.playMark p c pay))).setPool p pool).obj?
          id' with
      | none => rw [hx] at ho; simp at ho
      | some o0 =>
        rw [hx] at ho
        simp only [Option.map_some, Option.some.injEq] at ho
        subst ho
        rfl

/-- What a castable Spell is: the game is in the Main Phase, and the card is the player's Spell,
with an effect that asks for no choice, and a cost that the payment pays and the Pool covers. -/
theorem castable_spec {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} (h : castable s p c pay targets = true) :
    ∃ o d cost pool, s.phase = .main ∧ s.obj? c = some o ∧ s.cardDef? c = some d ∧
      o.owner = p ∧ d.hasType .spell = true ∧ s.effCost p c d = some cost ∧
      d.paysFor cost pay = true ∧ (s.poolOf p).spend pay = some pool := by
  unfold castable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hph, -⟩, hrest⟩ := h
  cases ho : s.obj? c with
  | none => rw [ho] at hrest; simp at hrest
  | some o =>
    cases hd : s.cardDef? c with
    | none => rw [ho, hd] at hrest; simp at hrest
    | some d =>
      rw [ho, hd] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨⟨⟨⟨howner, hty⟩, -⟩, hcost⟩, hspend⟩ := hrest
      cases hc : s.effCost p c d with
      | none => rw [hc] at hcost; simp at hcost
      | some cost =>
        rw [hc] at hcost
        obtain ⟨pool, hpool⟩ : ∃ pool, (s.poolOf p).spend pay = some pool := by
          cases hs : (s.poolOf p).spend pay with
          | none => rw [hs] at hspend; simp at hspend
          | some pool => exact ⟨pool, rfl⟩
        exact ⟨o, d, cost, pool, hph, rfl, rfl, howner, hty, hc, hcost, hpool⟩

/-- A castable card is a Spell whose effect the targets are a legal pick for. -/
theorem castable_targets {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} (h : castable s p c pay targets = true) :
    ∃ d e, s.cardDef? c = some d ∧ d.spellEffect = some e ∧
      targetsOk s p c e.choices targets = true := by
  unfold castable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨-, hrest⟩ := h
  cases ho : s.obj? c with
  | none => rw [ho] at hrest; simp at hrest
  | some o =>
    cases hd : s.cardDef? c with
    | none => rw [ho, hd] at hrest; simp at hrest
    | some d =>
      rw [ho, hd] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨⟨⟨⟨-, -⟩, htg⟩, -⟩, -⟩ := hrest
      cases he : d.spellEffect with
      | none => rw [he] at htg; simp at htg
      | some e =>
        rw [he] at htg
        exact ⟨d, e, rfl, he, htg⟩

/-- The shape of a Spell being cast: the Pool after paying, and the move to the Chain. -/
theorem applyCast_cases {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {es : List Event} (h : applyCast s p c pay targets = some (s', es)) :
    ∃ pool s2 id' rep, (s.poolOf p).spend pay = some pool ∧
      moveObj s c .chain = some (s2, id') ∧
      s' = (s2.setPool p pool).modObj id' (Object.withPlay targets rep) ∧
        es = [Event.moved c id' .chain] := by
  unfold applyCast at h
  cases hs : (s.poolOf p).spend pay with
  | none => simp [hs] at h
  | some pool =>
    simp only [hs, Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    exact ⟨pool, s2, id', _, rfl, hm, hr.1.symm, hr.2.symm⟩

/-- Casting a Spell keeps the game well formed. -/
theorem applyCast_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {es : List Event} (hwf : s.WF)
    (h : applyCast s p c pay targets = some (s', es)) : s'.WF := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  have h2 : (s2.setPool p pool).WF := (moveObj_wf hwf hm).congr rfl rfl rfl rfl
  exact GameState.wf_modObj h2 _ _

/-- Casting a Spell keeps the physical cards. -/
theorem applyCast_physIds {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {es : List Event} (hwf : s.WF)
    (h : applyCast s p c pay targets = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  have hp := moveObj_physIds hwf hm
  have h2 : (s2.setPool p pool).physIds = s2.physIds := rfl
  rw [GameState.physIds_modObj _ id' (f := Object.withPlay targets rep) (fun _ => rfl), h2]
  exact hp

/-- Casting a Spell keeps `OwnerOk`. -/
theorem applyCast_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : applyCast s p c pay targets = some (s', es)) :
    s'.OwnerOk := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  have h2 : (s2.setPool p pool).OwnerOk := (moveObj_ownerOk hwf hown hm).congr rfl rfl
  exact GameState.ownerOk_modObj h2 _ (fun _ => rfl)

/-- Casting a Spell changes nothing of the stack, the turn order, the phase, the result, the rules
or the cards. -/
theorem applyCast_meta {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {es : List Event} (h : applyCast s p c pay targets = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending ∧ s'.cards = s.cards := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have hcd : s2.cards = s.cards := by
    have := congrArg GameState.cards hs.other
    exact this
  exact ⟨hs.other.config, hs.other.turnOrder, hs.other.phase, hs.other.result, hs.other.pending,
    hcd⟩

/-- A castable Spell of the hand can be cast. -/
theorem applyCast_isSome {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} (hwf : s.WF) (hc : c ∈ s.zone (.player p .hand))
    (hp : castable s p c pay targets = true) :
    ∃ r, applyCast s p c pay targets = some r := by
  obtain ⟨o, d, cost, pool, -, ho, hd, howner, -, -, -, hpool⟩ := castable_spec hp
  have hpn : p.n < s.playerCount :=
    Zone.lt_of_valid_player (GameState.zone_valid_of_mem hwf hc)
  obtain ⟨r, hr⟩ := moveObj_isSome hwf hc .chain .top (fun o' ho' => by
    have : o' = o := Option.some.inj (ho'.symm.trans ho)
    subst this
    simp only [Zone.normalize]
    exact ⟨Zone.valid_chain _, by simp⟩)
  unfold applyCast
  rw [hpool]
  simp only [hr, Option.map_some]
  exact ⟨_, rfl⟩

/-- **Casting a Spell takes exactly the payment out of the Pool** (I8) (CR 357, 445). -/
theorem applyCast_pool {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {es : List Event} (h : applyCast s p c pay targets = some (s', es)) :
    ∃ pool, (s.poolOf p).spend pay = some pool ∧ s'.poolOf p = pool ∧
      ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  obtain ⟨pool, s2, id', rep, hspend, hm, rfl, -⟩ := applyCast_cases h
  obtain ⟨src, dd, hs⟩ := moveObj_spec hm
  have hpools : s2.pools = s.pools := hs.pools
  refine ⟨pool, hspend, GameState.poolOf_setPool_self s2 p pool, fun q hq => ?_⟩
  show (s2.setPool p pool).poolOf q = _
  rw [GameState.poolOf_setPool_ne _ hq]
  simp [GameState.poolOf, hpools]

/-- **Casting a Spell moves it from the hand to the Chain** (CR 354). -/
theorem applyCast_zones {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {es : List Event} (hwf : s.WF) (hc : c ∈ s.zone (.player p .hand))
    (h : applyCast s p c pay targets = some (s', es)) :
    (s'.zone (.player p .hand)).length + 1 = (s.zone (.player p .hand)).length ∧
      (s'.zone .chain).length = (s.zone .chain).length + 1 := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  obtain ⟨src, dd, hs, o', ho', hdd⟩ := moveObj_spec_dst hm
  have hsrc : src = .player p .hand :=
    Option.some.inj (hs.locate.symm.trans
      (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hc) hc))
  have hd2 : dd = .chain := by rw [hdd]; simp [Zone.normalize]
  have h1 := hs.zone_src
  have h2 := hs.zone_dst
  rw [hsrc] at h1
  rw [hd2] at h2
  refine ⟨?_, ?_⟩
  · show (s2.zone (.player p .hand)).length + 1 = _
    rw [h1, List.length_erase_of_mem hc]
    have : 0 < (s.zone (.player p .hand)).length := List.length_pos_of_mem hc
    omega
  · show (s2.zone .chain).length = _
    rw [h2, (Pos.insert_perm _ _ _).length_eq]
    simp

/-- A card of the hand can be played with the payment and the targets: a Unit or a Gear with no
targets, or a Spell with a legal pick of targets (CR 349-359). -/
def PlayOk (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) : Prop :=
  (targets = [] ∧ playable s p c pay = true) ∨ castable s p c pay targets = true

instance PlayOk.decidable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) : Decidable (PlayOk s p c pay targets) := by
  unfold PlayOk
  infer_instance

/-- The picks of targets worth trying for a card: none, and every legal pick of its Spell
effect. -/
def playTargets (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef) : List (List ObjId) :=
  [] :: (match d.spellEffect with
    | some e => (targetTuples s p c e.choices).filter (fun ts => decide (ts ≠ []))
    | none => [])

/-- The picks listed are no target, or a legal pick of the Spell effect. -/
theorem mem_playTargets (s : GameState) (p : PlayerId) (c : ObjId) (d : CardDef)
    (ts : List ObjId) : ts ∈ playTargets s p c d ↔
      ts = [] ∨ ∃ e, d.spellEffect = some e ∧ targetsOk s p c e.choices ts = true := by
  unfold playTargets
  rw [List.mem_cons]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      cases hs : d.spellEffect with
      | none => rw [hs] at h; simp at h
      | some e =>
        rw [hs] at h
        simp only [List.mem_filter, decide_eq_true_eq] at h
        exact ⟨e, rfl, (mem_targetTuples s p c e.choices ts).mp h.1⟩
  · rintro (h | ⟨e, he, hok⟩)
    · exact Or.inl h
    · by_cases hne : ts = []
      · exact Or.inl hne
      · right
        rw [he]
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨(mem_targetTuples s p c e.choices ts).mpr hok, hne⟩

/-- Every way the player can play a card of the hand: each card with each payment that pays its
cost, and each pick of targets, that the Pool covers. -/
def legalPlays (s : GameState) (p : PlayerId) : List Action :=
  (s.zone (.player p .hand)).flatMap (fun c =>
    match s.cardDef? c with
    | some d =>
      match s.effCost p c d with
      | some cost =>
        (d.playPayments cost).flatMap (fun pay =>
          ((playTargets s p c d).filter (fun ts => decide (PlayOk s p c pay ts))).map
            (fun ts => ⟨.player p, .playCard c pay ts⟩))
      | none => []
    | none => [])

/-- The plays listed are exactly the card, payment and targets that can be played. -/
theorem mem_legalPlays (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalPlays s p ↔ ∃ c pay ts, a = ⟨.player p, .playCard c pay ts⟩ ∧
      c ∈ s.zone (.player p .hand) ∧ PlayOk s p c pay ts := by
  unfold legalPlays
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, ha⟩
    cases hd : s.cardDef? c with
    | none => simp [hd] at ha
    | some d =>
      cases hcost : s.effCost p c d with
      | none => simp [hd, hcost] at ha
      | some cost =>
        simp only [hd, hcost, List.mem_flatMap, List.mem_map, List.mem_filter,
          decide_eq_true_eq] at ha
        obtain ⟨pay, -, ts, ⟨-, hok⟩, rfl⟩ := ha
        exact ⟨c, pay, ts, rfl, hc, hok⟩
  · rintro ⟨c, pay, ts, rfl, hc, hok⟩
    have hdc : ∃ d cost, s.cardDef? c = some d ∧ s.effCost p c d = some cost ∧
        d.paysFor cost pay = true ∧ ts ∈ playTargets s p c d := by
      rcases hok with ⟨hts, h⟩ | h
      · obtain ⟨o, d, cost, pool, -, -, hd, -, -, hcost, hpaid, -⟩ := playable_spec h
        exact ⟨d, cost, hd, hcost, hpaid, (mem_playTargets s p c d ts).mpr (Or.inl hts)⟩
      · obtain ⟨o, d, cost, pool, -, -, hd, -, -, hcost, hpaid, -⟩ := castable_spec h
        obtain ⟨d', e, hd', he, hok⟩ := castable_targets h
        have : d' = d := Option.some.inj (hd'.symm.trans hd)
        subst this
        exact ⟨d', cost, hd, hcost, hpaid,
          (mem_playTargets s p c d' ts).mpr (Or.inr ⟨e, he, hok⟩)⟩
    obtain ⟨d, cost, hd, hcost, hpaid, hts⟩ := hdc
    refine ⟨c, hc, ?_⟩
    simp only [hd, hcost, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨pay, (CardDef.mem_playPayments _ _ _).mpr hpaid, ts, ⟨hts, hok⟩, rfl⟩

/-- Play a card of the hand with the payment and the targets: a Spell is cast, and goes to the
Chain with the players to pass (CR 354, 311-313); a Unit or a Gear is played at once. `rest` is the
stack below the `priority` frame. -/
def applyPlayCard (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (targets : List ObjId) (rest : List Frame) : Option (GameState × List Event) :=
  if castable s p c pay targets = true then
    (applyCast s p c pay targets).map
      (fun r => ({ r.1 with pending := .chainPass p 0 :: .priority p :: rest }, r.2))
  else applyPlay s p c pay

/-- Playing a card keeps the game well formed. -/
theorem applyPlayCard_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {rest : List Frame} {es : List Event} (hwf : s.WF)
    (h : applyPlayCard s p c pay targets rest = some (s', es)) : s'.WF := by
  unfold applyPlayCard at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (applyCast_wf hwf hm).congr rfl rfl rfl rfl
  · exact applyPlay_wf hwf h

/-- Playing a card keeps the physical cards. -/
theorem applyPlayCard_physIds {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {targets : List ObjId} {rest : List Frame} {es : List Event}
    (hwf : s.WF) (h : applyPlayCard s p c pay targets rest = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  unfold applyPlayCard at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hp := applyCast_physIds hwf hm
    exact hp
  · exact applyPlay_physIds hwf h

/-- Playing a card keeps `OwnerOk`. -/
theorem applyPlayCard_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {targets : List ObjId} {rest : List Frame} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (h : applyPlayCard s p c pay targets rest = some (s', es)) :
    s'.OwnerOk := by
  unfold applyPlayCard at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (applyCast_ownerOk hwf hown hm).congr rfl rfl
  · exact applyPlay_ownerOk hwf hown h

/-- Playing a card changes nothing of the turn order, the phase, the result, the rules or the
cards; the stack is the same, or the Spell's players have to pass above the `priority` frame. -/
theorem applyPlayCard_meta {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {targets : List ObjId} {rest : List Frame} {es : List Event}
    (h : applyPlayCard s p c pay targets rest = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.cards = s.cards ∧
      (s'.pending = s.pending ∨ s'.pending = .chainPass p 0 :: .priority p :: rest) := by
  unfold applyPlayCard at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨h1, h2, h3, h4, -, h6⟩ := applyCast_meta hm
    exact ⟨h1, h2, h3, h4, h6, Or.inr rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := applyPlay_meta h
    exact ⟨h1, h2, h3, h4, h6, Or.inl h5⟩

/-- A card that can be played or cast is played in the Main Phase. -/
theorem playOk_main {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} (h : PlayOk s p c pay targets) : s.phase = .main := by
  rcases h with ⟨-, h⟩ | h
  · obtain ⟨-, -, -, -, hm, -⟩ := playable_spec h
    exact hm
  · obtain ⟨-, -, -, -, hm, -⟩ := castable_spec h
    exact hm

/-- A playable or castable card of the hand can be played. -/
theorem applyPlayCard_isSome {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {rest : List Frame} (hwf : s.WF)
    (hc : c ∈ s.zone (.player p .hand)) (hp : PlayOk s p c pay targets) :
    ∃ r, applyPlayCard s p c pay targets rest = some r := by
  unfold applyPlayCard
  by_cases hcast : castable s p c pay targets = true
  · obtain ⟨r, hr⟩ := applyCast_isSome hwf hc hcast
    simp only [hcast, ite_true, hr, Option.map_some]
    exact ⟨_, rfl⟩
  · simp only [hcast]
    rcases hp with ⟨-, h⟩ | h
    · exact applyPlay_isSome hwf hc h
    · exact absurd h hcast

end Riftbound

end
