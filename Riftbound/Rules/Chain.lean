module

public import Riftbound.Rules.Effects

/-!
# Activated abilities and Reactions

A player with priority can use an activated ability of an object they control (CR 361, 363): the
costs are paid, and the ability goes on the Chain as an object of its own (design.md §5.2). The
Chain holds Spells and abilities in the order they were put there (CR 337, 340). While it holds
an item, the players can answer it with a Reaction: a Spell with Reaction (CR 813), or an activated
ability with the speed Reaction, and the Basic Rune abilities (CR 164.2, 430).

The costs this model can pay are the exhaustion of the object and Energy with Power. An ability
with any other cost cannot be used yet.
-/

@[expose] public section

namespace Riftbound

/-- The costs of an ability the model can pay: whether to exhaust the object, and the Energy and
Power to pay. `none` for an ability with any other cost, or two payments. -/
def costPlan : List AbilityCost → Option (Bool × Option Cost)
  | [] => some (false, none)
  | .exhaustSelf :: cs =>
    match costPlan cs with
    | some (false, c) => some (true, c)
    | _ => none
  | .pay c :: cs =>
    match costPlan cs with
    | some (e, none) => some (e, some c)
    | _ => none
  | .fromHand :: cs => costPlan cs
  | .fromHidden :: cs => costPlan cs
  | .fromChampionZone :: cs => costPlan cs
  | _ :: _ => none

/-- Whether the costs exhaust the object. -/
def costExhausts (costs : List AbilityCost) : Bool :=
  match costPlan costs with
  | some (e, _) => e
  | none => false

/-- The object is one a player can use abilities of: they control it, and it is on their Base, on
their Legend Zone, or on the Battlefield Zone. -/
def GameState.usesAbilitiesOf (s : GameState) (p : PlayerId) (src : ObjId) : Bool :=
  (s.zone (.player p .base)).contains src || (s.zone (.player p .legendZone)).contains src ||
    (s.zone .battlefieldZone).contains src

/-- A card hidden at a Battlefield cannot be revealed by its owner `p` while a Unit of an opponent
there has the passive ability that forbids it (CR 811). -/
def GameState.hiddenBlocked (s : GameState) (p : PlayerId) (src : ObjId) : Bool :=
  match (s.obj? src).bind (·.hiddenAt) with
  | some bf =>
    (s.zone .battlefieldZone).any (fun u =>
      (s.obj? u).any (fun o => o.loc == some bf && o.controller != p) &&
        (s.activeMods u).contains .noHiddenReveal)
  | none => false

/-- The cost an ability pays when it resolves ("Recycle 3 from your trash: ...") is written as the
first part of the effect, guarded by a condition: the ability cannot be used while the condition is
false, as an ability whose cost cannot be paid cannot be used. A condition about the chosen objects
cannot be answered yet, and does not stop the use. An ability that only plays a card to a
Battlefield cannot be used while the opponents of its player play Units only to their Base (the
play by a triggered ability goes to the Base instead). A hidden card that cannot be revealed
stops its ability, too. -/
def guardOk (s : GameState) (p : PlayerId) (src : ObjId) (body : EffectDef) : Bool :=
  (match body.body with
    | .ifThen c _ .nop => c.eval s p src {} != some false
    | _ => true) && !s.hiddenBlocked p src &&
    -- the opponents of a Warden play Units only to their Base
    (match body.body with
      | .prim (.playTo _ _) => !s.oppHas p .oppsPlayToBaseOnly
      | .ifThen _ (.prim (.playTo _ _)) .nop => !s.oppHas p .oppsPlayToBaseOnly
      | _ => true)

/-- Where the object that has the ability is, for the ability at place `idx`: an ability that can be
used from the hand (Hide) or from hiding (CR 811) is used there, from the turn after the card was
hidden; the others, where the player uses abilities of objects. An ability with a guard is used
only while the guard holds. -/
def GameState.abilityZoneOk (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) : Bool :=
  match (s.cardDef? src).bind (fun d => d.fullAbilities[idx]?) with
  | some (.activated costs _ body _) =>
    guardOk s p src body &&
      (if costs.contains .fromHand then
        -- an ability that plays the card to a Battlefield is a play: "can't play" stops it
        (s.zone (.player p .hand)).contains src &&
          !((match body.body with
              | .prim (.playTo _ _) => true
              | .ifThen _ (.prim (.playTo _ _)) .nop => true
              | _ => false) && s.cantPlay p)
      else if costs.contains .fromHidden then
        (s.zone (.player p .hidden)).contains src &&
          ((s.obj? src).bind (·.hiddenTurn)).any (fun t => decide (t < s.turn))
      else if costs.contains .fromChampionZone then
        (s.zone (.player p .championZone)).contains src && !s.cantPlay p
      else s.usesAbilitiesOf p src)
  | _ => s.usesAbilitiesOf p src

/-- Where abilities are used from: the places of the board, the hand, the hidden cards and the
Champion Zone. -/
def GameState.abilityZones (s : GameState) (p : PlayerId) : List ObjId :=
  s.zone (.player p .base) ++ s.zone (.player p .legendZone) ++ s.zone .battlefieldZone ++
    s.zone (.player p .hand) ++ s.zone (.player p .hidden) ++ s.zone (.player p .championZone)

/-- An object the player uses abilities of is in one of these places. -/
theorem GameState.usesAbilitiesOf_mem {s : GameState} {p : PlayerId} {src : ObjId}
    (h : s.usesAbilitiesOf p src = true) : src ∈ s.abilityZones p := by
  simp only [GameState.usesAbilitiesOf, Bool.or_eq_true, List.contains_iff_mem] at h
  unfold GameState.abilityZones
  simp only [List.mem_append]
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))

/-- A usable ability is of an object in one of these places. -/
theorem GameState.abilityZoneOk_mem {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    (h : s.abilityZoneOk p src idx = true) : src ∈ s.abilityZones p := by
  unfold GameState.abilityZoneOk at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    split at h
    · unfold GameState.abilityZones
      simp only [List.mem_append]
      simp only [Bool.and_eq_true] at h
      exact Or.inl (Or.inl (Or.inr (by simpa [List.contains_iff_mem] using h.1)))
    · split at h
      · simp only [Bool.and_eq_true, List.contains_iff_mem] at h
        unfold GameState.abilityZones
        simp only [List.mem_append]
        exact Or.inl (Or.inr h.1)
      · split at h
        · simp only [Bool.and_eq_true] at h
          unfold GameState.abilityZones
          simp only [List.mem_append]
          exact Or.inr (by simpa [List.contains_iff_mem] using h.1)
        · exact GameState.usesAbilitiesOf_mem h
  · exact GameState.usesAbilitiesOf_mem h

/-- The change an object goes through when an ability is used: it is exhausted if the cost says
so, and the use is noted (CR 371, 386). -/
def useOf (idx : Nat) (ex : Bool) (o : Object) : Object :=
  { o with exhausted := o.exhausted || ex, used := o.used ++ [idx] }

/-- The object an ability becomes on the Chain: it belongs to the player who used it (CR 337). -/
def abilityItem (card : CardId) (idx : Nat) (src : ObjId) (p : PlayerId) (ts : List ObjId) :
    Object :=
  { kind := .chainAbility card idx src, owner := p, controller := p, timestamp := ⟨0⟩,
    targets := ts }

/-- What an Add ability adds. -/
inductive ManaKind where
  /-- Energy. -/
  | energy (n : Nat)
  /-- Power of a domain. -/
  | power (d : Domain) (n : Nat)
  /-- Power of any domain. -/
  | any (n : Nat)
deriving DecidableEq, Repr

/-- The Pool after adding. -/
def ManaKind.add : ManaKind → RunePool → RunePool
  | .energy n, p => p.addEnergy n
  | .power d n, p => p.addPower d n
  | .any n, p => p.addAny n

/-- The effect is an Add of a fixed amount, to the player, with no restriction. -/
def manaKind (body : EffectDef) : Option ManaKind :=
  match body.choices, body.body with
  | [], .prim (.addEnergy .you (.const n) none) => some (.energy n)
  | [], .prim (.addPower .you (.const n) (some d) none) => some (.power d n)
  | [], .prim (.addPower .you (.const n) none none) => some (.any n)
  -- an Add that works only while a condition holds: it is used only then (`guardOk`)
  | [], .ifThen _ (.prim (.addEnergy .you (.const n) none)) .nop => some (.energy n)
  | [], .ifThen _ (.prim (.addPower .you (.const n) (some d) none)) .nop => some (.power d n)
  | [], .ifThen _ (.prim (.addPower .you (.const n) none none)) .nop => some (.any n)
  | _, _ => none

/-- The player can use the activated ability at place `idx` of the object `src`, with the payment
and the targets, in the Main Phase (CR 361, 363, 355-357). `open_` is whether the Chain is empty:
an ability that is not a Reaction can be used only then (CR 312, 813). -/
def activatable (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (pay : RunePool.Payment)
    (ts : List ObjId) (open_ : Bool) : Bool :=
  s.phase == .main &&
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      o.controller == p && s.abilityZoneOk p src idx &&
        match d.fullAbilities[idx]? with
        | some (.activated costs speed body limit) =>
          match costPlan costs with
          | some (ex, pc) =>
            if (manaKind body).isSome then false
            else
              (open_ || speed == .reaction) && (!ex || !o.exhausted) &&
                (match pc with
                  | some c => c.paidBy d.domains pay
                  | none => pay == ⟨0, []⟩) &&
                ((s.poolOf p).spend pay).any (fun pool => s.deflectOk p pool ts) &&
                (match limit with
                  | .unlimited => true
                  | .perTurn n => decide (o.used.count idx < n)) &&
                targetsOk s p src body.choices ts
          | none => false
        | _ => false
    | _, _ => false

/-- Use an activated ability (CR 361, 363): pay, exhaust the object if the cost says so, and put
the ability on the Chain with the objects chosen. -/
def applyActivate (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat)
    (pay : RunePool.Payment) (ts : List ObjId) : Option (GameState × List Event) :=
  match s.cardDef? src, (s.poolOf p).spend pay with
  | some d, some pool =>
    match d.fullAbilities[idx]? with
    | some (.activated costs _ _ _) =>
      (addObject (((s.modObj src (useOf idx (costExhausts costs))).setPool p pool))
        (abilityItem d.id idx src p ts) .chain).map
        (fun r => (r.1, [Event.activated p src idx]))
    | _ => none
  | _, _ => none

/-- The shape of an ability being used. -/
theorem applyActivate_cases {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {es : List Event}
    (h : applyActivate s p src idx pay ts = some (s', es)) :
    ∃ f pool item id', (∀ o, (f o).kind = o.kind ∧ (f o).owner = o.owner) ∧
      (s.poolOf p).spend pay = some pool ∧ item.kind.phys? = none ∧ item.owner = p ∧
        addObject ((s.modObj src f).setPool p pool) item .chain = some (s', id') ∧
          es = [Event.activated p src idx] := by
  unfold applyActivate at h
  cases hd : s.cardDef? src with
  | none => simp [hd] at h
  | some d =>
    cases hs : (s.poolOf p).spend pay with
    | none => simp [hd, hs] at h
    | some pool =>
      cases ha : d.fullAbilities[idx]? with
      | none => simp [hd, hs, ha] at h
      | some ab =>
        cases ab with
        | activated costs sp body lim =>
          simp only [hd, hs, ha, Option.map_eq_some_iff] at h
          obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨useOf idx (costExhausts costs), pool,
            abilityItem d.id idx src p ts, id', fun o => ⟨rfl, rfl⟩, rfl, rfl, rfl, hm, rfl⟩
        | passive _ _ => simp [hd, hs, ha] at h
        | replacement _ _ _ => simp [hd, hs, ha] at h
        | triggered _ _ _ => simp [hd, hs, ha] at h

/-- Using an ability keeps the game well formed. -/
theorem applyActivate_wf {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {es : List Event} (hwf : s.WF)
    (h : applyActivate s p src idx pay ts = some (s', es)) : s'.WF := by
  obtain ⟨f, pool, item, id', hf, -, -, -, hm, -⟩ := applyActivate_cases h
  have h1 : ((s.modObj src f).setPool p pool).WF :=
    (GameState.wf_modObj hwf src f).congr rfl rfl rfl rfl
  exact addObject_wf h1 hm

/-- Using an ability keeps the physical cards. -/
theorem applyActivate_physIds {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {es : List Event} (hwf : s.WF)
    (h : applyActivate s p src idx pay ts = some (s', es)) : s'.physIds.Perm s.physIds := by
  obtain ⟨f, pool, item, id', hf, -, hk, -, hm, -⟩ := applyActivate_cases h
  have h1 : ((s.modObj src f).setPool p pool).WF :=
    (GameState.wf_modObj hwf src f).congr rfl rfl rfl rfl
  have hp := addObject_physIds h1 hm hk
  have h2 : ((s.modObj src f).setPool p pool).physIds = (s.modObj src f).physIds := rfl
  rw [h2, GameState.physIds_modObj s src (fun o => (hf o).1)] at hp
  exact hp

/-- Using an ability keeps `OwnerOk`. -/
theorem applyActivate_ownerOk {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : applyActivate s p src idx pay ts = some (s', es)) : s'.OwnerOk := by
  obtain ⟨f, pool, item, id', hf, -, -, -, hm, -⟩ := applyActivate_cases h
  have h1 : ((s.modObj src f).setPool p pool).WF :=
    (GameState.wf_modObj hwf src f).congr rfl rfl rfl rfl
  have h2 : ((s.modObj src f).setPool p pool).OwnerOk :=
    (GameState.ownerOk_modObj hown src (fun o => (hf o).2)).congr rfl rfl
  exact addObject_ownerOk h1 h2 hm

/-- Using an ability changes nothing of the stack, the turn order, the phase, the result, the rules
or the cards. -/
theorem applyActivate_meta {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {es : List Event}
    (h : applyActivate s p src idx pay ts = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.pending = s.pending ∧ s'.cards = s.cards := by
  obtain ⟨f, pool, item, id', hf, -, -, -, hm, -⟩ := applyActivate_cases h
  have hs1 := addObject_sameMeta hm
  have hs2 := GameState.sameMeta_modObj s src f
  have c1 : s'.cards = (s.modObj src f).cards := by
    have := congrArg GameState.cards hs1
    exact this
  have c2 : (s.modObj src f).cards = s.cards := by
    have := congrArg GameState.cards hs2
    exact this
  exact ⟨hs1.config.trans hs2.config, hs1.turnOrder.trans hs2.turnOrder,
    hs1.phase.trans hs2.phase, hs1.result.trans hs2.result, hs1.pending.trans hs2.pending,
    c1.trans c2⟩

/-- The hands are as they were after an ability is used. -/
theorem applyActivate_hand {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {es : List Event}
    (h : applyActivate s p src idx pay ts = some (s', es)) (q : PlayerId) :
    s'.zone (.player q .hand) = s.zone (.player q .hand) := by
  obtain ⟨f, pool, item, id', hf, -, -, -, hm, -⟩ := applyActivate_cases h
  rw [addObject_zone_other hm (by simp)]
  show (s.modObj src f).zone _ = _
  exact GameState.zone_modObj s src f _

/-- A usable ability can be used. -/
theorem applyActivate_isSome {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {open_ : Bool}
    (h : activatable s p src idx pay ts open_ = true) :
    ∃ r, applyActivate s p src idx pay ts = some r := by
  unfold activatable at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases ho : s.obj? src with
  | none => simp [ho] at h
  | some o =>
    cases hd : s.cardDef? src with
    | none => simp [ho, hd] at h
    | some d =>
      simp only [ho, hd, Bool.and_eq_true] at h
      obtain ⟨-, h⟩ := h
      cases ha : d.fullAbilities[idx]? with
      | none => simp [ha] at h
      | some ab =>
        cases ab with
        | activated costs sp body lim =>
          simp only [ha] at h
          cases hp : costPlan costs with
          | none => simp [hp] at h
          | some pe =>
            obtain ⟨ex, pc⟩ := pe
            simp only [hp] at h
            by_cases hm : (manaKind body).isSome = true
            · simp [hm] at h
            simp only [hm, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h
            have hpool := h.1.1.2
            cases hs : (s.poolOf p).spend pay with
            | none => rw [hs] at hpool; simp at hpool
            | some pool =>
              unfold applyActivate
              simp only [hd, hs, ha]
              have hv : (Zone.chain).Valid s.playerCount ∧ Zone.chain.fits
                  (abilityItem d.id idx src p ts).owner = true :=
                ⟨Zone.valid_chain _, by simp [Zone.fits]⟩
              unfold addObject
              simp only [hv]
              exact ⟨_, rfl⟩
        | passive _ _ => simp [ha] at h
        | replacement _ _ _ => simp [ha] at h
        | triggered _ _ _ => simp [ha] at h

/-- What a usable ability is: an activated ability of an object the player controls, in the Main
Phase, with a payment that pays the cost and the Pool covers, and a legal pick of targets. -/
theorem activatable_spec {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {open_ : Bool}
    (h : activatable s p src idx pay ts open_ = true) :
    ∃ d costs sp body lim pc, s.phase = .main ∧ s.abilityZoneOk p src idx = true ∧
      s.cardDef? src = some d ∧
        d.fullAbilities[idx]? = some (Ability.activated costs sp body lim) ∧
        costPlan costs = some (costExhausts costs, pc) ∧
          (match pc with
            | some c => c.paidBy d.domains pay = true
            | none => pay = ⟨0, []⟩) ∧
            targetsOk s p src body.choices ts = true ∧ ∃ o, s.obj? src = some o ∧
              o.controller = p := by
  unfold activatable at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hph, h⟩ := h
  cases ho : s.obj? src with
  | none => simp [ho] at h
  | some o =>
    cases hd : s.cardDef? src with
    | none => simp [ho, hd] at h
    | some d =>
      simp only [ho, hd, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hctl, huse⟩, h⟩ := h
      cases ha : d.fullAbilities[idx]? with
      | none => simp [ha] at h
      | some ab =>
        cases ab with
        | activated costs sp body lim =>
          simp only [ha] at h
          cases hp : costPlan costs with
          | none => simp [hp] at h
          | some pe =>
            obtain ⟨ex, pc⟩ := pe
            simp only [hp] at h
            by_cases hm : (manaKind body).isSome = true
            · simp [hm] at h
            simp only [hm, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h
            have hex : costExhausts costs = ex := by simp [costExhausts, hp]
            refine ⟨d, costs, sp, body, lim, pc, hph, huse, rfl, ha, by rw [hex]; exact hp, ?_,
              h.2, o, rfl, hctl⟩
            cases pc with
            | none =>
              have := h.1.1.1.2
              simpa using this
            | some c => exact h.1.1.1.2
        | passive _ _ => simp [ha] at h
        | replacement _ _ _ => simp [ha] at h
        | triggered _ _ _ => simp [ha] at h

/-- The Spell is a Reaction (CR 813). -/
def reactSpell (s : GameState) (c : ObjId) : Bool :=
  (s.cardDef? c).any (·.hasKeyword .reaction)

/-- The card of the hand can be cast in answer to an item of the Chain: a Spell with Reaction
(CR 813). -/
def reactable (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (ts : List ObjId) : Bool :=
  castable s p c pay ts && reactSpell s c

/-- Every way the player can use an activated ability: each object they use abilities of, each
ability, each payment that pays its cost, and each pick of targets, that the Pool covers. -/
def legalActivates (s : GameState) (p : PlayerId) (open_ : Bool) : List Action :=
  (s.abilityZones p).flatMap
    (fun src =>
      match s.cardDef? src with
      | some d =>
        (List.range d.fullAbilities.length).flatMap (fun (idx : Nat) =>
          match d.fullAbilities[idx]? with
          | some (Ability.activated costs _ body _) =>
            (match costPlan costs with
              | some (_, some c) => c.payments d.domains
              | _ => [⟨0, []⟩]).flatMap (fun pay =>
              (([] :: (targetTuples s p src body.choices).filter
                  (fun ts => decide (ts ≠ []))).filter
                (fun ts => activatable s p src idx pay ts open_)).map
                (fun ts => ⟨.player p, .activate src idx pay ts⟩))
          | _ => [])
      | none => [])

/-- Every way the player can cast a Spell with Reaction from the hand. -/
def legalReactions (s : GameState) (p : PlayerId) : List Action :=
  (legalPlays s p).filter (fun a =>
    match a.kind with
    | .playCard c pay ts => reactable s p c pay ts
    | _ => false)

/-- The abilities listed are exactly the ones that can be used. -/
theorem mem_legalActivates (s : GameState) (p : PlayerId) (open_ : Bool) (a : Action) :
    a ∈ legalActivates s p open_ ↔ ∃ src idx pay ts,
      a = ⟨.player p, .activate src idx pay ts⟩ ∧
        activatable s p src idx pay ts open_ = true := by
  constructor
  · intro ha
    unfold legalActivates at ha
    simp only [List.mem_flatMap] at ha
    obtain ⟨src, -, ha⟩ := ha
    cases hd : s.cardDef? src with
    | none => simp [hd] at ha
    | some d =>
      simp only [hd, List.mem_flatMap, List.mem_range] at ha
      obtain ⟨idx, hidx, ha⟩ := ha
      cases hab : d.fullAbilities[idx]? with
      | none => simp [hab] at ha
      | some ab =>
        cases ab with
        | activated costs sp body lim =>
          simp only [hab, List.mem_flatMap, List.mem_map, List.mem_filter] at ha
          obtain ⟨pay, -, ts, ⟨-, hact⟩, rfl⟩ := ha
          exact ⟨src, idx, pay, ts, rfl, hact⟩
        | passive _ _ => simp [hab] at ha
        | replacement _ _ _ => simp [hab] at ha
        | triggered _ _ _ => simp [hab] at ha
  · rintro ⟨src, idx, pay, ts, rfl, hact⟩
    obtain ⟨d, costs, sp, body, lim, pc, hph, huse, hd, hab, hplan, hpay, hts, o, ho, hctl⟩ :=
      activatable_spec hact
    unfold legalActivates
    simp only [List.mem_flatMap]
    refine ⟨src, ?_, ?_⟩
    · exact GameState.abilityZoneOk_mem huse
    · simp only [hd, List.mem_flatMap, List.mem_range]
      refine ⟨idx, (List.getElem?_eq_some_iff.mp hab).1, ?_⟩
      simp only [hab, List.mem_flatMap, List.mem_map, List.mem_filter]
      refine ⟨pay, ?_, ts, ⟨?_, hact⟩, rfl⟩
      · rw [hplan]
        cases pc with
        | none =>
          have : pay = ⟨0, []⟩ := hpay
          simp [this]
        | some c => exact (Cost.mem_payments _ _ _).mpr hpay
      · by_cases hn : ts = []
        · subst hn
          exact List.mem_cons_self
        · refine List.mem_cons_of_mem _ ?_
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨(mem_targetTuples s p src body.choices ts).mpr hts, hn⟩

/-- A Spell that can be cast in answer to an item of the Chain: it can be cast, and has Reaction. -/
theorem reactable_spec {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} : reactable s p c pay ts = true ↔
      castable s p c pay ts = true ∧ reactSpell s c = true := by
  simp [reactable]

/-- The Reactions listed are exactly the Spells that can be cast in answer. -/
theorem mem_legalReactions (s : GameState) (p : PlayerId) (a : Action) :
    a ∈ legalReactions s p ↔ ∃ c pay ts, a = ⟨.player p, .playCard c pay ts⟩ ∧
      c ∈ s.zone (.player p .hand) ∧ reactable s p c pay ts = true := by
  unfold legalReactions
  simp only [List.mem_filter, mem_legalPlays]
  constructor
  · rintro ⟨⟨c, pay, ts, rfl, hc, hok⟩, hr⟩
    exact ⟨c, pay, ts, rfl, hc, hr⟩
  · rintro ⟨c, pay, ts, rfl, hc, hr⟩
    exact ⟨⟨c, pay, ts, rfl, hc, Or.inr (reactable_spec.mp hr).1⟩, hr⟩

/-- Use an ability, and put `new` on the stack in place of the frame that was answered. -/
def activateStep (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (pay : RunePool.Payment)
    (ts : List ObjId) (new : List Frame) : Option (GameState × List Event) :=
  (applyActivate s p src idx pay ts).map (fun r => ({ r.1 with pending := new }, r.2))

/-- Cast a Spell in answer to the Chain, and put `new` on the stack in place of the frame that was
answered. -/
def castStep (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (ts : List ObjId) (new : List Frame) : Option (GameState × List Event) :=
  (applyCast s p c pay ts).map (fun r => ({ r.1 with pending := new }, r.2))

/-- What using an ability with a new stack does. -/
theorem activateStep_cases {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : activateStep s p src idx pay ts new = some (s', es)) :
    ∃ s2 es2, applyActivate s p src idx pay ts = some (s2, es2) ∧
      s' = { s2 with pending := new } := by
  unfold activateStep at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
  simp only [Prod.mk.injEq] at hr
  exact ⟨s2, es2, hm, hr.1.symm⟩

/-- Using an ability keeps the game well formed. -/
theorem activateStep_wf {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {new : List Frame} {es : List Event}
    (hwf : s.WF) (h : activateStep s p src idx pay ts new = some (s', es)) : s'.WF := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  exact (applyActivate_wf hwf hm).congr rfl rfl rfl rfl

/-- Using an ability keeps the physical cards. -/
theorem activateStep_physIds {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {new : List Frame} {es : List Event}
    (hwf : s.WF) (h : activateStep s p src idx pay ts new = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  have h2 := applyActivate_physIds hwf hm
  exact h2

/-- Using an ability keeps `OwnerOk`. -/
theorem activateStep_ownerOk {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {new : List Frame} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (h : activateStep s p src idx pay ts new = some (s', es)) :
    s'.OwnerOk := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  exact (applyActivate_ownerOk hwf hown hm).congr rfl rfl

/-- Using an ability changes nothing of the turn order, the phase, the result, the rules or the
cards, and leaves the hands; the stack is `new`. -/
theorem activateStep_meta {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : activateStep s p src idx pay ts new = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.cards = s.cards ∧ s'.pending = new ∧
        ∀ q, s'.zone (.player q .hand) = s.zone (.player q .hand) := by
  obtain ⟨s2, es2, hm, rfl⟩ := activateStep_cases h
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := applyActivate_meta hm
  exact ⟨h1, h2, h3, h4, h6, rfl, fun q => applyActivate_hand hm q⟩

/-- A usable ability can be used, with any new stack. -/
theorem activateStep_isSome {s : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {open_ : Bool} {new : List Frame}
    (h : activatable s p src idx pay ts open_ = true) :
    ∃ r, activateStep s p src idx pay ts new = some r := by
  obtain ⟨r, hr⟩ := applyActivate_isSome h
  exact ⟨_, by unfold activateStep; rw [hr]; rfl⟩

/-- What casting a Spell with a new stack does. -/
theorem castStep_cases {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : castStep s p c pay ts new = some (s', es)) :
    ∃ s2 es2, applyCast s p c pay ts = some (s2, es2) ∧ s' = { s2 with pending := new } := by
  unfold castStep at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
  simp only [Prod.mk.injEq] at hr
  exact ⟨s2, es2, hm, hr.1.symm⟩

/-- Casting a Spell keeps the game well formed. -/
theorem castStep_wf {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} {new : List Frame} {es : List Event} (hwf : s.WF)
    (h : castStep s p c pay ts new = some (s', es)) : s'.WF := by
  obtain ⟨s2, es2, hm, rfl⟩ := castStep_cases h
  exact (applyCast_wf hwf hm).congr rfl rfl rfl rfl

/-- Casting a Spell keeps the physical cards. -/
theorem castStep_physIds {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} {new : List Frame} {es : List Event} (hwf : s.WF)
    (h : castStep s p c pay ts new = some (s', es)) : s'.physIds.Perm s.physIds := by
  obtain ⟨s2, es2, hm, rfl⟩ := castStep_cases h
  have h2 := applyCast_physIds hwf hm
  exact h2

/-- Casting a Spell keeps `OwnerOk`. -/
theorem castStep_ownerOk {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} {new : List Frame} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (h : castStep s p c pay ts new = some (s', es)) : s'.OwnerOk := by
  obtain ⟨s2, es2, hm, rfl⟩ := castStep_cases h
  exact (applyCast_ownerOk hwf hown hm).congr rfl rfl

/-- Casting a Spell changes nothing of the turn order, the phase, the result, the rules or the
cards; the stack is `new`. -/
theorem castStep_meta {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} {new : List Frame} {es : List Event}
    (h : castStep s p c pay ts new = some (s', es)) :
    s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.phase = s.phase ∧
      s'.result = s.result ∧ s'.cards = s.cards ∧ s'.pending = new := by
  obtain ⟨s2, es2, hm, rfl⟩ := castStep_cases h
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := applyCast_meta hm
  exact ⟨h1, h2, h3, h4, h6, rfl⟩

/-- A castable Spell of the hand can be cast, with any new stack. -/
theorem castStep_isSome {s : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} {new : List Frame} (hwf : s.WF) (hc : c ∈ s.zone (.player p .hand))
    (h : castable s p c pay ts = true) :
    ∃ r, castStep s p c pay ts new = some r := by
  obtain ⟨r, hr⟩ := applyCast_isSome hwf hc h
  exact ⟨_, by unfold castStep; rw [hr]; rfl⟩

/-! ### I9: the Chain is last in, first out (CR 340.1) -/

/-- **An ability goes on top of the Chain**: the new item is the head of the Chain zone, and the
items that were there are below it, in the same order. -/
theorem applyActivate_chain {s s' : GameState} {p : PlayerId} {src : ObjId} {idx : Nat}
    {pay : RunePool.Payment} {ts : List ObjId} {es : List Event}
    (h : applyActivate s p src idx pay ts = some (s', es)) :
    ∃ id', s'.zone .chain = id' :: s.zone .chain := by
  obtain ⟨f, pool, item, id', hf, -, -, -, hm, -⟩ := applyActivate_cases h
  obtain ⟨hz, hid, hs'⟩ := addObject_spec hm
  refine ⟨id', ?_⟩
  rw [hs', hid]
  show ((((s.modObj src f).setPool p pool).setZone .chain
    (Pos.top.insert ⟨_⟩ (((s.modObj src f).setPool p pool).zone .chain)))).zone .chain = _
  rw [GameState.zone_setZone_self]
  have : ((s.modObj src f).setPool p pool).zone .chain = s.zone .chain :=
    GameState.zone_modObj s src f _
  rw [this]
  rfl

/-- **A Spell goes on top of the Chain**: the new item is the head of the Chain zone, and the
items that were there are below it, in the same order. -/
theorem applyCast_chain {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {ts : List ObjId} {es : List Event} (h : applyCast s p c pay ts = some (s', es)) :
    ∃ id', s'.zone .chain = id' :: s.zone .chain := by
  obtain ⟨pool, s2, id', rep, -, hm, rfl, -⟩ := applyCast_cases h
  obtain ⟨src, dd, hs, o', ho', hdd⟩ := moveObj_spec_dst hm
  have hd2 : dd = .chain := by rw [hdd]; simp [Zone.normalize]
  have h2 := hs.zone_dst
  rw [hd2] at h2
  refine ⟨id', ?_⟩
  show (s2.zone .chain) = _
  rw [h2]
  rfl

/-- **The item that resolves is the one on top** (CR 340.1): the frames that resolve the Chain
finish the head of the Chain zone, whichever kind of item it is. -/
theorem resolveFrames_top {s : GameState} {item : ObjId} {more : List ObjId}
    (hc : s.zone .chain = item :: more) (rest : List Frame) :
    Frame.finishSpell item ∈ resolveFrames s rest := by
  unfold resolveFrames
  rw [hc]
  cases ho : s.obj? item with
  | none => simp [ho]
  | some o =>
    cases hd : s.cardDef? item with
    | some d => simp [ho, hd]
    | none =>
      simp only [ho, hd, itemFrames]
      split <;> simp

/-- **An item that has resolved leaves the Chain**: what is left is the Chain without it. If the
item could not be finished, nothing changes. -/
theorem finishItem_chain {s : GameState} (hwf : s.WF) (item : ObjId) :
    (finishItem s item).1.zone .chain = (s.zone .chain).erase item ∨
      (finishItem s item).1 = s := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, hc, hm, h⟩ | ⟨o, s2, -, hc, -, hr, h⟩
  · exact Or.inr h
  · left
    rw [h]
    obtain ⟨src, dd, hs⟩ := moveObj_spec hm
    have hsrc : src = .chain :=
      Option.some.inj (hs.locate.symm.trans
        (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hc) hc))
    have := hs.zone_src
    rw [hsrc] at this
    exact this
  · left
    rw [h]
    obtain ⟨z, hz, hid, hs'⟩ := removeObj_spec hr
    have hzc : z = .chain :=
      GameState.zone_unique hwf (GameState.zone_valid_of_mem hwf hc) hz hc hid
    rw [hs']
    subst hzc
    exact GameState.zone_setZone_self s _ _

/-- **Last in, first out** (CR 340.1): with the Chain `item :: more`, an item that resolves is
`item`, and what is left is `more`. -/
theorem finishItem_top_chain {s : GameState} (hwf : s.WF) {item : ObjId} {more : List ObjId}
    (hc : s.zone .chain = item :: more) :
    (finishItem s item).1.zone .chain = more ∨ (finishItem s item).1 = s := by
  have hnd : (item :: more).Nodup := hc ▸ GameState.zone_nodup_any hwf .chain
  rcases finishItem_chain hwf item with h | h
  · left
    rw [h, hc]
    simp
  · exact Or.inr h

end Riftbound

end
