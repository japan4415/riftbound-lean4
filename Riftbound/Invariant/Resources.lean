module

public import Riftbound.Invariant.Turn

/-!
# Resources

The accounting of the Rune Pool (invariant I8, roadmap.md): an Add ability adds exactly one resource
and no more, a payment takes exactly what it says (`RunePool.total_spend`), and the Pool is empty at
the start of the Main Phase and at the end of the turn (CR 167). The Pool holds natural numbers, so
it cannot be negative.
-/

@[expose] public section

namespace Riftbound

/-- **The Rune Pool is empty when the Main Phase starts** (CR 167): every player's Pool. -/
theorem microStep_main_pools0 {s s' : GameState} {es : List Event} {rest : List Frame}
    (hp : s.pending = .phase .main :: rest) (h : microStep0 s = some (s', es)) (p : PlayerId) :
    s'.poolOf p = RunePool.empty := by
  unfold microStep0 at h
  rw [hp] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp [GameState.poolOf, RunePool.empty]

/-- **The Rune Pool is empty when the Main Phase starts** (CR 167): every player's Pool. -/
theorem microStep_main_pools {s s' : GameState} {es : List Event} {rest : List Frame}
    (hp : s.pending = .phase .main :: rest) (h : microStep s = some (s', es)) (p : PlayerId) :
    s'.poolOf p = RunePool.empty := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  obtain ⟨q, hq⟩ := withTriggers_pending s2 es
  have h2 := microStep_main_pools0 hp h0 p
  rw [hq]
  exact h2

/-- **The Rune Pool is empty at the end of the turn** (CR 167, 317.2). -/
theorem microStep_ending_pools0 {s s' : GameState} {es : List Event} {rest : List Frame}
    (hp : s.pending = .phase .ending :: rest) (h : microStep0 s = some (s', es)) (p : PlayerId) :
    s'.poolOf p = RunePool.empty := by
  unfold microStep0 at h
  rw [hp] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp [GameState.poolOf, RunePool.empty]

/-- **The Rune Pool is empty at the end of the turn** (CR 167, 317.2). -/
theorem microStep_ending_pools {s s' : GameState} {es : List Event} {rest : List Frame}
    (hp : s.pending = .phase .ending :: rest) (h : microStep s = some (s', es)) (p : PlayerId) :
    s'.poolOf p = RunePool.empty := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  obtain ⟨q, hq⟩ := withTriggers_pending s2 es
  have h2 := microStep_ending_pools0 hp h0 p
  rw [hq]
  exact h2

/-- **An Add ability adds exactly one resource** (I8) (CR 164.2, 430): the player's Pool grows by
one, Energy or Power of the Rune's domain, and every other Pool stays. -/
theorem applyRune_adds_one {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (h : applyRune s p c ab = some (s', es)) :
    (s'.poolOf p).total = (s.poolOf p).total + 1 ∧
      ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  cases ab with
  | exhaust =>
    obtain ⟨h1, h2⟩ := applyRune_exhaust_pool h
    exact ⟨by rw [h1, RunePool.total_addEnergy], h2⟩
  | recycle =>
    obtain ⟨d, h1, h2⟩ := applyRune_recycle_pool h
    exact ⟨by rw [h1, RunePool.total_addPower], h2⟩

/-- **Playing a card pays exactly its cost** (I8) (CR 356, 357, 445): the Pool of the player is
smaller by the total of the card's cost, or of its cost with an additional cost (Accelerate), and no
other player's Pool changes. -/
theorem applyPlay_pays_cost {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {es : List Event} (hp : playable s p c pay = true)
    (h : applyPlay s p c pay = some (s', es)) :
    ∃ d cost c', s.cardDef? c = some d ∧ s.effCost p c d = some cost ∧
      c' ∈ d.playCosts cost ∧
      (s'.poolOf p).total + c'.total = (s.poolOf p).total ∧
      ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  obtain ⟨o, d, cost, pool, -, -, hd, -, -, hc, hpaid, hpool⟩ := playable_spec hp
  obtain ⟨pool', hpool', hs', hq⟩ := applyPlay_pool h
  rw [hpool] at hpool'
  cases hpool'
  obtain ⟨c', hc', h2⟩ := CardDef.paysFor_total hpaid
  refine ⟨d, cost, c', hd, hc, hc', ?_, hq⟩
  rw [hs']
  have h1 := RunePool.total_spend hpool
  omega

/-- **A Unit that is played enters exhausted** (CR 359). -/
theorem applyPlay_unit_exhausted {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {es : List Event} {d : CardDef}
    (h : applyPlay s p c pay = some (s', es)) (hd : s.cardDef? c = some d)
    (hu : d.hasType .unit = true) (hr : s.readyNow p c d = false)
    (hx : s.paidExtra p c d pay = false) :
    ∃ id', es = [Event.moved c id' (.player p .base)] ∧
      ∀ o, s'.obj? id' = some o → o.exhausted = true := by
  obtain ⟨id', hes, hex⟩ := applyPlay_events h
  exact ⟨id', hes, hex d hd hu hr hx⟩

/-- **Casting a Spell pays exactly its cost** (I8) (CR 356, 357, 445): the Pool of the player is
smaller by the total of the card's cost, or of its cost with an additional cost (Repeat), and no
other player's Pool changes. -/
theorem applyCast_pays_cost {s s' : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {targets : List ObjId} {es : List Event}
    (hp : castable s p c pay targets = true)
    (h : applyCast s p c pay targets = some (s', es)) :
    ∃ d cost c', s.cardDef? c = some d ∧ s.effCost p c d = some cost ∧
      c' ∈ d.playCosts cost ∧
      (s'.poolOf p).total + c'.total = (s.poolOf p).total ∧
      ∀ q, q ≠ p → s'.poolOf q = s.poolOf q := by
  obtain ⟨o, d, cost, pool, -, -, hd, -, -, hc, hpaid, hpool⟩ := castable_spec hp
  obtain ⟨pool', hpool', hs', hq⟩ := applyCast_pool h
  rw [hpool] at hpool'
  cases hpool'
  obtain ⟨c', hc', h2⟩ := CardDef.paysFor_total hpaid
  refine ⟨d, cost, c', hd, hc, hc', ?_, hq⟩
  rw [hs']
  have h1 := RunePool.total_spend hpool
  omega

/-- **The Chain resolves when everyone has passed** (CR 311-313, 340): the last player to pass
hands the Chain to `resolveChain`. -/
theorem chainPass_last_resolves0 {s s' : GameState} {p : PlayerId} {n : Nat} {rest : List Frame}
    {es : List Event} (hp : s.pending = .chainPass p n :: rest) (hn : s.playerCount ≤ n + 1)
    (h : applyFrame0 s ⟨.player p, .pass⟩ = some (s', es)) :
    s'.pending = .resolveChain :: rest ∧ es = [] := by
  unfold applyFrame0 at h
  rw [hp] at h
  simp only [show ¬ n + 1 < s.playerCount by omega, ite_false, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- **The Chain resolves when everyone has passed** (CR 311-313, 340): the last player to pass
hands the Chain to `resolveChain`. -/
theorem chainPass_last_resolves {s s' : GameState} {p : PlayerId} {n : Nat} {rest : List Frame}
    {es : List Event} (hp : s.pending = .chainPass p n :: rest) (hn : s.playerCount ≤ n + 1)
    (h : applyFrame s ⟨.player p, .pass⟩ = some (s', es)) :
    s'.pending = .resolveChain :: rest := by
  obtain ⟨s2, es2, s3, h0, h3, rfl, -⟩ := applyFrame_cases h
  obtain ⟨hpend, rfl⟩ := chainPass_last_resolves0 hp hn h0
  simpa [extraEvents, withTriggers_nil, h3.pending_eq] using hpend

/-- **A Spell that has resolved goes to its owner's Trash** (CR 359.3.d). -/
theorem finishItem_trash {s : GameState} {item : ObjId} {o : Object}
    (ho : s.obj? item = some o) (hc : item ∈ s.zone .chain)
    (hk : ∀ card idx src, o.kind ≠ .chainAbility card idx src)
    (hm : ∃ r, moveObj s item (.player o.owner .trash) = some r) :
    ∃ id', (finishItem s item).2 = [Event.moved item id' (.player o.owner .trash)] ∧
      id' ∈ (finishItem s item).1.zone (.player o.owner .trash) := by
  obtain ⟨⟨s2, id'⟩, hm⟩ := hm
  have hf : finishItem s item = (s2, [Event.moved item id' (.player o.owner .trash)]) := by
    unfold finishItem
    simp only [ho, hc, ite_true]
    cases hkd : o.kind with
    | card ph cd => simp [hm]
    | token cd => simp [hm]
    | chainAbility card idx src => exact absurd hkd (hk card idx src)
  refine ⟨id', by rw [hf], ?_⟩
  rw [hf]
  obtain ⟨src, d, hs, o', ho', hdd⟩ := moveObj_spec_dst hm
  have hoo : o' = o := Option.some.inj (ho'.symm.trans ho)
  have h2 := hs.id'_mem
  have hd2 : d = .player o.owner .trash := by
    rw [hdd, hoo]; simp [Zone.normalize, Zone.isBoard]
  rw [hd2] at h2
  exact h2

/-- **A Spell on the Chain carries the objects chosen when it was cast** (CR 355): the object that
`applyCast` puts on the Chain has exactly the targets of the action. -/
theorem applyCast_targets {s s' : GameState} {p : PlayerId} {c : ObjId} {pay : RunePool.Payment}
    {targets : List ObjId} {es : List Event} (h : applyCast s p c pay targets = some (s', es)) :
    ∃ id', es = [Event.moved c id' .chain] ∧
      ∀ o, s'.obj? id' = some o → o.targets = targets := by
  obtain ⟨pool, s2, id', rep, -, -, rfl, hes⟩ := applyCast_cases h
  refine ⟨id', hes, fun o ho => ?_⟩
  rw [GameState.obj?_modObj] at ho
  simp only [ite_true] at ho
  cases hx : (s2.setPool p pool).obj? id' with
  | none => rw [hx] at ho; simp at ho
  | some o0 =>
    rw [hx] at ho
    simp only [Option.map_some, Option.some.injEq] at ho
    subst ho
    rfl

/-- **The targets of a Spell are objects in play** (CR 355), or Spells on the Chain: a Spell that
can be cast with some targets has all of them there. -/
theorem castable_targets_inPlay {s : GameState} {p : PlayerId} {c : ObjId}
    {pay : RunePool.Payment} {targets : List ObjId} (h : castable s p c pay targets = true) :
    ∀ t ∈ targets, t ∈ s.inPlay ∨ t ∈ s.zone .chain := by
  obtain ⟨d, e, -, -, hok⟩ := castable_targets h
  exact targetsOk_mem_inPlay hok

/-- **A Spell resolves with the targets it was cast with** (CR 340, 355): the effect is run with
the chosen objects as its slots, and the Spell goes to the Trash when the effect is done. -/
theorem resolveFrames_slots {s : GameState} {rest : List Frame} {item : ObjId} {more : List ObjId}
    {o : Object} {d : CardDef} (hc : s.zone .chain = item :: more) (ho : s.obj? item = some o)
    (hd : s.cardDef? item = some d) :
    resolveFrames s rest =
      .run o.controller item { slots := o.targets.map Value.obj }
        (match d.spellEffect with
          | some e => if o.paid then .cons e.body (.cons e.body .nil) else .cons e.body .nil
          | none => .nil) :: .finishSpell item :: rest := by
  unfold resolveFrames
  rw [hc]
  simp only [ho, hd]
  rfl

end Riftbound

end
