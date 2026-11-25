module

public import Riftbound.Rules.Passive

/-!
# Deflect (CR 809)

Deflect X: an opponent who chooses the object with a spell or an ability pays X Power of any
domain more, as an additional cost. The picks of targets are legal only when the Pool covers it
(`deflectOk`); the Power is taken out of the Pool at the same time as the pick is made
(`paySurcharge`), whichever kind of answer chose the target: a Spell, an activated ability, or a
triggered ability.

Model decision: the player does not choose which Power pays. The Power of a domain goes first, in
the order of the domains, and Power of any domain last, so the flexible Power is kept.
-/

@[expose] public section

namespace Riftbound

namespace RunePool

/-- Take one Power out of the Pool, if there is one: Power of a domain first, Power of any domain
last. -/
def takeOne (p : RunePool) : RunePool :=
  if 0 < p.fury then { p with fury := p.fury - 1 }
  else if 0 < p.calm then { p with calm := p.calm - 1 }
  else if 0 < p.mind then { p with mind := p.mind - 1 }
  else if 0 < p.body then { p with body := p.body - 1 }
  else if 0 < p.chaos then { p with chaos := p.chaos - 1 }
  else if 0 < p.order then { p with order := p.order - 1 }
  else if 0 < p.any then { p with any := p.any - 1 }
  else p

/-- Take `n` Power out of the Pool, one at a time. -/
def takeN (p : RunePool) : Nat → RunePool
  | 0 => p
  | n + 1 => (p.takeOne).takeN n

/-- Taking one Power takes exactly one when there is some. -/
theorem total_takeOne {p : RunePool} (h : 0 < p.totalPower) :
    p.takeOne.total + 1 = p.total := by
  unfold takeOne
  unfold total totalPower at *
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> simp_all <;> omega

/-- Taking one Power leaves one less. -/
theorem totalPower_takeOne {p : RunePool} (h : 0 < p.totalPower) :
    p.takeOne.totalPower + 1 = p.totalPower := by
  have h1 := total_takeOne h
  have h2 : p.takeOne.energy = p.energy := by
    unfold takeOne
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
      (try split) <;> simp
  unfold total at h1
  omega

/-- **Taking `n` Power takes exactly `n`** when the Pool has that much. -/
theorem total_takeN : ∀ (n : Nat) (p : RunePool), n ≤ p.totalPower →
    (p.takeN n).total + n = p.total
  | 0, p, _ => by simp [takeN]
  | n + 1, p, h => by
    have h0 : 0 < p.totalPower := by omega
    have h1 := totalPower_takeOne h0
    have h2 := total_takeOne h0
    have h3 := total_takeN n p.takeOne (by omega)
    simp only [takeN]
    omega

end RunePool

/-- The objects an answer chooses. -/
def Action.targetsOf (a : Action) : List ObjId :=
  match a.kind with
  | .playCard _ _ ts _ _ _ => ts
  | .activate _ _ _ ts _ => ts
  | .putTrigger _ ts _ => ts
  | _ => []

/-- An answer that plays a card can have a printed exception to the Deflect cost. -/
def Action.spellSource (a : Action) : Option ObjId :=
  match a.kind with
  | .playCard c _ _ _ _ _ => some c
  | _ => none

namespace GameState

/-- The X of the Deflect of an object: its card prints it, or an Equipment gives it. A Deflect with
no number is Deflect 1 (CR 809). -/
def deflectOf (s : GameState) (u : ObjId) : Nat :=
  let amount (i : KeywordInst) : Nat :=
    if i.keyword == .deflect then (match i.arg with | .amount n => n | _ => 1) else 0
  (match s.cardDef? u with
    | some d => (d.keywords.map amount).sum
    | none => 0) + ((s.grantedKws u).map amount).sum

/-- The Power the player pays more for choosing the objects. It may be waived by the spell
or by a Battlefield for objects there (CR 809). -/
def deflectCost (s : GameState) (p : PlayerId) (ts : List ObjId)
    (spell : Option ObjId := none) : Nat :=
  if spell.any (fun c => (s.activeMods c).contains .ignoreDeflectSpell) then 0
  else
    (ts.map (fun t =>
      if s.passiveSources.contains t && (s.obj? t).any (·.controller != p) &&
          !((s.obj? t).bind (·.loc)).any
            (fun bf => (s.activeMods bf).contains .ignoreDeflectHere) then
        s.deflectOf t
      else 0)).sum

/-- The Pool covers what the player pays more for choosing the objects. -/
def deflectOk (s : GameState) (p : PlayerId) (pool : RunePool) (ts : List ObjId)
    (spell : Option ObjId := none) : Bool :=
  decide (s.deflectCost p ts spell ≤ pool.totalPower)

/-- A qualifying spell gets each Battlefield's Power discount once, even when it chooses
several friendly Units there (CR 355-356). -/
def choosePowerCut (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId) : Nat :=
  if (s.cardDef? c).any (·.hasType .spell) then
    let fields := ts.filterMap (fun t =>
      if (s.cardDef? t).any (·.hasType .unit) then
        ((s.obj? t).filter (·.controller == p)).bind (·.loc)
      else none)
    (fields.eraseDups.flatMap (fun bf => (s.activeMods bf).filterMap (fun
      | .friendlyTargetPowerCut n => some n
      | _ => none))).sum
  else 0

/-- Deflect is part of the combined payment when a target-based Power discount applies
to the spell, including when the spell is played from Hidden (CR 356.4.d, 809). -/
def deflectInPayment (s : GameState) (p : PlayerId) (a : Action) : Bool :=
  match a.kind with
  | .playCard c _ ts _ _ _ => s.choosePowerCut p c ts != 0
  | .activate c idx _ ts _ =>
    s.choosePowerCut p c ts != 0 &&
      (match (s.cardDef? c).bind (fun d => d.fullAbilities[idx]?) with
      | some (.activated costs _ _ _) => costs.contains .fromHidden
      | _ => false)
  | _ => false

/-- Pay what choosing the objects of an answer costs more (CR 809): `s2` is the state the answer
leads to, and the objects are looked at as they were in `s`. -/
def paySurcharge (s : GameState) (a : Action) (s2 : GameState) : GameState :=
  match a.actor with
  | .player p =>
    if s.deflectInPayment p a then s2
    else s2.setPool p ((s2.poolOf p).takeN (s.deflectCost p a.targetsOf a.spellSource))
  | _ => s2

/-- Paying the surcharge changes nothing, or the Pool of a player. -/
theorem paySurcharge_cases (s : GameState) (a : Action) (s2 : GameState) :
    paySurcharge s a s2 = s2 ∨ ∃ p pool, paySurcharge s a s2 = s2.setPool p pool := by
  unfold paySurcharge
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl rfl

/-- `s3` is `s2`, or `s2` with the Pool of a player replaced: the change that paying a surcharge
makes. -/
def PoolStep (s2 s3 : GameState) : Prop :=
  s3 = s2 ∨ ∃ (q : PlayerId) (pool : RunePool), s3 = s2.setPool q pool

/-- A change of a Pool keeps the game well formed. -/
theorem PoolStep.wf {s2 s3 : GameState} (h : PoolStep s2 s3) (hw : s2.WF) : s3.WF := by
  rcases h with rfl | ⟨q, pool, rfl⟩
  · exact hw
  · exact hw.congr rfl rfl rfl rfl

/-- A change of a Pool keeps the physical cards. -/
theorem PoolStep.physIds_eq {s2 s3 : GameState} (h : PoolStep s2 s3) :
    s3.physIds = s2.physIds := by
  rcases h with rfl | ⟨q, pool, rfl⟩ <;> rfl

/-- A change of a Pool keeps `OwnerOk`. -/
theorem PoolStep.ownerOk {s2 s3 : GameState} (h : PoolStep s2 s3) (ho : s2.OwnerOk) :
    s3.OwnerOk := by
  rcases h with rfl | ⟨q, pool, rfl⟩
  · exact ho
  · exact ho.congr rfl rfl

/-- A change of a Pool keeps the stack. -/
theorem PoolStep.pending_eq {s2 s3 : GameState} (h : PoolStep s2 s3) :
    s3.pending = s2.pending := by
  rcases h with rfl | ⟨q, pool, rfl⟩ <;> rfl

/-- Paying the surcharge is a change of a Pool. -/
theorem paySurcharge_poolStep (s : GameState) (a : Action) (s2 : GameState) :
    PoolStep s2 (paySurcharge s a s2) := paySurcharge_cases s a s2

/-- Choosing no object costs no more. -/
theorem deflectCost_nil (s : GameState) (p : PlayerId) : s.deflectCost p [] = 0 := rfl

end GameState

end Riftbound

end
