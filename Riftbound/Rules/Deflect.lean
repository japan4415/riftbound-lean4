module

public import Riftbound.Rules.Passive

/-!
# Deflect (CR 809)

Deflect X: an opponent who chooses the object with a spell or an ability pays X Power of any
domain more, as an additional cost. The picks of targets are legal only when the Pool covers it
(`deflectOk`); the Power is taken out of the Pool at the same time as the pick is made
(`paySurcharge`), whichever kind of answer chose the target: a Spell, an activated ability, or a
triggered ability.

Direct Spells can declare exact sources for a separate surcharge. Its canonical allocation
spends domain Power first and flexible Power last. Other answers still use the canonical
allocation when their cost does not include Deflect in an ordinary payment.
-/

@[expose] public section

namespace Riftbound

namespace RunePool

/-- Take one Power out of the Pool, if there is one: Power of a domain first, Power of any domain
last. -/
def takeOne (p : RunePool) : RunePool :=
  (PowerBucket.all.findSome? (fun bucket => p.takeBucket bucket 1)).getD p

/-- Take `n` Power out of the Pool, one at a time. -/
def takeN (p : RunePool) : Nat → RunePool
  | 0 => p
  | n + 1 => (p.takeOne).takeN n

private theorem takeOne_paid {p : RunePool} (available : 0 < p.totalPower) :
    ∃ bucket, p.takeBucket bucket 1 = some p.takeOne := by
  unfold takeOne
  cases chosen : PowerBucket.all.findSome? (fun bucket => p.takeBucket bucket 1) with
  | some reduced =>
    obtain ⟨bucket, _, paid⟩ := List.exists_of_findSome?_eq_some chosen
    exact ⟨bucket, paid⟩
  | none =>
    have allEmpty (bucket : PowerBucket) : p.powerIn bucket < 1 :=
      (p.takeBucket_eq_none bucket 1).mp
        (List.findSome?_eq_none_iff.mp chosen bucket (PowerBucket.mem_all bucket))
    have fury := allEmpty (.domain .fury)
    have calm := allEmpty (.domain .calm)
    have mind := allEmpty (.domain .mind)
    have body := allEmpty (.domain .body)
    have chaos := allEmpty (.domain .chaos)
    have order := allEmpty (.domain .order)
    have flexible := allEmpty .flexible
    simp only [powerIn, get, totalPower] at *
    omega

/-- Taking one Power takes exactly one when there is some. -/
theorem total_takeOne {p : RunePool} (h : 0 < p.totalPower) : p.takeOne.total + 1 = p.total := by
  obtain ⟨_, paid⟩ := takeOne_paid h
  exact total_takeBucket paid

/-- Taking one Power leaves one less. -/
theorem totalPower_takeOne {p : RunePool} (h : 0 < p.totalPower) :
    p.takeOne.totalPower + 1 = p.totalPower := by
  obtain ⟨_, paid⟩ := takeOne_paid h
  exact totalPower_takeBucket paid

/-- The canonical deduction can always be witnessed by an exact source allocation. -/
theorem takeN_realizesBuckets : ∀ (n : Nat) (p : RunePool), n ≤ p.totalPower →
    ∃ sources : List PowerBucket, sources.length = n ∧ p.takeBuckets sources = some (p.takeN n)
  | 0, p, _ => ⟨[], rfl, rfl⟩
  | n + 1, p, budget => by
    have available : 0 < p.totalPower := by omega
    obtain ⟨first, used⟩ := takeOne_paid available
    have remaining := totalPower_takeBucket used
    obtain ⟨sources, length, paid⟩ := takeN_realizesBuckets n p.takeOne (by omega)
    exact ⟨first :: sources, by simp [length], by simp [takeN, takeBuckets, used, paid]⟩

/-- **Taking `n` Power takes exactly `n`** when the Pool has that much. -/
theorem total_takeN (n : Nat) (p : RunePool) (budget : n ≤ p.totalPower) :
    (p.takeN n).total + n = p.total := by
  obtain ⟨sources, length, paid⟩ := takeN_realizesBuckets n p budget
  simpa only [length] using total_takeBuckets paid

end RunePool

/-- The objects an answer chooses. -/
def Action.targetsOf (a : Action) : List ObjId :=
  match a.kind with
  | .playCard _ _ ts _ _ _ => ts
  | .activate _ _ _ ts _ _ _ _ => ts
  | .putTrigger _ ts _ => ts
  | _ => []

/-- An answer that plays a card can have a printed exception to the Deflect cost. -/
def Action.spellSource (a : Action) : Option ObjId :=
  match a.kind with
  | .playCard c _ _ _ _ _ => some c
  | _ => none

namespace GameState

/-- The total active Deflect of an object. A Deflect without a number is Deflect 1 (CR 809). -/
def deflectOf (s : GameState) (u : ObjId) : Nat :=
  let amount (i : KeywordInst) : Nat :=
    if i.keyword == .deflect then (match i.arg with | .amount n => n | _ => 1) else 0
  ((s.activeKeywords u).map amount).sum

/-- The Deflect surcharge for the entire spell or ability. Heisho waives it when any target
is there (CR 766-767, 809). -/
def deflectCost (s : GameState) (p : PlayerId) (ts : List ObjId)
    (spell : Option ObjId := none) : Nat :=
  if spell.any (fun c => (s.activeMods c).contains .ignoreDeflectSpell) ||
      ts.any (fun t => (s.zone .battlefieldZone).contains t &&
        ((s.obj? t).bind (·.loc)).any (fun bf => (s.activeMods bf).contains .ignoreDeflectHere)) then 0
  else
    (ts.map (fun t =>
      if s.passiveSources.contains t && (s.obj? t).any (fun o => !s.config.mode.sameSide p o.controller) then
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
        ((s.obj? t).filter (fun o => s.config.mode.sameSide p o.controller)).bind (·.loc)
      else none)
    (fields.eraseDups.flatMap (fun bf => (s.activeMods bf).filterMap (fun
      | .friendlyTargetPowerCut n => some n
      | _ => none))).sum
  else 0

/-- The Power reductions for a card play, from its targets and effects of the turn (CR 356.4). -/
def playPowerCut (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId) : Nat :=
  s.choosePowerCut p c ts + (s.nextCardDiscount p).2

/-- Deflect is part of the combined payment when a target-based Power discount applies
to the spell, including when the spell is played from Hidden (CR 356.4.d, 809). -/
def deflectInPayment (s : GameState) (p : PlayerId) (a : Action) : Bool :=
  match a.kind with
  | .putTrigger .. =>
    match s.pending with
    | .triggerOrder _ _ _ _ (some _) :: _ => true
    | _ => false
  | .playCard c _ ts _ _ _ => s.playPowerCut p c ts != 0
  | .activate c idx _ ts _ _ _ _ =>
    s.playPowerCut p c ts != 0 &&
      (match (s.cardDef? c).bind (fun d => d.fullAbilities[idx]?) with
      | some (.activated costs _ _ _) => costs.contains .fromHidden
      | _ => false)
  | _ => false

/-- The surcharge paid separately from a direct Spell's printed and additional costs. -/
def separateSpellDeflectCost (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId) : Nat :=
  if (s.cardDef? c).any (·.hasType .spell) && s.playPowerCut p c ts == 0 then
    s.deflectCost p ts (some c)
  else 0

/-- Exchange the canonical allocation for its named sources when describing a declaration. -/
def spellDeflectSources (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId)
    (pay : RunePool.Payment) (pick : SpellPick) : Option (List PowerBucket) := do
  let amount := s.separateSpellDeflectCost p c ts
  if amount == 0 then none else
    let pool ← s.spendFor p false pay (spell := true)
    if pool.totalPower < amount then none else
      let after := pool.takeN amount
      some (pick.deflectPayment.getD (PowerBucket.all.flatMap (fun source =>
        List.replicate (pool.powerIn source - after.powerIn source) source)))

/-- Offer each affordable alternative to the canonical allocation for a direct Spell's
separate Deflect cost. The canonical choice already has the ordinary input form. -/
def spellDeflectPicks (s : GameState) (p : PlayerId) (c : ObjId)
    (targets : List ObjId) (pay : RunePool.Payment) (pick : SpellPick) : List SpellPick :=
  let amount := s.separateSpellDeflectCost p c targets
  pick :: (if amount == 0 then [] else
    match s.spendFor p false pay (spell := true) with
    | some pool =>
      let canonical := pool.takeN amount
      ((pool.allocatedPowerPayments amount).filter
        (fun sources => pool.takeBuckets sources != some canonical)).map
        (SpellPick.withDeflectPayment pick)
    | none => [])

/-- The ordinary submission names the canonical separate payment. -/
theorem mem_spellDeflectPicks_base (s : GameState) (p : PlayerId) (c : ObjId)
    (targets : List ObjId) (pay : RunePool.Payment) (pick : SpellPick) :
    pick ∈ s.spellDeflectPicks p c targets pay pick :=
  List.mem_cons_self

/-- The separate surcharge uses any recorded sources and otherwise its canonical allocation. -/
def paidDeflectPool (pool : RunePool) (a : Action) (amount : Nat) : RunePool :=
  let explicitSources := match a.kind with
    | .playCard _ _ _ _ _ pick => pick.deflectPayment
    | _ => none
  let paid := (explicitSources.bind pool.takeBuckets).getD (pool.takeN amount)
  pool.recordDeflectDebit paid

/-- Pay what choosing the objects of an answer costs more (CR 809): `s2` is the state the answer
leads to, and the objects are looked at as they were in `s`. -/
def paySurcharge (s : GameState) (a : Action) (s2 : GameState) : GameState :=
  match a.actor with
  | .player p =>
    match a.kind with
    | .standardMove _ _ pay =>
      if pay == Cost.zero then s2
      else ((s2.spendSymbols p pay false).map (s2.setPool p)).getD s2
    | _ =>
      if s.deflectInPayment p a then s2
      else s2.setPool p (paidDeflectPool (s2.poolOf p) a (s.deflectCost p a.targetsOf a.spellSource))
  | _ => s2

/-- Paying the surcharge changes nothing, or the Pool of a player. -/
theorem paySurcharge_cases (s : GameState) (a : Action) (s2 : GameState) :
    paySurcharge s a s2 = s2 ∨ ∃ p pool, paySurcharge s a s2 = s2.setPool p pool := by
  unfold paySurcharge
  split
  · rename_i p _
    split
    · rename_i _ _ pay _
      split
      · exact Or.inl rfl
      · cases h : s2.spendSymbols p pay false with
        | none => exact Or.inl rfl
        | some pool => exact Or.inr ⟨p, pool, rfl⟩
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
