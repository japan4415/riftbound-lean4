module

public import Riftbound.Rules.Battlefield

/-!
# Combat

A Showdown at a Battlefield where the Units of two players are (CR 464) is a Combat. The player who
made the Battlefield Contested is the Attacker, the other the Defender (CR 466). When everyone has
passed in the Showdown there is Combat Damage (CR 467): each side adds up the Might of its Units
(an Attacker also Assault X, a Defender also Shield X) and assigns that much damage to the Units of
the other side, the Attacker first; the damage is dealt when both have assigned (CR 467.2.c.1).
Then the Combat Cleanup (CR 468.1, 324): the Units with lethal damage die, every Unit is healed,
the Attacker's Units are Recalled if a Defender's Unit is left, and the Battlefield goes to the
player whose Units are alone there, who Scores it by Conquer (CR 468.5).

**Assigning damage.** The assignment is a decision made one Unit at a time: the player says in
which order the Units of the other side are to be given lethal damage, Tank Units first (CR 815).
The damage then goes down that order (`greedy`): each Unit gets what it needs to die, and the last
one gets all that is left. `greedy_spec` shows that every such assignment satisfies the rules of
the rules (CR 467.2.c), written independently of the way the engine asks (`AssignOk`).

**Not yet:** Stun (CR 424), Backline (CR 826) in milestone M8b, Recall of Gear and of Permanents
on another player's Base (CR 323.6), the Staged Combat (CR 323.8-323.9), and more than two
players.
-/

@[expose] public section

namespace Riftbound

namespace GameState

/-- The Might of an object, counted for damage: a negative Might counts as 0 (CR 143.2.c). -/
def mightEff (s : GameState) (u : ObjId) : Nat := ((s.mightNow u).map Might.eff).getD 0

/-- The Unit has the passive ability that says it deals no combat damage. -/
def noCombatDamage (s : GameState) (u : ObjId) : Bool :=
  (s.activeMods u).contains .noCombatDamage ||
  -- another unit says the units it names deal none (Vilemaw)
  s.inPlay.any (fun g =>
    match s.obj? g, s.obj? u with
    | some og, some o =>
      (s.cardDef? g).any (fun d => d.fullAbilities.any (fun ab =>
        match ab with
        | Ability.passive .always mods =>
          mods.any (fun m => match m with
            | .noCombatDamageFor (.pick .all side place fs) =>
              side.admits og.controller o && ((s.placeObjs g place).getD []).contains u &&
                FilterList.holds s g {} u fs == some true
            | _ => false)
        | _ => false))
    | _, _ => false)

/-- The Might a Unit adds to the damage of its side: Assault X while attacking (CR 807), Shield X
while defending (CR 814). -/
def combatMight (s : GameState) (u : ObjId) (attacking : Bool) : Nat :=
  if ((s.obj? u).map (·.stunned)).getD false || s.noCombatDamage u then 0
  else s.mightEff u + (if attacking then s.kwAmount u .assault else s.kwAmount u .shield)

/-- The damage a side assigns: the sum of the Might of its Units at the Battlefield (CR 467.2). -/
def combatTotal (s : GameState) (bf : ObjId) (att side : PlayerId) : Nat :=
  ((s.unitsOf side bf).map (fun u => s.combatMight u (decide (side = att)))).sum

/-- The Units of the other side at the Battlefield: those the damage of `side` goes to. -/
def foes (s : GameState) (bf : ObjId) (side : PlayerId) : List ObjId :=
  (s.unitsAt bf).filter (fun u => !s.isControlledBy side u)

/-- The damage a Unit needs to be killed: what is missing to its Might, and at least 1 if it has no
damage, because lethal damage is not 0 (CR 142.4.b). -/
def need (s : GameState) (u : ObjId) : Nat :=
  let d := ((s.obj? u).map (·.damage)).getD 0
  -- any amount of the damage of a side kills, while a passive ability of it says so
  if ((s.obj? u).map (fun o => s.anyDamageKills o.controller)).getD false then
    (if d = 0 then 1 else 0)
  else max (s.mightEff u - d) (if d = 0 then 1 else 0)

/-- Whether Combat began at the Battlefield, or two sides are present in a constructed state. -/
def isCombat (s : GameState) (bf : ObjId) : Bool :=
  (s.combat.any (·.battlefield == bf)) ||
    decide (2 ≤ (s.players.filter (fun p => !(s.unitsOf p bf).isEmpty)).length)

/-- The Attacker of a Combat at the Battlefield: the player who made it Contested (CR 466). -/
def attackerAt (s : GameState) (bf : ObjId) : PlayerId :=
  ((s.combat.filter (·.battlefield == bf)).map (·.attacker)).getD
    (((s.obj? bf).bind (·.contested)).getD (s.active.getD ⟨0⟩))

/-- The Defender designated at the start of this Combat (CR 466.2.c.2). -/
def defenderAt (s : GameState) (bf : ObjId) (att : PlayerId) : PlayerId :=
  ((s.combat.filter (·.battlefield == bf)).map (·.defender)).getD (s.nextPlayer att)

end GameState

/-- The damage that goes to each Unit when the Units are given lethal damage in the order of the
list, and the last one gets what is left (CR 467.2.c.3-4). `need` says how much a Unit needs. -/
def greedy (need : ObjId → Nat) : Nat → List ObjId → List (ObjId × Nat)
  | _, [] => []
  | rem, [u] => [(u, rem)]
  | rem, u :: us => (u, min (need u) rem) :: greedy need (rem - min (need u) rem) us

/-- **The rules of assigning damage (CR 467.2.c), as a rule about an assignment** `l` (the Units in
the order they are given damage, with the damage each gets): all the damage `total` is assigned; a
Unit gets damage only when the ones before it have lethal damage (CR 467.2.c.3); a Unit that is not
the last gets no more than lethal damage (CR 467.2.c.4). It does not say how the engine asks for
the assignment. -/
structure AssignOk (need : ObjId → Nat) (total : Nat) (l : List (ObjId × Nat)) : Prop where
  /-- Everything is assigned, when there is a Unit to assign to. -/
  all : l ≠ [] → (l.map (·.2)).sum = total
  /-- Lethal damage before the next Unit gets any. -/
  lethal_first : ∀ i j (hi : i < l.length) (hj : j < l.length), i < j →
    0 < (l[j]'hj).2 → need (l[i]'hi).1 ≤ (l[i]'hi).2
  /-- No more than lethal damage, unless the Unit is the last one. -/
  no_overkill : ∀ i (hi : i < l.length), i + 1 < l.length → (l[i]'hi).2 ≤ need (l[i]'hi).1

/-- The damage `greedy` assigns is all of it. -/
theorem greedy_sum (need : ObjId → Nat) :
    ∀ (us : List ObjId) (rem : Nat), us ≠ [] → ((greedy need rem us).map (·.2)).sum = rem
  | [], _, h => absurd rfl h
  | [u], rem, _ => by simp [greedy]
  | u :: v :: us, rem, _ => by
    have ih := greedy_sum need (v :: us) (rem - min (need u) rem) (by simp)
    simp only [greedy, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- `greedy` keeps the Units in the order. -/
theorem greedy_length (need : ObjId → Nat) :
    ∀ (us : List ObjId) (rem : Nat), (greedy need rem us).length = us.length
  | [], _ => rfl
  | [u], _ => rfl
  | u :: v :: us, rem => by
    simp only [greedy, List.length_cons]
    rw [greedy_length need (v :: us)]
    simp

/-- When nothing is left to assign, every Unit gets 0. -/
theorem greedy_zero (need : ObjId → Nat) :
    ∀ (ws : List ObjId) (rem : Nat), rem = 0 → ∀ k (hk : k < (greedy need rem ws).length),
      ((greedy need rem ws)[k]'hk).2 = 0
  | [], _, _, k, hk => by simp [greedy] at hk
  | [w], rem, h, k, hk => by simp [greedy, h]
  | w :: x :: xs, rem, h, k, hk => by
    cases k with
    | zero => simp [greedy, h]
    | succ k =>
      simp only [greedy, List.getElem_cons_succ]
      exact greedy_zero need (x :: xs) _ (by omega) k (by simp [greedy] at hk ⊢; omega)

/-- **A relation specification (L5).** Giving lethal damage down a list of Units, and the rest to
the last one, is an assignment that the rules allow (CR 467.2.c). -/
theorem greedy_spec (need : ObjId → Nat) (us : List ObjId) (total : Nat) :
    AssignOk need total (greedy need total us) := by
  have key : ∀ (us : List ObjId) (rem : Nat),
      (∀ i j (hi : i < (greedy need rem us).length) (hj : j < (greedy need rem us).length),
        i < j → 0 < ((greedy need rem us)[j]'hj).2 →
          need ((greedy need rem us)[i]'hi).1 ≤ ((greedy need rem us)[i]'hi).2) ∧
      (∀ i (hi : i < (greedy need rem us).length), i + 1 < (greedy need rem us).length →
        ((greedy need rem us)[i]'hi).2 ≤ need ((greedy need rem us)[i]'hi).1) := by
    intro us
    induction us with
    | nil =>
      intro rem
      exact ⟨fun i j hi => by simp [greedy] at hi, fun i hi => by simp [greedy] at hi⟩
    | cons u us ih =>
      intro rem
      cases us with
      | nil =>
        exact ⟨fun i j hi hj hij => by simp [greedy] at hj; omega,
          fun i hi hi2 => by simp [greedy] at hi2⟩
      | cons v vs =>
        obtain ⟨ih1, ih2⟩ := ih (rem - min (need u) rem)
        refine ⟨fun i j hi hj hij hpos => ?_, fun i hi hi2 => ?_⟩
        · cases i with
          | succ i =>
            cases j with
            | zero => omega
            | succ j =>
              simp only [greedy, List.getElem_cons_succ] at hpos ⊢
              exact ih1 i j (by simp [greedy] at hi ⊢; omega) (by simp [greedy] at hj ⊢; omega)
                (by omega) hpos
          | zero =>
            cases j with
            | zero => omega
            | succ j =>
              -- the first Unit got `min (need u) rem`; something later got damage, so it is lethal
              have hge : 0 < ((greedy need (rem - min (need u) rem) (v :: vs))[j]'(by
                  simp [greedy] at hj ⊢; omega)).2 := by simpa [greedy] using hpos
              have hrem : 0 < rem - min (need u) rem := by
                cases hrr : rem - min (need u) rem with
                | succ k => omega
                | zero =>
                  exfalso
                  -- when nothing is left, nobody later gets damage
                  have := greedy_zero need (v :: vs) _ hrr j (by simp [greedy] at hj ⊢; omega)
                  omega
              simp only [greedy, List.getElem_cons_zero]
              omega
        · cases i with
          | zero => simp only [greedy, List.getElem_cons_zero]; exact Nat.min_le_left _ _
          | succ i =>
            simp only [greedy, List.getElem_cons_succ]
            exact ih2 i (by simp [greedy] at hi ⊢; omega) (by simp [greedy] at hi2 ⊢; omega)
  obtain ⟨k1, k2⟩ := key us total
  refine ⟨fun hne => ?_, k1, k2⟩
  cases us with
  | nil => exact absurd rfl hne
  | cons u us => exact greedy_sum need (u :: us) total (by simp)

/-! ### Asking for the assignment -/

namespace GameState

/-- Whether a Unit has Tank (CR 815). -/
def isTank (s : GameState) (u : ObjId) : Bool := s.hasKw u .tank

/-- Whether a Unit must be assigned damage last: a passive ability says so, and it has no Tank. -/
def isLast (s : GameState) (u : ObjId) : Bool :=
  !s.isTank u && (s.activeMods u).contains .assignedLast

/-- A Unit that can be named next in the order of the assignment: a Unit of the other side not
named yet, a Tank Unit before any Unit without Tank (CR 815, 467.2.c), and a Unit that must be
assigned damage last after the others. -/
def pickOk (s : GameState) (bf : ObjId) (side : PlayerId) (acc : List ObjId) (u : ObjId) : Bool :=
  decide (u ∈ s.foes bf side) && decide (u ∉ acc) &&
    ((s.isTank u || (s.foes bf side).all (fun v => !s.isTank v || decide (v ∈ acc))) &&
      (!s.isLast u || (s.foes bf side).all (fun v => s.isLast v || decide (v ∈ acc))))

/-- Every Unit of the other side has been named. -/
def doneOk (s : GameState) (bf : ObjId) (side : PlayerId) (acc : List ObjId) : Bool :=
  (s.foes bf side).all (fun v => decide (v ∈ acc))

end GameState

/-- The answers to the `assign` frame of `side`. -/
def legalAssigns (s : GameState) (bf : ObjId) (side : PlayerId) (acc : List ObjId) :
    List Action :=
  ((s.foes bf side).filter (fun u => s.pickOk bf side acc u)).map
      (fun u => ⟨.player side, .assignPick u⟩) ++
    (if s.doneOk bf side acc then [⟨.player side, .assignDone⟩] else [])

/-- The answers listed are exactly the legal ones. -/
theorem mem_legalAssigns {s : GameState} {bf : ObjId} {side : PlayerId} {acc : List ObjId}
    {a : Action} :
    a ∈ legalAssigns s bf side acc ↔
      (∃ u, a = ⟨.player side, .assignPick u⟩ ∧ s.pickOk bf side acc u = true) ∨
        (a = ⟨.player side, .assignDone⟩ ∧ s.doneOk bf side acc = true) := by
  unfold legalAssigns
  simp only [List.mem_append, List.mem_map, List.mem_filter]
  constructor
  · rintro (⟨u, ⟨-, hu⟩, rfl⟩ | h)
    · exact Or.inl ⟨u, rfl, hu⟩
    · split at h
      · rename_i hd
        simp only [List.mem_singleton] at h
        exact Or.inr ⟨h, hd⟩
      · simp at h
  · rintro (⟨u, rfl, hu⟩ | ⟨rfl, hd⟩)
    · have hm : u ∈ s.foes bf side := by
        unfold GameState.pickOk at hu
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
        exact hu.1.1
      exact Or.inl ⟨u, ⟨hm, hu⟩, rfl⟩
    · exact Or.inr (by simp [hd])

/-- **No dead end.** Whatever has been named so far, there is a legal answer: name a Unit, or say
that all are named. -/
theorem assign_exists (s : GameState) (bf : ObjId) (side : PlayerId) (acc : List ObjId) :
    ∃ a ∈ legalAssigns s bf side acc, a.kind ≠ .concede := by
  by_cases hd : s.doneOk bf side acc = true
  · exact ⟨⟨.player side, .assignDone⟩, mem_legalAssigns.mpr (Or.inr ⟨rfl, hd⟩),
      by simp⟩
  · -- some Unit is not named yet
    have hex : ∃ v ∈ s.foes bf side, v ∉ acc := by
      refine Classical.byContradiction (fun hn => hd ?_)
      unfold GameState.doneOk
      simp only [List.all_eq_true, decide_eq_true_eq]
      intro v hv
      exact Classical.byContradiction (fun hv2 => hn ⟨v, hv, hv2⟩)
    by_cases ht : ∃ t ∈ s.foes bf side, t ∉ acc ∧ s.isTank t = true
    · obtain ⟨t, htm, hta, htt⟩ := ht
      refine ⟨⟨.player side, .assignPick t⟩,
        mem_legalAssigns.mpr (Or.inl ⟨t, rfl, ?_⟩), by simp⟩
      have hl : s.isLast t = false := by simp [GameState.isLast, htt]
      unfold GameState.pickOk
      simp [htm, hta, htt, hl]
    · -- no Tank is left: a Unit that is not last if there is one, any Unit otherwise
      have htank (w : ObjId) (hw : w ∈ s.foes bf side) :
          (!s.isTank w || decide (w ∈ acc)) = true := by
        by_cases hwt : s.isTank w = true
        · have hwa : w ∈ acc := Classical.byContradiction (fun hwa => ht ⟨w, hw, hwa, hwt⟩)
          simp [hwa]
        · have : s.isTank w = false := by simpa using hwt
          simp [this]
      by_cases hn : ∃ v ∈ s.foes bf side, v ∉ acc ∧ s.isLast v = false
      · obtain ⟨v, hvm, hva, hvl⟩ := hn
        refine ⟨⟨.player side, .assignPick v⟩,
          mem_legalAssigns.mpr (Or.inl ⟨v, rfl, ?_⟩), by simp⟩
        unfold GameState.pickOk
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.all_eq_true,
          Bool.not_eq_true', hvl]
        exact ⟨⟨hvm, hva⟩, Or.inr (fun w hw => by simpa using htank w hw), Or.inl trivial⟩
      · obtain ⟨v, hvm, hva⟩ := hex
        refine ⟨⟨.player side, .assignPick v⟩,
          mem_legalAssigns.mpr (Or.inl ⟨v, rfl, ?_⟩), by simp⟩
        unfold GameState.pickOk
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.all_eq_true,
          Bool.not_eq_true']
        refine ⟨⟨hvm, hva⟩, Or.inr (fun w hw => by simpa using htank w hw),
          Or.inr (fun w hw => ?_)⟩
        by_cases hwa : w ∈ acc
        · right; exact hwa
        · left
          by_cases hwl : s.isLast w = false
          · exact absurd ⟨w, hw, hwa, hwl⟩ hn
          · simpa using hwl

/-! ### Dealing the damage and ending the Combat -/

/-- Deal the damages of a list, one after the other. They are one simultaneous event
(CR 467.2.c.1), so the order does not matter for the result. -/
def dealAll : GameState → List (ObjId × Nat) → GameState × List Event
  | s, [] => (s, [])
  | s, (u, n) :: l =>
    let r := dealObj n s u
    let r2 := dealAll r.1 l
    (r2.1, r.2 ++ r2.2)

/-- Dealing the damages is a safe change. -/
theorem dealAll_safe : ∀ (l : List (ObjId × Nat)) (s : GameState), Safe s (dealAll s l).1
  | [], s => Safe.refl s
  | (u, n) :: l, s => (dealObj_safe n s u).trans (dealAll_safe l (dealObj n s u).1)

/-- Recall a Unit to its controller's Base (CR 456): its damage and status stay. -/
def recallObj (s : GameState) (u : ObjId) : GameState × List Event :=
  match s.obj? u with
  | some o =>
    match moveObj s u (.player o.controller .base) with
    | some r => (r.1.modObj r.2 (fun o => { o with loc := none }), [Event.recalled r.2])
    | none => (s, [])
  | none => (s, [])

/-- Recalling is a safe change. -/
theorem recallObj_safe (s : GameState) (u : ObjId) : Safe s (recallObj s u).1 := by
  unfold recallObj
  split
  · split
    · rename_i r hm
      exact (Safe.moveObj hm).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl))
    · exact Safe.refl s
  · exact Safe.refl s

/-- Every object is healed: step 3c of the Combat Cleanup (CR 468.1, 324). -/
theorem safe_healAll (s : GameState) : Safe s (s.mapObjects healObj) :=
  ⟨fun h => GameState.wf_mapObjects h _,
    fun _ => by rw [GameState.physIds_mapObjects s (f := healObj) (fun o => healObj_kind o)],
    fun _ h => GameState.ownerOk_mapObjects h (fun o => healObj_owner o),
    GameState.sameMeta_mapObjects s _⟩

/-- The end of a Combat (CR 468): every Unit is healed, the Attacker's Units are Recalled if a
Unit of a Defender is left (a tie, if Units of the Attacker are left too: then all the Units are
Recalled, if a passive ability of the Attacker says so, as Symbol of the Solari does), and the
Battlefield goes to the player whose Units are alone there, who Scores it by Conquer. The Units
with lethal damage have been killed by the Cleanup before. -/
def combatResolve (s : GameState) (bf : ObjId) (att : PlayerId) :
    GameState × List Frame × List Event :=
  let s1 := s.mapObjects healObj
  let defenders :=
    (s1.players.filter (fun p => p ≠ att)).any (fun p => !(s1.unitsOf p bf).isEmpty)
  -- a tie: Units of both sides are left; a passive ability of the attacker recalls them all
  let tieAll := defenders && !(s1.unitsOf att bf).isEmpty &&
    s1.passiveSources.any (fun g => (s1.obj? g).any (fun o => o.controller == att) &&
      (s1.activeMods g).contains .recallAllOnTie)
  let victims :=
    if tieAll then s1.players.flatMap (fun p => s1.unitsOf p bf) else s1.unitsOf att bf
  let r := if defenders then applyEach recallObj s1 victims else (s1, [])
  let t := endShowdown r.1 bf false
  -- the player whose Units are the only ones left wins the Combat
  let won := (r.1.players.filter (fun p => !(r.1.unitsOf p bf).isEmpty)).map
    (fun p => Event.combatWon bf p)
  (t.1, t.2.1, r.2 ++ (match won with | [w] => [w] | _ => []) ++ t.2.2)

/-- The end of a Combat is a safe change, then points. -/
theorem combatResolve_safeP (s : GameState) (bf : ObjId) (att : PlayerId) :
    SafeP s (combatResolve s bf att).1 := by
  unfold combatResolve
  dsimp only
  have h1 := safe_healAll s
  let healed := s.mapObjects healObj
  let defenders := (healed.players.filter (fun p => p ≠ att)).any
    (fun p => !(healed.unitsOf p bf).isEmpty)
  let tieAll := defenders && !(healed.unitsOf att bf).isEmpty &&
    healed.passiveSources.any (fun g => (healed.obj? g).any (fun o => o.controller == att) &&
      (healed.activeMods g).contains .recallAllOnTie)
  let victims := if tieAll then healed.players.flatMap (fun p => healed.unitsOf p bf)
    else healed.unitsOf att bf
  have h2 : Safe healed
      (if defenders then applyEach recallObj healed victims else (healed, [])).1 := by
    split
    · exact applyEach_safe (fun s u => recallObj_safe s u) _ _
    · exact Safe.refl _
  exact SafeP.trans_safe (h1.trans h2) (endShowdown_safeP _ bf false)

/-- The frames the end of a Combat asks for are draws. -/
theorem combatResolve_frames (s : GameState) (bf : ObjId) (att : PlayerId) :
    ∀ f ∈ (combatResolve s bf att).2.1, ∃ r, f = Frame.draw r 1 := by
  intro f hf
  unfold combatResolve at hf
  dsimp only at hf
  exact endShowdown_frames _ bf false f hf

/-- The frames that start the Combat Damage: the Attacker assigns first, then the Defender; a side
with no damage to assign or no Unit to assign it to is skipped (CR 467.1-2). -/
def GameState.assignFrame (s : GameState) (bf : ObjId) (att side : PlayerId)
    (done : List (ObjId × Nat)) : Option Frame :=
  if 0 < s.combatTotal bf att side && !(s.foes bf side).isEmpty then
    some (.assign bf att side [] done)
  else none

/-- The frames of the Combat Damage. -/
def GameState.startCombat (s : GameState) (bf : ObjId) (att : PlayerId) : List Frame :=
  match s.assignFrame bf att att [] with
  | some f => [f]
  | none =>
    match s.assignFrame bf att (s.defenderAt bf att) [] with
    | some f => [f]
    | none => [.cleanup, .combatResolve bf att]

/-- The frames of the Combat Damage are `assign` frames, or the end of the Combat. -/
theorem startCombat_mem (s : GameState) (bf : ObjId) (att : PlayerId) :
    ∀ f ∈ s.startCombat bf att,
      (∃ b a q, f = Frame.assign b a q [] []) ∨ f = Frame.cleanup ∨
      f = Frame.combatResolve bf att := by
  intro f hf
  unfold GameState.startCombat at hf
  split at hf
  · rename_i g hg
    unfold GameState.assignFrame at hg
    split at hg
    · simp only [Option.some.injEq] at hg
      subst hg
      simp only [List.mem_singleton] at hf
      subst hf
      exact Or.inl ⟨_, _, _, rfl⟩
    · simp at hg
  · split at hf
    · rename_i g hg
      unfold GameState.assignFrame at hg
      split at hg
      · simp only [Option.some.injEq] at hg
        subst hg
        simp only [List.mem_singleton] at hf
        subst hf
        exact Or.inl ⟨_, _, _, rfl⟩
      · simp at hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

/-- The damage assigned to Units of other players than `att` beyond what is lethal to them (the
last Unit of an order gets what is left). -/
def excessOf (s : GameState) (att : PlayerId) (done : List (ObjId × Nat)) : Nat :=
  (done.filter (fun e => (s.obj? e.1).any (fun o => o.controller != att))).foldl
    (fun acc e => acc + (e.2 - s.need e.1)) 0

/-- Note the excess damage of the player, in place of the note of an earlier Combat of the turn. -/
def noteExcess (s : GameState) (att : PlayerId) (k : Nat) : GameState :=
  { s with turnFx := s.turnFx.filter (fun f =>
      !(f.who == att && (match f.kind with | .excessDamage _ => true | _ => false))) ++
    [{ who := att, turn := s.turn, stamp := s.nextTimestamp, kind := .excessDamage k }] }

/-- Noting the excess damage is a safe change. -/
theorem noteExcess_safe (s : GameState) (att : PlayerId) (k : Nat) : Safe s (noteExcess s att k) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- The answer `assignDone`: the damage of this side is assigned down the order, and the next side
asks, or all the damage is dealt (CR 467.2.c.1) and the Combat Cleanup begins. -/
def assignDoneStep (s : GameState) (bf : ObjId) (att side : PlayerId) (acc : List ObjId)
    (done : List (ObjId × Nat)) (rest : List Frame) : GameState × List Event :=
  let done' := done ++ greedy s.need (s.combatTotal bf att side) acc
  match (if side = att then s.assignFrame bf att (s.defenderAt bf att) done' else none) with
  | some f => ({ s with pending := f :: rest }, [])
  | none =>
    let r := dealAll s done'
    -- the excess damage the attacker assigned is noted (the last Combat of the turn counts)
    let r2 := noteExcess r.1 att (excessOf s att done')
    ({ r2 with pending := .cleanup :: .combatResolve bf att :: rest }, r.2)

/-- What `assignDoneStep` does, in the cases the invariants look at. -/
theorem assignDoneStep_cases (s : GameState) (bf : ObjId) (att side : PlayerId) (acc : List ObjId)
    (done : List (ObjId × Nat)) (rest : List Frame) :
    (∃ b a q d, (assignDoneStep s bf att side acc done rest).1 =
      { s with pending := Frame.assign b a q [] d :: rest }) ∨
    (∃ r, Safe s r ∧ (assignDoneStep s bf att side acc done rest).1 =
      { r with pending := .cleanup :: .combatResolve bf att :: rest }) := by
  unfold assignDoneStep
  dsimp only
  split
  · rename_i f hf
    left
    split at hf
    · unfold GameState.assignFrame at hf
      split at hf
      · simp only [Option.some.injEq] at hf
        subst hf
        exact ⟨_, _, _, _, rfl⟩
      · simp at hf
    · simp at hf
  · right
    exact ⟨_, (dealAll_safe _ s).trans (noteExcess_safe _ _ _), rfl⟩

/-- The end of the Showdown at `bf`: a Combat if the Units of two players are there, otherwise the
Control of the Battlefield goes to the player whose Units are alone there (CR 348). -/
def showdownEnd (s : GameState) (bf : ObjId) (rest : List Frame) : GameState × List Event :=
  if s.isCombat bf then ({ s with pending := .combatDamage bf (s.attackerAt bf) :: rest }, [])
  else ({ (endShowdown s bf).1 with pending := (endShowdown s bf).2.1 ++ rest },
    (endShowdown s bf).2.2)

/-- What `showdownEnd` does, in the cases the invariants look at. -/
theorem showdownEnd_cases (s : GameState) (bf : ObjId) (rest : List Frame) :
    (∃ a, (showdownEnd s bf rest).1 = { s with pending := .combatDamage bf a :: rest }) ∨
    ((showdownEnd s bf rest).1 =
      { (endShowdown s bf).1 with pending := (endShowdown s bf).2.1 ++ rest }) := by
  unfold showdownEnd
  split
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr rfl

end Riftbound

end
