module

public import Riftbound.Rules.Passive

/-! # Sending objects to owner zones and resolving death -/

@[expose] public section

namespace Riftbound

/-- Heal all marked damage, recording the amount cleared (CR 419). -/
def healAllOn (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id healObj, match (s.obj? id).map (·.damage) with
    | some (n + 1) => [Event.healed id (n + 1)]
    | _ => [])

theorem healAllOn_safe (s : GameState) (id : ObjId) : Safe s (healAllOn s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- Send an object to the zone `k` of its owner. Nothing happens if it is not on a zone. -/
def sendObj (k : ZoneKind) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    let dest := s.ownerDestination id o k
    match moveObj s id (.player o.owner dest) with
    | some r => (r.1, o.ownerMoveEvents id r.2 dest (k != dest))
    | none => (s, [])
  | none => (s, [])

/-- Sending an object to a zone is a safe change. -/
theorem sendObj_safe (k : ZoneKind) (s : GameState) (id : ObjId) :
    Safe s (sendObj k s id).1 := by
  unfold sendObj
  split
  · dsimp only
    split
    · rename_i r hm
      exact Safe.moveObj hm
    · exact Safe.refl s
  · exact Safe.refl s

/-- Attribute a successful move into Banishment to the player performing Banish (CR 428). -/
def banishCardEvents (actor : PlayerId) (s : GameState) (id : ObjId)
    (moves : List Event) : List Event :=
  if (s.obj? id).any (·.kind.phys?.isSome) then
    moves.filterMap (fun
      | .moved _ new (.player owner .banishment) => some (.banished actor owner new)
      | _ => none)
  else []

/-- Banish an object and, for a card, record who performed the action. -/
def banishObj (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := sendObj .banishment s id
  (r.1, r.2 ++ banishCardEvents p s id r.2)

/-- Banish has the same state invariants as the zone move it records. -/
theorem banishObj_safe (p : PlayerId) (s : GameState) (id : ObjId) :
    Safe s (banishObj p s id).1 := sendObj_safe .banishment s id

/-- Make an effect true for the rest of the turn, for the player. -/
def GameState.addTurnFx (s : GameState) (p : PlayerId) (e : TurnEffect) : GameState :=
  let playCount := match e with
    | .nextCardCostMinus .. => s.finalizedCount p
    | _ => 0
  { s with turnFx := s.turnFx ++
      [{ who := p, turn := s.turn, stamp := s.nextTimestamp, kind := e, playCount }] }

/-- The same, about an object. -/
def GameState.addTurnFxOn (s : GameState) (p : PlayerId) (id : ObjId) (e : TurnEffect) :
    GameState :=
  { s with turnFx := s.turnFx ++
      [{ who := p, turn := s.turn, stamp := s.nextTimestamp, kind := e, target := some id }] }

/-- A lasting effect about an object is a safe change. -/
theorem addTurnFxOn_safe (s : GameState) (p : PlayerId) (id : ObjId) (e : TurnEffect) :
    Safe s (s.addTurnFxOn p id e) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- A lasting effect of the turn is a safe change: it is not part of what a safe change keeps. -/
theorem addTurnFx_safe (s : GameState) (p : PlayerId) (e : TurnEffect) :
    Safe s (s.addTurnFx p e) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- A unit of the player died: noted for the turn, and as one that died during a Beginning Phase if
the Beginning Phase is going on. -/
def GameState.noteUnitDied (c : PlayerId) (t : GameState) : GameState :=
  let t1 := t.addTurnFx c .unitDied
  if t.phase == .beginning then t1.addTurnFx c .diedInBeginning else t1

/-- Noting that a unit died is a safe change. -/
theorem noteUnitDied_safe (c : PlayerId) (t : GameState) : Safe t (t.noteUnitDied c) := by
  unfold GameState.noteUnitDied
  split
  · exact (addTurnFx_safe t c _).trans (addTurnFx_safe _ c _)
  · exact addTurnFx_safe t c _

/-- Noting that a unit died leaves the zone as it was. -/
theorem noteUnitDied_zone (c : PlayerId) (t : GameState) (z : Zone) :
    (t.noteUnitDied c).zone z = t.zone z := by
  unfold GameState.noteUnitDied
  split <;> rfl

/-- Noting that a unit died leaves the objects in play as they were. -/
theorem noteUnitDied_inPlay (c : PlayerId) (t : GameState) :
    (t.noteUnitDied c).inPlay = t.inPlay := by
  unfold GameState.noteUnitDied
  split <;> rfl

/-- Do the change if the condition holds. -/
def noteIf (b : Bool) (f : GameState → GameState) (s : GameState) : GameState :=
  if b then f s else s

/-- A change that is safe, done if a condition holds, is a safe change. -/
theorem noteIf_safe (b : Bool) (f : GameState → GameState) (hf : ∀ t, Safe t (f t))
    (s : GameState) : Safe s (noteIf b f s) := by
  unfold noteIf
  split
  · exact hf s
  · exact Safe.refl s

/-- The notes of the death of a unit: that it died, and whether it was buffed or stunned as it died
(the notes are about the dead card, which is the object it has become). -/
def noteDeath (s : GameState) (o : Object) (isUnit : Bool) (marked : Bool) (mighty : Bool)
    (moved : Option ObjId) (banisher : Option ObjId) : GameState :=
  let s1 := noteIf (isUnit && moved.isSome) (fun t => t.noteUnitDied o.controller) s
  match moved with
  | some n =>
    let s2 := noteIf (isUnit && o.buffed)
      (fun t => t.addTurnFxOn o.controller n .buffedUnitDied) s1
    let s3 := noteIf (isUnit && o.stunned)
      (fun t => t.addTurnFxOn o.controller n .stunnedUnitDied) s2
    let s4 := noteIf (isUnit && mighty)
      (fun t => t.addTurnFxOn o.controller n .mightyUnitDied) s3
    let s5 := noteIf (isUnit && marked) (fun t => t.addTurnFxOn o.controller n .recallDied) s4
    -- the card remembers the Equipment that banished it
    noteIf banisher.isSome (fun t => t.modObj n (fun x => { x with banishedWith := banisher })) s5
  | none => s1

/-- Noting a death is a safe change. -/
theorem noteDeath_safe (s : GameState) (o : Object) (isUnit marked mighty : Bool)
    (moved : Option ObjId) (banisher : Option ObjId) :
    Safe s (noteDeath s o isUnit marked mighty moved banisher) := by
  unfold noteDeath
  have h1 := noteIf_safe (isUnit && moved.isSome) (fun t => t.noteUnitDied o.controller)
    (fun t => noteUnitDied_safe _ t) s
  cases moved with
  | none => exact h1
  | some n =>
    refine h1.trans ?_
    exact ((((noteIf_safe _ _ (fun t => addTurnFxOn_safe t _ _ _) _).trans
      (noteIf_safe _ _ (fun t => addTurnFxOn_safe t _ _ _) _)).trans
      (noteIf_safe _ _ (fun t => addTurnFxOn_safe t _ _ _) _)).trans
      (noteIf_safe _ _ (fun t => addTurnFxOn_safe t _ _ _) _)).trans
      (noteIf_safe _ (fun t => t.modObj n (fun x => { x with banishedWith := banisher }))
        (fun t => Safe.modObj t n (fun _ => rfl) (fun _ => rfl)) _)

/-- Whether this turn note has the given kind and applies to the object. -/
def TurnFx.appliesTo (note : TurnFx) (turn : Nat) (id : ObjId) (kind : TurnEffect) : Bool :=
  note.kind == kind && note.target == some id && note.turn == turn

/-- The controller's chosen replacement for this Unit's pending death. -/
def GameState.chosenDeathBanisher (s : GameState) (id : ObjId) : Option PlayerId :=
  (s.turnFx.find? (·.appliesTo s.turn id .chosenDeathBanisher)).map (·.who)

/-- The player whose effect replaces the kill with a Banish (Smite). A later Deathknell
banishes separately. -/
def GameState.banishOnDeathBy (s : GameState) (id : ObjId) : Option PlayerId :=
  s.chosenDeathBanisher id <|>
    (s.turnFx.find? (·.appliesTo s.turn id .banishInstead)).map (·.who)

/-- A replacement banishes the object instead of sending it to the Trash on death. -/
def GameState.banishedOnDeath (s : GameState) (id : ObjId) : Bool :=
  (s.banishOnDeathBy id).isSome

/-- The Equipment attached to the object that banishes it when it dies. -/
def GameState.banisherOf (s : GameState) (id : ObjId) : Option ObjId :=
  s.inPlay.find? (fun g => (s.obj? g).any (·.attached == some id) &&
    (s.cardDef? g).any (fun d => d.grants.any (fun ab =>
      match ab with
      | Ability.passive .always mods => mods.contains .banishOnDeath
      | _ => false)))

/-- The note that a unit died alone (no other unit of its player was where it was), about the dead
card. -/
def noteAlone (s : GameState) (o : Object) (moved : Option ObjId) (alone : Bool) : GameState :=
  match moved with
  | some n => noteIf alone (fun t => t.addTurnFxOn o.controller n .diedAlone) s
  | none => s

/-- Noting that a unit died alone is a safe change. -/
theorem noteAlone_safe (s : GameState) (o : Object) (moved : Option ObjId) (alone : Bool) :
    Safe s (noteAlone s o moved alone) := by
  unfold noteAlone
  cases moved with
  | none => exact Safe.refl s
  | some n => exact noteIf_safe _ _ (fun t => addTurnFxOn_safe t _ _ _) s

/-- A kill sends a Permanent to its owner's Trash. Replacing it with Banish suppresses the
death event and attributes the Banish to the selected effect (CR 370.1.a.1, 428.2.a, 429.1). -/
def killObj (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := sendObj (if s.banishedOnDeath id then ZoneKind.banishment else .trash) s id
  match s.obj? id with
  | some o =>
    if s.banishedOnDeath id || r.2.any (fun | .banished .. => true | _ => false) then
      (r.1, r.2 ++ (s.banishOnDeathBy id).toList.flatMap (fun p => banishCardEvents p s id r.2))
    else
    -- the death of a unit is noted for the turn (its controller, as it died)
    (noteAlone
        (noteDeath r.1 o ((s.cardDef? id).any (·.hasType .unit))
          (s.turnFx.any (fun f => f.kind == .recallOnDeath && f.target == some id &&
            f.turn == s.turn))
          ((s.mightNow id).any (fun m => decide (5 ≤ m)))
          (r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none))
          (s.banisherOf id))
        o (r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none))
        ((s.cardDef? id).any (·.hasType .unit) &&
          !(s.inPlay.any (fun u => u != id && (s.cardDef? u).any (·.hasType .unit) &&
            (s.obj? u).any (fun x => x.controller == o.controller && x.loc == o.loc)))),
      r.2 ++ r.2.filterMap (fun e => match e with
      | .moved _ n _ => some (Event.died n o.controller)
      | _ => none))
  | none => r

/-- Killing an object is a safe change. -/
theorem killObj_safe (s : GameState) (id : ObjId) : Safe s (killObj s id).1 := by
  unfold killObj
  generalize (if s.banishedOnDeath id = true then ZoneKind.banishment else ZoneKind.trash) = dest
  split
  · dsimp only
    split
    · exact sendObj_safe dest s id
    · exact ((sendObj_safe dest s id).trans (noteDeath_safe _ _ _ _ _ _ _)).trans
        (noteAlone_safe _ _ _ _)
  · exact sendObj_safe dest s id

/-- What the zone of an object in a well-formed game says: no other zone holds it. -/
theorem ne_of_mem_other_zone {s : GameState} (hwf : s.WF) {z x : Zone} {id y : ObjId}
    (hid : id ∈ s.zone z) (hy : y ∈ s.zone x) (hxz : x ≠ z) : y ≠ id := by
  intro h
  subst h
  have h1 := GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hid) hid
  have h2 := GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hy) hy
  exact hxz (Option.some.inj (h2.symm.trans h1))

/-- Noting that a unit died alone leaves the zones as they are. -/
theorem noteAlone_zone (s : GameState) (o : Object) (moved : Option ObjId) (alone : Bool)
    (z : Zone) : (noteAlone s o moved alone).zone z = s.zone z := by
  unfold noteAlone
  cases moved with
  | none => rfl
  | some n =>
    unfold noteIf
    by_cases h : alone = true
    · simp only [h, ite_true]; rfl
    · simp [h]

/-- Noting a death leaves the zones as they are. -/
theorem noteDeath_zone (s : GameState) (o : Object) (isUnit marked mighty : Bool)
    (moved : Option ObjId) (banisher : Option ObjId) (z : Zone) :
    (noteDeath s o isUnit marked mighty moved banisher).zone z = s.zone z := by
  have key : ∀ (b : Bool) (f : GameState → GameState), (∀ t, (f t).zone z = t.zone z) →
      ∀ t, (noteIf b f t).zone z = t.zone z := by
    intro b f hf t
    unfold noteIf
    split
    · exact hf t
    · rfl
  unfold noteDeath
  cases moved with
  | none =>
    dsimp only
    exact key _ (fun t => t.noteUnitDied o.controller) (fun t => noteUnitDied_zone _ t z) s
  | some n =>
    dsimp only
    rw [key _ (fun t => t.modObj n (fun x => { x with banishedWith := banisher }))
        (fun t => by simp only [GameState.zone_modObj]),
      key _ (fun t => t.addTurnFxOn o.controller n .recallDied) (fun t => rfl),
      key _ (fun t => t.addTurnFxOn o.controller n .mightyUnitDied) (fun t => rfl),
      key _ (fun t => t.addTurnFxOn o.controller n .stunnedUnitDied) (fun t => rfl),
      key _ (fun t => t.addTurnFxOn o.controller n .buffedUnitDied) (fun t => rfl),
      key _ (fun t => t.noteUnitDied o.controller) (fun t => noteUnitDied_zone _ t z)]

/-- Killing an object that is on a zone other than `z`, when the Trash and the Banishment are not
`z`, leaves `z` as it was. -/
theorem killObj_zone_other {s : GameState} (hwf : s.WF) {u : ObjId} {z0 z : Zone}
    (hu : u ∈ s.zone z0) (hne : z ≠ z0)
    (hd : ∀ q k, (k = ZoneKind.trash ∨ k = ZoneKind.banishment) → z ≠ Zone.player q k) :
    (killObj s u).1.zone z = s.zone z := by
  obtain ⟨dk, hdk⟩ : ∃ dk, dk = (if s.banishedOnDeath u = true then ZoneKind.banishment
      else ZoneKind.trash) := ⟨_, rfl⟩
  have hk : dk = ZoneKind.trash ∨ dk = ZoneKind.banishment := by
    rw [hdk]; split <;> simp
  obtain ⟨o, ho⟩ := GameState.obj_of_mem hwf hu
  unfold killObj sendObj
  rw [← hdk, ho]
  simp only
  let dest := s.ownerDestination u o dk
  have hdest := s.ownerDestination_trash_or_banishment u o hk
  cases hm : moveObj s u (.player o.owner dest) with
  | none =>
    dsimp only
    split
    · rfl
    · rw [noteAlone_zone, noteDeath_zone]
  | some r =>
    obtain ⟨s', id'⟩ := r
    obtain ⟨src, d, hs, o2, ho2, hdd⟩ := moveObj_spec_dst hm
    have hloc : s.locate u = some z0 :=
      GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hu) hu
    have hsrc : src = z0 := Option.some.inj (hs.locate.symm.trans hloc)
    subst hsrc
    have hdn : d = .player o.owner dest := by
      have : o2 = o := Option.some.inj (ho2.symm.trans ho)
      subst this
      exact hdd.trans (Zone.normalize_owner _ _)
    have hzone := hs.zone_other hne (by rw [hdn]; exact hd _ _ hdest)
    simp only
    split
    · exact hzone
    · simpa only [noteAlone_zone, noteDeath_zone] using hzone

/-- Make an object ready or exhausted (CR 415, 416). -/
def setExhausted (b : Bool) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    -- only an object that was exhausted is readied, and only a ready one is exhausted (CR 416)
    (s.modObj id (fun o => { o with exhausted := b }),
      if b then (if o.exhausted then [] else [Event.exhausted id])
      else if o.exhausted then [Event.readied id] else [])
  | none => (s, [])

/-- Readying or exhausting is a safe change. -/
theorem setExhausted_safe (b : Bool) (s : GameState) (id : ObjId) :
    Safe s (setExhausted b s id).1 := by
  unfold setExhausted
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- Move an object to its controller's Base: a move, not a Recall (CR 144, 456). Its damage and
status stay. -/
def sendHome (s : GameState) (u : ObjId) : GameState × List Event :=
  match s.obj? u with
  | some o =>
    match moveObj s u (.player o.controller .base) with
    | some r => (r.1.modObj r.2 (fun o => { o with loc := none }), [])
    | none => (s, [])
  | none => (s, [])

/-- Moving to the Base is a safe change. -/
theorem sendHome_safe (s : GameState) (u : ObjId) : Safe s (sendHome s u).1 := by
  unfold sendHome
  split
  · split
    · rename_i r hm
      exact (Safe.moveObj hm).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl))
    · exact Safe.refl s
  · exact Safe.refl s

/-- Recall a Unit: it goes to its controller's Base, and is exhausted if the effect says so. It is
not a move, so no ability of a move fires (CR 456). -/
def recallFx (ex : Bool) (s : GameState) (u : ObjId) : GameState × List Event :=
  let moved := sendHome s u
  let recalled := if (s.obj? u).any (·.loc.isSome) && (moved.1.obj? u).any (·.loc.isNone) then
    [Event.recalled u] else []
  if ex then
    let tired := setExhausted true moved.1 u
    (tired.1, moved.2 ++ recalled ++ tired.2)
  else (moved.1, moved.2 ++ recalled)

/-- Recalling is a safe change. -/
theorem recallFx_safe (ex : Bool) (s : GameState) (u : ObjId) : Safe s (recallFx ex s u).1 := by
  unfold recallFx
  cases ex
  · exact sendHome_safe s u
  · exact (sendHome_safe s u).trans (setExhausted_safe true _ u)

/-- The next Tactical Retreat on this Unit. Each resolved spell supplies one rescue this turn. -/
def GameState.tacticalRetreatFor (s : GameState) (id : ObjId) : Option TurnFx :=
  let available := s.turnFx.foldl (init := []) fun notes note =>
    if note.appliesTo s.turn id .saveOnce then notes ++ [note]
    else if note.appliesTo s.turn id .saveUsed then notes.drop 1
    else notes
  available.head?

/-- The controller has already answered the optional replacement for the current death. -/
def GameState.deathSacrificeDecision (s : GameState) (id : ObjId) : Option (Option ObjId) :=
  s.turnFx.findSome? (fun note =>
    if note.turn == s.turn && note.target == some id then
      match note.kind with
      | .deathSacrificeChoice cost => some cost
      | _ => none
    else none)

/-- The friendly Units that can pay, including teammates' Units (CR 491.8.e). A Unit can
pay for its own replacement, using that replacement once across the resulting Kills (CR 370.2). -/
def GameState.deathSacrificeUnits (s : GameState) (p : PlayerId) (id : ObjId) : List ObjId :=
  let options := s.inPlay.eraseDups.filter (fun unit =>
    (s.obj? unit).any (fun o => s.config.mode.sameSide p o.controller) &&
    (s.cardDef? unit).any (·.hasType .unit) &&
    !s.turnFx.any (fun note => note.turn == s.turn && note.target != some id &&
      note.kind == .deathSacrificeChoice (some unit)))
  (options.filter (· != id)) ++ (options.filter (· == id))

/-- Check a declared sacrifice again as the original death is replaced. -/
def GameState.selectedDeathSacrifice (s : GameState) (id : ObjId) : Option ObjId := do
  let cost ← (s.deathSacrificeDecision id).join
  let o ← s.obj? id
  (s.deathSacrificeUnits o.controller id).find? (· == cost)

/-- An elected sacrifice is still on the Board when it is used. -/
theorem GameState.selectedDeathSacrifice_mem {s : GameState} {id unit : ObjId}
    (h : s.selectedDeathSacrifice id = some unit) : unit ∈ s.inPlay := by
  unfold GameState.selectedDeathSacrifice at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, o, _, picked⟩ := h
  have hm := List.mem_of_find?_eq_some picked
  unfold GameState.deathSacrificeUnits at hm
  dsimp only at hm
  rcases List.mem_append.mp hm with member | member
  all_goals exact List.mem_eraseDups.mp (List.mem_filter.mp (List.mem_filter.mp member).1).1

/-- The Gear the affected controller selected to die in place of the Unit (CR 372). -/
def GameState.chosenDeathGear (s : GameState) (id : ObjId) : Option ObjId :=
  s.turnFx.findSome? fun note =>
    if note.turn == s.turn && note.target == some id then
      match note.kind with | .chosenDeathGear gear => some gear | _ => none
    else none

/-- The selected free rescue. An inner None represents Tactical Retreat. -/
def GameState.chosenDeathFree (s : GameState) (id : ObjId) : Option (Option ObjId) :=
  s.turnFx.findSome? fun note =>
    if note.turn == s.turn && note.target == some id then
      match note.kind with | .chosenDeathFree source => some source | _ => none
    else none

/-- Sequences closed for this root event of a simultaneous group (CR 373.2). -/
def GameState.closedDeathSequences (s : GameState) (id : ObjId) : List DeathSequenceSource :=
  (s.turnFx.findSome? fun note =>
    if note.turn != s.turn || note.target != some id then none else
      match note.kind with | .closedDeathSequences sources => some sources | _ => none).getD []

/-- Remove the transient group context before a nested Kill, or after applying the root event. -/
def clearClosedDeathSequences (s : GameState) : GameState :=
  { s with turnFx := s.turnFx.filter fun note =>
      match note.kind with | .closedDeathSequences _ => false | _ => true }

theorem clearClosedDeathSequences_safe (s : GameState) : Safe s (clearClosedDeathSequences s) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- The in-play sources that could die in the Unit's place. An inherent replacement works
across a team, while an Equipment's granted replacement belongs to its wearer (CR 491.8.e). -/
def GameState.deathGearOptions (s : GameState) (id : ObjId) (used : List (ObjId × Bool)) : List ObjId :=
  let closed := s.closedDeathSequences id
  (s.obj? id).elim [] fun victim =>
    s.inPlay.eraseDups.filter fun gear => !used.contains (gear, false) &&
      !closed.contains (.gear gear) &&
      ((s.obj? gear).any (fun o => s.config.mode.sameSide victim.controller o.controller) &&
        (s.activeMods gear).contains .diesInsteadOfFriendly ||
       (s.obj? gear).any (·.attached == some id) &&
        (s.cardDef? gear).any (fun d => d.grants.any fun
          | .passive .always mods => mods.contains .diesInsteadGear
          | _ => false))

/-- Use the recorded source when available. A simultaneous death may have consumed it already. -/
def GameState.selectedDeathGear (s : GameState) (id : ObjId) (used : List (ObjId × Bool)) : Option ObjId :=
  let options := s.deathGearOptions id used
  (options.find? (fun gear => s.chosenDeathGear id == some gear)) <|> options.head?

private theorem GameState.selectedDeathGear_mem {s : GameState} {id gear : ObjId}
    {used : List (ObjId × Bool)} (h : s.selectedDeathGear id used = some gear) : gear ∈ s.inPlay := by
  unfold GameState.selectedDeathGear at h
  dsimp only at h
  have found : gear ∈ s.deathGearOptions id used := by
    cases hp : (s.deathGearOptions id used).find? (fun x => s.chosenDeathGear id == some x) with
    | none =>
      have hd : (s.deathGearOptions id used).head? = some gear := by simpa [hp] using h
      exact List.mem_of_head? hd
    | some x =>
      have he : x = gear := by simpa [hp] using h
      subst x
      exact List.mem_of_find?_eq_some hp
  unfold GameState.deathGearOptions at found
  cases hobj : s.obj? id with
  | none => simp [hobj] at found
  | some _ =>
    simp only [hobj, Option.elim_some] at found
    exact List.mem_eraseDups.mp (List.mem_filter.mp found).1

/-- Free replacements are scoped to the marked Unit or the rescuer at its location. -/
def GameState.deathFreeOptions (s : GameState) (id : ObjId)
    (used : List (ObjId × Bool)) : List (Option ObjId) :=
  let closed := s.closedDeathSequences id
  (s.obj? id).elim [] fun victim =>
    let retreat := if (s.tacticalRetreatFor id).isSome then [none] else []
    let rescuers := s.inPlay.eraseDups.filter fun u =>
      u != id && !closed.contains (.rescuer u) &&
      (s.obj? u).any (fun o => o.controller == victim.controller && o.loc == victim.loc) &&
      (s.activeMods u).contains .rescueWeakerHere &&
      decide ((s.mightNow id).getD 0 < (s.mightNow u).getD 0)
    (retreat ++ rescuers.map some).filter fun source => !used.contains (source.getD id, false)

/-- The recorded free rescue, if it still applies to this Kill. -/
def GameState.selectedDeathFree (s : GameState) (id : ObjId)
    (used : List (ObjId × Bool)) : Option (Option ObjId) :=
  (s.chosenDeathFree id).filter fun source => (s.deathFreeOptions id used).contains source

/-- The free rescue applied if this Kill has no automatic cost. -/
def GameState.freeDeathSaver (s : GameState) (id : ObjId)
    (used : List (ObjId × Bool) := []) : Option (Option ObjId) :=
  s.selectedDeathFree id used <|> (s.deathFreeOptions id used).head?

/-- The automatic save returns a cost for Gear and no cost for a free rescue. -/
def GameState.automaticDeathSaver (s : GameState) (id : ObjId)
    (used : List (ObjId × Bool) := []) : Option (Option ObjId) :=
  if (s.selectedDeathFree id used).isSome then some none
  else (s.selectedDeathGear id used).map some <|> (s.freeDeathSaver id used).map (fun _ => none)

private theorem GameState.automaticDeathSaver_cost_mem {s : GameState} {id cost : ObjId}
    {used : List (ObjId × Bool)} (h : s.automaticDeathSaver id used = some (some cost)) :
    cost ∈ s.inPlay := by
  unfold GameState.automaticDeathSaver at h
  split at h
  · simp at h
  · cases found : s.selectedDeathGear id used with
    | some gear =>
      have eq : gear = cost := by simpa [found] using h
      subst gear
      exact GameState.selectedDeathGear_mem found
    | none => cases free : s.freeDeathSaver id used <;> simp [found, free] at h

/-- The choice of the affected object's controller takes precedence over an automatic saver. -/
def GameState.deathSaver (s : GameState) (id : ObjId) : Option (Option ObjId) :=
  if (s.chosenDeathBanisher id).isSome then none else
    match s.selectedDeathSacrifice id with
    | some cost => some (some cost)
    | none => s.automaticDeathSaver id

/-- The object selected to pay for a death replacement is in play. -/
theorem GameState.deathSaver_cost_mem {s : GameState} {id cost : ObjId}
    (h : s.deathSaver id = some (some cost)) : cost ∈ s.inPlay := by
  unfold GameState.deathSaver at h
  split at h
  · contradiction
  · split at h
    · rename_i unit hu
      cases h
      exact GameState.selectedDeathSacrifice_mem hu
    · exact GameState.automaticDeathSaver_cost_mem h

/-- Forget the decision after this event, so declining does not disable a later replacement. -/
def closeDeathSacrifice (s : GameState) (id : ObjId) : GameState :=
  { s with turnFx := s.turnFx.filter (fun note =>
    note.target != some id || match note.kind with
      | .deathSacrificeChoice _ | .chosenDeathGear _ | .chosenDeathFree _ => false
      | _ => true) }

theorem closeDeathSacrifice_safe (s : GameState) (id : ObjId) : Safe s (closeDeathSacrifice s id) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Use the decision for this event in place of any other death choices about this Unit. -/
def GameState.applyDeathDecision (s : GameState) (id : ObjId)
    (decision : Option (PlayerId × DeathDecision)) : GameState :=
  let cleared := (closeDeathSacrifice s id).turnFx.filter (fun note =>
    !note.appliesTo s.turn id .chosenDeathBanisher)
  let selected := decision.map fun (p, choice) =>
    let (actor, kind) := match choice with
      | .gear gear => (p, TurnEffect.chosenDeathGear gear)
      | .free source => (p, .chosenDeathFree source)
      | .banish player => (player, .chosenDeathBanisher)
      | .sacrifice cost => (p, .deathSacrificeChoice cost)
    { who := actor, turn := s.turn, stamp := s.nextTimestamp, kind, target := some id : TurnFx }
  { s with turnFx := cleared ++ selected.toList }

theorem GameState.applyDeathDecision_safe (s : GameState) (id : ObjId)
    (decision : Option (PlayerId × DeathDecision)) : Safe s (s.applyDeathDecision id decision) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Look up this exact occurrence, even if an earlier Kill targeted the same Unit. -/
def GameState.nestedDeathDecision (s : GameState) (root id : ObjId) (used : List (ObjId × Bool)) :
    Option (PlayerId × DeathDecision) :=
  s.turnFx.reverse.findSome? fun note =>
    if note.turn != s.turn || note.target != some id then none else
      match note.kind with
      | .nestedDeathDecision r prior choice none =>
        if r == root && prior == used then some (note.who, choice) else none
      | _ => none

/-- Read or apply a nested Kill with only the selections for that occurrence available. -/
def prepareNestedDeath (s : GameState) (root id : ObjId) (used : List (ObjId × Bool)) : GameState :=
  { s with turnFx := if used.isEmpty then s.turnFx else
      (clearClosedDeathSequences (s.applyDeathDecision id (s.nestedDeathDecision root id used))).turnFx }

/-- Clear the chain's choices once its original Kill has finished. -/
def finishNestedDeaths (s : GameState) (root : ObjId) : GameState :=
  { s with turnFx := s.turnFx.filter fun note =>
      match note.kind with | .nestedDeathDecision r _ _ none => r != root | _ => true }

theorem finishNestedDeaths_safe (s : GameState) (root : ObjId) : Safe s (finishNestedDeaths s root) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Clear the decisions for this death and record which limited rescue it spent, if any. -/
def finishDeathSave (s : GameState) (id : ObjId) (p : PlayerId)
    (mark : Option TurnEffect) (clear : Bool := true) : GameState :=
  let notes := if clear then (closeDeathSacrifice s id).turnFx else s.turnFx
  { s with turnFx := notes ++ mark.toList.map (fun kind =>
      { who := p, turn := s.turn, stamp := s.nextTimestamp, kind, target := some id }) }

theorem finishDeathSave_safe (s : GameState) (id : ObjId) (p : PlayerId)
    (mark : Option TurnEffect) (clear : Bool) : Safe s (finishDeathSave s id p mark clear) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Only the replacement that actually saved the Unit spends its once-per-turn permission. -/
def GameState.deathSaveMark (s : GameState) (id : ObjId) (sacrifice : Bool)
    (cost : Option ObjId) (used : List (ObjId × Bool) := []) : Option TurnEffect :=
  if sacrifice then some .deathSacrificeUsed
  -- Retain the rescue note in existing replays when there is no Tactical Retreat to consume.
  else if (s.tacticalRetreatFor id).isNone ||
      (cost.isNone && s.freeDeathSaver id used == some none) then some .saveUsed
  else none

/-- The Unit is saved: the permanent that dies instead is killed, and the Unit is healed, exhausted
and recalled. -/
def saveUnitCore (s : GameState) (id : ObjId) (g : Option ObjId) : GameState × List Event :=
  let k := match g with | some g => killObj s g | none => (s, [])
  let healed := healAllOn k.1 id
  let recalled := recallFx false healed.1 id
  -- Recall preserves readiness, so the Exhaust event can precede the Recall event as instructed.
  let exhausted := setExhausted true recalled.1 id
  (exhausted.1, k.2 ++ healed.2 ++ exhausted.2 ++ recalled.2)

/-- Saving a Unit is a safe change. -/
theorem saveUnitCore_safe (s : GameState) (id : ObjId) (g : Option ObjId) :
    Safe s (saveUnitCore s id g).1 := by
  unfold saveUnitCore
  have hk : Safe s (match g with | some g => killObj s g | none => (s, [])).1 := by
    cases g with
    | none => exact Safe.refl s
    | some g => exact killObj_safe s g
  exact hk.trans ((healAllOn_safe _ id).trans
    ((recallFx_safe false _ id).trans (setExhausted_safe true _ id)))

/-- The Unit is saved, and the note that it has been saved is made (what saves it once is used up). -/
def saveUnit (s : GameState) (id : ObjId) (g : Option ObjId) : GameState × List Event :=
  let r := saveUnitCore s id g
  let p := ((s.obj? id).map (·.controller)).getD ⟨0⟩
  let used := g.isSome && g == s.selectedDeathSacrifice id
  (finishDeathSave r.1 id p (s.deathSaveMark id used g), r.2)

/-- Saving a Unit is a safe change. -/
theorem saveUnit_safe (s : GameState) (id : ObjId) (g : Option ObjId) :
    Safe s (saveUnit s id g).1 := by
  unfold saveUnit
  dsimp only
  exact (saveUnitCore_safe s id g).trans (finishDeathSave_safe _ id _ _ true)

/-- A survival replacement can have a Kill of its own (CR 370.2). -/
structure DeathSave where
  /-- Use the Unit's selected once-per-turn sacrifice. -/
  isSacrifice : Bool
  /-- The permanent that would die as part of the replacement's instructions. -/
  cost : Option ObjId

/-- An automatic sacrifice of Gear is keyed by its source. A Unit's own sacrifice and a free
replacement are keyed by the affected Unit (CR 370.2). -/
def DeathSave.useKey (save : DeathSave) (victim : ObjId) : ObjId × Bool :=
  if save.isSacrifice then (victim, true) else (save.cost.getD victim, false)

/-- Each survival replacement is available only once across one resulting sequence of deaths. -/
def GameState.deathSaveFor (s : GameState) (id : ObjId)
    (used : List (ObjId × Bool)) : Option DeathSave :=
  if !(s.cardDef? id).any (·.hasType .unit) || (s.chosenDeathBanisher id).isSome then none else
    let sacrifice := if used.contains (id, true) then none else s.selectedDeathSacrifice id
    match sacrifice with
    | some cost => some ⟨true, some cost⟩
    | none => (s.automaticDeathSaver id used).map (fun cost => ⟨false, cost⟩)

/-- Each replacement Kill can involve only a permanent that is still on the Board. -/
theorem GameState.deathSaveFor_cost_mem {s : GameState} {id cost : ObjId}
    {used : List (ObjId × Bool)} {isSacrifice : Bool}
    (h : s.deathSaveFor id used = some ⟨isSacrifice, some cost⟩) : cost ∈ s.inPlay := by
  unfold GameState.deathSaveFor at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · rename_i chosen hchosen
      have heq := congrArg DeathSave.cost (Option.some.inj h)
      have eq : chosen = cost := Option.some.inj heq
      subst chosen
      split at hchosen
      · contradiction
      · exact GameState.selectedDeathSacrifice_mem hchosen
    · cases ha : s.automaticDeathSaver id used with
      | none => simp [ha] at h
      | some chosen =>
        have heq := congrArg DeathSave.cost (Option.some.inj (by simpa only [ha, Option.map_some] using h))
        exact GameState.automaticDeathSaver_cost_mem (ha.trans (congrArg some heq))

/-- Heal, exhaust, and recall after the replacement Kill has completed. -/
def completeDeathSave (s : GameState) (id : ObjId) (mark : Option TurnEffect)
    (p : PlayerId) (clear : Bool) : GameState × List Event :=
  let recalled := saveUnitCore s id none
  (finishDeathSave recalled.1 id p mark clear, recalled.2)

theorem completeDeathSave_safe (s : GameState) (id : ObjId) (mark : Option TurnEffect)
    (p : PlayerId) (clear : Bool) : Safe s (completeDeathSave s id mark p clear).1 :=
  (saveUnitCore_safe s id none).trans (finishDeathSave_safe _ id p mark clear)

/-- Resolve any Kill that is part of a replacement before performing its remaining instructions. -/
def killOrSaveFrom (root : ObjId) :
    Nat → GameState → ObjId → List (ObjId × Bool) → GameState × List Event
  | 0, s, id, used => killObj (prepareNestedDeath s root id used) id
  | fuel + 1, s, id, used =>
    let ready := prepareNestedDeath s root id used
    match ready.deathSaveFor id used with
    | none => killObj ready id
    | some save =>
      let replaced := save.cost.elim (s, [])
        (fun cost => killOrSaveFrom root fuel s cost (save.useKey id :: used))
      let owner := ((s.obj? id).map (·.controller)).getD ⟨0⟩
      let completed := completeDeathSave replaced.1 id
        (ready.deathSaveMark id save.isSacrifice save.cost used) owner used.isEmpty
      (completed.1, replaced.2 ++ completed.2)

/-- Resolve a Kill, allowing each in-play Unit its own and its automatic replacement. -/
def killOrSave (s : GameState) (id : ObjId) : GameState × List Event :=
  let resolved := killOrSaveFrom id (2 * s.inPlay.length) s id []
  (finishNestedDeaths resolved.1 id, resolved.2)

theorem prepareNestedDeath_safe (s : GameState) (root id : ObjId)
    (used : List (ObjId × Bool)) : Safe s (prepareNestedDeath s root id used) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

theorem killOrSaveFrom_safe (root : ObjId) :
    ∀ (fuel : Nat) (s : GameState) (id : ObjId) (used : List (ObjId × Bool)),
      Safe s (killOrSaveFrom root fuel s id used).1
  | 0, s, id, used => (prepareNestedDeath_safe s root id used).trans (killObj_safe _ _)
  | fuel + 1, s, id, used => by
    unfold killOrSaveFrom
    dsimp only
    split
    · exact (prepareNestedDeath_safe s root id used).trans (killObj_safe _ _)
    · rename_i save _
      have prior : Safe s
          (save.cost.elim (s, []) (fun cost => killOrSaveFrom root fuel s cost
            (save.useKey id :: used))).1 := by
        cases h : save.cost with
        | none => exact Safe.refl s
        | some cost => exact killOrSaveFrom_safe root fuel s cost _
      exact prior.trans (completeDeathSave_safe _ id _ _ _)

/-- Killing or saving preserves the game invariants, including the entire sequence of costs. -/
theorem killOrSave_safe (s : GameState) (id : ObjId) : Safe s (killOrSave s id).1 :=
  (killOrSaveFrom_safe id _ _ _ _).trans (finishNestedDeaths_safe _ _)

/-- Every in-play object is in a Board zone. -/
theorem GameState.mem_inPlay_zone {s : GameState} {id : ObjId} (h : id ∈ s.inPlay) :
    ∃ origin, origin.isBoard = true ∧ id ∈ s.zone origin := by
  simp only [GameState.inPlay, List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨p, _, h⟩ | h
  · exact ⟨.player p .base, rfl, h⟩
  · exact ⟨.battlefieldZone, rfl, h⟩

/-- A recall keeps any Non-Board zone that does not contain the recalled object. -/
theorem recallFx_zone_of_not_mem {s : GameState} {u : ObjId} {z : Zone}
    (ex : Bool) (hz : z.isBoard = false) (hu : u ∉ s.zone z) :
    (recallFx ex s u).1.zone z = s.zone z := by
  have hs : (sendHome s u).1.zone z = s.zone z := by
    unfold sendHome
    split
    · split
      · rename_i _ _ result hm
        obtain ⟨src, dst, spec, o, _, hdst⟩ := moveObj_spec_dst hm
        have hsrc : z ≠ src := by
          intro h
          subst h
          exact hu (GameState.locate_spec spec.locate).2
        have hbase : z ≠ dst := by
          intro h
          subst h
          rw [hdst] at hz
          contradiction
        exact (GameState.zone_modObj _ _ _ _).trans (spec.zone_other hsrc hbase)
      · rfl
    · rfl
  cases ex with
  | false => exact hs
  | true =>
    have he : (setExhausted true (sendHome s u).1 u).1.zone z = (sendHome s u).1.zone z := by
      unfold setExhausted
      split
      · exact GameState.zone_modObj _ _ _ _
      · rfl
    exact he.trans hs

/-- The Kill and its replacements affect only Board, Trash, and Banishment zones. -/
theorem killOrSaveFrom_zone_other (root : ObjId) (fuel : Nat) {s : GameState} (hwf : s.WF)
    {id : ObjId} {used : List (ObjId × Bool)} {z : Zone}
    (hid : id ∈ s.inPlay) (hz : z.isBoard = false)
    (hd : ∀ q k, (k = ZoneKind.trash ∨ k = ZoneKind.banishment) → z ≠ .player q k) :
    (killOrSaveFrom root fuel s id used).1.zone z = s.zone z := by
  induction fuel generalizing s id used with
  | zero =>
    obtain ⟨origin, hboard, hmem⟩ := GameState.mem_inPlay_zone hid
    exact killObj_zone_other ((prepareNestedDeath_safe s root id used).wf hwf)
      hmem (by rintro rfl; simp [hboard] at hz) hd
  | succ fuel ih =>
    obtain ⟨origin, hboard, hmem⟩ := GameState.mem_inPlay_zone hid
    have hother : z ≠ origin := by rintro rfl; simp [hboard] at hz
    have hnot : id ∉ s.zone z := by
      intro hm
      have h₁ := GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hm) hm
      have h₂ := GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hmem) hmem
      exact hother (Option.some.inj (h₁.symm.trans h₂))
    unfold killOrSaveFrom
    dsimp only
    split
    · exact killObj_zone_other ((prepareNestedDeath_safe s root id used).wf hwf) hmem hother hd
    · rename_i save found
      let paid := (save.cost.elim (s, []) (fun cost => killOrSaveFrom root fuel s cost
        (save.useKey id :: used))).1
      have hpaid : paid.zone z = s.zone z := by
        unfold paid
        cases save with
        | mk mode cost =>
          cases cost with
          | none => rfl
          | some next =>
            have member : next ∈ (prepareNestedDeath s root id used).inPlay :=
              GameState.deathSaveFor_cost_mem found
            exact ih hwf member
      let healed := paid.modObj id (fun o => { o with damage := 0 })
      have hzone : healed.zone z = s.zone z := (GameState.zone_modObj _ _ _ _).trans hpaid
      have hpresent : id ∉ healed.zone z := by rw [hzone]; exact hnot
      exact (recallFx_zone_of_not_mem true hz hpresent).trans hzone

theorem killOrSave_zone_other {s : GameState} (hwf : s.WF) {id : ObjId} {z : Zone}
    (hid : id ∈ s.inPlay) (hz : z.isBoard = false)
    (hd : ∀ q k, (k = ZoneKind.trash ∨ k = ZoneKind.banishment) → z ≠ .player q k) :
    (killOrSave s id).1.zone z = s.zone z :=
  killOrSaveFrom_zone_other id _ hwf hid hz hd

/-- A card held off the Board cannot be the chosen Board object. -/
theorem offBoard_ne_of_inPlay {s : GameState} (hwf : s.WF) {z : Zone} {c id : ObjId}
    (hz : z.isBoard = false) (hc : c ∈ s.zone z) (hi : id ∈ s.inPlay) : c ≠ id := by
  obtain ⟨origin, board, there⟩ := GameState.mem_inPlay_zone hi
  exact ne_of_mem_other_zone hwf there hc (by intro eq; rw [eq, board] at hz; contradiction)

/-- Modifying a different object retains the declared card and the resources. -/
theorem RetainsCard.modOther {s : GameState} {z : Zone} {c id : ObjId}
    (different : c ≠ id) (hc : c ∈ s.zone z) (f : Object → Object) :
    RetainsCard s (s.modObj id f) z c := by
  have n : id.n ≠ c.n := by
    intro eq
    exact different (by cases c; cases id; simp_all)
  exact ⟨hc, by rw [GameState.obj?_modObj, ite_eq_right n], rfl⟩

private theorem noteIf_retains {s : GameState} {z : Zone} {c : ObjId}
    (b : Bool) (f : GameState → GameState)
    (keep : RetainsCard s (f s) z c) (hc : c ∈ s.zone z) :
    RetainsCard s (noteIf b f s) z c := by
  unfold noteIf
  split
  · exact keep
  · exact RetainsCard.refl hc

/-- The notes from a Kill retain every card other than the recorded victim. -/
theorem noteDeath_retains {s : GameState} {z : Zone} {c : ObjId} (hc : c ∈ s.zone z)
    (o : Object) (isUnit marked mighty : Bool) (moved banisher : Option ObjId)
    (different : moved ≠ some c) : RetainsCard s (noteDeath s o isUnit marked mighty moved banisher) z c := by
  unfold noteDeath
  have unitNote : RetainsCard s (s.noteUnitDied o.controller) z c := by
    unfold GameState.noteUnitDied
    split <;> exact ⟨hc, rfl, rfl⟩
  have first := noteIf_retains (isUnit && moved.isSome) (·.noteUnitDied o.controller) unitNote hc
  cases moved with
  | none => exact first
  | some n =>
    have hne : c ≠ n := fun h => different (congrArg some h.symm)
    let mark (b : Bool) (kind : TurnEffect) {s0 : GameState} (member : c ∈ s0.zone z) :=
      noteIf_retains b (·.addTurnFxOn o.controller n kind) ⟨member, rfl, rfl⟩ member
    have buffs := mark (isUnit && o.buffed) .buffedUnitDied first.member
    have stun := mark (isUnit && o.stunned) .stunnedUnitDied buffs.member
    have big := mark (isUnit && mighty) .mightyUnitDied stun.member
    have recalled := mark (isUnit && marked) .recallDied big.member
    have banish := noteIf_retains banisher.isSome (fun t => t.modObj n (fun x => { x with banishedWith := banisher }))
      (RetainsCard.modOther hne recalled.member _) recalled.member
    exact first.trans (buffs.trans (stun.trans (big.trans (recalled.trans banish))))

private theorem retains_noteAlone {s t : GameState} {z : Zone} {c : ObjId}
    (keep : RetainsCard s t z c) (o : Object) (moved : Option ObjId) (alone : Bool) :
    RetainsCard s (noteAlone t o moved alone) z c := by
  cases moved with
  | none => exact keep
  | some n =>
    cases alone <;> exact ⟨keep.member, keep.object, keep.pools⟩

/-- Killing another object keeps the card in its zone, including when the victim goes to that zone. -/
theorem killObj_retains {s : GameState} (hwf : s.WF) {z : Zone} {c id : ObjId}
    (hc : c ∈ s.zone z) (different : c ≠ id) : RetainsCard s (killObj s id).1 z c := by
  unfold killObj sendObj
  generalize (if s.banishedOnDeath id = true then ZoneKind.banishment else .trash) = dest
  cases found : s.obj? id with
  | none => exact RetainsCard.refl hc
  | some o =>
    cases moved : moveObj s id (.player o.owner (s.ownerDestination id o dest)) with
    | none =>
      dsimp only
      rw [moved]
      dsimp only
      split
      · exact RetainsCard.refl hc
      · dsimp only
        apply retains_noteAlone
        exact noteDeath_retains hc o _ _ _ none _ (by simp)
    | some result =>
      obtain ⟨paid, new⟩ := result
      dsimp only
      rw [moved]
      obtain ⟨_, _, spec⟩ := moveObj_spec moved
      obtain ⟨kept, hne⟩ := spec.retainsOther hwf (GameState.zone_valid_of_mem hwf hc) hc different
      dsimp only
      split
      · exact kept
      · dsimp only
        apply retains_noteAlone
        refine kept.trans (noteDeath_retains kept.member o _ _ _ _ _ ?_)
        simp [Object.ownerMoveEvents, Ne.symm hne]

/-- Recalling and updating another Unit leaves the card and the Rune Pools where they are. -/
theorem completeDeathSave_retains {s : GameState} (hwf : s.WF) {z : Zone} {c id : ObjId}
    (hc : c ∈ s.zone z) (different : c ≠ id) (mark : Option TurnEffect) (p : PlayerId) (clear : Bool) :
    RetainsCard s (completeDeathSave s id mark p clear).1 z c := by
  unfold completeDeathSave saveUnitCore
  dsimp only
  have healed := RetainsCard.modOther different hc healObj
  have recalled : RetainsCard (healAllOn s id).1 (sendHome (healAllOn s id).1 id).1 z c := by
    unfold sendHome
    split
    · split
      · rename_i r moved
        obtain ⟨_, _, spec⟩ := moveObj_spec moved
        have h := (healAllOn_safe s id).wf hwf
        obtain ⟨kept, distinct⟩ := spec.retainsOther h (GameState.zone_valid_of_mem h healed.member)
          healed.member different
        exact kept.trans (RetainsCard.modOther distinct kept.member _)
      · exact RetainsCard.refl healed.member
    · exact RetainsCard.refl healed.member
  have exhausted : RetainsCard (sendHome (healAllOn s id).1 id).1
      (setExhausted true (sendHome (healAllOn s id).1 id).1 id).1 z c := by
    unfold setExhausted
    split
    · exact RetainsCard.modOther different recalled.member _
    · exact RetainsCard.refl recalled.member
  have keep := healed.trans (recalled.trans exhausted)
  exact ⟨keep.member, keep.object, keep.pools⟩

/-- A nested Kill and its replacements retain the card being played off the Board. -/
theorem killOrSaveFrom_retains (root : ObjId) (fuel : Nat) {s : GameState} (hwf : s.WF)
    {id : ObjId} {used : List (ObjId × Bool)} {z : Zone} {c : ObjId}
    (hi : id ∈ s.inPlay) (hz : z.isBoard = false) (hc : c ∈ s.zone z) :
    RetainsCard s (killOrSaveFrom root fuel s id used).1 z c := by
  induction fuel generalizing s id used with
  | zero =>
    have keep := killObj_retains ((prepareNestedDeath_safe s root id used).wf hwf) hc
      (offBoard_ne_of_inPlay hwf hz hc hi)
    exact ⟨keep.member, keep.object, keep.pools⟩
  | succ fuel ih =>
    have distinct := offBoard_ne_of_inPlay hwf hz hc hi
    unfold killOrSaveFrom
    dsimp only
    split
    · have keep := killObj_retains ((prepareNestedDeath_safe s root id used).wf hwf) hc distinct
      exact ⟨keep.member, keep.object, keep.pools⟩
    · rename_i save found
      cases cost : save.cost with
      | none => exact completeDeathSave_retains hwf hc distinct _ _ _
      | some next =>
        have valid : next ∈ s.inPlay := by
          have eq : save = ⟨save.isSacrifice, some next⟩ := by cases save; simp_all
          have h := GameState.deathSaveFor_cost_mem (found.trans (congrArg some eq))
          exact h
        have first := ih hwf (used := save.useKey id :: used) valid hc
        have safe := (killOrSaveFrom_safe root fuel s next (save.useKey id :: used)).wf hwf
        simpa only [cost, Option.elim_some] using first.trans
          (completeDeathSave_retains safe first.member distinct _ _ _)

/-- Killing or replacing the Kill of a Board object retains an off-Board card and the Pools. -/
theorem killOrSave_retains {s : GameState} (hwf : s.WF) {id : ObjId} {z : Zone} {c : ObjId}
    (hi : id ∈ s.inPlay) (hz : z.isBoard = false) (hc : c ∈ s.zone z) :
    RetainsCard s (killOrSave s id).1 z c := by
  have keep := killOrSaveFrom_retains id (2 * s.inPlay.length) (used := []) hwf hi hz hc
  exact ⟨keep.member, keep.object, keep.pools⟩

end Riftbound

end
