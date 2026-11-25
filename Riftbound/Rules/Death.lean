module

public import Riftbound.Rules.Passive

/-! # Sending objects to owner zones and resolving death -/

@[expose] public section

namespace Riftbound

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
  let r := sendHome s u
  if ex then ((setExhausted true r.1 u).1, r.2 ++ (setExhausted true r.1 u).2) else r

/-- Recalling is a safe change. -/
theorem recallFx_safe (ex : Bool) (s : GameState) (u : ObjId) : Safe s (recallFx ex s u).1 := by
  unfold recallFx
  cases ex
  · exact sendHome_safe s u
  · exact (sendHome_safe s u).trans (setExhausted_safe true _ u)

/-- An effect of this turn saves the unit the next time it would die, and has not saved it yet
(Tactical Retreat). -/
def GameState.saveOnceFor (s : GameState) (id : ObjId) : Bool :=
  s.turnFx.any (fun f => f.kind == .saveOnce && f.target == some id && f.turn == s.turn) &&
    !s.turnFx.any (fun f => f.kind == .saveUsed && f.target == some id && f.turn == s.turn)

/-- What would save a Unit that is about to die ("If I would die, ... instead"): an Equipment
attached to it that says so (Guardian Angel: it dies instead), or a Unit of the same player at the
same Battlefield with more Might that says so (Soraka). `some (some g)` if the Equipment `g` dies
instead, `some none` if nothing does. -/
def GameState.deathSaver (s : GameState) (id : ObjId) : Option (Option ObjId) :=
  match s.inPlay.find? (fun g => (s.obj? g).any (·.attached == some id) &&
      (s.cardDef? g).any (fun d => d.grants.any (fun ab =>
        match ab with
        | Ability.passive .always mods => mods.contains .diesInsteadGear
        | _ => false))) with
  | some g => some (some g)
  | none =>
    match s.obj? id with
    | some o =>
      if s.saveOnceFor id || s.inPlay.any (fun u => u != id &&
          (s.obj? u).any (fun v => v.controller == o.controller && v.loc == o.loc) &&
          (s.activeMods u).contains .rescueWeakerHere &&
          decide ((s.mightNow id).getD 0 < (s.mightNow u).getD 0)) then some none
      else none
    | none => none

/-- The Unit is saved: the Equipment that dies instead is killed, and the Unit is healed, exhausted
and recalled. -/
def saveUnitCore (s : GameState) (id : ObjId) (g : Option ObjId) : GameState × List Event :=
  let k := match g with | some g => killObj s g | none => (s, [])
  let h := k.1.modObj id (fun o => { o with damage := 0 })
  let r := recallFx true h id
  (r.1, k.2 ++ r.2)

/-- Saving a Unit is a safe change. -/
theorem saveUnitCore_safe (s : GameState) (id : ObjId) (g : Option ObjId) :
    Safe s (saveUnitCore s id g).1 := by
  unfold saveUnitCore
  have hk : Safe s (match g with | some g => killObj s g | none => (s, [])).1 := by
    cases g with
    | none => exact Safe.refl s
    | some g => exact killObj_safe s g
  have hm := Safe.modObj (match g with | some g => killObj s g | none => (s, [])).1 id
    (f := fun o => { o with damage := 0 }) (fun _ => rfl) (fun _ => rfl)
  exact hk.trans (hm.trans (recallFx_safe true _ id))

/-- The Unit is saved, and the note that it has been saved is made (what saves it once is used up). -/
def saveUnit (s : GameState) (id : ObjId) (g : Option ObjId) : GameState × List Event :=
  let r := saveUnitCore s id g
  (r.1.addTurnFxOn (match s.obj? id with | some o => o.controller | none => ⟨0⟩) id .saveUsed, r.2)

/-- Saving a Unit is a safe change. -/
theorem saveUnit_safe (s : GameState) (id : ObjId) (g : Option ObjId) :
    Safe s (saveUnit s id g).1 :=
  (saveUnitCore_safe s id g).trans (addTurnFxOn_safe _ _ _ _)

/-- Kill an object, unless something saves it (it would die). -/
def killOrSave (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.deathSaver id with
  | some g => if (s.cardDef? id).any (·.hasType .unit) then saveUnit s id g else killObj s id
  | none => killObj s id

/-- Killing, or saving, is a safe change. -/
theorem killOrSave_safe (s : GameState) (id : ObjId) : Safe s (killOrSave s id).1 := by
  unfold killOrSave
  split
  · split
    · exact saveUnit_safe s id _
    · exact killObj_safe s id
  · exact killObj_safe s id

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

/-- A saved object stays on the Board. Killing its replacement Gear changes no other zone
besides the Gear's own position, Trash, and Banishment (CR 370, 456). -/
theorem killOrSave_zone_other {s : GameState} (hwf : s.WF) {id : ObjId} {z : Zone}
    (hid : id ∈ s.inPlay) (hz : z.isBoard = false)
    (hd : ∀ q k, (k = ZoneKind.trash ∨ k = ZoneKind.banishment) → z ≠ .player q k) :
    (killOrSave s id).1.zone z = s.zone z := by
  obtain ⟨origin, hboard, hmem⟩ := GameState.mem_inPlay_zone hid
  have hother : z ≠ origin := by intro h; subst h; simp [hboard] at hz
  have hkill := killObj_zone_other hwf hmem hother hd
  have hnot : id ∉ s.zone z := by
    intro hm
    have h₁ := GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hm) hm
    have h₂ := GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hmem) hmem
    exact hother (Option.some.inj (h₁.symm.trans h₂))
  unfold killOrSave
  split
  · rename_i saver hsaver
    split
    · have hgear : ∀ gear, saver = some gear → gear ∈ s.inPlay := by
        intro gear he
        subst saver
        unfold GameState.deathSaver at hsaver
        split at hsaver
        · rename_i g hg
          cases hsaver
          exact List.mem_of_find?_eq_some hg
        · split at hsaver
          · split at hsaver <;> simp at hsaver
          · simp at hsaver
      have hk : (match saver with | some gear => killObj s gear | none => (s, [])).1.zone z =
          s.zone z := by
        cases h : saver with
        | none => rfl
        | some gear =>
          obtain ⟨source, hb, hm⟩ := GameState.mem_inPlay_zone (hgear gear h)
          have hne : z ≠ source := by intro eq; subst eq; simp [hb] at hz
          exact killObj_zone_other hwf hm hne hd
      unfold saveUnit saveUnitCore
      let killed := (match saver with | some gear => killObj s gear | none => (s, [])).1
      let healed := killed.modObj id (fun o => { o with damage := 0 })
      have hzone : healed.zone z = s.zone z := (GameState.zone_modObj _ _ _ _).trans hk
      have hn : id ∉ healed.zone z := by rw [hzone]; exact hnot
      exact (recallFx_zone_of_not_mem true hz hn).trans hzone
    · exact hkill
  · exact hkill

end Riftbound

end
