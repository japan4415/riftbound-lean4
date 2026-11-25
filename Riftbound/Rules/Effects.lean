module

public import Riftbound.Rules.Play
public import Riftbound.Rules.Remove
public import Riftbound.Rules.Owner
public import Riftbound.Rules.Actions.BurnOut
public import Riftbound.Tournament.DeckLegality

/-!
# Running an effect

The interpreter of the effect IR, one step at a time (design.md §6.1, §7.1). A `run` frame holds
the effects still to do; `runEffect` looks at the first and says which frames replace the `run`
frame. Only a few instructions have a meaning yet: doing nothing, a sequence, a bound variable,
and drawing. An instruction that cannot be done is skipped with an event, never an error (design.md
§7.1), so that the interpreter is total.
-/

@[expose] public section

namespace Riftbound

/-- The effects of the first list, then those of the second. -/
def EffectList.append : EffectList → EffectList → EffectList
  | .nil, l => l
  | .cons e rest, l => .cons e (rest.append l)

/-- `n` copies of an effect. -/
def EffectList.replicate : Nat → Effect → EffectList
  | 0, _ => .nil
  | n + 1, e => .cons e (EffectList.replicate n e)

namespace GameState

/-- The player who gets priority after `p`: the next one in the turn order (CR 311). -/
def nextPlayer (s : GameState) (p : PlayerId) : PlayerId :=
  match s.turnOrder.idxOf? p with
  | some i => s.turnOrder.getD ((i + 1) % s.turnOrder.length) p
  | none => p

end GameState

/-- Put each object of the list through `g`, one after the other: the last state, and all the
events. -/
def applyEach (g : GameState → ObjId → GameState × List Event) :
    GameState → List ObjId → GameState × List Event
  | s, [] => (s, [])
  | s, id :: ids =>
    let r := g s id
    let r2 := applyEach g r.1 ids
    (r2.1, r.2 ++ r2.2)

/-- Putting each object through changes that are safe is a safe change. -/
theorem applyEach_safe {g : GameState → ObjId → GameState × List Event}
    (hg : ∀ s id, Safe s (g s id).1) : ∀ (ids : List ObjId) (s : GameState),
      Safe s (applyEach g s ids).1
  | [], s => Safe.refl s
  | id :: ids, s => (hg s id).trans (applyEach_safe hg ids (g s id).1)

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

/-- The Chosen Champion of the player: a Unit of the Champion the Legend of the player is about
(they share a tag). The card data does not tell Champions from other Units, nor the Chosen
Champion from its copies. -/
def GameState.chosenOf (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  let tags := (s.zone (.player p .legendZone)).flatMap (fun l =>
    ((s.cardDef? l).map (·.tags)).getD [])
  (s.cardDef? id).any (fun d =>
    d.hasType .unit && d.tags.any (fun t => tags.contains t))

/-- The player returns their Chosen Champion from their Trash to their Champion Zone, if the
Champion Zone is empty. -/
def returnChampion (p : PlayerId) (s : GameState) : GameState × List Event :=
  if (s.zone (.player p .championZone)).isEmpty then
    match (s.zone (.player p .trash)).find? (fun u => s.chosenOf p u) with
    | some id => sendObj .championZone s id
    | none => (s, [])
  else (s, [])

/-- Returning the Chosen Champion is a safe change. -/
theorem returnChampion_safe (p : PlayerId) (s : GameState) : Safe s (returnChampion p s).1 := by
  unfold returnChampion
  split
  · split
    · exact sendObj_safe _ _ _
    · exact Safe.refl s
  · exact Safe.refl s

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

/-- The player whose effect banishes the Unit instead of sending it to the Trash on death
(Smite). A later Deathknell banishes separately. -/
def GameState.banishOnDeathBy (s : GameState) (id : ObjId) : Option PlayerId :=
  (s.turnFx.find? (fun f =>
    f.kind == .banishInstead && f.target == some id && f.turn == s.turn)).map (·.who)

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

/-- Kill an object: it goes to its owner's Trash (or is banished, if an Equipment says so). -/
def killObj (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := sendObj (if s.banishedOnDeath id then ZoneKind.banishment else .trash) s id
  match s.obj? id with
  | some o =>
    if r.2.any (fun | .banished .. => true | _ => false) then r else
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
      | _ => none) ++ (s.banishOnDeathBy id).toList.flatMap
        (fun p => banishCardEvents p s id r.2))
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
    simp only [List.any_nil, Bool.false_eq_true, ite_false, noteAlone_zone, noteDeath_zone]
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

/-- Heal `n` damage from an object (CR 419). -/
def healOne (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some _ => (s.modObj id (fun o => { o with damage := o.damage - n }), [Event.healed id n])
  | none => (s, [])

/-- Healing is a safe change. -/
theorem healOne_safe (n : Nat) (s : GameState) (id : ObjId) : Safe s (healOne n s id).1 := by
  unfold healOne
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- Make an object ready or exhausted (CR 415, 416). -/
def setExhausted (b : Bool) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    -- only an object that was exhausted is readied, and only a ready one is exhausted (CR 416)
    (s.modObj id (fun o => { o with exhausted := b }),
      if b then [Event.exhausted id] else if o.exhausted then [Event.readied id] else [])
  | none => (s, [])

/-- Readying or exhausting is a safe change. -/
theorem setExhausted_safe (b : Bool) (s : GameState) (id : ObjId) :
    Safe s (setExhausted b s id).1 := by
  unfold setExhausted
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- A spell or an ability cannot ready the Units and Gear of the opponents of a player who has a
passive ability that says so. -/
def readyBlocked (s : GameState) (id : ObjId) : Bool :=
  ((s.obj? id).any (fun o => s.oppHas o.controller .noReadyOfOpps) &&
    (s.cardDef? id).any (fun d => d.hasType .unit || d.hasType .gear)) ||
  (s.obj? id).any (·.cantReady)

/-- A spell or an ability readies an object, unless it cannot. -/
def readyEffect (s : GameState) (id : ObjId) : GameState × List Event :=
  if readyBlocked s id then (s, []) else setExhausted false s id

/-- Readying by an effect is a safe change. -/
theorem readyEffect_safe (s : GameState) (id : ObjId) : Safe s (readyEffect s id).1 := by
  unfold readyEffect
  split
  · exact Safe.refl s
  · exact setExhausted_safe false s id

/-- Put each object that the selector stands for through `g`. `none` if the selector cannot be
answered yet. -/
def onSelected (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (g : GameState → ObjId → GameState × List Event) : Option (GameState × List Event) :=
  (sel.eval s p src env).map (fun ids => applyEach g s ids)

/-- Changes of the selected objects that are safe are a safe change. -/
theorem onSelected_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {sel : Selector}
    {g : GameState → ObjId → GameState × List Event} (hg : ∀ s id, Safe s (g s id).1)
    {r : GameState × List Event} (h : onSelected s p src env sel g = some r) : Safe s r.1 := by
  unfold onSelected at h
  cases hs : sel.eval s p src env with
  | none => simp [hs] at h
  | some ids =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst h
    exact applyEach_safe hg ids s

/-- Adding an object that is not a physical card is a safe change. -/
theorem safe_addObject {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (hk : o.kind.phys? = none) (h : addObject s o z pos = some (s', id)) : Safe s s' :=
  ⟨fun hwf => addObject_wf hwf h, fun hwf => addObject_physIds hwf h hk,
    fun hwf hown => addObject_ownerOk hwf hown h, addObject_sameMeta h⟩

/-- The identifier of the card of a token the model defines itself (CR 179). -/
def tokenId (name : String) : CardId := ⟨"TKN-" ++ name⟩

/-- The card is a token the rules print: its number has a T, as SFD-T03 (Gold) has. -/
def CardDef.isTokenCard (c : CardDef) : Bool := (c.id.code.splitOn "-T").length > 1

/-- Cards that can be named for this type, whether or not a copy exists in the game (CR 759-762). -/
def GameState.nameableCards (s : GameState) (kind : CardType) : List CardId :=
  (s.cards.cards.filter (fun d =>
    d.hasType kind && !d.isTokenCard && !d.id.code.startsWith "TKN-" &&
      (match s.config.ruleSet, s.config.formatLegality with
        | .tournament .constructed, some env => decide (CardLegal env d)
        | .tournament _, some env => decide (NotBanned env d)
        | _, _ => true))).map (·.id)

/-- The card of the token with the name: one the model defines, or one of the printed tokens. -/
def GameState.tokenCard (s : GameState) (name : String) : Option CardDef :=
  match s.cards.find? (tokenId name) with
  | some c => some c
  | none => s.cards.cards.find? (fun c => c.isTokenCard && c.name == name)

/-- Add an object that is not a physical card to a zone; nothing if it cannot be added. -/
def addTok (s : GameState) (o : Object) (z : Zone) : GameState :=
  match addObject s o z with
  | some r => r.1
  | none => s

/-- Adding a token is a safe change. -/
theorem addTok_safe (s : GameState) (o : Object) (z : Zone) (hk : o.kind.phys? = none) :
    Safe s (addTok s o z) := by
  unfold addTok
  split
  · rename_i r hr
    exact safe_addObject hk hr
  · exact Safe.refl s

/-- Make one token for the player: on their Base, or at the Battlefield `dest` (CR 183). -/
def createOne (card : CardId) (p : PlayerId) (dest : Option ObjId) (ready : Bool)
    (s : GameState) : GameState :=
  let o : Object :=
    { kind := .token card, owner := p, controller := p, exhausted := !ready,
      timestamp := ⟨0⟩, loc := dest }
  match dest with
  | some _ => addTok s o .battlefieldZone
  | none => addTok s o (.player p .base)

/-- Making a token is a safe change. -/
theorem createOne_safe (card : CardId) (p : PlayerId) (dest : Option ObjId) (ready : Bool)
    (s : GameState) : Safe s (createOne card p dest ready s) := by
  unfold createOne
  cases dest <;> exact addTok_safe _ _ _ rfl

/-- Make `n` tokens. -/
def createN (card : CardId) (p : PlayerId) (dest : Option ObjId) (ready : Bool) :
    Nat → GameState → GameState
  | 0, s => s
  | n + 1, s => createN card p dest ready n (createOne card p dest ready s)

/-- Making tokens is a safe change. -/
theorem createN_safe (card : CardId) (p : PlayerId) (dest : Option ObjId) (ready : Bool) :
    ∀ (n : Nat) (s : GameState), Safe s (createN card p dest ready n s)
  | 0, s => Safe.refl s
  | n + 1, s => (createOne_safe card p dest ready s).trans (createN_safe card p dest ready n _)

/-- Stun an object: it deals no combat damage this turn (CR 424). -/
def stunObj (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with stunned := true }), [Event.stunned id])

/-- Stunning is a safe change. -/
theorem stunObj_safe (s : GameState) (id : ObjId) : Safe s (stunObj s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- Add a lasting change of Might to an object (CR 475-478). -/
def addMightMod (m : MightMod) (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with mightMods := o.mightMods ++ [m] }), [])

/-- Adding a change of Might is a safe change. -/
theorem addMightMod_safe (m : MightMod) (s : GameState) (id : ObjId) :
    Safe s (addMightMod m s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- Replace a stun, a Might reduction or a return to hand on a chosen Unit with a
Might bonus if its active abilities say so (CR 370). -/
def replaceChosenHarm (env : Env) (apply : GameState → ObjId → GameState × List Event)
    (s : GameState) (id : ObjId) : GameState × List Event :=
  if env.targetObjs.contains id && s.inPlay.contains id then
    match (s.activeMods id).findSome? (fun
      | .chosenHarmToMight n => some n
      | _ => none) with
    | some n => addMightMod ⟨(n : Int), .turn⟩ s id
    | none => apply s id
  else apply s id

/-- Replacing chosen harm preserves safety when the original instruction does. -/
theorem replaceChosenHarm_safe (env : Env) {apply : GameState → ObjId → GameState × List Event}
    (h : ∀ s id, Safe s (apply s id).1) (s : GameState) (id : ObjId) :
    Safe s (replaceChosenHarm env apply s id).1 := by
  unfold replaceChosenHarm
  split
  · split
    · exact addMightMod_safe _ s id
    · exact h s id
  · exact h s id

/-- Buff an object: it gets a +1 Might buff if it has none (CR 701). -/
def buffObj (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    -- a Unit that can have any number of buffs gets one more
    if o.buffed && (s.activeMods id).contains .anyBuffs then
      (s.modObj id (fun o => { o with extraBuffs := o.extraBuffs + 1 }), [Event.buffed id])
    else
      (s.modObj id (fun o => { o with buffed := true }),
        if o.buffed then [] else [Event.buffed id])
  | none => (s, [])

/-- Buffing is a safe change. -/
theorem buffObj_safe (s : GameState) (id : ObjId) : Safe s (buffObj s id).1 := by
  unfold buffObj
  split
  · split <;> exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- Spend the buff of an object: it loses it (CR 704). -/
def unbuffObj (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o =>
    if 0 < o.extraBuffs then { o with extraBuffs := o.extraBuffs - 1 }
    else { o with buffed := false }),
    match s.obj? id with
    | some o => if o.buffed || 0 < o.extraBuffs then [Event.buffSpent o.controller] else []
    | none => [])

/-- Spending a buff is a safe change. -/
theorem unbuffObj_safe (s : GameState) (id : ObjId) : Safe s (unbuffObj s id).1 :=
  Safe.modObj s id (fun _ => by split <;> rfl) (fun _ => by split <;> rfl)

/-- The player gains XP (CR 728): it goes to their Legend, and the turn notes that they gained XP. -/
def gainXPOf (n : Nat) (s : GameState) (p : PlayerId) : GameState :=
  match s.zone (.player p .legendZone) with
  | l :: _ =>
    let s1 := s.modObj l (fun o => { o with xp := o.xp + n })
    if 0 < n then s1.addTurnFx p .gainedXP else s1
  | [] => s

/-- Gaining XP is a safe change. -/
theorem gainXPOf_safe (n : Nat) (s : GameState) (p : PlayerId) : Safe s (gainXPOf n s p) := by
  unfold gainXPOf
  split
  · rename_i l tl hl
    have h1 : Safe s (s.modObj l (fun o => { o with xp := o.xp + n })) :=
      Safe.modObj s l (fun _ => rfl) (fun _ => rfl)
    dsimp only
    split
    · exact h1.trans (addTurnFx_safe _ p _)
    · exact h1
  · exact Safe.refl s

/-- The players gain XP, one after the other. -/
def gainXPAll (n : Nat) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, p :: ps => gainXPAll n (gainXPOf n s p) ps

/-- Gaining XP is a safe change, for any players. -/
theorem gainXPAll_safe (n : Nat) : ∀ (ps : List PlayerId) (s : GameState),
    Safe s (gainXPAll n s ps)
  | [], s => Safe.refl s
  | p :: ps, s => (gainXPOf_safe n s p).trans (gainXPAll_safe n ps _)

/-- The player spends XP: it goes down, to 0 at the least. -/
def spendXPOf (n : Nat) (s : GameState) (p : PlayerId) : GameState :=
  match s.zone (.player p .legendZone) with
  | l :: _ => s.modObj l (fun o => { o with xp := o.xp - n })
  | [] => s

/-- Spending XP is a safe change. -/
theorem spendXPOf_safe (n : Nat) (s : GameState) (p : PlayerId) : Safe s (spendXPOf n s p) := by
  unfold spendXPOf
  split
  · exact Safe.modObj s _ (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- The players spend XP, one after the other. -/
def spendXPAll (n : Nat) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, p :: ps => spendXPAll n (spendXPOf n s p) ps

/-- Spending XP is a safe change, for any players. -/
theorem spendXPAll_safe (n : Nat) : ∀ (ps : List PlayerId) (s : GameState),
    Safe s (spendXPAll n s ps)
  | [], s => Safe.refl s
  | p :: ps, s => (spendXPOf_safe n s p).trans (spendXPAll_safe n ps _)

/-- The player recycles the top card of their Main Deck: it goes to the bottom (CR 417). -/
def recycleTopOf (q : PlayerId) (s : GameState) : GameState :=
  match s.zone (.player q .mainDeck) with
  | [] => s
  | x :: rest =>
    if (Zone.player q .mainDeck).Valid s.playerCount then
      s.reorder (.player q .mainDeck) (rest ++ [x])
    else s

/-- Recycling the top card is a safe change. -/
theorem recycleTopOf_safe (q : PlayerId) (s : GameState) : Safe s (recycleTopOf q s) := by
  unfold recycleTopOf
  split
  · exact Safe.refl s
  · rename_i x rest hz
    split
    · rename_i hv
      have hp : (rest ++ [x]).Perm (s.zone (.player q .mainDeck)) := by
        rw [hz]; exact List.perm_append_singleton x rest
      exact ⟨fun hwf => GameState.wf_reorder hwf hv hp, fun _ => GameState.physIds_reorder hv hp,
        fun _ hown => GameState.ownerOk_reorder hown hp, rfl⟩
    · exact Safe.refl s

/-- The player swaps the top two cards of their Main Deck. -/
def swapTopOf (q : PlayerId) (s : GameState) : GameState :=
  match s.zone (.player q .mainDeck) with
  | a :: b :: rest =>
    if (Zone.player q .mainDeck).Valid s.playerCount then
      s.reorder (.player q .mainDeck) (b :: a :: rest)
    else s
  | _ => s

/-- Swapping the top two cards is a safe change. -/
theorem swapTopOf_safe (q : PlayerId) (s : GameState) : Safe s (swapTopOf q s) := by
  unfold swapTopOf
  split
  · rename_i a b rest hz
    split
    · rename_i hv
      have hp : (b :: a :: rest).Perm (s.zone (.player q .mainDeck)) := by
        rw [hz]; exact List.Perm.swap a b rest
      exact ⟨fun hwf => GameState.wf_reorder hwf hv hp, fun _ => GameState.physIds_reorder hv hp,
        fun _ hown => GameState.ownerOk_reorder hown hp, rfl⟩
    · exact Safe.refl s
  · exact Safe.refl s

/-- The players swap the top two cards of their Main Deck, one after the other. -/
def swapTopAll : GameState → List PlayerId → GameState
  | s, [] => s
  | s, q :: qs => swapTopAll (swapTopOf q s) qs

/-- Swapping the top cards is a safe change. -/
theorem swapTopAll_safe : ∀ (qs : List PlayerId) (s : GameState), Safe s (swapTopAll s qs)
  | [], s => Safe.refl s
  | q :: qs, s => (swapTopOf_safe q s).trans (swapTopAll_safe qs _)

/-- The players recycle the top card of their Main Deck, one after the other. -/
def recycleTopAll : GameState → List PlayerId → GameState
  | s, [] => s
  | s, q :: qs => recycleTopAll (recycleTopOf q s) qs

/-- Recycling the top cards is a safe change. -/
theorem recycleTopAll_safe : ∀ (qs : List PlayerId) (s : GameState), Safe s (recycleTopAll s qs)
  | [], s => Safe.refl s
  | q :: qs, s => (recycleTopOf_safe q s).trans (recycleTopAll_safe qs _)

/-- The deck a card is recycled to: a Rune goes to the Rune Deck, any other card to the Main Deck
(CR 417). -/
def recycleKind (s : GameState) (id : ObjId) : ZoneKind :=
  if (s.cardDef? id).any (·.hasType .rune) then .runeDeck else .mainDeck

/-- Recycle a card: it goes to the bottom of its owner's deck (CR 417). -/
def recycleOne (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    let z := Zone.player o.owner (recycleKind s id)
    -- a card of the deck goes to its bottom, in the same zone
    if (s.zone z).contains id ∧ z.Valid s.playerCount then
      (s.reorder z (((s.zone z).erase id) ++ [id]), [])
    else
    match moveObj s id z .bottom with
    | some r => (r.1, [Event.moved id r.2 z])
    | none => (s, [])
  | none => (s, [])

/-- Recycling a card is a safe change. -/
theorem recycleOne_safe (s : GameState) (id : ObjId) : Safe s (recycleOne s id).1 := by
  unfold recycleOne
  cases ho : s.obj? id with
  | none => simpa [ho] using Safe.refl s
  | some o =>
    by_cases hc : ((s.zone (Zone.player o.owner (recycleKind s id))).contains id = true ∧
        (Zone.player o.owner (recycleKind s id)).Valid s.playerCount)
    · simp only [hc, and_self, ite_true]
      have hmem : id ∈ s.zone (Zone.player o.owner (recycleKind s id)) :=
        List.contains_iff_mem.mp hc.1
      have hp : (((s.zone (Zone.player o.owner (recycleKind s id))).erase id) ++ [id]).Perm
          (s.zone (Zone.player o.owner (recycleKind s id))) :=
        (List.perm_append_singleton id _).trans (List.perm_cons_erase hmem).symm
      exact ⟨fun hwf => GameState.wf_reorder hwf hc.2 hp,
        fun _ => GameState.physIds_reorder hc.2 hp,
        fun _ hown => GameState.ownerOk_reorder hown hp, rfl⟩
    · simp only [hc, ite_false]
      cases hm : moveObj s id (Zone.player o.owner (recycleKind s id)) .bottom with
      | none => simpa [hm] using Safe.refl s
      | some r => simpa [hm] using Safe.moveObj hm

/-- The note on a card hidden at the Battlefield on the turn (CR 811). -/
def hiddenOf (bf : ObjId) (t : Nat) (x : Object) : Object :=
  { x with hiddenAt := some bf, hiddenTurn := some t }

/-- Hide a card face down at the Battlefield (CR 811): it goes to its owner's hidden cards, and is
noted with the Battlefield and the turn. -/
def hideObj (bf : ObjId) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    -- only a card that is in the hand of its owner can be hidden
    if !(s.zone (.player o.owner .hand)).contains id then (s, []) else
    match moveObj s id (.player o.owner .hidden) with
    | some r =>
      (r.1.modObj r.2 (hiddenOf bf s.turn), [Event.moved id r.2 (.player o.owner .hidden)])
    | none => (s, [])
  | none => (s, [])

/-- Hiding a card is a safe change. -/
theorem hideObj_safe (bf : ObjId) (s : GameState) (id : ObjId) : Safe s (hideObj bf s id).1 := by
  unfold hideObj
  split
  · split
    · exact Safe.refl s
    · split
      · rename_i r hr
        have h1 : Safe r.1 (r.1.modObj r.2 (hiddenOf bf s.turn)) :=
          Safe.modObj r.1 r.2 (fun _ => rfl) (fun _ => rfl)
        exact (Safe.moveObj hr).trans h1
      · exact Safe.refl s
  · exact Safe.refl s

/-- The object played anew: not at a Battlefield, with the note of the play. -/
def Object.freshPlay (mk : PlayMark) (o : Object) : Object :=
  { Object.withPlay [] mk o with loc := none }

/-- What a card played anew has not: damage, a buff, a stun, lasting changes. -/
def Object.cleared (o : Object) : Object :=
  { o with damage := 0, buffed := false, extraBuffs := 0, stunned := false, mightMods := [],
           tempKws := [] }

/-- A card enters the Base as a new object, played. -/
def enterBase (p : PlayerId) (d : CardDef) (mk : PlayMark) (rdy : Bool) (s : GameState)
    (id : ObjId) : GameState :=
  -- the player who plays it controls it, even if the card is another player's (Blind Fury)
  let s2 := s.modObj id (fun o =>
    { (Object.freshPlay mk o).cleared with controller := p, buffed := mk.buff })
  if (d.hasType .unit && !rdy) || d.entersExhausted then (setExhausted true s2 id).1 else s2

/-- Entering the Base is a safe change. -/
theorem enterBase_safe (p : PlayerId) (d : CardDef) (mk : PlayMark) (rdy : Bool) (s : GameState)
    (id : ObjId) : Safe s (enterBase p d mk rdy s id) := by
  have h1 : Safe s (s.modObj id (fun o =>
      { (Object.freshPlay mk o).cleared with controller := p, buffed := mk.buff })) :=
    Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  unfold enterBase
  split
  · exact h1.trans (setExhausted_safe true _ _)
  · exact h1

/-- The facts of playing the card for free: nothing was paid, so no additional cost was (Legion and
the turn are as for any play). -/
def GameState.freeMark (s : GameState) (p : PlayerId) (c : ObjId) : PlayMark :=
  { s.playMark p c ⟨0, []⟩ with paid := false, extraPaid := 0 }

/-- Play a card without paying its cost (CR 349): a Unit or a Gear goes to the Base of the player,
exhausted if it is a Unit that does not enter ready, and the play is noted, so that what waits for a
card to be played fires. A card that is in the Base already is played again where it is. -/
def playFree (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.cardDef? id with
  | some d =>
    -- only a Unit or a Gear enters the Base; a Spell is played by `playSpellStep`
    if !(d.hasType .unit || d.hasType .gear) || s.blocksPlay p id d then (s, []) else
    match moveObj s id (.player p .base) with
    | some r =>
      (enterBase p d (s.freeMark p id) (s.readyNow p id d) r.1 r.2,
        [Event.moved id r.2 (.player p .base), Event.played p r.2])
    | none =>
      if s.locate id = some (.player p .base) then
        (enterBase p d (s.freeMark p id) (s.readyNow p id d) s id, [Event.played p id])
      else (s, [])
  | none => (s, [])

/-- Playing a card without paying is a safe change. -/
theorem playFree_safe (p : PlayerId) (s : GameState) (id : ObjId) : Safe s (playFree p s id).1 := by
  unfold playFree
  split
  · split
    · exact Safe.refl s
    · split
      · rename_i d hd r hr
        exact (Safe.moveObj hr).trans (enterBase_safe _ _ _ _ _ _)
      · split
        · exact enterBase_safe _ _ _ _ _ _
        · exact Safe.refl s
  · exact Safe.refl s

/-- Recycle the cards one after the other, the first one first. -/
def recycleList : List ObjId → GameState → GameState × List Event
  | [], s => (s, [])
  | id :: ids, s =>
    let r := recycleOne s id
    let r2 := recycleList ids r.1
    (r2.1, r.2 ++ r2.2)

/-- Recycling cards is a safe change. -/
theorem recycleList_safe : ∀ (ids : List ObjId) (s : GameState), Safe s (recycleList ids s).1
  | [], s => Safe.refl s
  | id :: ids, s => (recycleOne_safe s id).trans (recycleList_safe ids _)

/-- Reveal from the top of the Main Deck until a card with the properties is revealed: it is played
for free, and the others revealed are recycled (all of the deck if no card matches). -/
def playFirstOf (fs : FilterList) (p : PlayerId) (src : ObjId) (env : Env) (s : GameState) :
    GameState × List Event :=
  let deck := s.zone (.player p .mainDeck)
  match deck.find? (fun id => fs.holds s src env id == some true) with
  | some u =>
    let r := playFree p s u
    let r2 := recycleList (deck.takeWhile (fun id => id != u)) r.1
    (r2.1, r.2 ++ r2.2)
  | none => recycleList deck s

/-- Playing the first card is a safe change. -/
theorem playFirstOf_safe (fs : FilterList) (p : PlayerId) (src : ObjId) (env : Env)
    (s : GameState) : Safe s (playFirstOf fs p src env s).1 := by
  unfold playFirstOf
  dsimp only
  split
  · exact (playFree_safe p s _).trans (recycleList_safe _ _)
  · exact recycleList_safe _ _

/-- The destination of a card removed from the Chain, after applying Flow and Trash replacements
(CR 367-370, 829.1.b.1). -/
def GameState.chainDestinationKind (s : GameState) (id : ObjId) (o : Object)
    (otherwise : ZoneKind) : ZoneKind :=
  if o.flowed then .banishment else s.ownerDestination id o otherwise

/-- A card leaving the Chain always goes to an owner's zone. -/
def GameState.chainDestination (s : GameState) (id : ObjId) (o : Object)
    (otherwise : ZoneKind) : Zone :=
  .player o.owner (s.chainDestinationKind id o otherwise)

/-- Attribute a banishing replacement to its controller, the card's owner (CR 391.3.a). -/
def GameState.chainExitEvents (s : GameState) (o : Object) (id new : ObjId)
    (otherwise : ZoneKind) : List Event :=
  let dest := s.chainDestinationKind id o otherwise
  o.ownerMoveEvents id new dest (o.flowed || otherwise != dest)

/-- Counter a spell: it leaves the Chain for the Trash of its owner without resolving (CR 359.3.d).
Nothing happens to what is not a spell on the Chain. -/
def counterObjTo (k : ZoneKind) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    if id ∈ s.zone .chain ∧ !(s.activeMods id).contains .uncounterable ∧
      !(s.controlledMods o.controller).contains .controlledItemsUncounterable then
      match o.kind with
      | .chainAbility .. =>
        -- a countered ability ceases to exist
        match removeObj s id with
        | some s2 => (s2, [])
        | none => (s, [])
      | _ =>
        match moveObj s id (s.chainDestination id o k) with
        | some r => (r.1, s.chainExitEvents o id r.2 k)
        | none => (s, [])
    else (s, [])
  | none => (s, [])

/-- Countering a spell or an ability is a safe change. -/
theorem counterObjTo_safe (k : ZoneKind) (s : GameState) (id : ObjId) :
    Safe s (counterObjTo k s id).1 := by
  unfold counterObjTo
  split
  · rename_i o ho
    split
    · split
      · split
        · rename_i s2 hr
          exact ⟨fun hwf => removeObj_wf hwf hr,
            fun hwf => removeObj_physIds hwf hr ho (by simp_all [ObjKind.phys?]),
            fun hwf hown => removeObj_ownerOk hwf hown hr, removeObj_sameMeta hr⟩
        · exact Safe.refl s
      · split
        · rename_i r hr
          exact Safe.moveObj hr
        · exact Safe.refl s
    · exact Safe.refl s
  · exact Safe.refl s

/-- Counter a spell: it goes to the Trash of its owner (CR 356). -/
def counterObj (s : GameState) (id : ObjId) : GameState × List Event := counterObjTo .trash s id

/-- Countering a spell is a safe change. -/
theorem counterObj_safe (s : GameState) (id : ObjId) : Safe s (counterObj s id).1 :=
  counterObjTo_safe .trash s id

/-- Counter a spell and return it to its owner's hand instead (Abandon). -/
def counterObjHand (s : GameState) (id : ObjId) : GameState × List Event :=
  counterObjTo .hand s id

/-- Countering a spell to the hand is a safe change. -/
theorem counterObjHand_safe (s : GameState) (id : ObjId) : Safe s (counterObjHand s id).1 :=
  counterObjTo_safe .hand s id

/-- Discard a card: it goes to the Trash of its owner, and the discard is noted (CR 423). -/
def discardObj (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := sendObj .trash s id
  match s.obj? id with
  | some o =>
    let discards := r.2.filterMap (fun e =>
      match e with
      | .moved _ n (.player _ .trash) => some (Event.discarded o.owner n true)
      | _ => none)
    ((if discards.isEmpty then r.1 else r.1.addTurnFx o.owner .cardDiscarded), r.2 ++ discards)
  | none => r

/-- Discarding a card is a safe change. -/
theorem discardObj_safe (s : GameState) (id : ObjId) : Safe s (discardObj s id).1 := by
  unfold discardObj
  split
  · dsimp only
    split
    · exact sendObj_safe .trash s id
    · exact (sendObj_safe .trash s id).trans (addTurnFx_safe _ _ _)
  · exact sendObj_safe .trash s id

/-- Discard the selected hand cards to pay the cost before the ability enters the Chain (CR 423.3).
The last discard event closes the group for effects that watch one or more discards. -/
def payDiscards (p : PlayerId) : GameState → List ObjId → GameState × List Event
  | s, [] => (s, [])
  | s, id :: ids =>
    if (s.zone (.player p .hand)).contains id then
      let r := discardObj s id
      let next := payDiscards p r.1 ids
      let events := if ids.isEmpty then r.2 else r.2.map (fun e => match e with
        | .discarded q card _ => .discarded q card false
        | other => other)
      (next.1, events ++ next.2)
    else payDiscards p s ids

/-- Paying with hand cards preserves well-formedness, card identities and ownership. -/
theorem payDiscards_safe (p : PlayerId) :
    ∀ (ds : List ObjId) (s : GameState), Safe s (payDiscards p s ds).1
  | [], s => Safe.refl s
  | id :: ids, s => by
    simp only [payDiscards]
    split
    · exact (discardObj_safe s id).trans (payDiscards_safe p ids _)
    · exact payDiscards_safe p ids s

/-- Pay the optional discard after the mana payment, recording it on the card before the
play and discard triggers are processed (CR 357.1-357.2, 423.3). -/
def payPlayDiscard (p : PlayerId) (c : ObjId) (discard : Option ObjId)
    (r : GameState × List Event) : GameState × List Event :=
  match discard with
  | none => r
  | some id =>
    let paid := payDiscards p r.1 [id]
    let played := r.2.findSome? (fun
      | .moved old new _ => if old == c then some new else none
      | _ => none)
    (if paid.2.isEmpty then paid.1 else markPaid paid.1 played true, r.2 ++ paid.2)

/-- Paying the optional discard of a play preserves the structural invariants. -/
theorem payPlayDiscard_safe (p : PlayerId) (c : ObjId) (discard : Option ObjId)
    (r : GameState × List Event) : Safe r.1 (payPlayDiscard p c discard r).1 := by
  unfold payPlayDiscard
  split
  · exact Safe.refl _
  · dsimp only
    split
    · exact payDiscards_safe _ _ _
    · exact (payDiscards_safe _ _ _).trans (markPaid_safe _ _ true)

/-- Replacing a Rune Pool is a safe change. -/
theorem setPool_safe (s : GameState) (p : PlayerId) (pool : RunePool) : Safe s (s.setPool p pool) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Use the Rune abilities one after the other. -/
def applyRunes (s : GameState) (p : PlayerId) :
    List (ObjId × RuneAbility) → Option (GameState × List Event)
  | [] => some (s, [])
  | (r, ab) :: rest =>
    (applyRune s p r ab).bind (fun x =>
      (applyRunes x.1 p rest).map (fun y => (y.1, x.2 ++ y.2)))

/-- Using a Rune is a safe change. -/
theorem applyRune_safe {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (h : applyRune s p c ab = some (s', es)) : Safe s s' := by
  unfold applyRune at h
  split at h
  · rename_i o ho
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have h1 : Safe s (s.exhaustObj c) :=
        ⟨fun hwf => GameState.wf_exhaustObj hwf c,
         fun _ => (GameState.physIds_exhaustObj s c) ▸ List.Perm.refl _,
         fun _ hown => GameState.ownerOk_exhaustObj hown c, GameState.sameMeta_exhaustObj s c⟩
      exact h1.trans (setPool_safe _ _ _)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact (Safe.moveObj hm).trans (setPool_safe _ _ _)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Using Runes is a safe change. -/
theorem applyRunes_safe {p : PlayerId} :
    ∀ (plan : List (ObjId × RuneAbility)) {s s' : GameState} {es : List Event},
      applyRunes s p plan = some (s', es) → Safe s s'
  | [], s, s', es, h => by
    simp only [applyRunes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Safe.refl s
  | (r, ab) :: rest, s, s', es, h => by
    simp only [applyRunes, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (applyRune_safe hx).trans (applyRunes_safe rest hy)

/-- Set the Pool of the player after paying for the object `src`: the Power of Any domain that a
Gear spent is no longer noted as Power that only pays for Gear (that Power is spent first). -/
def GameState.setPoolFor (s : GameState) (p : PlayerId) (src : ObjId) (pool : RunePool) :
    GameState :=
  let t := s.setPool p pool
  if (s.cardDef? src).any (·.hasType .gear) then
    let spent := (s.poolOf p).any - pool.any
    { t with turnFx := dropGearFx s.turn p spent t.turnFx }
  else t

/-- Setting the Pool after paying is a safe change. -/
theorem setPoolFor_safe (s : GameState) (p : PlayerId) (src : ObjId) (pool : RunePool) :
    Safe s (s.setPoolFor p src pool) := by
  unfold GameState.setPoolFor
  split
  · exact (setPool_safe s p pool).trans
      ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
        fun _ hown => hown.congr rfl rfl, rfl⟩
  · exact setPool_safe s p pool

/-- Pay the cost `c` for the object `src`: from the Pool, or, if it falls short, with Runes (exhaust a
ready Rune for each Energy missing, recycle a Rune of the domain for each Power missing). `none` if
it cannot be paid. -/
def payByRunes (s : GameState) (p : PlayerId) (src : ObjId) (c : Cost)
    (unit : Bool := false) :
    Option (GameState × List Event) :=
  match s.payNow p src c unit with
  | some pool => some (s.setPoolFor p src pool, [])
  | none =>
    match s.runePlan p src c unit with
    | some plan =>
      (applyRunes s p plan).bind (fun r =>
        (r.1.payNow p src c unit).map (fun pool => (r.1.setPoolFor p src pool, r.2)))
    | none => none

/-- Paying is a safe change. -/
theorem payByRunes_safe {s : GameState} {p : PlayerId} {src : ObjId} {c : Cost}
    {unit : Bool} {r : GameState × List Event} (h : payByRunes s p src c unit = some r) :
    Safe s r.1 := by
  unfold payByRunes at h
  cases hp : s.payNow p src c unit with
  | some pool =>
    simp only [hp, Option.some.injEq] at h
    rw [← h]
    exact setPoolFor_safe s p src pool
  | none =>
    simp only [hp] at h
    cases hq : s.runePlan p src c unit with
    | none => simp [hq] at h
    | some plan =>
      simp only [hq, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, hr⟩ := h
      cases hy : x.1.payNow p src c unit with
      | none => simp [hy] at hr
      | some pool =>
        simp only [hy, Option.map_some, Option.some.injEq] at hr
        rw [← hr]
        exact (applyRunes_safe plan hx).trans (setPoolFor_safe _ _ _ _)

/-- Paying the first affordable cost option preserves the same invariants as the payment itself. -/
theorem payPlayOption_safe {s : GameState} {p : PlayerId} {id : ObjId} {costs : List Cost}
    {unit : Bool} {r : GameState × List Event}
    (h : costs.findSome? (fun c => payByRunes s p id c unit) = some r) :
    Safe s r.1 := by
  obtain ⟨_, _, _, _, paid, _⟩ := List.findSome?_eq_some_iff.mp h
  exact payByRunes_safe paid

/-- Play a card ignoring its Energy cost: its Power cost is paid from the Pool; if that cannot be
done, or the card is not a Unit or a Gear, nothing is paid and the card is not played. -/
def playPaying (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  if !((s.cardDef? id).any (fun d =>
      (d.hasType .unit || d.hasType .gear) && !s.blocksPlay p id d)) then (s, []) else
  match (s.cardDef? id).bind (·.cost) with
  | some c =>
    match (s.targetCostOptions p id [] ⟨0, s.adjustPower id c.power⟩).findSome? (payByRunes s p id) with
    | some r => ((playFree p r.1 id).1, r.2 ++ (playFree p r.1 id).2)
    | none => (s, [])
  | none => playFree p s id

/-- Playing a card for its Power is a safe change. -/
theorem playPaying_safe (p : PlayerId) (s : GameState) (id : ObjId) :
    Safe s (playPaying p s id).1 := by
  unfold playPaying
  split
  · exact Safe.refl s
  · split
    · split
      · rename_i r hr
        exact (payPlayOption_safe hr).trans (playFree_safe p _ id)
      · exact Safe.refl s
    · exact playFree_safe p s id

/-- Power that pays only for Gear and has been spent is no longer noted: only as much as the Pool
still holds stays noted (the Power that is added later is free to pay for anything). -/
def GameState.trimGear (s : GameState) (p : PlayerId) : GameState :=
  let noted :=
    (s.turnFx.filter (fun f => f.turn == s.turn && f.who == p && f.kind == .gearMana)).length
  { s with turnFx := dropGearFx s.turn p (noted - (s.poolOf p).any) s.turnFx }

/-- Trimming the note of Gear Power is a safe change. -/
theorem trimGear_safe (s : GameState) (p : PlayerId) : Safe s (s.trimGear p) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Add Power of any domain to the Pools of the players, one after the other. -/
def poolsAddAny (k : Nat) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, q :: qs =>
    let t := s.trimGear q
    poolsAddAny k (t.setPool q ((t.poolOf q).addAny k)) qs

/-- Adding Power is a safe change. -/
theorem poolsAddAny_safe (k : Nat) :
    ∀ (qs : List PlayerId) (s : GameState), Safe s (poolsAddAny k s qs)
  | [], s => Safe.refl s
  | q :: qs, s => ((trimGear_safe s q).trans (setPool_safe _ q _)).trans (poolsAddAny_safe k qs _)

/-- Change the Rune Pools of the players, one after the other. -/
def poolsMap (f : RunePool → RunePool) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, q :: qs => poolsMap f (s.setPool q (f (s.poolOf q))) qs

/-- Changing Rune Pools is a safe change. -/
theorem poolsMap_safe (f : RunePool → RunePool) :
    ∀ (qs : List PlayerId) (s : GameState), Safe s (poolsMap f s qs)
  | [], s => Safe.refl s
  | q :: qs, s => (setPool_safe s q _).trans (poolsMap_safe f qs _)

/-- Giving points is a safe change: the points are not part of what a safe change keeps. -/
theorem gainPoints_safe (s : GameState) (p : PlayerId) (n : Nat) : Safe s (s.gainPoints p n) :=
  ⟨fun hwf => GameState.wf_gainPoints hwf p n, fun _ => List.Perm.refl _,
    fun _ hown => GameState.ownerOk_gainPoints hown p n, rfl⟩

/-- The players gain points, one after the other. -/
def gainPointsAll (n : Nat) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, p :: ps => gainPointsAll n (s.gainPoints p n) ps

/-- Giving points to any players is a safe change. -/
theorem gainPointsAll_safe (n : Nat) : ∀ (ps : List PlayerId) (s : GameState),
    Safe s (gainPointsAll n s ps)
  | [], s => Safe.refl s
  | p :: ps, s => (gainPoints_safe s p n).trans (gainPointsAll_safe n ps _)

/-- Channeling is a safe change. -/
theorem channel_safe (p : PlayerId) (n : Nat) (s : GameState) : Safe s (channel p n s).1 :=
  ⟨fun hwf => channel_wf p n hwf, fun hwf => channel_physIds p n hwf,
    fun hwf hown => channel_ownerOk p n hwf hown, channel_sameMeta p n s⟩

/-- The new identifiers of the objects that moved. -/
def movedNew : List Event → List ObjId
  | [] => []
  | .moved _ id _ :: es => id :: movedNew es
  | _ :: es => movedNew es

/-- Exhaust the objects. -/
def exhaustAll : List ObjId → GameState → GameState
  | [], s => s
  | id :: ids, s => exhaustAll ids (setExhausted true s id).1

/-- Exhausting objects is a safe change. -/
theorem exhaustAll_safe : ∀ (ids : List ObjId) (s : GameState), Safe s (exhaustAll ids s)
  | [], s => Safe.refl s
  | id :: ids, s => (setExhausted_safe true s id).trans (exhaustAll_safe ids _)

/-- Channel `n` Runes ready, and `extra` more that enter exhausted (CR 431). -/
def channelEx (p : PlayerId) (n extra : Nat) (s : GameState) : GameState × List Event :=
  let r1 := channel p n s
  let r2 := channel p extra r1.1
  (exhaustAll (movedNew r2.2) r2.1, r1.2 ++ r2.2)

/-- Channeling some Runes exhausted is a safe change. -/
theorem channelEx_safe (p : PlayerId) (n extra : Nat) (s : GameState) :
    Safe s (channelEx p n extra s).1 :=
  ((channel_safe p n s).trans (channel_safe p extra _)).trans (exhaustAll_safe _ _)

/-- The players channel. -/
def channelAll (n extra : Nat) : GameState → List PlayerId → GameState × List Event
  | s, [] => (s, [])
  | s, p :: ps =>
    let r := channelEx p n extra s
    let r' := channelAll n extra r.1 ps
    (r'.1, r.2 ++ r'.2)

/-- Channeling for any players is a safe change. -/
theorem channelAll_safe (n extra : Nat) :
    ∀ (ps : List PlayerId) (s : GameState), Safe s (channelAll n extra s ps).1
  | [], s => Safe.refl s
  | p :: ps, s => (channelEx_safe p n extra s).trans (channelAll_safe n extra ps _)

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

/-- Move a Unit to its controller's Base once the move is allowed, counting it and emitting its
movement event (CR 447). -/
def moveHomeUnchecked (s : GameState) (u : ObjId) : GameState × List Event :=
  match s.obj? u with
  | some o =>
    match moveObj s u (.player o.controller .base) with
    | some r =>
      (r.1.modObj r.2 (fun x => ({ x with loc := none } : Object).countMove s.turn o.loc),
        [Event.standardMoved r.2 none])
    | none => (s, [])
  | none => (s, [])

/-- Moving an allowed Unit to its Base preserves the structural invariants. -/
theorem moveHomeUnchecked_safe (s : GameState) (u : ObjId) :
    Safe s (moveHomeUnchecked s u).1 := by
  unfold moveHomeUnchecked
  split
  · split
    · rename_i r hr
      exact (Safe.moveObj hr).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl))
    · exact Safe.refl s
  · exact Safe.refl s

/-- Move a Unit to the Base of its controller by an effect, unless the move is forbidden
(CR 447). -/
def moveHome (s : GameState) (u : ObjId) : GameState × List Event :=
  if ((s.obj? u).bind (·.loc)).any (fun bf => s.homeForbiddenFor u bf) then
    (s, [])
  else moveHomeUnchecked s u

/-- Moving home is a safe change. -/
theorem moveHome_safe (s : GameState) (u : ObjId) : Safe s (moveHome s u).1 := by
  unfold moveHome
  split
  · exact Safe.refl s
  · exact moveHomeUnchecked_safe s u

/-- Move a Unit to a place by an effect: a Battlefield (`some`) or its controller's Base. -/
def sendToLoc (loc : Option ObjId) (s : GameState) (u : ObjId) : GameState × List Event :=
  match loc with
  | some bf => sendToBf bf s u
  | none => moveHomeUnchecked s u

/-- Moving to a place is a safe change. -/
theorem sendToLoc_safe (loc : Option ObjId) (s : GameState) (u : ObjId) :
    Safe s (sendToLoc loc s u).1 := by
  cases loc with
  | none => exact moveHomeUnchecked_safe s u
  | some bf => exact sendToBf_safe bf s u

/-- A Unit's move protection applies to enemy effects while its ability is active, including
when it is granted by attached Equipment (CR 137, 451). -/
def GameState.blocksEnemyMove (s : GameState) (p : PlayerId) (u : ObjId) : Bool :=
  (s.obj? u).any (·.controller != p) &&
    ((s.activeMods u).contains .noEnemyEffectMove ||
      s.inPlay.any (fun gear =>
        (s.obj? gear).any (·.attached == some u) &&
          (s.cardDef? gear).any (fun d => d.grants.any (fun
            | .passive .always mods => mods.contains .noEnemyEffectMove
            | _ => false))))

/-- Move the Unit only if the spell or ability that would move it is allowed to do so. -/
def moveByEffect (controller : PlayerId) (loc : Option ObjId) (s : GameState) (u : ObjId) :
    GameState × List Event :=
  if s.blocksEnemyMove controller u then (s, [])
  else match loc with
    | none => moveHome s u
    | some bf => sendToBf bf s u

/-- Applying or preventing an effect move preserves the structural invariants. -/
theorem moveByEffect_safe (p : PlayerId) (loc : Option ObjId) (s : GameState) (u : ObjId) :
    Safe s (moveByEffect p loc s u).1 := by
  unfold moveByEffect
  split
  · exact Safe.refl s
  · cases loc
    · exact moveHome_safe s u
    · exact sendToBf_safe _ s u

/-- Two Units swap places by an effect: each goes to where the other is. Nothing happens if they are
at the same place or either move is forbidden. -/
def swapPlaces (s : GameState) (x y : ObjId) (controller : Option PlayerId := none) :
    GameState × List Event :=
  let lx := (s.obj? x).bind (·.loc)
  let ly := (s.obj? y).bind (·.loc)
  if controller.any (fun p => s.blocksEnemyMove p x || s.blocksEnemyMove p y) ||
      lx == ly || (lx.isNone && ly.any (s.homeForbiddenFor y)) ||
      (ly.isNone && lx.any (s.homeForbiddenFor x)) then (s, [])
  else
    let r1 := sendToLoc ly s x
    let r2 := sendToLoc lx r1.1 y
    (r2.1, r1.2 ++ r2.2)

/-- Swapping places is a safe change. -/
theorem swapPlaces_safe (s : GameState) (x y : ObjId) (controller : Option PlayerId := none) :
    Safe s (swapPlaces s x y controller).1 := by
  unfold swapPlaces
  dsimp only
  split
  · exact Safe.refl s
  · exact (sendToLoc_safe _ s x).trans (sendToLoc_safe _ _ y)

/-- Play a card without paying, to a Battlefield: it is played, and moved there (CR 447). -/
def playFreeAt (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := playFree p s id
  match movedNew r.2 with
  | n :: _ =>
    -- the card is played there: it does not move, so nothing that waits for a move fires, and
    -- no move is counted
    (((sendToBf bf r.1 n).1.modObj n (fun x => { x with moves := 0, movesTurn := none })), r.2)
  | [] => r

/-- Playing a card to a Battlefield is a safe change. -/
theorem playFreeAt_safe (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) :
    Safe s (playFreeAt p bf s id).1 := by
  unfold playFreeAt
  cases hm : movedNew (playFree p s id).2 with
  | nil => simpa [hm] using playFree_safe p s id
  | cons n _ =>
    simp only [hm]
    exact ((playFree_safe p s id).trans (sendToBf_safe bf _ _)).trans
      (Safe.modObj _ n (fun _ => rfl) (fun _ => rfl))


/-- Banish a unit, then its owner plays it, ignoring its cost: it comes back as a new object, with
nothing of what it had. Replay to the previous Battlefield when the effect says the location
stays the same. A token ceases to exist when banished (CR 187, 428). -/
def banishReplay (p : PlayerId) (s : GameState) (id : ObjId) (sameLocation : Bool := false) :
    GameState × List Event :=
  let r := banishObj p s id
  match r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none),
      (s.obj? id) with
  | some n, some o =>
    match o.kind with
    | .token _ => r
    | _ =>
      let t := match if sameLocation then o.loc else none with
        | some bf => playFreeAt o.owner bf r.1 n
        | none => playFree o.owner r.1 n
      (t.1, r.2 ++ t.2)
  | _, _ => r

/-- Banishing a unit and playing it again is a safe change. -/
theorem banishReplay_safe (p : PlayerId) (s : GameState) (id : ObjId) (sameLocation : Bool) :
    Safe s (banishReplay p s id sameLocation).1 := by
  unfold banishReplay
  dsimp only
  split
  · rename_i n o
    split
    · exact sendObj_safe .banishment s id
    · split
      · exact (sendObj_safe .banishment s id).trans (playFreeAt_safe _ _ _ _)
      · exact (sendObj_safe .banishment s id).trans (playFree_safe _ _ _)
  · exact sendObj_safe .banishment s id

/-- Play a card without paying, to a Battlefield: to its Base, if the opponents of the player play
Units only to their Base (Mageseeker Warden). -/
def playToOrBase (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if s.oppHas p .oppsPlayToBaseOnly || s.cantActHere p .play bf then playFree p s id
  else playFreeAt p bf s id

/-- Playing a card to a Battlefield or to the Base is a safe change. -/
theorem playToOrBase_safe (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) :
    Safe s (playToOrBase p bf s id).1 := by
  unfold playToOrBase
  split
  · exact playFree_safe p s id
  · exact playFreeAt_safe p bf s id

/-- A Unit or Gear can be played by an effect to the location it specifies (CR 355.17.b). -/
def GameState.permanentPlayAllowed (s : GameState) (p : PlayerId) (id : ObjId)
    (d : CardDef) (dest : Option ObjId) : Bool :=
  (d.hasType .unit || d.hasType .gear) && !s.blocksPlay p id d &&
    dest.elim (!d.playsOnlyToBattlefield) (fun bf => d.hasType .unit && s.playBfLocationAllowed p id d bf)

/-- Play a Unit or Gear with its Energy cost reduced by `k`. Check that the required destination
is legal before paying (CR 355.17.b, 358.5). -/
def playReducedOne (p : PlayerId) (k : Nat) (dest : Option ObjId) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if !(s.cardDef? id).any (fun d => s.permanentPlayAllowed p id d dest) then (s, []) else
  -- the cost the card is played for now (the other reductions count too), less `k` Energy
  match (s.cardDef? id).bind (fun d => s.effCost p id d) with
  | some c =>
    match (s.targetCostOptions p id [] (c.lessEnergy k)).findSome? (fun cost =>
        payByRunes s p id cost ((s.cardDef? id).any (·.hasType .unit))) with
    | some r =>
      let played := match dest with
        | some bf => playFreeAt p bf r.1 id
        | none => playFree p r.1 id
      (played.1, r.2 ++ played.2)
    | none => (s, [])
  | none =>
    match dest with
    | some bf => playFreeAt p bf s id
    | none => playFree p s id

/-- The legal locations satisfying maximal compatible sets of requirements (CR 355.17).
A requirement can be met alongside all others matched by a location only when a legal
location matches the larger set. -/
def effectPlayLocations (s : GameState) (p : PlayerId) (id : ObjId) (d : CardDef)
    (requirements : List (List (Option ObjId))) : List (Option ObjId) :=
  if requirements.isEmpty then
    (if d.playsOnlyToBattlefield then [] else [none]) ++ (s.playBfOptions p id).map some
  else
    let legal := requirements.flatten.eraseDups.filter (s.permanentPlayAllowed p id d)
    let satisfied (loc : Option ObjId) := requirements.map (·.contains loc)
    legal.filter (fun loc =>
      let kept := satisfied loc
      !legal.any (fun other =>
        let more := satisfied other
        kept != more && (kept.zip more).all (fun (wanted, present) => !wanted || present)))

/-- The adjusted base cost when an effect lets a card be played (CR 356.1). -/
def EffectPlayPrice.baseCost (price : EffectPlayPrice) (s : GameState) (p : PlayerId)
    (id : ObjId) (d : CardDef) : Option Cost :=
  match price with
  | .reduceEnergy _ => s.effCost p id d
  | .ignoreEnergy => d.cost.map (fun c => s.adjustCost p id { c with energy := 0 })
  | .ignoreBase => some (s.adjustCost p id Cost.zero)

/-- Any further reduction of optional and base Energy combined. -/
def EffectPlayPrice.energyCut : EffectPlayPrice → Nat
  | .reduceEnergy k => k
  | _ => 0

/-- Costs and destinations for a Unit or Gear played by an effect, before obtaining the resources
to pay (CR 355-357, 420.3). -/
def permanentPlayOptions (s : GameState) (p : PlayerId) (id : ObjId) (terms : EffectPlayTerms) :
    List ReducedPermanentPlay := Id.run do
  let some d := s.cardDef? id | return []
  if s.cantPlay p || s.blocksPlay p id d || !(d.hasType .unit || d.hasType .gear) ||
      d.hasType .spell then return []
  let some base := terms.price.baseCost s p id d | return []
  let extraObjects := none :: ((d.playExtra.toList.flatMap (fun (k, _) =>
    s.extraCandidates p k)).map some)
  let discardOptions := s.playDiscards p id
  let mut plans := []
  for battlefieldFees in [] :: s.battlefieldFeeChoices p id d do
    let requirements := terms.requirements ++ battlefieldFees.map (fun b => [some b])
    for battlefield in effectPlayLocations s p id d requirements do
      for extraObject in extraObjects do
        let extra := extraObject.toList
        if !s.extraOk p id extra then continue
        for cost in s.cutOptionsOf p id base extra do
          for (total, picked) in s.playCostPlans p id d cost do
            let additionalPaid := d.additionalCost.isSome && picked.contains 0
            let accelerated := d.hasType .unit && d.hasKeyword .accelerate &&
              picked.contains (if d.additionalCost.isSome then 1 else 0)
            for fee in s.battlefieldFeeTotals p d battlefieldFees do
              let combined := (total.plus fee).lessEnergy terms.price.energyCut
              for adjusted in s.targetCostOptions p id (battlefield.toList ++ extra) combined do
                for pay in adjusted.payments d.domains do
                  let fixed : Cost := ⟨pay.energy, pay.power.map PowerSym.domain⟩
                  for discard in discardOptions do
                    let plan : ReducedPermanentPlay := {
                      cost := fixed
                      battlefield
                      extraObject
                      discard
                      additionalPaid
                      accelerated
                      battlefieldFees }
                    plans := plan :: plans
  return plans.reverse.eraseDups

/-- The legal finalizations that can already be funded with the Pool and Basic Runes. -/
def permanentPlayPlans (s : GameState) (p : PlayerId) (id : ObjId) (terms : EffectPlayTerms) :
    List ReducedPermanentPlay :=
  let unit := (s.cardDef? id).any (·.hasType .unit)
  (permanentPlayOptions s p id terms).filter (fun plan =>
    (payByRunes s p id plan.cost unit).isSome)

/-- The possible reduced plays when the effect leaves the destination to the Unit's player. -/
def reducedPermanentPlays (s : GameState) (p : PlayerId) (id : ObjId) (less : Nat) :
    List ReducedPermanentPlay :=
  permanentPlayPlans s p id { price := .reduceEnergy less }

/-- Play a Unit or Gear with a chosen reduced-cost finalization. Emit the play after its costs
have been paid and return the identifier it acquired when it entered play. -/
def applyReducedPermanent (s : GameState) (p : PlayerId) (id : ObjId)
    (plan : ReducedPermanentPlay) : Option (GameState × ObjId × List Event) := do
  let d ← s.cardDef? id
  let paid ← payByRunes s p id plan.cost (d.hasType .unit)
  let zone := plan.battlefield.elim (.player p .base) (fun _ => .battlefieldZone)
  let (onBoard, new) ← moveObj paid.1 id zone
  let ownCosts := (if plan.additionalPaid then [0] else []) ++
    (if plan.accelerated then [if d.additionalCost.isSome then 1 else 0] else [])
  let mark := { s.playMark p id ⟨plan.cost.energy, []⟩ with
    paid := !ownCosts.isEmpty, extraPaid := ownCosts.length
    spellPick := if plan.battlefieldFees.isEmpty then .plain
      else .payForBattlefield plan.battlefieldFees ownCosts }
  let ready := s.readyNow p id d || plan.accelerated
  let moved := (enterBase p d mark ready onBoard new, [Event.moved id new zone])
  let placed := placeAtBf s plan.battlefield.toList moved
  let extra ← payExtra0 s id plan.extraObject.toList placed
  let result := payPlayDiscard p id plan.discard extra
  some (result.1, new, paid.2 ++ result.2 ++ [Event.played p new])

/-- Reduced-cost finalization preserves the structural and ownership invariants. -/
theorem applyReducedPermanent_safe {s : GameState} {p : PlayerId} {id : ObjId}
    {plan : ReducedPermanentPlay} {r : GameState × ObjId × List Event}
    (h : applyReducedPermanent s p id plan = some r) : Safe s r.1 := by
  unfold applyReducedPermanent at h
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨d, hd, paid, hp, ⟨onBoard, new⟩, hm, extra, he, rfl⟩ := h
  exact (payByRunes_safe hp).trans ((Safe.moveObj hm).trans
    ((enterBase_safe _ _ _ _ _ _).trans ((placeAtBf_safe _ _ _).trans
      ((payExtra0_safe he).trans (payPlayDiscard_safe _ _ _ _)))))

/-- The new identity created by banishing the chosen card. -/
def banishedPlayId (es : List Event) : Option ObjId :=
  es.findSome? (fun
    | .moved _ id (.player _ .banishment) => some id
    | _ => none)

/-- A looked-at card may be offered only if it meets the filter, is still in the same deck,
and will have a legal finalization after leaving it for Banishment (CR 355.16, 420.3.c). -/
def lookedPlayCandidates (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (less : Nat) (fs : FilterList) : List ObjId :=
  let deck := s.zone (.player p .mainDeck)
  env.lookedCards.filter (fun id =>
    deck.contains id && FilterList.holds s src env id fs == some true &&
    (let banished := banishObj p s id
     (banishedPlayId banished.2).any (fun new =>
       !(reducedPermanentPlays banished.1 p new less).isEmpty)))

/-- The effect choices that are legal for the Spell's controller, before considering any costs. -/
def spellChoices (s : GameState) (p : PlayerId) (id : ObjId) (d : CardDef) (e : EffectDef) :
    List (SpellPick × List ObjId) :=
  (s.spellPicks p d).flatMap (fun pick =>
    (e.forPick pick).toList.flatMap (fun branch =>
      if s.spellPlayerTargetOk p branch pick then
        ((targetTuples s p id s.mightTable branch.choices).filter
          (fun ts => s.moveTargetOk id branch ts pick)).map (pick, ·)
      else []))

/-- Targets, finalization choices and costs for a Spell played by another effect (CR 420.3). -/
def reducedSpellChoices (s : GameState) (p : PlayerId) (id : ObjId) (d : CardDef)
    (e : EffectDef) (less : Nat) : List (List ObjId × Cost × SpellPick) :=
  let hasCosts := !(s.extrasRaw p id d).isEmpty
  let choices := (s.effCost p id d).toList.flatMap (fun base =>
    (spellChoices s p id d e).flatMap (fun (pick, ts) =>
      let surcharge := if s.playPowerCut p id ts == 0 then s.deflectCost p ts (some id) else 0
      (s.spellCostPlans p id d (base.lessEnergy less) ts).map (fun (cost, paid) =>
        let choice := if hasCosts then .withCosts pick paid.1 paid.2 else pick
        (ts, { cost with power := cost.power ++ List.replicate surcharge .any }, choice))))
  choices.eraseDups.filter (fun (_, cost, _) => (payByRunes s p id cost).isSome)

/-- Cast a Spell at the chosen reduced cost, with the targets of that choice (CR 420.3).
If the cost cannot be paid or the choice is unavailable, it is not cast. -/
def castPickedOne (p : PlayerId) (k idx : Nat) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  match ((s.cardDef? id).filter (fun d => !s.blocksPlay p id d)).bind
      (fun d => d.spellEffect.map (fun e => (d, e))) with
  | some (d, e) =>
    match (reducedSpellChoices s p id d e k)[idx]? with
    | some (ts, cost, pick) =>
      match payByRunes s p id cost with
      | some r =>
        match moveObj r.1 id .chain with
        | some m =>
          let chosen := pick.optionalCosts.getD (false, 0)
          let mark := { r.1.freeMark p id with
            spellPick := pick, paid := chosen.1, extraPaid := chosen.2 }
          (m.1.modObj m.2 (Object.withPlay ts mark),
            r.2 ++ [Event.moved id m.2 .chain, Event.played p m.2] ++ ts.map (Event.chosenBySpell p))
        | none => (s, [])
      | none => (s, [])
    | none => (s, [])
  | none => (s, [])

/-- Casting a Spell for a reduced cost is a safe change. -/
theorem castPickedOne_safe (p : PlayerId) (k idx : Nat) (s : GameState) (id : ObjId) :
    Safe s (castPickedOne p k idx s id).1 := by
  unfold castPickedOne
  split
  · split
    · split
      · rename_i r hr
        split
        · rename_i m hm
          exact (payByRunes_safe hr).trans
            ((Safe.moveObj hm).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl)))
        · exact Safe.refl s
      · exact Safe.refl s
    · exact Safe.refl s
  · exact Safe.refl s

/-- Playing a card for a reduced cost is a safe change. -/
theorem playReducedOne_safe (p : PlayerId) (k : Nat) (dest : Option ObjId) (s : GameState)
    (id : ObjId) : Safe s (playReducedOne p k dest s id).1 := by
  unfold playReducedOne
  split
  · exact Safe.refl s
  · split
    · split
      · rename_i r hr
        cases dest with
        | none => exact (payPlayOption_safe hr).trans (playFree_safe p _ id)
        | some bf => exact (payPlayOption_safe hr).trans (playFreeAt_safe p bf _ id)
      · exact Safe.refl s
    · cases dest with
      | none => exact playFree_safe p s id
      | some bf => exact playFreeAt_safe p bf s id
/-- The owner of an object has control of it again (CR 740). -/
def giveBack (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with controller := o.owner }), [])

/-- Giving control back is a safe change. -/
theorem giveBack_safe (s : GameState) (id : ObjId) : Safe s (giveBack s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- The object after it becomes a copy of an object of the kind: a token has the card of it. A card
stays what it is. -/
def copyKind (card : CardId) (x : Object) : Object :=
  match x.kind with
  | .token _ => { x with kind := .token card }
  | _ => x

/-- Becoming a copy keeps the physical card and the owner. -/
theorem copyKind_phys (card : CardId) (x : Object) :
    (copyKind card x).kind.phys? = x.kind.phys? ∧ (copyKind card x).owner = x.owner := by
  unfold copyKind
  split <;> simp_all [ObjKind.phys?]

/-- A token becomes a copy of another object: it has its card. A card stays what it is. -/
def becomeCopyOf (src : ObjId) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.cardDef? src with
  | some d => (s.modObj id (copyKind d.id), [])
  | none => (s, [])

/-- A change of one object that keeps its owner and the physical card it has (a token that
changes its card). -/
theorem Safe.modObjPhys (s : GameState) (id : ObjId) {f : Object → Object}
    (hk : ∀ o, (f o).kind.phys? = o.kind.phys?) (ho : ∀ o, (f o).owner = o.owner) :
    Safe s (s.modObj id f) :=
  ⟨fun h => GameState.wf_modObj h id f, fun _ => by
    have : (s.modObj id f).physIds = s.physIds := by
      unfold GameState.physIds
      apply filterMap_congr_mem
      intro x _
      rw [GameState.obj?_modObj]
      by_cases h : id.n = x.n
      · have hx : id = x := by cases id; cases x; simp_all
        subst hx
        cases s.obj? id <;> simp [hk]
      · simp [h]
    rw [this],
    fun _ h => GameState.ownerOk_modObj h id ho, GameState.sameMeta_modObj s id f⟩

/-- Becoming a copy is a safe change. -/
theorem becomeCopyOf_safe (src : ObjId) (s : GameState) (id : ObjId) :
    Safe s (becomeCopyOf src s id).1 := by
  unfold becomeCopyOf
  split
  · exact Safe.modObjPhys s id (fun x => (copyKind_phys _ x).1) (fun x => (copyKind_phys _ x).2)
  · exact Safe.refl s

/-- Add the Battlefield token to the board, if a Battlefield of the card is not there already. -/
def addBattlefieldTok (c : CardDef) (p : PlayerId) (s : GameState) : GameState :=
  if (s.zone .battlefieldZone).any (fun b => (s.cardDef? b).any (·.id == c.id)) then s
  else addTok s { kind := .token c.id, owner := p, controller := p, timestamp := ⟨0⟩ }
    .battlefieldZone

/-- Adding a Battlefield token is a safe change. -/
theorem addBattlefieldTok_safe (c : CardDef) (p : PlayerId) (s : GameState) :
    Safe s (addBattlefieldTok c p s) := by
  unfold addBattlefieldTok
  split
  · exact Safe.refl s
  · exact addTok_safe _ _ _ rfl

/-- A player takes control of an object (CR 740). -/
def setController (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  let s1 := s.modObj id (fun o => { o with controller := p })
  -- a Unit at a Battlefield makes it Contested by its new controller (CR 190.3)
  match (s.obj? id).bind (·.loc) with
  | some bf => (contestFor p bf s1, [])
  | none => (s1, [])

/-- Taking control is a safe change. -/
theorem setController_safe (p : PlayerId) (s : GameState) (id : ObjId) :
    Safe s (setController p s id).1 := by
  unfold setController
  have h1 : Safe s (s.modObj id (fun o => { o with controller := p })) :=
    Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  split
  · exact h1.trans (contestFor_safe _ _ _)
  · exact h1

/-- A player takes control of an object until the Unit of the card leaves the board. -/
def takeUntil (p : PlayerId) (card : Option ObjId) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  let r := setController p s id
  (r.1.modObj id (fun o => { o with takenBy := card }), r.2)

/-- Taking control until a Unit leaves is a safe change. -/
theorem takeUntil_safe (p : PlayerId) (card : Option ObjId) (s : GameState) (id : ObjId) :
    Safe s (takeUntil p card s id).1 :=
  (setController_safe p s id).trans (Safe.modObj _ id (fun _ => rfl) (fun _ => rfl))

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

/-- A Trash replacement can still apply to a simultaneous kill after its own source was removed
by the same instruction (CR 370.1.a.2, 370.4). -/
def killOrSaveInGroup (before s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    if before.replacesTrash id o && !s.banishedOnDeath id &&
        (s.deathSaver id).isNone then banishObj o.owner s id
    else killOrSave s id
  | none => killOrSave s id

/-- A simultaneous kill with a surviving replacement is a safe change. -/
theorem killOrSaveInGroup_safe (before s : GameState) (id : ObjId) :
    Safe s (killOrSaveInGroup before s id).1 := by
  unfold killOrSaveInGroup
  split
  · split
    · exact banishObj_safe _ _ _
    · exact killOrSave_safe _ _
  · exact killOrSave_safe _ _

/-- An effect of this turn prevents the next damage to the object. -/
def GameState.shielded (s : GameState) (id : ObjId) : Bool :=
  s.turnFx.any (fun f => f.turn == s.turn && f.kind == .damagePrevented && f.target == some id)

/-- An effect of this turn doubles the damage dealt to the object. -/
def GameState.doubleDmg (s : GameState) (id : ObjId) : Bool :=
  s.turnFx.any (fun f => f.turn == s.turn && f.kind == .doubleDamage && f.target == some id)

/-- The prevention of the next damage to the object is used up. -/
def GameState.useShield (s : GameState) (id : ObjId) : GameState :=
  { s with turnFx := s.turnFx.eraseP (fun f =>
      f.turn == s.turn && f.kind == .damagePrevented && f.target == some id) }

/-- Using up a prevention is a safe change. -/
theorem useShield_safe (s : GameState) (id : ObjId) : Safe s (s.useShield id) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- The remaining finite Prevent Value on this Unit in the current turn (CR 438.3). -/
def GameState.preventValue (s : GameState) (id : ObjId) : Nat :=
  s.turnFx.foldl (fun sum f =>
    match f.kind with
    | .preventDamage k => if f.turn == s.turn && f.target == some id then sum + k else sum
    | _ => sum) 0

/-- Spend the Prevent Values on the Unit, in the order their effects were created (CR 438.3). -/
def spendPrevent (turn : Nat) (id : ObjId) : Nat → List TurnFx → List TurnFx
  | 0, notes => notes
  | _ + 1, [] => []
  | amount + 1, note :: rest =>
    match note.kind with
    | .preventDamage n =>
      if note.turn == turn && note.target == some id then
        if amount + 1 < n then { note with kind := .preventDamage (n - (amount + 1)) } :: rest
        else spendPrevent turn id (amount + 1 - n) rest
      else note :: spendPrevent turn id (amount + 1) rest
    | _ => note :: spendPrevent turn id (amount + 1) rest
termination_by _ notes => notes.length

/-- Spending a Prevent Value changes only the turn effects. -/
theorem spendPrevent_safe (s : GameState) (id : ObjId) (n : Nat) :
    Safe s { s with turnFx := spendPrevent s.turn id n s.turnFx } :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Record positive damage even if a subsequent game effect heals the object (CR 418-419). -/
def Object.takeDamage (o : Object) (turn n : Nat) : Object :=
  { o with damage := o.damage + n, damagedTurn := if n = 0 then o.damagedTurn else some turn }

/-- In the current Combat, this Unit's controller chose to apply Prevent before doubling. -/
def GameState.preventFirst (s : GameState) (id : ObjId) : Bool :=
  s.turnFx.any (fun note =>
    note.turn == s.turn && note.target == some id && note.kind == .preventBeforeDouble)

/-- Record applied damage, then process effects that react directly to it (CR 418). -/
def dealRemaining (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  let damagingUnit := decide (0 < n) && (s.cardDef? id).any (·.hasType .unit)
  let lethal := (s.mightNow id).getD 0 ≤ ((s.obj? id).map (·.damage)).getD 0 + n
  let saver := if damagingUnit && decide lethal then s.deathSaver id else none
  let damaged := s.modObj id (fun o => o.takeDamage s.turn n)
  let event := Event.damaged id n
  match saver with
  | some g =>
    let saved := saveUnit damaged id g
    (saved.1, event :: saved.2)
  | none =>
    if damagingUnit && s.killOnHit id then
      let killed := killOrSave damaged id
      (killed.1, event :: killed.2)
    else (damaged, [event])

/-- Recording damage and applying direct reactions preserve the structural invariants. -/
theorem dealRemaining_safe (n : Nat) (s : GameState) (id : ObjId) :
    Safe s (dealRemaining n s id).1 := by
  have damaged := Safe.modObj s id (f := fun o => o.takeDamage s.turn n) (fun _ => rfl) (fun _ => rfl)
  unfold dealRemaining
  dsimp only
  split
  · exact damaged.trans (saveUnit_safe _ id _)
  · split
    · exact damaged.trans (killOrSave_safe _ id)
    · exact damaged

/-- Preview how much finite prevention is spent and how much damage remains, in the chosen order
(CR 438.2-438.4, 467.2.c.5). -/
def GameState.previewPrevent (s : GameState) (id : ObjId) (n : Nat) : Nat × Nat :=
  let scale := if s.doubleDmg id then 2 else 1
  let early := s.preventFirst id
  let incoming := if early then n else n * scale
  let prevented := min incoming (s.preventValue id)
  (prevented, (incoming - prevented) * (if early then scale else 1))

/-- Spend finite prevention, then apply any damage left (CR 438.2-438.4). -/
def dealThroughPrevent (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  let (prevented, damage) := s.previewPrevent id n
  let after := { s with turnFx := spendPrevent s.turn id prevented s.turnFx }
  if 0 < n ∧ damage = 0 then (after, [])
  else dealRemaining damage after id

/-- Applying finite prevention preserves the structural invariants. -/
theorem dealThroughPrevent_safe (n : Nat) (s : GameState) (id : ObjId) :
    Safe s (dealThroughPrevent n s id).1 := by
  unfold dealThroughPrevent
  split
  split
  · exact spendPrevent_safe s id _
  · exact (spendPrevent_safe s id _).trans (dealRemaining_safe _ _ _)

/-- Apply damage after accounting for immunity, doubling and prevention (CR 418, 438). An object
whose damage reaches its Might is killed by the next Cleanup (CR 323.4), not here. -/
def dealObj (n : Nat) (s : GameState) (id : ObjId) (effectController : Option PlayerId := none) :
    GameState × List Event :=
  match s.obj? id with
  | some o =>
    let mods := s.activeMods id
    if mods.contains .noDamage ||
        (effectController.any (· != o.controller) && mods.contains .noEnemyEffectDamage) then
      (s, [])
    else if decide (0 < n) && s.shielded id then (s.useShield id, [])
    else dealThroughPrevent n s id
  | none => (s, [])

/-- Dealing damage is a safe change. -/
theorem dealObj_safe (n : Nat) (s : GameState) (id : ObjId)
    (effectController : Option PlayerId := none) : Safe s (dealObj n s id effectController).1 := by
  unfold dealObj
  dsimp only
  split
  · split
    · exact Safe.refl s
    · split
      · exact useShield_safe s id
      · exact dealThroughPrevent_safe n s id
  · exact Safe.refl s

/-- Read both Mights before marking damage. The Units themselves are the sources, so
modifiers for damage from a Spell do not apply (CR 418.6.b.3). -/
def exchangeDamage (s : GameState) (a b : ObjId) : GameState × List Event :=
  match s.mightNow a, s.mightNow b with
  | some am, some bm =>
    let hit := dealObj am.toNat s b
    let reply := dealObj bm.toNat hit.1 a
    (reply.1, hit.2 ++ reply.2)
  | _, _ => (s, [])

/-- The exchange keeps the structural invariants. -/
theorem exchangeDamage_safe (s : GameState) (a b : ObjId) :
    Safe s (exchangeDamage s a b).1 := by
  unfold exchangeDamage
  split
  · exact (dealObj_safe _ s b).trans (dealObj_safe _ _ a)
  · exact Safe.refl s

/-- Attach an Equipment to a Unit (CR 137, 825). -/
def attachTo (u : ObjId) (s : GameState) (g : ObjId) : GameState × List Event :=
  if (s.obj? g).any (·.attached != some u) && !((s.cardDef? g).any (·.hasType .unit)) then
    let attach (o : Object) := { o with
      attached := some u, attachedTurn := some s.turn, attachmentCopyStamp := none }
    (s.modObj g attach, [Event.attached g u])
  else (s, [])

/-- Attaching is a safe change. -/
theorem attachTo_safe (u : ObjId) (s : GameState) (g : ObjId) : Safe s (attachTo u s g).1 := by
  unfold attachTo
  split
  · exact Safe.modObj s g (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- Capture the copyable traits of `model` for the current attachment (CR 479.1). -/
def copyAttachedUnit (g : ObjId) (s : GameState) (model : ObjId) : GameState × List Event :=
  match (s.obj? g).bind (·.attached), s.cardDef? model with
  | some unit, some d =>
    if model != unit && d.hasType .unit && (s.printedCardDef? unit).any (·.hasType .unit) &&
        s.inPlay.contains model && s.inPlay.contains unit then
      let stamp : Timestamp := ⟨s.nextTimestamp⟩
      let copy : AttachmentCopy := ⟨g, d.id, stamp⟩
      let source := s.modObj g (fun o => { o with attachmentCopyStamp := some stamp })
      let copied := source.modObj unit (fun o =>
        { o with attachmentCopies := copy :: o.attachmentCopies.filter (source.attachmentCopyActive unit) })
      ({ copied with nextTimestamp := s.nextTimestamp + 1 }, [])
    else (s, [])
  | _, _ => (s, [])

/-- Installing a copy preserves the object's physical identity and ownership. -/
theorem copyAttachedUnit_safe (g : ObjId) (s : GameState) (model : ObjId) :
    Safe s (copyAttachedUnit g s model).1 := by
  unfold copyAttachedUnit
  split
  · rename_i unit d _ _
    split
    · let stamp : Timestamp := ⟨s.nextTimestamp⟩
      let copy : AttachmentCopy := ⟨g, d.id, stamp⟩
      let setStamp (o : Object) := { o with attachmentCopyStamp := some stamp }
      let stamped := s.modObj g setStamp
      let setCopy (o : Object) := { o with
        attachmentCopies := copy :: o.attachmentCopies.filter (stamped.attachmentCopyActive unit) }
      have h := (Safe.modObj s g (f := setStamp) (fun _ => rfl) (fun _ => rfl)).trans
        (Safe.modObj stamped unit (f := setCopy) (fun _ => rfl) (fun _ => rfl))
      exact ⟨fun hwf => (h.wf hwf).congr rfl rfl rfl rfl, h.phys,
        fun hwf hown => (h.own hwf hown).congr rfl rfl, h.same⟩
    · exact Safe.refl s
  · exact Safe.refl s

/-- Double Might this turn by adding its current amount, with a minimum increase of zero
(CR 433.1, 479.4.c). -/
def doubleObj (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.mightNow id with
  | some m => (s.modObj id (fun o => { o with mightMods := o.mightMods ++ [⟨max 0 m, .turn⟩] }), [])
  | none => (s, [])

/-- Doubling the Might is a safe change. -/
theorem doubleObj_safe (s : GameState) (id : ObjId) : Safe s (doubleObj s id).1 := by
  unfold doubleObj
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- The activated ability described by a grant, when the referenced definition contains one. -/
def GameState.grantedActivation (s : GameState) (grant : AbilityGrant) : Option Ability :=
  match (s.cards.find? grant.card).bind (fun d => d.grants[grant.index]?) with
  | some (a@(.activated ..)) => some a
  | _ => none

/-- The object's ordinary abilities with their original indices, followed by the temporary
activations in the order they were granted. A grant identifies the reusable definition. -/
def GameState.activationList (s : GameState) (src : ObjId) (d : CardDef) :
    List (Option AbilityGrant × Ability) :=
  let grants := ((s.obj? src).map (·.tempActivations)).getD []
  d.fullAbilities.map (none, ·) ++ grants.filterMap
    (fun grant => (s.grantedActivation grant).map (some grant, ·))

/-- The available ability at its activation-menu index. -/
def GameState.activationAt (s : GameState) (src : ObjId) (idx : Nat) :
    Option (Option AbilityGrant × Ability) :=
  (s.cardDef? src).bind (fun d => (s.activationList src d)[idx]?)

/-- Give a board object an instance of the activated ability for the turn (CR 479.3). -/
def grantActivationObj (grant : AbilityGrant) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if (s.locate id).any Zone.isBoard && (s.grantedActivation grant).isSome then
    (s.modObj id (fun o => { o with tempActivations := o.tempActivations ++ [grant] }), [])
  else (s, [])

/-- Adding an activated ability to an object preserves structural invariants. -/
theorem grantActivationObj_safe (grant : AbilityGrant) (s : GameState) (id : ObjId) :
    Safe s (grantActivationObj grant s id).1 := by
  unfold grantActivationObj
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- Set the Unit's base Might without changing other effects on its Might (CR 479.2). -/
def setBaseMight (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  if (s.cardDef? id).any (·.hasType .unit) then
    (s.modObj id (fun o => { o with baseMightThisTurn := some n }), [])
  else (s, [])

/-- Changing the base Might preserves the structural invariants. -/
theorem setBaseMight_safe (n : Nat) (s : GameState) (id : ObjId) : Safe s (setBaseMight n s id).1 := by
  unfold setBaseMight
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- Detach an Equipment: it is attached to nothing. -/
def detachObj (s : GameState) (g : ObjId) : GameState × List Event :=
  (s.modObj g (fun o => { o with attached := none }), [])

/-- Detaching is a safe change. -/
theorem detachObj_safe (s : GameState) (g : ObjId) : Safe s (detachObj s g).1 :=
  Safe.modObj s g (fun _ => rfl) (fun _ => rfl)

/-- Attach the objects the first selector stands for to the one the second stands for. `none` if
the second is not exactly one object, or either cannot be answered. -/
def applyAttach (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (gears to : Selector) :
    Option (GameState × List Event) :=
  (gears.eval s p src env).bind (fun gs =>
    (to.eval s p src env).bind (fun tos =>
      match tos with
      | [u] => some (applyEach (attachTo u) s gs)
      | _ => none))

/-- Attaching objects is a safe change. -/
theorem applyAttach_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {gears to : Selector} {r : GameState × List Event}
    (h : applyAttach s p src env gears to = some r) : Safe s r.1 := by
  unfold applyAttach at h
  cases hg : gears.eval s p src env with
  | none => simp [hg] at h
  | some gs =>
    cases ht : to.eval s p src env with
    | none => simp [hg, ht] at h
    | some tos =>
      simp only [hg, ht, Option.bind_some] at h
      cases tos with
      | nil => simp at h
      | cons u rest =>
        cases rest with
        | nil =>
          simp only [Option.some.injEq] at h
          rw [← h]
          exact applyEach_safe (fun s id => attachTo_safe u s id) gs s
        | cons _ _ => simp at h

/-- Attach the Equipment to the unit, paying the Equip cost of each, less `less` Power
(Weaponmaster): an Equipment whose cost cannot be paid stays where it is, and one with no Equip
cost is not attached. `none` if the unit is not exactly one object, or either cannot be
answered. -/
def applyAttachPaying (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (gears to : Selector) (less : Nat) : Option (GameState × List Event) :=
  (gears.eval s p src env).bind (fun gs =>
    (to.eval s p src env).bind (fun tos =>
      match tos with
      | [u] =>
        if u ∈ s.inPlay then
        some (gs.foldl (fun (r : GameState × List Event) g =>
          match (r.1.cardDef? g).bind CardDef.equipCost with
          | some c =>
            match payByRunes r.1 p g (c.dropPower less) with
            | some q => ((attachTo u q.1 g).1, r.2 ++ q.2 ++ (attachTo u q.1 g).2)
            | none => r
          | none => r) (s, []))
        else some (s, [])
      | _ => none))

/-- Attaching Equipment for a cost is a safe change. -/
theorem applyAttachPaying_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {gears to : Selector} {less : Nat} {r : GameState × List Event}
    (h : applyAttachPaying s p src env gears to less = some r) : Safe s r.1 := by
  unfold applyAttachPaying at h
  cases hg : gears.eval s p src env with
  | none => simp [hg] at h
  | some gs =>
    cases ht : to.eval s p src env with
    | none => simp [hg, ht] at h
    | some tos =>
      simp only [hg, ht, Option.bind_some] at h
      cases tos with
      | nil => simp at h
      | cons u rest =>
        cases rest with
        | nil =>
          by_cases hu : u ∈ s.inPlay
          · simp only [hu, ite_true, Option.some.injEq] at h
            rw [← h]
            have key : ∀ (l : List ObjId) (r0 : GameState × List Event), Safe s r0.1 →
                Safe s (l.foldl (fun (r : GameState × List Event) g =>
                  match (r.1.cardDef? g).bind CardDef.equipCost with
                  | some c =>
                    match payByRunes r.1 p g (c.dropPower less) with
                    | some q => ((attachTo u q.1 g).1, r.2 ++ q.2 ++ (attachTo u q.1 g).2)
                    | none => r
                  | none => r) r0).1 := by
              intro l
              induction l with
              | nil => intro r0 h0; exact h0
              | cons g rest ih =>
                intro r0 h0
                simp only [List.foldl_cons]
                apply ih
                cases hc : (r0.1.cardDef? g).bind CardDef.equipCost with
                | none => simpa [hc] using h0
                | some c =>
                  cases hp : payByRunes r0.1 p g (c.dropPower less) with
                  | none => simpa [hc, hp] using h0
                  | some q =>
                    simp only [hp]
                    exact h0.trans ((payByRunes_safe hp).trans (attachTo_safe u _ g))
            exact key gs (s, []) (Safe.refl s)
          · simp only [hu, ite_false, Option.some.injEq] at h
            rw [← h]
            exact Safe.refl s
        | cons _ _ => simp at h

/-- A Unit token the player plays enters ready: an effect of the turn says the units the player
plays enter ready ("Friendly units enter ready this turn"), or a passive ability of an object they
control says their tokens do. -/
def GameState.tokenReady (s : GameState) (p : PlayerId) (c : CardDef) : Bool :=
  c.hasType .unit && ((s.fxOf p).any (fun k => k == .unitsReady) ||
    -- a passive ability of an object the player controls: "your tokens enter ready"
    s.passiveSources.any (fun g => (s.obj? g).any (·.controller == p) &&
      (s.activeMods g).any (fun m =>
        match m with
        | .entersReady (.pick .all .friendly .anywhere fs) => fs == FilterList.ofList [.token]
        | _ => false)))

/-- The Units played as tokens between two states: they were played, as the abilities that wait for
a Unit to be played see it (the tokens made are the objects with the new identifiers). -/
def tokenPlays (s s' : GameState) (p : PlayerId) : List Event :=
  (List.range (s'.nextId - s.nextId)).filterMap (fun i =>
    if (s.obj? ⟨s.nextId + i⟩).isNone &&
        (s'.cardDef? ⟨s.nextId + i⟩).any (·.hasType .unit) then
      some (Event.tokenPlayed p ⟨s.nextId + i⟩)
    else none)

/-- A Unit played as a token is buffed. -/
def buffTokenEv (t : GameState) (e : Event) : GameState :=
  match e with
  | .tokenPlayed _ id => t.modObj id (fun o => { o with buffed := true })
  | _ => t

/-- Buffing a token is a safe change. -/
theorem buffTokenEv_safe (t : GameState) (e : Event) : Safe t (buffTokenEv t e) := by
  unfold buffTokenEv
  split
  · exact Safe.modObj t _ (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl t

/-- Buffing the tokens that were played is a safe change. -/
theorem foldl_buffTokenEv_safe : ∀ (l : List Event) (t : GameState),
    Safe t (l.foldl buffTokenEv t)
  | [], t => Safe.refl t
  | e :: l, t => (buffTokenEv_safe t e).trans (foldl_buffTokenEv_safe l _)

/-- The Units played as tokens enter buffed, by an effect of the turn (Rally the Troops): `r` is
the state after the tokens were made from `s`. -/
def buffNewTokens (s r : GameState) (p : PlayerId) : GameState :=
  if (s.fxOf p).any (· == .unitsBuffed) then (tokenPlays s r p).foldl buffTokenEv r else r

/-- Buffing the new tokens is a safe change. -/
theorem buffNewTokens_safe (s r : GameState) (p : PlayerId) : Safe r (buffNewTokens s r p) := by
  unfold buffNewTokens
  split
  · exact foldl_buffTokenEv_safe _ r
  · exact Safe.refl r

/-- The locations a Unit token can be played to. Its controller may use their Base or a Battlefield
they control, and effects can grant or restrict Battlefield permissions (CR 184.2, 355.2). -/
def GameState.unitTokenDestinations (s : GameState) (p : PlayerId) (c : CardDef) :
    List (Option ObjId) :=
  let preview := createOne c.id p none false s
  let extra := preview.playBfOptions p ⟨s.nextId⟩
  let fields := (s.zone .battlefieldZone).filter (fun bf =>
    (s.cardDef? bf).any (·.hasType .battlefield) &&
    !s.oppHas p .oppsPlayToBaseOnly && !s.cantActHere p .play bf &&
    FilterList.holds s bf {} bf (.cons .unitsPlayable .nil) == some true &&
    ((s.obj? bf).any (·.control == some p) || extra.contains bf))
  none :: fields.map some

/-- Play a Unit token at a valid destination. -/
def playUnitTokenAt (s : GameState) (p : PlayerId) (name : String) (dest : Option ObjId) :
    GameState × List Event :=
  match s.tokenCard name with
  | some c =>
    if c.hasType .unit && (s.unitTokenDestinations p c).contains dest then
      let r := createOne c.id p dest (s.tokenReady p c) s
      let next := dest.elim r (fun bf => contestFor p bf r)
      (buffNewTokens s next p, tokenPlays s next p)
    else (s, [])
  | none => (s, [])

/-- Playing a Unit token at its destination is a safe change. -/
theorem playUnitTokenAt_safe (s : GameState) (p : PlayerId) (name : String) (dest : Option ObjId) :
    Safe s (playUnitTokenAt s p name dest).1 := by
  unfold playUnitTokenAt
  split
  · rename_i c _
    split
    · have place := createOne_safe c.id p dest (s.tokenReady p c) s
      cases dest with
      | none => exact place.trans (buffNewTokens_safe _ _ _)
      | some bf => exact place.trans ((contestFor_safe p bf _).trans (buffNewTokens_safe _ _ _))
    · exact Safe.refl s
  · exact Safe.refl s

/-- Play tokens: `n` of them on the player's Base or here, if the token is in the game's cards
(CR 183). `none` if it cannot be done yet. -/
def applyCreate (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (name : String)
    (n : Amount) (place : Place) (ready : Bool) : Option (GameState × List Event) :=
  (n.evalS s p src env).bind (fun k =>
    match s.tokenCard name with
    | none => none
    | some c =>
      match place with
      | .atBase =>
        let r := createN c.id p none (ready || s.tokenReady p c) k s
        some (buffNewTokens s r p, tokenPlays s r p)
      | .here =>
        match s.hereOf src with
        | some bf =>
          let r := createN c.id p (some bf) (ready || s.tokenReady p c) k s
          some (buffNewTokens s r p, tokenPlays s r p)
        | none =>
          -- at a Base, "here" is that Base
          if s.baseHere src then
            let r := createN c.id p none (ready || s.tokenReady p c) k s
            some (buffNewTokens s r p, tokenPlays s r p)
          else none
      | _ => none)

/-- Playing tokens is a safe change. -/
theorem applyCreate_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {name : String}
    {n : Amount} {place : Place} {ready : Bool} {r : GameState × List Event}
    (h : applyCreate s p src env name n place ready = some r) : Safe s r.1 := by
  unfold applyCreate at h
  cases hn : n.evalS s p src env with
  | none => simp [hn] at h
  | some k =>
    simp only [hn, Option.bind_some] at h
    cases ht : s.tokenCard name with
    | none => simp [ht] at h
    | some c =>
      simp only [ht] at h
      cases place with
      | atBase =>
        simp only [Option.some.injEq] at h
        rw [← h]
        exact (createN_safe _ _ _ _ _ _).trans (buffNewTokens_safe _ _ _)
      | here =>
        cases hh : s.hereOf src with
        | none =>
          simp only [hh] at h
          split at h
          · simp only [Option.some.injEq] at h
            rw [← h]
            exact (createN_safe _ _ _ _ _ _).trans (buffNewTokens_safe _ _ _)
          · simp at h
        | some bf =>
          simp only [hh, Option.some.injEq] at h
          rw [← h]
          exact (createN_safe _ _ _ _ _ _).trans (buffNewTokens_safe _ _ _)
      | anywhere => simp at h
      | boardOrLegend => simp at h
      | atBattlefield => simp at h
      | inHand => simp at h
      | inTrash => simp at h
      | inMainDeck => simp at h
      | inRuneDeck => simp at h
      | inChampionZone => simp at h
      | inLegendZone => simp at h
      | inHidden => simp at h
      | inBanishment => simp at h
      | inCombat => simp at h
      | onChain => simp at h
      | onChainAll => simp at h

/-- Play tokens at the Battlefield the object left by its last move, or at the Base (Lillia). -/
def applyCreateAtPrev (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (name : String)
    (n : Amount) (ready : Bool) : Option (GameState × List Event) :=
  (n.evalS s p src env).bind (fun k =>
    (s.tokenCard name).map (fun c =>
      let r := createN c.id p ((s.obj? src).bind (·.prevLoc)) (ready || s.tokenReady p c) k s
      (buffNewTokens s r p, tokenPlays s r p)))

/-- Playing tokens at the place an object came from is a safe change. -/
theorem applyCreateAtPrev_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {name : String} {n : Amount} {ready : Bool} {r : GameState × List Event}
    (h : applyCreateAtPrev s p src env name n ready = some r) : Safe s r.1 := by
  unfold applyCreateAtPrev at h
  cases hn : n.evalS s p src env with
  | none => simp [hn] at h
  | some k =>
    simp only [hn, Option.bind_some] at h
    cases ht : s.tokenCard name with
    | none => simp [ht] at h
    | some c =>
      simp only [ht, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact (createN_safe _ _ _ _ _ _).trans (buffNewTokens_safe _ _ _)

/-- Play one more token like the one the object is, where it is. -/
def cloneTok (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    match o.kind with
    | .token c =>
      let card := (s.attachmentCopyOf id o).elim c (·.card)
      (createOne card o.controller o.loc (!o.exhausted) s, [])
    | _ => (s, [])
  | none => (s, [])

/-- Playing a copy of a token is a safe change. -/
theorem cloneTok_safe (s : GameState) (id : ObjId) : Safe s (cloneTok s id).1 := by
  unfold cloneTok
  split
  · split
    · exact createOne_safe _ _ _ _ s
    · exact Safe.refl s
  · exact Safe.refl s

/-- Banish an object, and note on the banished card that `src` banished it. -/
def banishMarked (p : PlayerId) (src : ObjId) (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := banishObj p s id
  match r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none) with
  | some n => (r.1.modObj n (fun x => { x with banishedWith := some src }), r.2)
  | none => r

/-- Banishing an object, noting who did it, is a safe change. -/
theorem banishMarked_safe (p : PlayerId) (src : ObjId) (s : GameState) (id : ObjId) :
    Safe s (banishMarked p src s id).1 := by
  unfold banishMarked
  dsimp only
  split
  · rename_i n hn
    exact (sendObj_safe .banishment s id).trans (Safe.modObj _ n (fun _ => rfl) (fun _ => rfl))
  · exact sendObj_safe .banishment s id

/-- Move the card to the zone of its owner, noting that `src` did it if asked. -/
def sendMarked (p : PlayerId) (src : ObjId) (mark : Bool) (k : ZoneKind) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if mark then banishMarked p src s id
  else if k == .banishment then banishObj p s id
  else sendObj k s id

/-- Moving a card, noting who did it, is a safe change. -/
theorem sendMarked_safe (p : PlayerId) (src : ObjId) (mark : Bool) (k : ZoneKind)
    (s : GameState) (id : ObjId) : Safe s (sendMarked p src mark k s id).1 := by
  unfold sendMarked
  split
  · exact banishMarked_safe p src s id
  · split
    · exact sendObj_safe .banishment s id
    · exact sendObj_safe k s id

/-- Move every card of the sides in a zone of theirs that has the properties to another zone. -/
def applyMoveAll (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (side : Side)
    (place : Place) (fs : FilterList) (dest : Place) (mark : Bool) :
    Option (GameState × List Event) :=
  match place.zoneKind?, dest.zoneKind? with
  | some z, some k =>
    let ids := (s.players.filter (fun q => side.admitsPlayer p q)).flatMap (fun q =>
      (s.zone (.player q z)).filter (fun u => FilterList.holds s src env u fs == some true))
    some (applyEach (sendMarked p src mark k) s ids)
  | _, _ => none

/-- The object gains a tag. -/
def gainTagObj (name : String) (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with tagsGained := o.tagsGained ++ [name] }), [])

/-- Gaining a tag is a safe change. -/
theorem gainTagObj_safe (name : String) (s : GameState) (id : ObjId) :
    Safe s (gainTagObj name s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- An effect of the player moved the units: the events say so. -/
def movedEvents (p : PlayerId) (r : GameState × List Event) : GameState × List Event :=
  (r.1, r.2 ++ r.2.filterMap (fun e => match e with
    | .standardMoved u _ => some (Event.movedByEffect p u)
    | _ => none))

/-- The units at the Battlefield `old` are at `new` instead. -/
def relocateUnits (old new : ObjId) (s : GameState) : GameState :=
  (s.zone .battlefieldZone).foldl (fun t u =>
    if (t.obj? u).any (·.loc == some old) then t.modObj u (fun o => { o with loc := some new })
    else t) s

/-- Moving the units from one Battlefield to another is a safe change. -/
theorem relocateUnits_safe (old new : ObjId) (s : GameState) : Safe s (relocateUnits old new s) := by
  unfold relocateUnits
  suffices h : ∀ (l : List ObjId) (t : GameState), Safe t (l.foldl (fun t u =>
      if (t.obj? u).any (·.loc == some old) then t.modObj u (fun o => { o with loc := some new })
      else t) t) from h _ s
  intro l
  induction l with
  | nil => intro t; exact Safe.refl t
  | cons u l ih =>
    intro t
    simp only [List.foldl_cons]
    refine Safe.trans ?_ (ih _)
    split
    · exact Safe.modObj t u (fun _ => rfl) (fun _ => rfl)
    · exact Safe.refl t

/-- The object of the Battlefield token that replaces the Battlefield `old` that is set aside as `r`. -/
def bfToken (c : CardDef) (p : PlayerId) (old : Object) (aside : ObjId) : Object :=
  { kind := .token c.id, owner := p, controller := p, timestamp := ⟨0⟩, control := old.control,
    replaces := some aside }

/-- Replace the Battlefield `b` with the Battlefield token: `b` is set aside, the token is in its
place with the units that were there, and the control of it is the one `b` had. -/
def replaceBf (c : CardDef) (p : PlayerId) (s : GameState) (b : ObjId) : GameState × List Event :=
  match s.obj? b with
  | some o =>
    match moveObj s b (.player o.owner .banishment) with
    | some r =>
      match addObject r.1 (bfToken c p o r.2) .battlefieldZone with
      | some t => (relocateUnits b t.2 t.1, [])
      | none => (s, [])
    | none => (s, [])
  | none => (s, [])

/-- Replacing a Battlefield is a safe change. -/
theorem replaceBf_safe (c : CardDef) (p : PlayerId) (s : GameState) (b : ObjId) :
    Safe s (replaceBf c p s b).1 := by
  unfold replaceBf
  cases ho : s.obj? b with
  | none => simp only []; exact Safe.refl s
  | some o =>
    simp only []
    cases hr : moveObj s b (.player o.owner .banishment) with
    | none => simp only []; exact Safe.refl s
    | some r =>
      simp only []
      cases ht : addObject r.1 (bfToken c p o r.2) .battlefieldZone with
      | none => simp only []; exact Safe.refl s
      | some t =>
        simp only []
        exact (Safe.moveObj hr).trans ((safe_addObject rfl ht).trans (relocateUnits_safe _ _ _))

/-- The Battlefield `old` is back, as `r`, where the token `cur` was: with its control, and its units. -/
def restoreStep (cur : ObjId) (o : Object) (r : GameState × ObjId) : GameState :=
  relocateUnits cur r.2 (r.1.modObj r.2 (fun x => { x with control := o.control }))

/-- Putting a Battlefield back in place of a token is a safe change. -/
theorem restoreStep_safe (cur : ObjId) (o : Object) (r : GameState × ObjId) :
    Safe r.1 (restoreStep cur o r) :=
  (Safe.modObj r.1 r.2 (f := fun x => { x with control := o.control }) (fun _ => rfl)
    (fun _ => rfl)).trans (relocateUnits_safe _ _ _)

/-- Put the Battlefield the token `cur` replaced back in its place, and the token away. -/
def restoreBf (s : GameState) (cur : ObjId) : GameState × List Event :=
  match s.obj? cur with
  | some o =>
    match o.replaces with
    | some old =>
      match moveObj s old .battlefieldZone with
      | some r =>
        match moveObj (restoreStep cur o r) cur (.player o.owner .trash) with
        | some t => (t.1, [])
        | none => (restoreStep cur o r, [])
      | none => (s, [])
    | none => (s, [])
  | none => (s, [])

/-- Putting a replaced Battlefield back is a safe change. -/
theorem restoreBf_safe (s : GameState) (cur : ObjId) : Safe s (restoreBf s cur).1 := by
  unfold restoreBf
  cases ho : s.obj? cur with
  | none => simp only []; exact Safe.refl s
  | some o =>
    simp only []
    cases hq : o.replaces with
    | none => simp only []; exact Safe.refl s
    | some old =>
      simp only []
      cases hr : moveObj s old .battlefieldZone with
      | none => simp only []; exact Safe.refl s
      | some r =>
        simp only []
        cases ht : moveObj (restoreStep cur o r) cur (.player o.owner .trash) with
        | none => simp only []; exact (Safe.moveObj hr).trans (restoreStep_safe cur o r)
        | some t =>
          simp only []
          exact ((Safe.moveObj hr).trans (restoreStep_safe cur o r)).trans (Safe.moveObj ht)

/-- The event that says the player chose the object while the effect of `src` resolved: a choice by
a spell, or by an ability. -/
def chosenAt (s : GameState) (p : PlayerId) (src o : ObjId) : List Event :=
  if (s.cardDef? src).any (·.hasType .spell) then [Event.chosenBySpell p o]
  else [Event.chosenByAbility p o]

/-- Give an object a keyword for a while (CR 479.3). -/
def addTempKw (k : KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  (s.modObj id (fun o => { o with tempKws := o.tempKws ++ [(k, ends)] }), [])

/-- Giving a keyword for a while is a safe change. -/
theorem addTempKw_safe (k : KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (addTempKw k ends s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- Give an object several keywords for a while. -/
def addTempKws (ks : List KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  (ks.foldl (fun t k => (addTempKw k ends t id).1) s, [])

/-- Giving several keywords for a while is a safe change. -/
theorem addTempKws_safe (ks : List KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (addTempKws ks ends s id).1 := by
  unfold addTempKws
  suffices h : ∀ (l : List KeywordInst) (t : GameState),
      Safe t (l.foldl (fun t k => (addTempKw k ends t id).1) t) from h ks s
  intro l
  induction l with
  | nil => intro t; exact Safe.refl t
  | cons k l ih => intro t; exact (addTempKw_safe k ends t id).trans (ih _)

/-- The keywords an object has now: those printed on its card, and those it was given. -/
def GameState.keywordsNow (s : GameState) (id : ObjId) : List KeywordInst :=
  ((s.cardDef? id).map (·.keywords)).getD [] ++ s.grantedKws id

/-- Give an object an instance of Empowered if it is in play and below its limit (CR 442). -/
def empowerObj (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id, s.cardDef? id with
  | some o, some c =>
    if o.empowerCount < c.empowerLimit &&
        (s.inPlay.contains id ||
          (c.hasType .legend && (s.zone (.player o.owner .legendZone)).contains id)) then
      (s.modObj id (fun x => { x with empowerCount := x.empowerCount + 1 }), [.empowered p id])
    else (s, [])
  | _, _ => (s, [])

/-- Empower preserves structural invariants and physical cards. -/
theorem empowerObj_safe (p : PlayerId) (s : GameState) (id : ObjId) :
    Safe s (empowerObj p s id).1 := by
  unfold empowerObj
  split
  · split
    · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
    · exact Safe.refl s
  · exact Safe.refl s

/-- Remove an instance of Empowered (CR 443). -/
def disempowerObj (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with empowerCount := o.empowerCount - 1 }), [])

/-- Disempower preserves structural invariants and physical cards. -/
theorem disempowerObj_safe (s : GameState) (id : ObjId) :
    Safe s (disempowerObj s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- A finalized Spell resolves for its current controller (CR 420.4.a, 750). -/
def spellCompletion (s : GameState) (id : ObjId) (events : List Event) (inPlace : Bool := false) :
    List Event :=
  if (s.cardDef? id).any (·.hasType .spell) then
    let moved := events.findSome? (fun
      | .moved old next _ => if old == id then some next else none
      | _ => none)
    match (s.obj? id).filter (fun _ =>
        s.playLog.any (fun play => play.object == id && play.moment == .finalized)),
        moved <|> (if inPlace then some id else none) with
    | some o, some next => [.spellResolved o.controller next] ++
      (if o.fromHidden && o.hiddenAt.isSome then [.hiddenPlayed o.controller] else [])
    | _, _ => []
  else []

/-- Do a game action that changes objects: the new state and the events. `none` if the action is
not understood yet, or what it names cannot be found. -/
def applyPrim (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) :
    Prim → Option (GameState × List Event)
  | .deal sel n =>
    if s.damageOff then some (s, []) else
    (n.evalS s p src env).bind (fun k => onSelected s p src env sel
      (fun t id => dealObj (if 0 < k then k + s.bonusOn p src id else k) t id
        (some (env.effectController.getD p))))
  | .exchangeDamage a b =>
    match a.eval s p src env, b.eval s p src env with
    | some (x :: _), some (y :: _) => some (exchangeDamage s x y)
    | _, _ => some (s, [])
  | .setBaseMight sel n =>
    (n.evalS s p src env).bind (fun k => onSelected s p src env sel (setBaseMight k))
  | .heal sel n => (n.evalS s p src env).bind (fun k => onSelected s p src env sel (healOne k))
  | .kill sel =>
    -- a unit killed by a spell is noted, for what waits for that (Immortal Phoenix)
    (onSelected s p src env sel (killOrSaveInGroup s)).map (fun r =>
      (r.1, r.2 ++ (if (s.cardDef? src).any (·.hasType .spell) &&
          r.2.any (fun e => match e with
            | .died n _ => (r.1.cardDef? n).any (·.hasType .unit)
            | _ => false)
        then [Event.killedBySpell p] else [])))
  | .ready sel => onSelected s p src env sel readyEffect
  | .exhaust sel => onSelected s p src env sel (setExhausted true)
  | .banish sel => onSelected s p src env sel (banishObj p)
  | .returnToHand sel => onSelected s p src env sel (replaceChosenHarm env (sendObj .hand))
  | .create name n place ready => applyCreate s p src env name n place ready
  | .playUnitTokenAt name dest => some (playUnitTokenAt s p name dest)
  | .attach gears to => applyAttach s p src env gears to
  | .copyAttachedFrom model => onSelected s p src env model (copyAttachedUnit src)
  | .detach sel => onSelected s p src env sel detachObj
  | .double sel => onSelected s p src env sel doubleObj
  | .grantActivation sel grant => onSelected s p src env sel (grantActivationObj grant)
  | .topdeck sel => onSelected s p src env sel (sendObj .mainDeck)
  | .attachPaying gears to less => applyAttachPaying s p src env gears to less
  | .move sel .base =>
    (onSelected s p src env sel (moveByEffect (env.effectController.getD p) none)).map (movedEvents p)
  | .move sel (.at_ dsel) =>
    -- the place of the first object the destination names: a Battlefield, or where a Unit is
    match dsel.eval s p src env with
    | some (d :: _) =>
      -- a Battlefield, or the Battlefield a Unit is at; a Unit at a Base names no place yet
      match (if (s.cardDef? d).any (·.hasType .battlefield) then some d
          else (s.obj? d).bind (·.loc)) with
      | some bf =>
        (onSelected s p src env sel (moveByEffect (env.effectController.getD p) (some bf))).map
          (movedEvents p)
      | none => none
    | _ => none
  | .swapPlaces a b =>
    match a.eval s p src env, b.eval s p src env with
    | some (x :: _), some (y :: _) =>
      some (movedEvents p (swapPlaces s x y (some (env.effectController.getD p))))
    | _, _ => none
  | .stun sel => onSelected s p src env sel (replaceChosenHarm env stunObj)
  | .buff sel => onSelected s p src env sel buffObj
  | .empower sel => onSelected s p src env sel (empowerObj p)
  | .disempower sel => onSelected s p src env sel disempowerObj
  | .gainXP ps n =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k => (gainXPAll k s l, [])))
  | .spendXP ps n =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k => (spendXPAll k s l, [])))
  | .channel ps n extra =>
    (ps.resolve s p env).bind (fun l =>
      (n.evalS s p src env).bind (fun k =>
        (extra.evalS s p src env).map (fun x => channelAll k x s l)))
  | .recycle sel =>
    -- recycling a card that is a card (not a Rune), even in its deck, is noted
    (sel.eval s p src env).map (fun ids =>
      let r := applyEach recycleOne s ids
      (r.1, r.2 ++ (if ids.any (fun id => (s.obj? id).isSome && recycleKind s id == .mainDeck)
        then [Event.recycled p] else []) ++
        (if sel == .self then spellCompletion s src r.2 true else [])))
  -- revealing shows information: nothing changes, but the object is chosen
  | .reveal sel =>
    -- a card revealed from its owner's deck is noted: what waits for it fires (Undertitan)
    some (s, ((sel.eval s p src env).getD []).filterMap (fun id =>
      match s.obj? id with
      | some o => if (s.zone (.player o.owner .mainDeck)).contains id then
          some (Event.revealed o.owner id) else none
      | none => none))
  | .revealTop n =>
    -- the top cards of the Main Deck are revealed: what waits for them fires
    some (s, ((s.zone (.player p .mainDeck)).take n).map (fun id => Event.revealed p id))
  | .revealTopNow n =>
    some (s, ((s.zone (.player p .mainDeck)).take n).map (fun id => Event.revealed p id))
  | .revealNow sel =>
    -- a card revealed from its owner's deck is noted: what waits for it fires (Undertitan)
    some (s, ((sel.eval s p src env).getD []).filterMap (fun id =>
      match s.obj? id with
      | some o => if (s.zone (.player o.owner .mainDeck)).contains id then
          some (Event.revealed o.owner id) else none
      | none => none))
  | .spendBuff sel => onSelected s p src env sel unbuffObj
  | .play sel => onSelected s p src env sel (playFree p)
  | .banishReplay sel keep =>
    onSelected s p src env sel (fun t id => banishReplay p t id keep)
  | .playPaying sel => onSelected s p src env sel (playPaying p)
  | .playTo sel bfs =>
    match bfs.eval s p src env with
    | some (b :: _) => onSelected s p src env sel (playToOrBase p b)
    | _ => none
  | .playReduced sel less dest =>
    (less.evalS s p src env).bind (fun k =>
      match dest with
      | none => onSelected s p src env sel (playReducedOne p k none)
      | some bfs =>
        match bfs.eval s p src env with
        | some (b :: _) => onSelected s p src env sel (playReducedOne p k (some b))
        | _ => none)
  | .giveKeywords to from_ =>
    (from_.eval s p src env).bind (fun l =>
      match l with
      | f :: _ => onSelected s p src env to (addTempKws (s.keywordsNow f) .turn)
      | [] => none)
  | .castPicked sel less idx =>
    (less.evalS s p src env).bind (fun k => onSelected s p src env sel (castPickedOne p k idx))
  | .bin sel => (onSelected s p src env sel (sendObj .trash)).map
    (fun r => (r.1, r.2 ++ spellCompletion s src r.2))
  | .discardCard sel => onSelected s p src env sel discardObj
  | .counter sel => onSelected s p src env sel counterObj
  | .counterToHand sel => onSelected s p src env sel counterObjHand
  | .hideAt sel bfs =>
    match bfs.eval s p src env with
    | some (b :: _) => onSelected s p src env sel (hideObj b)
    | _ => none
  | .recycleTop ps =>
    (ps.resolve s p env).map (fun l => (recycleTopAll s l,
      l.filterMap (fun q =>
        if (s.zone (.player q .mainDeck)).isEmpty then none else some (Event.recycled q))))
  | .swapTop ps => (ps.resolve s p env).map (fun l => (swapTopAll s l, []))
  | .takeControl sel => onSelected s p src env sel (setController p)
  | .addBattlefield name => (s.tokenCard name).map (fun c => (addBattlefieldTok c p s, []))
  | .createAtPrev name n ready => applyCreateAtPrev s p src env name n ready
  | .cloneToken sel => onSelected s p src env sel cloneTok
  | .banishWith sel => onSelected s p src env sel (banishMarked p src)
  | .gainTag sel name => onSelected s p src env sel (gainTagObj name)
  | .replaceBattlefield sel name =>
    (s.tokenCard name).bind (fun c => onSelected s p src env sel (replaceBf c p))
  | .restoreBattlefield sel => onSelected s p src env sel restoreBf
  | .moveAll side place fs dest mark => applyMoveAll s p src env side place fs dest mark
  | .becomeCopy sel from_ =>
    match from_.eval s p src env with
    | some (c :: _) => onSelected s p src env sel (becomeCopyOf c)
    | _ => none
  | .playBanishedWith =>
    some (applyEach (playFree p) s ((s.zone (.player p .banishment)).filter (fun id =>
      (s.obj? id).any (·.banishedWith == some src) && (s.cardDef? id).any (·.hasType .unit))))
  | .returnControl sel => onSelected s p src env sel giveBack
  | .takeControlUntilLeaves sel =>
    onSelected s p src env sel (takeUntil p (some src))
  | .recall sel ex => onSelected s p src env sel (recallFx ex)
  | .win ps =>
    -- winning is reaching the Victory Score: the Cleanup that follows declares the winner
    (ps.resolve s p env).map (fun l =>
      (gainPointsAll s.victoryScore s l, []))
  | .score ps n =>
    -- a player who cannot score gets no point from the effect either (Tianna)
    (ps.resolve s p env).bind (fun l0 => (n.evalS s p src env).map (fun k =>
      let l := l0.filter (fun q => !s.cantActHere q .score src)
      (gainPointsAll k s l, if k = 0 then [] else l.map (fun q => Event.pointsGained q k))))
  | .turnEffect e =>
    -- a Spell played from hiding is played too (what waits for a spell played fires)
    some (s.addTurnFx p e, if e == .hiddenPlayed then
      Event.hiddenPlayed p :: (if (s.cardDef? src).any (·.hasType .spell) then
        [Event.played p src] else [])
      else [])
  | .playFirst fs => some (playFirstOf fs p src env s)
  | .markOn sel e => onSelected s p src env sel
      (fun t id => (t.addTurnFxOn p id (e.forCopy env.abilityCopyStamp), []))
  | .delayUntilDeath sel idx =>
    (env.sourceCard <|> (s.cardDef? src).map (·.id)).bind (fun card =>
      onSelected s p src env sel (fun t id =>
        (t.addTurnFxOn p id (.triggerOnDeath src card idx), [])))
  | .returnChampion => some (returnChampion p s)
  | .extraTurn ps =>
    (ps.resolve s p env).map (fun l => ({ s with extraTurns := s.extraTurns ++ l }, []))
  | .lookTop n => some (s, ((s.zone (.player p .mainDeck)).take n).map (Event.lookedAt p))
  | .choose sel => (sel.eval s p src env).map (fun ids => (s, ids.flatMap (chosenAt s p src)))
  | .activateConquer sel =>
    onSelected s p src env sel (fun t id => (t, [Event.conquerActivated id]))
  | .pay c =>
    -- from the Pool, or with Runes if it falls short; nothing is paid if it cannot be
    match payByRunes s p src c with
    | some r => some r
    | none => some (s, [])
  | .addEnergy ps n none =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addEnergy k) s l, [])))
  | .addUnitEnergy ps n =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addUnitEnergy k) s l, [])))
  | .addPower ps n (some d) none =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addPower d k) s l, [])))
  | .addPower ps n none none =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsAddAny k s l, [])))
  | _ => none

/-- An action that is done is a safe change. -/
theorem applyPrim_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {pr : Prim}
    {r : GameState × List Event} (h : applyPrim s p src env pr = some r) : Safe s r.1 := by
  cases pr with
  | deal sel n =>
    simp only [applyPrim] at h
    by_cases hd : s.damageOff = true
    · simp only [hd, ite_true, Option.some.injEq] at h
      subst h
      exact Safe.refl s
    · simp only [hd] at h
      cases hn : n.evalS s p src env with
      | none => simp [hn] at h
      | some k =>
        simp only [hn, Option.bind_some] at h
        exact onSelected_safe (fun t id => dealObj_safe _ t id (some (env.effectController.getD p))) h
  | exchangeDamage a b =>
    simp only [applyPrim] at h
    split at h
    · rename_i x xs y ys _ _
      cases h
      exact exchangeDamage_safe s x y
    · cases h
      exact Safe.refl s
  | setBaseMight sel n =>
    simp only [applyPrim] at h
    cases hn : n.evalS s p src env with
    | none => simp [hn] at h
    | some k => exact onSelected_safe (setBaseMight_safe k) (by simpa [hn] using h)
  | heal sel n =>
    simp only [applyPrim] at h
    cases hn : n.evalS s p src env with
    | none => simp [hn] at h
    | some k =>
      simp only [hn, Option.bind_some] at h
      exact onSelected_safe (healOne_safe k) h
  | kill sel =>
    simp only [applyPrim] at h
    cases hs : onSelected s p src env sel (killOrSaveInGroup s) with
    | none => simp [hs] at h
    | some r0 =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      have h0 := onSelected_safe (killOrSaveInGroup_safe s) hs
      rw [← h]
      exact h0
  | ready sel => exact onSelected_safe readyEffect_safe h
  | exhaust sel => exact onSelected_safe (setExhausted_safe true) h
  | banish sel => exact onSelected_safe (banishObj_safe p) h
  | returnToHand sel => exact onSelected_safe (replaceChosenHarm_safe env (sendObj_safe .hand)) h
  | create name n place ready => exact applyCreate_safe h
  | playUnitTokenAt name dest =>
    cases h
    exact playUnitTokenAt_safe s p name dest
  | attach gears to => exact applyAttach_safe h
  | copyAttachedFrom model => exact onSelected_safe (copyAttachedUnit_safe src) h
  | attachPaying gears to less => exact applyAttachPaying_safe h
  | move sel dest =>
    cases dest with
    | base =>
      simp only [applyPrim] at h
      obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.mp h
      show Safe s r0.1
      exact onSelected_safe (moveByEffect_safe _ none) hr0
    | at_ t =>
      simp only [applyPrim] at h
      cases hd : t.eval s p src env with
      | none => simp [hd] at h
      | some l =>
        cases l with
        | nil => simp [hd] at h
        | cons d _ =>
          simp only [hd] at h
          split at h
          · obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.mp h
            show Safe s r0.1
            exact onSelected_safe (moveByEffect_safe _ _) hr0
          · simp at h
  | stun sel => exact onSelected_safe (replaceChosenHarm_safe env stunObj_safe) h
  | detach sel => exact onSelected_safe detachObj_safe h
  | double sel => exact onSelected_safe doubleObj_safe h
  | grantActivation sel grant => exact onSelected_safe (grantActivationObj_safe grant) h
  | topdeck sel => exact onSelected_safe (sendObj_safe .mainDeck) h
  | buff sel => exact onSelected_safe buffObj_safe h
  | empower sel => exact onSelected_safe (empowerObj_safe p) h
  | disempower sel => exact onSelected_safe disempowerObj_safe h
  | gainXP ps n =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h]
        exact gainXPAll_safe k l s
  | spendXP ps n =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h]
        exact spendXPAll_safe k l s
  | recycle sel =>
    simp only [applyPrim] at h
    cases hs : sel.eval s p src env with
    | none => simp [hs] at h
    | some ids =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact applyEach_safe (fun t u => recycleOne_safe t u) _ _
  | reveal sel =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | revealNow sel =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | revealTop n =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | revealTopNow n =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | spendBuff sel => exact onSelected_safe unbuffObj_safe h
  | play sel => exact onSelected_safe (playFree_safe p) h
  | banishReplay sel keep => exact onSelected_safe (fun t id => banishReplay_safe p t id keep) h
  | playPaying sel => exact onSelected_safe (playPaying_safe p) h
  | playTo sel bfs =>
    simp only [applyPrim] at h
    cases hb : bfs.eval s p src env with
    | none => simp [hb] at h
    | some l =>
      cases l with
      | nil => simp [hb] at h
      | cons b _ =>
        simp only [hb] at h
        exact onSelected_safe (playToOrBase_safe p b) h
  | playReduced sel less dest =>
    simp only [applyPrim] at h
    cases hk : less.evalS s p src env with
    | none => simp [hk] at h
    | some k =>
      simp only [hk, Option.bind_some] at h
      cases dest with
      | none => exact onSelected_safe (playReducedOne_safe p k none) h
      | some bfs =>
        cases hb : bfs.eval s p src env with
        | none => simp [hb] at h
        | some l =>
          cases l with
          | nil => simp [hb] at h
          | cons b _ =>
            simp only [hb] at h
            exact onSelected_safe (playReducedOne_safe p k (some b)) h
  | giveKeywords to from_ =>
    simp only [applyPrim] at h
    cases hf : from_.eval s p src env with
    | none => simp [hf] at h
    | some l =>
      cases l with
      | nil => simp [hf] at h
      | cons f _ =>
        simp only [hf, Option.bind_some] at h
        exact onSelected_safe (addTempKws_safe _ _) h
  | castPicked sel less idx =>
    simp only [applyPrim] at h
    cases hk : less.evalS s p src env with
    | none => simp [hk] at h
    | some k =>
      simp only [hk, Option.bind_some] at h
      exact onSelected_safe (castPickedOne_safe p k idx) h
  | bin sel =>
    simp only [applyPrim, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    have hs : Safe s r.1 := onSelected_safe (sendObj_safe .trash) hr
    exact hs
  | discardCard sel => exact onSelected_safe discardObj_safe h
  | counter sel => exact onSelected_safe counterObj_safe h
  | counterToHand sel => exact onSelected_safe counterObjHand_safe h
  | hideAt sel bfs =>
    simp only [applyPrim] at h
    cases hb : bfs.eval s p src env with
    | none => simp [hb] at h
    | some l =>
      cases l with
      | nil => simp [hb] at h
      | cons b _ =>
        simp only [hb] at h
        exact onSelected_safe (hideObj_safe b) h
  | recycleTop ps =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact recycleTopAll_safe l s
  | swapTop ps =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact swapTopAll_safe l s
  | becomeCopy sel from_ =>
    simp only [applyPrim] at h
    cases hf : from_.eval s p src env with
    | none => simp [hf] at h
    | some l =>
      cases l with
      | nil => simp [hf] at h
      | cons c _ =>
        simp only [hf] at h
        exact onSelected_safe (becomeCopyOf_safe c) h
  | createAtPrev name n ready =>
    simp only [applyPrim] at h
    exact applyCreateAtPrev_safe h
  | cloneToken sel => exact onSelected_safe cloneTok_safe h
  | banishWith sel => exact onSelected_safe (banishMarked_safe p src) h
  | gainTag sel name => exact onSelected_safe (gainTagObj_safe name) h
  | replaceBattlefield sel name =>
    simp only [applyPrim] at h
    cases ht : s.tokenCard name with
    | none => simp [ht] at h
    | some c =>
      simp only [ht, Option.bind_some] at h
      exact onSelected_safe (replaceBf_safe c p) h
  | restoreBattlefield sel => exact onSelected_safe restoreBf_safe h
  | moveAll side place fs dest mark =>
    simp only [applyPrim, applyMoveAll] at h
    split at h
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact applyEach_safe (fun t id => sendMarked_safe p src mark _ t id) _ _
    · simp at h
  | addBattlefield name =>
    simp only [applyPrim] at h
    cases ht : s.tokenCard name with
    | none => simp [ht] at h
    | some c =>
      simp only [ht, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact addBattlefieldTok_safe c p s
  | takeControl sel => exact onSelected_safe (setController_safe p) h
  | playBanishedWith =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact applyEach_safe (fun t u => playFree_safe p t u) _ _
  | returnControl sel => exact onSelected_safe giveBack_safe h
  | takeControlUntilLeaves sel => exact onSelected_safe (takeUntil_safe p _) h
  | «recall» sel ex => exact onSelected_safe (recallFx_safe ex) h
  | win ps =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact gainPointsAll_safe _ l s
  | score ps n =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h]
        exact gainPointsAll_safe k _ s
  | channel ps n extra =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        cases hx : extra.evalS s p src env with
        | none => simp [hl, hn, hx] at h
        | some x =>
          simp only [hl, hn, hx, Option.bind_some, Option.map_some, Option.some.injEq] at h
          rw [← h]
          exact channelAll_safe k x l s
  | playFirst fs =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact playFirstOf_safe fs p src env s
  | extraTurn ps =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
        fun _ hown => hown.congr rfl rfl, rfl⟩
  | lookTop n =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | choose sel =>
    simp only [applyPrim] at h
    cases hs : sel.eval s p src env with
    | none => simp [hs] at h
    | some ids =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact Safe.refl s
  | returnChampion =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact returnChampion_safe p s
  | swapPlaces a b =>
    simp only [applyPrim] at h
    cases ha : a.eval s p src env with
    | none => simp [ha] at h
    | some la =>
      cases lb : b.eval s p src env with
      | none => simp [ha, lb] at h
      | some lb' =>
        cases la with
        | nil => simp [ha, lb] at h
        | cons x _ =>
          cases lb' with
          | nil => simp [ha, lb] at h
          | cons y _ =>
            simp only [ha, lb, Option.some.injEq] at h
            rw [← h]
            exact swapPlaces_safe s x y _
  | activateConquer sel =>
    simp only [applyPrim] at h
    exact onSelected_safe (fun t id => Safe.refl t) h
  | markOn sel e =>
    simp only [applyPrim] at h
    exact onSelected_safe (fun t id => addTurnFxOn_safe t p id (e.forCopy env.abilityCopyStamp)) h
  | delayUntilDeath sel idx =>
    simp only [applyPrim, Option.bind_eq_some_iff] at h
    obtain ⟨card, -, h⟩ := h
    exact onSelected_safe (fun t id => addTurnFxOn_safe t p id (.triggerOnDeath src card idx)) h
  | turnEffect e =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact addTurnFx_safe s p e
  | addEnergy ps n only =>
    cases only with
    | some a => simp [applyPrim] at h
    | none =>
      simp only [applyPrim] at h
      cases hl : ps.resolve s p env with
      | none => simp [hl] at h
      | some l =>
        cases hn : n.evalS s p src env with
        | none => simp [hl, hn] at h
        | some k =>
          simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
          rw [← h]
          exact poolsMap_safe _ l s
  | addUnitEnergy ps n =>
    simp only [applyPrim, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨l, -, k, -, rfl⟩ := h
    exact poolsMap_safe _ l s
  | addPower ps n d only =>
    cases d with
    | none =>
      cases only with
      | some a => simp [applyPrim] at h
      | none =>
        simp only [applyPrim] at h
        cases hl : ps.resolve s p env with
        | none => simp [hl] at h
        | some l =>
          cases hn : n.evalS s p src env with
          | none => simp [hl, hn] at h
          | some k =>
            simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
            rw [← h]
            exact poolsAddAny_safe _ l s
    | some dom =>
      cases only with
      | some a => simp [applyPrim] at h
      | none =>
        simp only [applyPrim] at h
        cases hl : ps.resolve s p env with
        | none => simp [hl] at h
        | some l =>
          cases hn : n.evalS s p src env with
          | none => simp [hl, hn] at h
          | some k =>
            simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
            rw [← h]
            exact poolsMap_safe _ l s
  | pay c =>
    simp only [applyPrim] at h
    cases hp : payByRunes s p src c with
    | none => simp only [hp, Option.some.injEq] at h; subst h; exact Safe.refl s
    | some x =>
      simp only [hp, Option.some.injEq] at h
      subst h
      exact payByRunes_safe hp
  | _ => simp [applyPrim] at h

/-- When a lasting effect ends, if the model has a way to end it. -/
def Duration.endPoint? : Duration → Option EndPoint
  | .thisTurn => some .turn
  | .thisCombat => some .combat
  | .permanent => some .never
  | _ => none

/-- The Might an object has for the choice of "to a minimum": the Might the rules read now, with
the lasting changes, the buff, the Equipment and the passive abilities (CR 479.4). -/
def GameState.mightBase (s : GameState) (id : ObjId) : Int :=
  (s.mightNow id).getD 0

/-- Take `k` Might from an object for a while, but not below `floor`: the change is as much as
the Might has above the floor, at most `k` (CR 475). -/
def addMightFloor (k floor : Nat) (ends : EndPoint) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  addMightMod ⟨-((Nat.min k (s.mightBase id - floor).toNat : Nat) : Int), ends⟩ s id

/-- Taking Might to a minimum is a safe change. -/
theorem addMightFloor_safe (k floor : Nat) (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (addMightFloor k floor ends s id).1 :=
  addMightMod_safe _ s id

/-- Give negative Might, applying replacements from the chosen Unit and the effect's controller
while keeping any minimum on the reduction (CR 370). -/
def reduceMight (p : PlayerId) (env : Env) (n : Nat) (floor : Option Nat) (ends : EndPoint)
    (s : GameState) (id : ObjId) : GameState × List Event :=
  if n == 0 then (s, [])
  else replaceChosenHarm env (fun t target =>
    let extra := if env.targetObjs.contains target && (t.cardDef? target).any (·.hasType .unit) then
      ((t.controlledMods (env.effectController.getD p)).filterMap (fun
        | .targetMightPenalty k => some k
        | _ => none)).sum
      else 0
    match floor with
    | some fl => addMightFloor (n + extra) fl ends t target
    | none => addMightMod ⟨-((n + extra : Nat) : Int), ends⟩ t target) s id

/-- Giving negative Might, including replacement effects, preserves safety. -/
theorem reduceMight_safe (p : PlayerId) (env : Env) (n : Nat) (floor : Option Nat)
    (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (reduceMight p env n floor ends s id).1 := by
  unfold reduceMight
  split
  · exact Safe.refl s
  · apply replaceChosenHarm_safe
    intro t target
    cases floor
    · exact addMightMod_safe _ t target
    · exact addMightFloor_safe _ _ _ t target

/-- Grant Flow for a Spell's base cost before any play-time adjustments (CR 356.1, 829). -/
def addFlowAtBaseCost (ends : EndPoint) (s : GameState) (id : ObjId) : GameState × List Event :=
  match (s.cardDef? id).bind (fun d => if d.hasType .spell then d.cost else none) with
  | some cost => addTempKw ⟨.flow, .cost cost⟩ ends s id
  | none => (s, [])

/-- Granting Flow at the base cost preserves the structural and ownership invariants. -/
theorem addFlowAtBaseCost_safe (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (addFlowAtBaseCost ends s id).1 := by
  unfold addFlowAtBaseCost
  split
  · exact addTempKw_safe _ _ _ _
  · exact Safe.refl s

/-- Grant a temporary change to the selected objects. -/
def applyGrant (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (m : StaticMod) (d : Duration) : Option (GameState × List Event) :=
  let minus (a : Amount) (floor : Option Nat) : Option (GameState × List Event) :=
    d.endPoint?.bind (fun ends => (a.evalS s p src env).bind (fun k =>
      onSelected s p src env sel (reduceMight p env k floor ends)))
  match m with
  | .mightPlus .it a =>
    d.endPoint?.bind (fun ends => (a.evalS s p src env).bind (fun k =>
      onSelected s p src env sel (addMightMod ⟨(k : Int), ends⟩)))
  | .mightMinus .it a => minus a none
  | .mightMinusMin .it a fl => minus a (some fl)
  | .keyword .it k => d.endPoint?.bind (fun ends => onSelected s p src env sel (addTempKw k ends))
  | .flowAtBaseCost => d.endPoint?.bind (fun ends => onSelected s p src env sel (addFlowAtBaseCost ends))
  | _ => none

/-- A lasting change that is made is a safe change. -/
theorem applyGrant_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {sel : Selector}
    {m : StaticMod} {d : Duration} {r : GameState × List Event}
    (h : applyGrant s p src env sel m d = some r) : Safe s r.1 := by
  unfold applyGrant at h
  split at h
  · simp only at h
    cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      cases hk : (‹Amount›).evalS s p src env with
      | none => simp [hd, hk] at h
      | some k =>
        simp only [hd, hk, Option.bind_some] at h
        exact onSelected_safe (addMightMod_safe _) h
  · simp only at h
    cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      cases hk : (‹Amount›).evalS s p src env with
      | none => simp [hd, hk] at h
      | some k =>
        simp only [hd, hk, Option.bind_some] at h
        exact onSelected_safe (reduceMight_safe p env k none ends) h
  · simp only at h
    cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      cases hk : (‹Amount›).evalS s p src env with
      | none => simp [hd, hk] at h
      | some k =>
        simp only [hd, hk, Option.bind_some] at h
        exact onSelected_safe (reduceMight_safe p env k (some _) ends) h
  · cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      simp only [hd, Option.bind_some] at h
      exact onSelected_safe (addTempKw_safe _ _) h
  · cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      simp only [hd, Option.bind_some] at h
      exact onSelected_safe (addFlowAtBaseCost_safe _) h
  · simp at h

/-- The selector of a primitive that is chosen while the effect resolves, if it has one. -/
def Prim.pickSel? : Prim → Option Selector
  | .detach s => some s
  | .copyAttachedFrom s => some s
  | .double s => some s
  | .topdeck s => some s
  | .deal s _ => some s
  | .setBaseMight s _ => some s
  | .heal s _ => some s
  | .kill s => some s
  | .ready s => some s
  | .exhaust s => some s
  | .banish s => some s
  | .returnToHand s => some s
  | .stun s => some s
  | .buff s => some s
  | .empower s => some s
  | .disempower s => some s
  | .recycle s => some s
  | .spendBuff s => some s
  | .bin s => some s
  | .discardCard s => some s
  | .play s => some s
  | .banishReplay s _ => some s
  | .playPaying s => some s
  | .playReduced s _ _ => some s
  | .castPicked s _ _ => some s
  | .castInline s => some s
  | .markOn s _ => some s
  | .delayUntilDeath s _ => some s
  | .playTo s _ => some s
  | .banishWith s => some s
  | .counterToHand s => some s
  | .replaceBattlefield s _ => some s
  | .reveal s => some s
  | .revealNow s => some s
  | .move s d =>
    match s, d with
    | .pick .one _ _ _, _ => some s
    | _, .at_ (.pick .one side place fs) => some (.pick .one side place fs)
    | _, _ => none
  | _ => none

/-- The primitive with its selector replaced. -/
def Prim.withSel (p : Prim) (sel : Selector) : Prim :=
  match p with
  | .copyAttachedFrom _ => .copyAttachedFrom sel
  | .deal _ n => .deal sel n
  | .setBaseMight _ n => .setBaseMight sel n
  | .heal _ n => .heal sel n
  | .detach _ => .detach sel
  | .double _ => .double sel
  | .topdeck _ => .topdeck sel
  | .kill _ => .kill sel
  | .ready _ => .ready sel
  | .exhaust _ => .exhaust sel
  | .banish _ => .banish sel
  | .returnToHand _ => .returnToHand sel
  | .stun _ => .stun sel
  | .buff _ => .buff sel
  | .empower _ => .empower sel
  | .disempower _ => .disempower sel
  | .recycle _ => .recycle sel
  | .spendBuff _ => .spendBuff sel
  | .bin _ => .bin sel
  | .discardCard _ => .discardCard sel
  | .play _ => .play sel
  | .banishReplay _ keep => .banishReplay sel keep
  | .playPaying _ => .playPaying sel
  | .playReduced _ l d => .playReduced sel l d
  | .castPicked _ l i => .castPicked sel l i
  | .castInline _ => .castInline sel
  | .markOn _ e => .markOn sel e
  | .delayUntilDeath _ idx => .delayUntilDeath sel idx
  | .playTo _ bf => .playTo sel bf
  | .banishWith _ => .banishWith sel
  | .counterToHand _ => .counterToHand sel
  | .replaceBattlefield _ n => .replaceBattlefield sel n
  | .reveal _ => .reveal sel
  | .revealNow _ => .revealNow sel
  | .move s d =>
    match s, d with
    | .pick .one _ _ _, _ => .move sel d
    | _, .at_ (.pick .one _ _ _) => .move s (.at_ sel)
    | _, _ => .move s d
  | q => q

/-- The effect names one object to choose while it resolves ("kill a gear", "stun a unit"): the
selector that does it. -/
def Effect.pickSel? : Effect → Option Selector
  | .doThen (.prim (.banish (.pick .one side place fs))) _
  | .doThen (.prim (.disempower (.pick .one side place fs))) _ =>
    some (.pick .one side place fs)
  | .prim p =>
    match p.pickSel? with
    | some (.pick .one side place fs) => some (.pick .one side place fs)
    | _ => none
  | .grant (.pick .one side place fs) _ _ => some (.pick .one side place fs)
  | .fillSlot _ (.pick .one side place fs) => some (.pick .one side place fs)
  | .chooseObject side place fs _ => some (.pick .one side place fs)
  | _ => none

/-- The effect with the chosen object, named by `pickVar`, in place of the selector. -/
def Effect.withPick : Effect → Effect
  | .doThen (.prim a) b => .doThen (.prim (a.withSel (.var pickVar))) b
  | .prim p => .prim (p.withSel (.var pickVar))
  | .grant (.pick .one _ _ _) m d => .grant (.var pickVar) m d
  | .fillSlot i _ => .fillFromPick i
  | .chooseObject _ _ _ body => .seq (.cons body .nil)
  | e => e

/-- Whether the object is picked for the cost of a linked instruction (CR 355.10.c.1). -/
def Effect.isLinkedCost : Effect → Bool
  | .doThen (.prim (.banish _)) _ | .doThen (.prim (.disempower _)) _ => true
  | _ => false

/-- Picks for costs or by multiple players do not fire target effects (CR 355.10.c.1, 355.10.e).
Keeping original targets does not choose them again (CR 355.11.b). Movement destinations only
name the location (CR 355.18). -/
def Effect.pickTargets (e : Effect) : Bool :=
  match e with
  | .retainTargetSet _ | .collectOwnPicks .. | .doThen (.prim (.move ..)) _ => false
  | _ => !e.isLinkedCost

/-- A resolution pick in a private or secret zone is not a target (CR 355.10.a). -/
def Effect.pickIsTarget (e : Effect) (s : GameState) (id : ObjId) : Bool :=
  e.pickTargets && match s.locate id with
    | some (.player _ .hand) | some (.player _ .mainDeck) | some (.player _ .runeDeck) => false
    | _ => true

/-- Emit the choice event for a new target picked during resolution. -/
def Effect.pickEvents (e : Effect) (s : GameState) (p : PlayerId) (src id : ObjId) : List Event :=
  if e.pickIsTarget s id then chosenAt s p src id else []

/-- Cast the spell now, in place (Kai'Sa): its Power is paid, its effect is done, and the card is
recycled after; if the Power cannot be paid, the instruction is skipped. -/
def castInlineStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (es : EffectList) : GameState × List Frame × List Event :=
  let skip : GameState × List Frame × List Event := (s, [.run p src env es], [Event.skipped src])
  match sel.eval s p src env with
  | some (id :: _) =>
    match ((s.cardDef? id).filter (fun d => !s.blocksPlay p id d)).bind
        (fun d =>
          let branch := d.spellEffect.bind (·.forPick .plain)
          (branch.filter (·.playerTarget.isNone)).map (fun e => (d, e))) with
    | some (d, e) =>
      match (s.targetCostOptions p id [] ⟨0, s.adjustPower id ((d.cost.map (·.power)).getD [])⟩).findSome?
          (payByRunes s p id) with
      | some r =>
        (r.1, [.run p id {} (.cons e.body (.cons (.prim (.recycle .self)) .nil)),
          .run p src env es], r.2 ++ [Event.played p id])
      | none => skip
    | none => skip
  | _ => skip

/-- A Spell that a card plays for a reduced cost (Void Rush): the player chooses the pick of its
targets, as one of the ways to cast it. A card that is no Spell is played as a Unit or a Gear. -/
def castReducedStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (less : Amount) (dest : Option Selector) (es : EffectList) :
    Option (GameState × List Frame × List Event) :=
  match dest, sel.eval s p src env with
  | _, some (id :: _) =>
    match ((s.cardDef? id).filter (fun d => !s.blocksPlay p id d)).bind
        (fun d => d.spellEffect.map (fun e => (d, e))) with
    | some (d, e) =>
      let n := (reducedSpellChoices s p id d e ((less.evalS s p src env).getD 0)).length
      some (s, [.run p src env (.cons (.eitherOf (EffectList.ofList
        ((List.range n).map (fun i => Effect.prim (.castPicked sel less i))))) es)], [])
    | none => none
  | _, _ => none

/-- Choosing how to cast a Spell changes nothing of the state. -/
theorem castReducedStep_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {less : Amount} {dest : Option Selector} {es : EffectList}
    {r : GameState × List Frame × List Event}
    (h : castReducedStep s p src env sel less dest es = some r) : Safe s r.1 := by
  unfold castReducedStep at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact Safe.refl s
    · simp at h
  · simp at h

/-- The frames that choosing how to cast a Spell leaves are frames of the Spell. -/
theorem castReducedStep_frames {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {less : Amount} {dest : Option Selector} {es : EffectList}
    {r : GameState × List Frame × List Event}
    (h : castReducedStep s p src env sel less dest es = some r) {f : Frame} (hf : f ∈ r.2.1) :
    f.isPlay = true := by
  unfold castReducedStep at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      rw [← h] at hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl
      rfl
    · simp at h
  · simp at h

/-- Casting in place is a safe change of the state. -/
theorem castInlineStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (sel : Selector) (es : EffectList) : Safe s (castInlineStep s p src env sel es).1 := by
  unfold castInlineStep
  split
  · split
    · split
      · rename_i r hr
        exact payPlayOption_safe hr
      · exact Safe.refl s
    · exact Safe.refl s
  · exact Safe.refl s

/-- Play a Spell for free (CR 349): it goes on the Chain as a new object, played by `p`, and its
effect is done at once, as it would resolve; then it goes to its owner's Trash, and the Cleanup
follows. The Chain is not opened again, so an item that is being resolved is not resolved twice.
Only a Spell whose effect makes no choice is played this way; the Chain is not opened for answers
(design.md §7). `none` if it is not such a Spell. -/
def playSpellStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (es : EffectList) : Option (GameState × List Frame × List Event) :=
  match sel.eval s p src env with
  | some (id :: _) =>
    match (s.cardDef? id).bind (fun d => (d.spellEffect.bind (·.forPick .plain)).map (fun e => (d, e))) with
    | some (d, e) =>
      if d.hasType .spell && e.choices.isEmpty && e.playerTarget.isNone && !s.blocksPlay p id d then
        (moveObj s id .chain).map (fun r =>
          ((r.1.modObj r.2 (fun o =>
              { Object.withPlay [] (s.freeMark p id) o with controller := p })),
            [.run p r.2 {} (.cons e.body (.cons (.prim (.bin .self)) .nil)), .cleanup,
              .run p src env es],
            [Event.moved id r.2 .chain, Event.played p r.2]))
      else none
    | none => none
  | _ => none

/-- Playing a Spell for free is a safe change of the state. -/
theorem playSpellStep_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {es : EffectList} {r : GameState × List Frame × List Event}
    (h : playSpellStep s p src env sel es = some r) : Safe s r.1 := by
  unfold playSpellStep at h
  split at h
  · split at h
    · split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨s2, id'⟩, hm, rfl⟩ := h
        exact (Safe.moveObj hm).trans
          (Safe.modObj s2 id' (fun _ => rfl) (fun _ => rfl))
      · simp at h
    · simp at h
  · simp at h

/-- The frames that playing a Spell for free leaves are frames of the Spell or of the rest. -/
theorem playSpellStep_frames {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {es : EffectList} {r : GameState × List Frame × List Event}
    (h : playSpellStep s p src env sel es = some r) {f : Frame} (hf : f ∈ r.2.1) :
    f.isPlay = true := by
  unfold playSpellStep at h
  split at h
  · split at h
    · split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨s2, id'⟩, hm, rfl⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl <;> rfl
      · simp at h
    · simp at h
  · simp at h

/-- The player would reveal a card from a Main Deck and has a passive
ability that says to look at the top card first (Void Hatchling). -/
def GameState.lookFirst (s : GameState) (p : PlayerId) (env : Env) (sel : Selector) : Bool :=
  (match sel with
    | .var v =>
      match env.lookup v with
      | some (.obj o) =>
        (s.obj? o).any (fun x => (s.zone (.player x.owner .mainDeck)).contains o)
      | _ => false
    | _ => false) &&
    s.passiveSources.any (fun g => (s.obj? g).any (·.controller == p) &&
      (s.activeMods g).contains .lookBeforeReveal)

/-- The kinds of Power in the Pool that can pay each symbol, including flexible Power. -/
def resolutionPowerChoices (own : List Domain) : List PowerSym → List (List PowerSym)
  | [] => [[]]
  | symbol :: rest =>
    let domains := symbol.choices own
    let eligible := if domains.isEmpty then [] else (domains.map PowerSym.domain) ++ [.any]
    let tails := resolutionPowerChoices own rest
    eligible.flatMap (fun power => tails.map (power :: ·))

/-- Spend exactly the resources selected for an instruction (CR 445.1). -/
def spendResolutionPayment (s : GameState) (p : PlayerId) (src : ObjId) (cost : Cost) :
    Option RunePool := do
  let pool ← (s.poolOf p).spend ⟨cost.energy, []⟩
  let paid ← cost.power.foldlM (fun (balance : RunePool) symbol =>
    match symbol with
    | .domain d => if 0 < balance.get d then balance.takePower d else none
    | .any => if 0 < balance.any then some { balance with any := balance.any - 1 } else none
    | .own => none) pool
  if !(s.cardDef? src).any (·.hasType .gear) && paid.any < s.restrictedNow p then none
  else some { paid with spent := paid.spent + cost.power.length }

/-- Distinct ways of paying a resource instruction from the Pool (CR 445.1). -/
def resolutionPayments (s : GameState) (p : PlayerId) (src : ObjId) (cost : Cost) :
    List (Cost × RunePool) :=
  let own := ((s.cardDef? src).map (·.domains)).getD []
  let paid := (resolutionPowerChoices own cost.power).filterMap (fun power =>
    let resources : Cost := ⟨cost.energy, power⟩
    (spendResolutionPayment s p src resources).map (fun pool => (resources, pool)))
  paid.eraseDupsBy (fun a b => a.2 == b.2)

mutual

/-- Whether a branch of a choice can be chosen: a branch that is a condition and nothing else is
chosen only while the condition holds ("choose one that hasn't been chosen"). -/
def Effect.viable (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) : Effect → Bool
  | .ifThen c _ .nop => c.eval s p src env == some true
  | .eitherOf es => EffectList.anyViable s p src env es
  | .payThen cost _ => !(resolutionPayments s p src cost).isEmpty
  | _ => true

/-- Whether some branch of a choice can be chosen. -/
def EffectList.anyViable (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) :
    EffectList → Bool
  | .nil => false
  | .cons e rest => Effect.viable s p src env e || EffectList.anyViable s p src env rest

end

/-- The player may answer the choice between the effects `a` and `b` with `yes` (the first) or not
(the others): the branch must be one that can be chosen, unless none can. -/
def eitherOk (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (a b : Effect)
    (yes : Bool) : Bool :=
  let va := a.viable s p src env
  let vb := b.viable s p src env
  (if yes then va else vb) || (!va && !vb)

/-- Capture the Unit cards actually put in the Trash by a linked Burn instruction. -/
def linkedBurnEvents (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (idx : Nat)
    (moves : List Event) : List Event :=
  let sourceCard := env.sourceCard <|> (s.cardDef? src).map (·.id)
  match sourceCard with
  | none => []
  | some card => moves.filterMap (fun
    | .moved _ burned (.player _ .trash) => do
      let d ← s.cardDef? burned
      if d.hasType .unit then
        some (.burnedUnitFor p src card idx burned (d.might.getD 0).toNat)
      else none
    | _ => none)

/-- Move the available top cards to the Trash for a Burn instruction or cost (CR 441). -/
def burnTop (s : GameState) (p : PlayerId) (count : Nat) : GameState × List Event :=
  applyEach (sendObj .trash) s ((s.zone (.player p .mainDeck)).take count)

/-- Burn cards for the first player and schedule the others with the same count. An exhausted
deck is refilled through the ordinary Burn Out decisions before the remainder is burned
(CR 432.1.b, 441.4). -/
def burnEffect (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (who : PlayerSel)
    (n : Amount) (es : EffectList) (unitTrigger : Option Nat := none) :
    GameState × List Frame × List Event :=
  match who.resolve s p env, n.evalS s p src env with
  | some (q :: qs), some count =>
    let available := (s.zone (.player q .mainDeck)).length
    let r := burnTop s q count
    let burnFor (pl : PlayerId) (k : Nat) :=
      let burn := match unitTrigger with
        | some idx => Prim.burnWithUnitTrigger (.const k) idx
        | none => Prim.burn .you (.const k)
      Frame.run pl src env (.cons (.prim burn) .nil)
    let rest := qs.map (fun pl => burnFor pl count) ++ [.run p src env es]
    let next :=
      if available < count then
        .chanceBurnOut q :: burnFor q (count - available) :: rest
      else rest
    let triggers := unitTrigger.toList.flatMap (fun idx => linkedBurnEvents r.1 q src env idx r.2)
    (r.1, next, r.2 ++ triggers)
  | some [], some _ => (s, [.run p src env es], [])
  | _, _ => (s, [.run p src env es], [.skipped src])

/-- Burning cards and scheduling Burn Out preserves the structural invariants. -/
theorem burnEffect_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (who : PlayerSel) (n : Amount) (es : EffectList) (link : Option Nat) :
    Safe s (burnEffect s p src env who n es link).1 := by
  unfold burnEffect
  split
  · exact applyEach_safe (sendObj_safe .trash) _ _
  · exact Safe.refl s
  · exact Safe.refl s

/-- Execute an instruction whose follow-up requires that the first action happened
(CR 359.3.e.14.b). -/
def linkedAction (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (a : Prim) :
    GameState × Bool × List Event :=
  match applyPrim s p src env a with
  | none => (s, false, [])
  | some r =>
    let done := match a with
      | .banish _ => r.2.any (fun
        | .moved _ _ (.player _ .banishment) => true
        | _ => false)
      | .disempower sel => ((sel.eval s p src env).getD []).any (fun id =>
        ((r.1.obj? id).map (·.empowerCount)).getD 0 <
          ((s.obj? id).map (·.empowerCount)).getD 0)
      | .move .. => r.2.any (fun | .standardMoved _ _ => true | _ => false)
      | _ => false
    (r.1, done, r.2)

/-- A linked action preserves the structural invariants. -/
theorem linkedAction_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (a : Prim) :
    Safe s (linkedAction s p src env a).1 := by
  unfold linkedAction
  split
  · exact Safe.refl s
  · rename_i r h
    exact applyPrim_safe h

/-- Each answer keeps the remaining groups containing that unit. Only units that distinguish
groups are offered, so an answer always reduces the number of alternatives (CR 355.11.b). -/
def retainTargetSetFrame (p : PlayerId) (src : ObjId) (env : Env)
    (groups : List (List ObjId)) (es : EffectList) : Frame :=
  let remaining := match env.lookup pickVar with
    | some (.obj id) => groups.filter (·.contains id)
    | _ => groups
  let candidates := remaining.flatten.eraseDups.filter
    (fun id => remaining.any (fun group => !group.contains id))
  match candidates with
  | id :: more => .pickDo p src env id more (.retainTargetSet remaining) es
  | [] =>
    let retained := remaining.headD []
    .run p src { env with
      slots := retained.map Value.obj
      targetObjs := env.targetObjs.filter retained.contains } es

/-- Ask the next player with more than one candidate, or record their sole pick and move on.
The original effect resumes after every player has picked (CR 355.10.e). -/
def collectOwnPicksFrame (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (remaining : List PlayerId) (place : Place) (fs : FilterList) (body : Effect)
    (capture : Bool) (es : EffectList) : Frame :=
  let env := if capture then
    { env with slots := env.slots ++ (env.lookup pickVar).toList }
    else env
  match remaining with
  | [] => .run p src env (.cons body es)
  | q :: qs =>
    let candidates := (s.pickCandidates q src env .friendly place fs false).getD []
    let next := .cons (.collectOwnPicks p qs place fs body false) es
    match candidates with
    | [] => .run p src env next
    | [id] => .run p src { env with slots := env.slots ++ [.obj id] } next
    | id :: other :: more =>
      .pickDo q src env id (other :: more) (.collectOwnPicks p qs place fs body true) es

/-- Use the destination chosen when the Spell was finalized (CR 355.4, 359.3.e).
A destination forbidden by the global movement rules requires a Recall (CR 449.2.c). -/
def chosenMove (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (slot : Nat) (allowBase : Bool) (fs : FilterList) (afterMove : Effect) : Env × Effect :=
  let unit := Selector.slot slot
  let resume := (env, Effect.nop)
  match (s.obj? src).map (fun (o : Object) => SpellPick.effectChoice o.spellPick), env.slots[slot]? with
  | some (.destination dest), some (.obj id) =>
    if s.blocksEnemyMove (env.effectController.getD p) id then resume
    else match s.obj? id, dest with
      | some o, none =>
        if allowBase && o.loc.isSome then (env, .doThen (.prim (.move unit .base)) afterMove)
        else resume
      | some o, some bf =>
        if o.loc == some bf || !(s.cardDef? bf).any (·.hasType .battlefield) ||
            !(FilterList.holds s src env bf fs).getD false then resume
        else if !s.effectMoveBattlefieldOk o bf then (env, .prim (.recall unit false))
        else (env.bind pickVar (.obj bf), .doThen (.prim (.move unit (.at_ (.var pickVar)))) afterMove)
      | none, _ => resume
  | _, _ => resume

/-- Recycle the remaining looked-at cards. Put a random ordering decision before the rest
when at least two cards are Recycled together (CR 417.5). -/
def recycleLookedStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (es : EffectList) : GameState × List Frame × List Event :=
  let deck := s.zone (.player p .mainDeck)
  let remaining := deck.filter env.lookedCards.contains
  if 2 ≤ remaining.length then
    let keep := deck.filter (fun id => !env.lookedCards.contains id)
    (s, [.chancePredict p deck.length keep remaining, .run p src env es], [])
  else
    let r := recycleList remaining s
    (r.1, [.run p src env es], r.2 ++ (if remaining.isEmpty then [] else [.recycled p]))

/-- Recycling or asking for an order preserves the structural invariants. -/
theorem recycleLookedStep_safe (s : GameState) (p : PlayerId) (src : ObjId)
    (env : Env) (es : EffectList) : Safe s (recycleLookedStep s p src env es).1 := by
  unfold recycleLookedStep
  dsimp only
  split
  · exact Safe.refl s
  · exact recycleList_safe _ _

/-- A Recycle ordering decision and its continuation are both play frames. -/
theorem recycleLookedStep_mem {s : GameState} {p : PlayerId} {src : ObjId}
    {env : Env} {es : EffectList} {f : Frame} (h : f ∈ (recycleLookedStep s p src env es).2.1) :
    f.isPlay = true := by
  unfold recycleLookedStep at h
  dsimp only at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  · simp only [List.mem_singleton] at h
    subst f
    rfl

/-- Mandatory locations imposed by resolving a Hidden spell or the play effect of a Unit
that was played from hiding (CR 811.1.d.5). -/
def Env.hiddenPlayRequirements (env : Env) : List (List (Option ObjId)) :=
  env.hiddenPlayLocation.toList.map (fun b => [some b])

/-- Build an effect play's requirements from its own location instruction and the Hidden effect. -/
def Env.permanentPlayTerms (env : Env) (price : EffectPlayPrice) (places : Option (List ObjId)) :
    EffectPlayTerms :=
  { price, requirements := env.hiddenPlayRequirements ++ places.toList.map (·.map some) }

/-- When an effect offers to play a card to a required location, its resolution picks must have a
legal finalization (CR 355.16, 355.17). -/
def requiredPlayCandidates (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (e : Effect) : Option (List ObjId) :=
  match e with
  | .prim (.playReduced sel less (some dest)) => do
    let some amount := less.evalS s p src env | return []
    let candidates := match sel with
      | .pick .one side place fs => s.pickCandidates p src env side place fs false
      | _ => sel.eval s p src env
    let terms := env.permanentPlayTerms (.reduceEnergy amount)
      (some ((dest.eval s p src env).getD []))
    return (candidates.getD []).filter (fun card => !(permanentPlayPlans s p card terms).isEmpty)
  | _ => none

/-- Use the shared finalization choices when a Unit can elect a fee or an effect specifies a
set of mandatory locations. For other plays the existing immediate instructions apply. -/
def permanentPlayEffects (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (pr : Prim) : Option (Env × EffectList) :=
  let needsChoices (id : ObjId) := (s.cardDef? id).any (fun d =>
    d.hasType .unit && (env.hiddenPlayLocation.isSome ||
      !(s.battlefieldFeeChoices p id d).isEmpty))
  let schedule (ids : List ObjId) (price : EffectPlayPrice)
      (places : Option (List ObjId)) (mandatory : Bool := false) :=
    if mandatory || ids.any needsChoices then
      let terms := env.permanentPlayTerms price places
      some (env, EffectList.ofList (ids.map (fun card => .planPermanentPlay card terms)))
    else none
  let locations (sel : Selector) := (sel.eval s p src env).getD []
  match pr with
  | .play sel => schedule (locations sel) .ignoreBase none
  | .playPaying sel => schedule (locations sel) .ignoreEnergy none
  | .playTo sel dest => schedule (locations sel) .ignoreBase (some (locations dest))
  | .playReduced sel less dest => do
    let amount ← less.evalS s p src env
    schedule (locations sel) (.reduceEnergy amount) (dest.map locations) dest.isSome
  | .playBanishedWith =>
    let ids := (s.zone (.player p .banishment)).filter (fun id =>
      (s.obj? id).any (·.banishedWith == some src) && (s.cardDef? id).any (·.hasType .unit))
    schedule ids .ignoreBase none
  | .playFirst fs => do
    let deck := s.zone (.player p .mainDeck)
    let card ← deck.find? (fun id => fs.holds s src env id == some true)
    let (ctx, play) ← schedule [card] .ignoreBase none
    let previous := deck.takeWhile (· != card)
    some ({ ctx with slots := previous.map Value.obj },
      play.append (.cons (.prim (.recycle (.slotsFrom 0))) .nil))
  | _ => none

/-- After Banish, the owner chooses how to play the new object. The rest of the effect belongs to
its original controller (CR 355.17, 428). -/
def replayFrames (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (id : ObjId)
    (sameLocation : Bool) (events : List Event) (es : EffectList) : List Frame :=
  match s.obj? id, banishedPlayId events with
  | some original, some card =>
    let previous := if sameLocation then [[original.loc]] else []
    let hidden := if original.owner == p then env.hiddenPlayRequirements else []
    let terms : EffectPlayTerms := { price := .ignoreBase, requirements := previous ++ hidden }
    [.run original.owner src env (.cons (.planPermanentPlay card terms) .nil), .run p src env es]
  | _, _ => [.run p src env es]

/-- The continuation of replay contains only frames of play. -/
theorem replayFrames_mem {s : GameState} {p : PlayerId} {src id : ObjId} {env : Env}
    {sameLocation : Bool} {events : List Event} {es : EffectList} {f : Frame}
    (h : f ∈ replayFrames s p src env id sameLocation events es) : f.isPlay = true := by
  unfold replayFrames at h
  split at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  · rcases h with rfl | rfl <;> rfl
  · subst f
    rfl

/-- "As this is attached" instructions run after the attachment event has been observed
(CR 370.1.b.1, 725.1). Each receives the newly equipped Unit in slot 0. -/
def attachmentReplacementFrames (s : GameState) (events : List Event) : List Frame :=
  events.flatMap (fun
    | .attached gear unit =>
      match s.obj? gear, s.cardDef? gear with
      | some o, some d =>
        let env : Env := { slots := [.obj unit] }
        let effects := d.fullAbilities.filterMap (fun
          | .replacement .attach cond body =>
            if cond.eval s o.controller gear env == some true then some body.body else none
          | _ => none)
        effects.map (fun body => .run o.controller gear env (.cons body .nil))
      | _, _ => []
    | _ => [])

/-- An attachment replacement only adds effect-resolution work. -/
theorem attachmentReplacementFrames_play {s : GameState} {events : List Event} {f : Frame}
    (h : f ∈ attachmentReplacementFrames s events) : f.isPlay = true := by
  obtain ⟨ev, _, h⟩ := List.mem_flatMap.mp h
  cases ev <;> simp only [List.not_mem_nil] at h
  split at h
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
    rfl
  · contradiction

/-- Offer complete new finalization choices, or let the Spell keep the original ones. -/
def remakeSpellChoicesFrame (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (spell : Selector) (es : EffectList) : Frame :=
  let options := ((spell.eval s p src env).getD []).flatMap (fun id =>
    ((s.cardDef? id).filter (·.hasType .spell)).toList.flatMap (fun d =>
      d.spellEffect.toList.flatMap (fun effect =>
        (spellChoices s p id d effect).filterMap (fun (pick, targets) =>
          if pick == .plain && effect.choices.isEmpty then none
          else some (.setSpellChoices id pick targets)))))
  if options.isEmpty then .run p src env es
  else .mayDo p src env (.eitherOf (EffectList.ofList options)) es

/-- Execute one effect and prepare the frames that continue it. -/
def runEffect1 (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : GameState × List Frame × List Event :=
  let skip : GameState × List Frame × List Event := (s, [.run p src env es], [Event.skipped src])
  let linked (a : Prim) (body : Effect) :=
    let r := linkedAction s p src env a
    (r.1, [.run p src env (if r.2.1 then .cons body es else es)], r.2.2)
  match e with
  | .nop => (s, [.run p src env es], [])
  | .seq l => (s, [.run p src env (l.append es)], [])
  | .bind v a e' =>
    match a.evalS s p src env with
    | some k => (s, [.run p src (env.bind v (.int k)) (.cons e' .nil), .run p src env es], [])
    | none => skip
  | .ifThen c t e' =>
    match c.eval s p src (env.withMight s.mightTable) with
    | some b => (s, [.run p src env (.cons (if b then t else e') es)], [])
    | none => skip
  | .fillFromPick i =>
    -- the object that was chosen becomes slot `i`
    match env.lookup pickVar with
    | some v => (s, [.run p src { env with slots := env.slots.set i v } es], [])
    | none => skip
  | .preventNext sel amount .thisTurn =>
    match amount.evalS s p src env with
    | some (k + 1) =>
      (s, [.run p src env (.cons (.prim (.markOn sel (.preventDamage (k + 1)))) es)], [])
    | _ => (s, [.run p src env es], [])
  | .retainTargetSet groups => (s, [retainTargetSetFrame p src env groups es], [])
  | .remakeSpellChoices spell =>
    (s, [remakeSpellChoicesFrame s p src env spell es], [])
  | .setSpellChoices spell pick targets =>
    let updated := s.modObj spell fun o =>
      let newPick := match o.spellPick.optionalCosts with
        | some (printed, repeats) => .withCosts pick printed repeats
        | none => pick
      { o with targets, spellPick := newPick, targetPlayer := pick.playerTarget }
    (updated, [.run p src env es], targets.map (Event.chosenBySpell p))
  | .moveChoosing unit home fs afterMove =>
    let chosen := chosenMove s p src env unit home fs afterMove
    (s, [.run p src chosen.1 (.cons chosen.2 es)], [])
  | .pickOwn place fs body =>
    (s, [.run p src env (.cons (.collectOwnPicks p s.pickOrder place fs body false) es)], [])
  | .collectOwnPicks controller players place fs body capture =>
    (s, [collectOwnPicksFrame s controller src env players place fs body capture es], [])
  | .forEach sel body =>
    match sel.eval s p src env with
    | some ids =>
      (s, ids.map (fun id => Frame.run p src { env with it := some id } (.cons body .nil)) ++
        [.run p src env es], [])
    | none => skip
  | .repeatN n e' =>
    match n.evalS s p src env with
    | some k => (s, [.run p src env ((EffectList.replicate k e').append es)], [])
    | none => skip
  | .eachPlayer who body =>
    match (match who with
      | .controllerOf i =>
        -- the controller of the object chosen at the slot
        match env.slots[i]? with
        | some (.obj o) => (s.obj? o).map (fun (x : Object) => [x.controller])
        | _ => none
      | _ => who.resolve s p env : Option (List PlayerId)) with
    | some ps =>
      let playerEnv := { env with effectController := env.effectController <|> some p }
      (s, ps.map (fun q => Frame.run q src playerEnv (.cons body .nil)) ++ [.run p src env es], [])
    | none => skip
  | .revealHand who body =>
    match who.resolve s p env with
    | some ps =>
      let hands := ps.map (fun q => (q, s.zone (.player q .hand)))
      let known := { env with revealedCards := hands.flatMap Prod.snd ++ env.revealedCards }
      (s, [.run p src known (.cons body .nil), .run p src env es],
        hands.map (fun (q, cards) => .handRevealed q cards))
    | none => skip
  | .nameCard kind =>
    match s.nameableCards kind with
    | first :: more => (s, [.nameCard p src env first more es], [])
    | [] => skip
  | .rememberNamedCard card =>
    (s.modObj src (fun o => { o with namedCard := some card }), [.run p src env es],
      [.namedCard p src card])
  | .lookAtTop n body =>
    let cards := (s.zone (.player p .mainDeck)).take n
    (s, [.run p src { env with lookedCards := cards } (.cons body .nil), .run p src env es],
      cards.map (.lookedAt p))
  | .banishAndPlayLooked less fs =>
    match lookedPlayCandidates s p src env less fs with
    | first :: more => (s, [.mayDo p src env (.chooseLookedToPlay less first more) es], [])
    | [] => (s, [.run p src env es], [])
  | .chooseLookedToPlay less first more =>
    (s, [.pickDo p src env first more (.banishLookedForPlay less) es], [])
  | .banishLookedForPlay less =>
    match env.lookup pickVar with
    | some (.obj id) =>
      if env.lookedCards.contains id && (s.zone (.player p .mainDeck)).contains id then
        let r := banishObj p s id
        let options := (banishedPlayId r.2).toList.flatMap (fun card =>
          (reducedPermanentPlays r.1 p card less).map (.finishReducedPermanent card { price := .reduceEnergy less }))
        (r.1, [.run p src env (.cons (.eitherOf (EffectList.ofList options)) es)], r.2)
      else skip
    | _ => skip
  | .planPermanentPlay card terms =>
    match permanentPlayPlans s p card terms with
    | [] => skip
    | plans =>
      let options := plans.map (.finishReducedPermanent card terms)
      let decline := if plans.all (fun plan => !plan.battlefieldFees.isEmpty) then [.nop] else []
      (s, [.run p src env (.cons (.eitherOf (EffectList.ofList (options ++ decline))) es)], [])
  | .banishForReplay id sameLocation =>
    let banished := banishObj p s id
    (banished.1, replayFrames s p src env id sameLocation banished.2 es, banished.2)
  | .finishReducedPermanent card terms plan =>
    if (permanentPlayPlans s p card terms).contains plan then
      match applyReducedPermanent s p card plan with
      | some (t, entered, events) =>
        (t, [.run p src (env.bind pickVar (.obj entered)) es], events)
      | none => skip
    else skip
  | .recycleLooked => recycleLookedStep s p src env es
  | .may e' =>
    if (requiredPlayCandidates s p src env e').any List.isEmpty then skip
    else (s, [.mayDo p src env e' es], [])
  | .doThen (.prim (.banish sel)) body => linked (.banish sel) body
  | .doThen (.prim (.disempower sel)) body => linked (.disempower sel) body
  | .doThen (.prim (.move sel dest)) body => linked (.move sel dest) body
  | .prim (.playUnitToken name) =>
    match s.tokenCard name with
    | some c =>
      let options := (s.unitTokenDestinations p c).map (fun dest => Effect.prim (.playUnitTokenAt name dest))
      (s, [.run p src env (.cons (.eitherOf (EffectList.ofList options)) es)], [])
    | none => skip
  | .payThen cost body =>
    match resolutionPayments s p src cost with
    | [] => skip
    | [(_, pool)] => (s.setPoolFor p src pool, [.run p src env (.cons body es)], [])
    | first :: second :: more =>
      let choices := (first :: second :: more).map (fun plan => Effect.paySelected plan.1 body)
      (s, [.run p src env (.cons (.eitherOf (EffectList.ofList choices)) es)], [])
  | .paySelected cost body =>
    match spendResolutionPayment s p src cost with
    | none => skip
    | some pool => (s.setPoolFor p src pool, [.run p src env (.cons body es)], [])
  | .eitherOf .nil => skip
  | .eitherOf (.cons a rest) =>
    -- the player chooses between the first effect ("yes") and the others ("no"), and so on
    match rest with
    | .nil => (s, [.run p src env (.cons a es)], [])
    | .cons b .nil => (s, [.eitherDo p src env a b es], [])
    | r => (s, [.eitherDo p src env a (.eitherOf r) es], [])
  | .prim (.burn who n) => burnEffect s p src env who n es
  | .prim (.burnWithUnitTrigger n idx) => burnEffect s p src env .you n es (some idx)
  | .prim (.predict n) =>
    match n.evalS s p src env with
    | some count =>
      match (s.zone (.player p .mainDeck)).take count with
      | [] => (s, [.run p src env es], [])
      | c :: cs =>
        (s, [.predict p count c cs [] [], .run p src env es], (c :: cs).map (Event.lookedAt p))
    | none => skip
  | .prim (.draw sel n) =>
    match sel.resolve s p env, n.evalS s p src env with
    | some ps, some k => (s, ps.map (fun q => Frame.draw q k) ++ [.run p src env es], [])
    | _, _ => skip
  | .prim (.reveal sel) =>
    -- the player looks at the top card first, and may recycle it, and then the cards are revealed
    if s.lookFirst p env sel then
      (s, [.run p src env (.cons (.prim (.lookTop 1)) (.cons (.may (.prim (.recycleTop .you)))
        (.cons (.prim (.revealNow sel)) es)))], [])
    else
      match applyPrim s p src env (.reveal sel) with
      | some r => (r.1, [.run p src env es], r.2)
      | none => skip
  | .prim (.revealTop n) =>
    -- the player looks at the top card first, and may recycle it, and then the cards are revealed
    if s.passiveSources.any (fun g => (s.obj? g).any (·.controller == p) &&
        (s.activeMods g).contains .lookBeforeReveal) then
      (s, [.run p src env (.cons (.prim (.lookTop 1)) (.cons (.may (.prim (.recycleTop .you)))
        (.cons (.prim (.revealTopNow n)) es)))], [])
    else
      match applyPrim s p src env (.revealTop n) with
      | some r => (r.1, [.run p src env es], r.2)
      | none => skip
  | .prim (.castInline sel) => castInlineStep s p src env sel es
  | .prim (.banishReplay sel sameLocation) =>
    let units := (sel.eval s p src env).getD []
    let replays := EffectList.ofList (units.map (fun unit => .banishForReplay unit sameLocation))
    (s, [.run p src env (replays.append es)], [])
  | .prim (.playReduced sel less dest) =>
    match castReducedStep s p src env sel less dest es with
    | some r => r
    | none =>
      match permanentPlayEffects s p src env (.playReduced sel less dest) with
      | some (context, plays) => (s, [.run p src context plays, .run p src env es], [])
      | none =>
        match applyPrim s p src env (.playReduced sel less dest) with
        | some r => (r.1, [.run p src env es], r.2)
        | none => skip
  | .prim (.play sel) =>
    match playSpellStep s p src env sel es with
    | some r => r
    | none =>
      match permanentPlayEffects s p src env (.play sel) with
      | some (context, plays) => (s, [.run p src context plays, .run p src env es], [])
      | none =>
        match applyPrim s p src env (.play sel) with
        | some r => (r.1, [.run p src env es], r.2)
        | none => skip
  | .prim (.discard sel n) =>
    match sel.resolve s p env, n.evalS s p src env with
    | some ps, some k => (s, ps.map (fun q => Frame.discard q k) ++ [.run p src env es], [])
    | _, _ => skip
  | .prim pr =>
    match permanentPlayEffects s p src env pr with
    | some (context, plays) => (s, [.run p src context plays, .run p src env es], [])
    | none =>
      match applyPrim s p src env pr with
      | some r => (r.1, attachmentReplacementFrames r.1 r.2 ++ [.run p src env es], r.2)
      | none => skip
  | .grant sel m d =>
    match applyGrant s p src env sel m d with
    | some r => (r.1, [.run p src env es], r.2)
    | none => skip
  | _ => skip

/-- Doing an effect, but not a choice, is a safe change of the state. -/
theorem runEffect1_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : Safe s (runEffect1 s p src env e es).1 := by
  unfold runEffect1
  split <;> (try split) <;> (try split) <;> (try split) <;> first
    | exact Safe.refl s
    | exact Safe.modObj s src (fun _ => rfl) (fun _ => rfl)
    | exact Safe.modObj s _ (fun _ => rfl) (fun _ => rfl)
    | exact castInlineStep_safe s p src env _ es
    | exact burnEffect_safe s p src env _ _ es _
    | exact linkedAction_safe s p src env _
    | exact banishObj_safe p s _
    | exact recycleLookedStep_safe s p src env es
    | exact setPoolFor_safe s p src _
    | (exact applyReducedPermanent_safe (by assumption))
    | exact playSpellStep_safe (by assumption)
    | exact castReducedStep_safe (by assumption)
    | exact applyPrim_safe (by assumption)
    | exact applyGrant_safe (by assumption)

/-- Do the first effect of `e :: es`: the new state, the frames that replace the `run` frame, and
the events. An instruction that cannot be done is skipped (design.md §7.1). An effect that names an
object to choose while it resolves ("kill a gear") asks the player when there is more than one to
choose from, and goes on with the only one when there is one (CR 355). -/
def runEffect (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : GameState × List Frame × List Event :=
  match e.pickSel? with
  | some (.pick _ side place fs) =>
    -- A linked first action is a cost. Its pick is not a target (CR 355.10.c.1).
    match requiredPlayCandidates s p src env e <|>
        s.pickCandidates p src env side place fs (!e.isLinkedCost) with
    | some [o] =>
      match e with
      | .chooseObject .. => (s, [.pickDo p src env o [] e.withPick es], [])
      | _ =>
        (s, [.run p src (env.bindPick o (e.pickIsTarget s o)) (.cons e.withPick es)],
          e.pickEvents s p src o)
    | some (o :: o2 :: more) => (s, [.pickDo p src env o (o2 :: more) e.withPick es], [])
    | _ => (s, [.run p src env es], [Event.skipped src])
  | _ => runEffect1 s p src env e es

/-- Doing an effect is a safe change of the state. -/
theorem runEffect_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : Safe s (runEffect s p src env e es).1 := by
  unfold runEffect
  split
  · split
    · split <;> exact Safe.refl s
    · exact Safe.refl s
    · exact Safe.refl s
  · exact runEffect1_safe s p src env e es

/-- The ability of the card identified by an item on the Chain (CR 337). -/
def abilityAt (s : GameState) (card : CardId) (idx : Nat) : Option Ability :=
  (s.cards.find? card).bind (fun d => d.allAbilities[idx]?)

/-- The choices and body of an ability that can go on the Chain. -/
def Ability.effectDef : Ability → Option EffectDef
  | .activated _ _ body _ | .triggered _ body _ => some body
  | _ => none

/-- The effect of the ability of a card: its choices and its body. -/
def abilityDef (s : GameState) (card : CardId) (idx : Nat) : Option EffectDef :=
  (abilityAt s card idx).bind Ability.effectDef

/-- The slots of a Spell or an ability: the objects chosen, and a filler for each target of up to one that was
left out (it selects nothing). -/
def slotValues (ts : List ObjId) (e : Option EffectDef) : List Value :=
  let n := (e.map (fun d => (d.choices.filter Choice.isTarget).length)).getD 0
  ts.map Value.obj ++ List.replicate (n - ts.length) (Value.int 0)

/-- Recheck independent target slots or a single bounded group (CR 359.3.e.2).
Invalid targets leave an empty value in their original slot. -/
def recheckedSlots (s : GameState) (p : PlayerId) (src : ObjId) (ts : List ObjId)
    (definition : Option EffectDef) : List Value :=
  match definition with
  | some e =>
    let choices := e.choices.filter Choice.isTarget
    let might := s.mightTable
    let check (choice : Choice) (i : Nat) : Value :=
      match ts[i]? with
      | some id =>
        if (choice.candidatesAfter s p src might (ts.take i)).contains id then .obj id
        else .int 0
      | none => .int 0
    match choices.getLast? with
    | some (choice@(.target (.upTo n) ..)) =>
      let fixed := choices.dropLast
      let group := ts.drop fixed.length
      let valid := choice.candidatesAfter s p src might (ts.take fixed.length)
      fixed.zipIdx.map (fun (c, i) => check c i) ++
        (group.take n).map (fun id => if valid.contains id then .obj id else .int 0) ++
        List.replicate (n - group.length) (.int 0)
    | _ => choices.zipIdx.map (fun (c, i) => check c i)
  | none => []

/-- Recheck targets for a recorded choice, when the effect opts in, or after a change of control. -/
def finalizedSlots (s : GameState) (p : PlayerId) (src : ObjId) (ts : List ObjId)
    (definition : Option EffectDef) (pick : SpellPick) : List Value :=
  let changedController := s.playLog.any (fun play =>
    play.object == src && play.moment == .finalized && play.who != p)
  if pick != .plain || definition.any (·.recheckTargets) || changedController ||
      (s.obj? src).any (·.hiddenAt.isSome) then
    recheckedSlots s p src ts definition
  else slotValues ts definition

/-- Before an open-ended group resolves, filter invalid original targets and ask its controller
to keep a legal subset if the remaining group is over budget (CR 355.11.b, 359.3.e.2). -/
def EffectDef.recheckTargetGroup (e : EffectDef) (s : GameState) (p : PlayerId)
    (src : ObjId) (targets : List ObjId) (body : EffectList) : EffectList :=
  match e.choices.getLast? with
  | some c =>
    match c with
    | .target .anyNumber _ _ _ | .target (.combinedMightAtMost _) _ _ _ =>
      let fixed := targets.take (e.choices.length - 1)
      let pm := s.mightTable
      let legal := c.candidatesAfter s p src pm fixed
      let original := (targets.drop fixed.length).filter legal.contains
      let weight := c.groupWeight s pm
      let limit := c.groupLimit
      let total (ids : List ObjId) := (ids.map weight).sum
      let groups := if total original ≤ limit then [original] else
        (subseqsWithin weight limit original).filter (fun group =>
          original.all (fun id => group.contains id || decide (limit < total group + weight id)))
      .cons (.retainTargetSet (groups.map (fixed ++ ·))) body
    | _ => body
  | none => body

/-- The frames that resolve an item of the Chain that is not a card: an ability runs its effect for
its controller, with the objects chosen as the slots, and then it leaves the Chain (CR 340). -/
def itemFrames (s : GameState) (item : ObjId) (o : Object) (rest : List Frame) : List Frame :=
  match o.kind with
  | .chainAbility card idx src =>
    let ability := match o.activationGrant with
      | some grant => s.grantedActivation grant
      | none => abilityAt s card idx
    let definition := (ability.bind Ability.effectDef).bind (·.forPick o.spellPick)
    let recheck := o.spellPick != .plain || definition.any (fun e =>
      e.recheckTargets || (!e.choices.isEmpty && e.choices.all (fun
        | .target .one .. | .target (.upTo 1) .. => true
        | _ => false)))
    let subject := o.triggerSubject.toList
    let targets := if o.spellPick == .plain then o.targets.take (o.targets.length - subject.length)
      else o.targets
    let slots := if recheck then recheckedSlots s o.controller src targets definition ++
      subject.map Value.obj else slotValues o.targets definition
    let targetObjs := match ability with
      | some (.activated costs _ _ _) =>
        if costs.any (fun | .killFriendly .. => true | _ => false) then targets.dropLast
        else targets
      | _ => targets
    let hiddenPlayLocation := match ability, s.obj? src with
      | some (.activated costs _ _ _), some source =>
        if costs.contains .fromHidden then source.hiddenAt else none
      | some (.triggered trigger _ _), some source =>
        if trigger.event == .play && trigger.subject == .self && source.fromHidden then source.loc
        else none
      | _, _ => none
    let env : Env := {
      slots
      targetObjs
      playerTargets := o.targetPlayer.toList
      hiddenPlayLocation
      sourceCard := some card
      abilityCopyStamp := o.abilityCopyStamp
      eventAmount := o.eventAmount }
    let body := match definition with
      | some e => e.recheckTargetGroup s o.controller src o.targets (.cons e.body .nil)
      | none => .nil
    .run o.controller src env body :: .finishSpell item :: rest
  | _ => .finishSpell item :: rest

/-- The effects that choose the targets of an effect again: one for each target of exactly one
object (the others keep what they were) (CR 820). -/
def EffectDef.refills (e : EffectDef) : List Effect :=
  let rec go : List Choice → Nat → List Effect
    | [], _ => []
    | .target .one side place fs :: cs, i =>
      .fillSlot i (Selector.pick .one side place fs) :: go cs (i + 1)
    | .target _ _ _ _ :: cs, i => go cs (i + 1)
    | _ :: cs, i => go cs i
  go e.choices 0

/-- What a repeated effect does after the first time: the targets are chosen again, then the effect
is done (CR 820). -/
def EffectDef.repeats (e : EffectDef) : Nat → EffectList
  | 0 => .nil
  | m + 1 => (EffectList.ofList e.refills).append (.cons e.body (e.repeats m))

/-- An effect done `n` times: the first time with the targets chosen when the Spell was played, the
others with the targets chosen again (CR 820). -/
def EffectDef.executions (e : EffectDef) (n : Nat) : EffectList :=
  match n with
  | 0 => .nil
  | m + 1 => .cons e.body (e.repeats m)

/-- The frames that resolve the item on top of the Chain (CR 340): run its effect, then it leaves
the Chain (a Spell goes to the Trash, an ability ceases to exist). Nothing to resolve when the
Chain is empty. -/
def resolveFrames (s : GameState) (rest : List Frame) : List Frame :=
  match s.zone .chain with
  | item :: _ =>
    match s.obj? item, s.cardDef? item with
    | some o, some d =>
      let definition := d.spellEffect.bind (·.forPick o.spellPick)
      .run o.controller item {
        slots := finalizedSlots s o.controller item o.targets definition o.spellPick
        targetObjs := o.targets
        hiddenPlayLocation := o.hiddenAt
        playerTargets := if definition.any (fun e => s.spellPlayerTargetOk o.controller e o.spellPick)
          then o.targetPlayer.toList else [] }
        (match definition with
          | some e =>
            -- once, and once more for each Repeat that was paid (CR 820)
            e.recheckTargetGroup s o.controller item o.targets
              (e.executions (if !d.repeatChooses then 1 + o.extraPaid else 1))
          | none => .nil) :: .finishSpell item :: rest
    | some o, none => itemFrames s item o rest
    | none, _ => .finishSpell item :: rest
  | [] => rest

/-- Finish a Chain item: a Spell moves to its destination and an ability ceases to exist
(CR 359.3.d, 829.1.b.1). Nothing happens if it has already left the Chain. -/
def finishItem (s : GameState) (item : ObjId) : GameState × List Event :=
  match s.obj? item with
  | some o =>
    if item ∈ s.zone .chain then
      match o.kind with
      | .chainAbility .. =>
        match removeObj s item with
        | some s2 => (s2, [])
        | none => (s, [])
      | _ =>
        match moveObj s item (s.chainDestination item o .trash) with
        | some r =>
          let es := s.chainExitEvents o item r.2 .trash
          (r.1, es ++ spellCompletion s item es)
        | none => (s, [])
    else (s, [])
  | none => (s, [])

/-- The frames to put under the Cleanup after an item has resolved: while the Chain still holds
items, the turn player gets priority again (CR 340). -/
def afterItem (s : GameState) : List Frame :=
  if (s.zone .chain).isEmpty then [] else [.chainPass (s.active.getD ⟨0⟩) 0]

/-- The frames under the Cleanup after an item has resolved are a `chainPass`. -/
theorem afterItem_mem {s : GameState} {f : Frame} (h : f ∈ afterItem s) :
    ∃ p, f = .chainPass p 0 := by
  unfold afterItem at h
  split at h
  · simp at h
  · simp only [List.mem_singleton] at h
    exact ⟨_, h⟩

/-- Finishing an item either changes nothing, moves a Spell, or removes an ability. -/
theorem finishItem_cases (s : GameState) (item : ObjId) :
    (finishItem s item).1 = s ∨
      (∃ o s2 id', s.obj? item = some o ∧ item ∈ s.zone .chain ∧
        moveObj s item (s.chainDestination item o .trash) = some (s2, id') ∧
          (finishItem s item).1 = s2) ∨
      (∃ o s2, s.obj? item = some o ∧ item ∈ s.zone .chain ∧ o.kind.phys? = none ∧
          removeObj s item = some s2 ∧ (finishItem s item).1 = s2) := by
  unfold finishItem
  split
  · rename_i o ho
    split
    · rename_i hc
      split
      · rename_i card idx src hk
        split
        · rename_i s2 hr
          exact Or.inr (Or.inr ⟨o, s2, ho, hc, by rw [hk]; rfl, hr, rfl⟩)
        · exact Or.inl rfl
      · split
        · rename_i r hm
          exact Or.inr (Or.inl ⟨o, r.1, r.2, ho, hc, hm, rfl⟩)
        · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- Finishing an item keeps the game well formed. -/
theorem finishItem_wf {s : GameState} (hwf : s.WF) (item : ObjId) : (finishItem s item).1.WF := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, -, hm, h⟩ | ⟨o, s2, -, -, -, hr, h⟩
  · rw [h]; exact hwf
  · rw [h]; exact moveObj_wf hwf hm
  · rw [h]; exact removeObj_wf hwf hr

/-- Finishing an item keeps the physical cards. -/
theorem finishItem_physIds {s : GameState} (hwf : s.WF) (item : ObjId) :
    (finishItem s item).1.physIds.Perm s.physIds := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, -, hm, h⟩ | ⟨o, s2, ho, -, hk, hr, h⟩
  · rw [h]
  · rw [h]; exact moveObj_physIds hwf hm
  · rw [h]; exact removeObj_physIds hwf hr ho hk

/-- Finishing an item keeps `OwnerOk`. -/
theorem finishItem_ownerOk {s : GameState} (hwf : s.WF) (hown : s.OwnerOk) (item : ObjId) :
    (finishItem s item).1.OwnerOk := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, -, hm, h⟩ | ⟨o, s2, -, -, -, hr, h⟩
  · rw [h]; exact hown
  · rw [h]; exact moveObj_ownerOk hwf hown hm
  · rw [h]; exact removeObj_ownerOk hwf hown hr

/-- Finishing an item changes only the zones, the objects and the counters. -/
theorem finishItem_sameMeta (s : GameState) (item : ObjId) : SameMeta s (finishItem s item).1 := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, -, hm, h⟩ | ⟨o, s2, -, -, -, hr, h⟩
  · rw [h]; exact SameMeta.refl s
  · rw [h]; exact (moveObj_spec hm).choose_spec.choose_spec.other
  · rw [h]; exact removeObj_sameMeta hr

/-- Resolving the Chain puts some frames on top of the stack below. -/
theorem resolveFrames_eq (s : GameState) (rest : List Frame) :
    ∃ pre, resolveFrames s rest = pre ++ rest ∧ ∀ g ∈ pre, g.isPlay = true := by
  unfold resolveFrames
  split
  · split
    · exact ⟨[.run _ _ _ _, .finishSpell _], rfl, by simp [Frame.isPlay]⟩
    · unfold itemFrames
      split
      · exact ⟨[.run _ _ _ _, .finishSpell _], rfl, by simp [Frame.isPlay]⟩
      · exact ⟨[.finishSpell _], rfl, by simp [Frame.isPlay]⟩
    · exact ⟨[.finishSpell _], rfl, by simp [Frame.isPlay]⟩
  · exact ⟨[], rfl, by simp⟩

end Riftbound

end
