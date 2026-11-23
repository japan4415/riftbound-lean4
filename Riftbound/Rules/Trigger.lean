module

public import Riftbound.Rules.Chain

/-!
# Triggered abilities

A triggered ability fires when something it waits for happens (CR 382-385). The step that did it
leaves events; `detect` reads them and names the abilities that fire. They wait on the stack, in a
`triggers` frame beneath the work that is still to do, until a player would next receive priority
(CR 383.1); then each goes on the Chain as an object of its own, the turn player's first (CR 383.3).

The abilities that fire are those with the object itself as subject, no condition, and every time.
A player with several abilities to put on the Chain chooses the order, and the targets of each, one
at a time (CR 383.3.d, 355): the decision is the `triggerOrder` frame. With one ability and nothing
to choose, it goes on the Chain at once. An ability with no legal targets is removed (CR 355).
The abilities of other objects, such as a Unit that watches the plays of the others (CR 382), fire
too, when the subject of the ability is the object that was played, killed or moved (`watchersOf`).
Triggers at a point of the turn are later.
-/

@[expose] public section

namespace Riftbound

/-- The events that say a card was played: for the object it became (CR 349). -/
def playedOf (p : PlayerId) (es : List Event) : List Event :=
  es.filterMap (fun e => match e with
    | .moved _ n _ => some (Event.played p n)
    | _ => none)

/-- The events a step has besides those of the rules it ran: playing a card (CR 349). -/
def extraEvents (a : Action) (es : List Event) : List Event :=
  match a.kind, a.actor with
  | .playCard _ _ ts, .player p => playedOf p es ++ ts.map (Event.chosenBySpell p)
  | _, _ => []

/-- The condition holds for the object when the event happens: none, a fact of how the object was
played (CR 812), or a question about the game, asked for the player `who` the ability works for,
that `Condition.eval` can answer (it is false when it cannot). -/
def condOkEnv (s : GameState) (src : ObjId) (who : PlayerId) (env : Env) : Condition → Bool
  | .always => true
  | .paid => (s.obj? src).any (·.paid)
  | .legion => (s.obj? src).any (·.legion)
  | c => c.eval s who src env == some true

/-- The same, where nothing was chosen. -/
def condOk (s : GameState) (src : ObjId) (who : PlayerId) : Condition → Bool :=
  condOkEnv s src who {}

/-- The ability can fire on the event: it is about the object itself, every time, and its condition
holds. -/
def trigOk (s : GameState) (src : ObjId) (who : PlayerId) (t : Trigger) (_body : EffectDef) :
    Bool :=
  t.subject == .self && condOk s src who t.condition && t.occurrence == .every

/-- The ability can be used again this turn (CR 371, 386). -/
def limitOk (s : GameState) (src : ObjId) (idx : Nat) : Limit → Bool
  | .unlimited => true
  | .perTurn n => (s.obj? src).any (fun o => decide (o.used.count idx < n))

/-- The triggered abilities at the places `lo` up to `hi` of the card `d`, as abilities of the
object `src` controlled by `p`, that fire on the event. -/
def triggersAmong (s : GameState) (src : ObjId) (p : PlayerId) (ev : TriggerEvent) (d : CardDef)
    (lo hi : Nat) : List PendTrigger :=
  (List.range (hi - lo)).filterMap (fun (j : Nat) =>
    match d.allAbilities[lo + j]? with
    | some (Ability.triggered t body lim) =>
      if t.event == ev && trigOk s src p t body && limitOk s src (lo + j) lim then
        some { source := src, card := d.id, idx := lo + j, controller := p }
      else none
    | _ => none)

/-- The triggered abilities of the object `src`, controlled by `p`, that fire on the event: those
of its card, and those the Equipment attached to it gives it (CR 137). -/
def triggersOf (s : GameState) (src : ObjId) (p : PlayerId) (ev : TriggerEvent) :
    List PendTrigger :=
  (match s.cardDef? src with
    | some d => triggersAmong s src p ev d 0 d.fullAbilities.length
    | none => []) ++
  s.inPlay.flatMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      if o.attached == some src then
        triggersAmong s src p ev d d.fullAbilities.length d.allAbilities.length
      else []
    | _, _ => [])

/-- Whether the object `subj`, which the player `who` plays, loses or moves, is what the subject of
a trigger of `src` (controlled by `c`) describes. The place of the subject is not asked: the object
may have left the game, as a Spell on its way to the Chain has. A subject at a place (here, at a
base) is not understood yet: it never holds. -/
def subjectHolds (s : GameState) (src : ObjId) (c : PlayerId) (subj : ObjId) (who : PlayerId) :
    Selector → Bool
  | .pick .all side .anywhere fs =>
    (match side with | .friendly => who == c | .enemy => who != c | .any => true) &&
      (fs.holds s src {} subj == some true)
  | _ => false

/-- The abilities of the objects in play and of the Legends that watch for the object `subj` of the
player `who`, on the event: those whose subject is not the object itself. -/
def watchersOf (s : GameState) (subj : ObjId) (who : PlayerId) (ev : TriggerEvent) :
    List PendTrigger :=
  (s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))).flatMap (fun src =>
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      (List.range d.fullAbilities.length).filterMap (fun (j : Nat) =>
        match d.allAbilities[j]? with
        | some (Ability.triggered t _ lim) =>
          if t.event == ev && t.subject != .self &&
              subjectHolds s src o.controller subj who t.subject &&
              condOkEnv s src o.controller { slots := [.obj subj] } t.condition &&
                t.occurrence == .every &&
                limitOk s src j lim then
            some { source := src, card := d.id, idx := j, controller := o.controller,
                   subject := some subj }
          else none
        | _ => none)
    | _, _ => [])

/-- The Units of the player at the Battlefield. -/
def GameState.trigUnitsAt (s : GameState) (bf : ObjId) (p : PlayerId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun u =>
    (s.obj? u).any (fun o => o.loc == some bf && o.controller == p))

/-- The unit has an Equipment attached that makes its hold effects conquer effects, and the other
way round. -/
def GameState.holdIsConquer (s : GameState) (u : ObjId) : Bool :=
  s.inPlay.any (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      o.attached == some u && d.grants.any (fun ab =>
        match ab with
        | Ability.passive .always mods => mods.contains .holdIsConquer
        | _ => false)
    | _, _ => false)

/-- The Units at the Battlefield, of every player. -/
def GameState.trigAllUnitsAt (s : GameState) (bf : ObjId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun u => (s.obj? u).any (fun o => o.loc == some bf))

/-- The point of the turn that the start of a phase is (CR 314-317). -/
def Phase.timing? : Phase → Option Timing
  | .awaken => some .startOfTurn
  | .beginning => some .beginning
  | .main => some .startOfMain
  | .ending => some .endOfTurn
  | _ => none

/-- The abilities of the objects in play and of the Legends that wait for the point of the turn
`tm`, in the turn of the player `p`: those of the objects `p` controls, and those of a Battlefield,
which work for `p` (CR 314-317). -/
def GameState.timedTriggers (s : GameState) (p : PlayerId) (tm : Timing) : List PendTrigger :=
  (s.inPlay ++ s.players.flatMap (fun q => s.zone (.player q .legendZone))).flatMap (fun src =>
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      let who := if d.hasType .battlefield then p else o.controller
      if who == p then
        (List.range d.fullAbilities.length).filterMap (fun (j : Nat) =>
          match d.allAbilities[j]? with
          | some (Ability.triggered t _ lim) =>
            if t.event == .at_ tm && t.subject == .self && condOk s src who t.condition &&
                t.occurrence == .every && limitOk s src j lim then
              some { source := src, card := d.id, idx := j, controller := who }
            else none
          | _ => none)
      else []
    | _, _ => [])

/-- A passive ability of an object the player controls makes the abilities of the event `.die` fire
one more time. -/
def GameState.dieExtra (s : GameState) (p : PlayerId) : Bool :=
  s.passiveSources.any (fun g => (s.obj? g).any (fun o => o.controller == p) &&
    (s.activeMods g).any (fun m => match m with | .triggersExtra .die _ => true | _ => false))

/-- The abilities that fire because of one event (CR 389). -/
def detectOne (s : GameState) : Event → List PendTrigger
  | .played p obj => triggersOf s obj p .play ++ watchersOf s obj p .play
  | .died obj p =>
    let own := triggersOf s obj p .die
    -- the Deathknell abilities of a unit fire one more time while a passive ability says so
    let again :=
      if (s.cardDef? obj).any (·.hasKeyword .deathknell) && s.dieExtra p then own else []
    own ++ again ++ watchersOf s obj p .die
  | .standardMoved u _ =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .move ++ watchersOf s u o.controller .move
    | none => []
  | .phaseStarted p ph =>
    match ph.timing? with
    | some tm => s.timedTriggers p tm
    | none => []
  | .conquerActivated u =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .conquer
    | none => []
  | .lookedAt p c => triggersOf s c p .seenOnTop
  | .chosenBySpell p t =>
    -- a Battlefield waits for its player's chosen unit at it
    (s.zone .battlefieldZone).flatMap (fun bf =>
      if (s.cardDef? t).any (·.hasType .unit) &&
          (s.obj? t).any (fun o => o.controller == p && o.loc == some bf) then
        triggersOf s bf p .chosenHere
      else []) ++
    -- a unit of the player that is chosen by their spell, and what watches the units they choose
    (if (s.obj? t).any (·.controller == p) then
      triggersOf s t p .chosen ++ watchersOf s t p .chosen
    else [])
  | .killedBySpell p =>
    (s.zone (.player p .trash)).flatMap (fun u => triggersOf s u p .killBySpell)
  | .recycled p =>
    s.inPlay.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then triggersOf s u p .recycle else [])
  | .hiddenPlayed p =>
    s.inPlay.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then triggersOf s u p .playHidden else [])
  | .buffed u =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .buff ++ watchersOf s u o.controller .buff
    | none => []
  | .readied u =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .ready ++ watchersOf s u o.controller .ready
    | none => []
  | .stunned u =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .stun ++ watchersOf s u o.controller .stun
    | none => []
  | .discarded p obj last =>
    triggersOf s obj p .discard ++ (if last then watchersOf s obj p .discard else [])
  | .scored p bf conquer =>
    (s.trigUnitsAt bf p).flatMap
      (fun u => triggersOf s u p (if conquer then .conquer else .hold) ++
        -- Skyfall of Areion: the hold effects of the unit are conquer effects too, and back
        (if s.holdIsConquer u then triggersOf s u p (if conquer then .hold else .conquer)
         else [])) ++
    (s.zone (.player p .legendZone)).flatMap
      (fun l => triggersOf s l p (if conquer then .youConquer else .youHold)) ++
    triggersOf s bf p (if conquer then .youConquer else .youHold) ++
    -- the cards in the Trash that wait for a conquer of their player
    (if conquer then
      (s.zone (.player p .trash)).flatMap (fun u => triggersOf s u p .conquerFromTrash)
    else [])
  | .attached _ u =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .attachedTo
    | none => []
  | .buffSpent p =>
    s.inPlay.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then triggersOf s u p .spendBuff else [])
  | .activated p src _ =>
    -- an ability of a gear on the Board (not Hide, not the play of a hidden gear)
    if (s.cardDef? src).any (·.hasType .gear) && src ∈ s.inPlay then
      s.inPlay.flatMap (fun u =>
        if (s.obj? u).any (·.controller == p) then triggersOf s u p .useGearAbility else [])
    else []
  | .combatWon bf w =>
    (s.trigUnitsAt bf w).flatMap (fun u => triggersOf s u w .winCombat) ++
    (s.zone (.player w .legendZone)).flatMap (fun l => triggersOf s l w .winCombat)
  | .combatStarted bf att =>
    (s.trigAllUnitsAt bf).flatMap (fun u =>
      match s.obj? u with
      | some o =>
        let ev := if o.controller == att then TriggerEvent.attack else .defend
        triggersOf s u o.controller ev ++ watchersOf s u o.controller ev
      | none => []) ++
    -- the abilities of the Battlefield: for the players who attack and defend there
    (s.players.filter (fun q => !(s.trigUnitsAt bf q).isEmpty)).flatMap (fun q =>
      triggersOf s bf q (if q == att then TriggerEvent.attack else .defend)) ++
    -- the units of a defending player that are elsewhere: "when you defend at a battlefield"
    (s.players.filter (fun q => q != att && !(s.trigUnitsAt bf q).isEmpty)).flatMap (fun q =>
      s.inPlay.flatMap (fun u =>
        if (s.obj? u).any (fun o => o.controller == q && o.loc != some bf) &&
            (s.cardDef? u).any (·.hasType .unit) then
          (triggersOf s u q .youDefend).map (fun t => { t with subject := some bf })
        else []))
  | _ => []

/-- Keep the abilities that a limit of times per turn lets fire: the events of one step may set
off the same ability more than once, and the limit counts the times it fired before and those it
fires now (CR 371). -/
def GameState.trimLimits (s : GameState) (l : List PendTrigger) : List PendTrigger :=
  l.foldl (fun kept t =>
    let taken := (kept.filter (fun k => k.source == t.source && k.idx == t.idx)).length
    match (s.cardDef? t.source).bind (fun d => d.allAbilities[t.idx]?),
        (s.obj? t.source).map (·.used) with
    | some (Ability.triggered _ _ (.perTurn n)), some used =>
      if used.count t.idx + taken < n then kept ++ [t] else kept
    | _, _ => kept ++ [t]) []

/-- The abilities that fire because of the events of a step, the turn player's first (CR 383.3). -/
def GameState.detect (s : GameState) (es : List Event) : List PendTrigger :=
  let all := s.trimLimits (es.flatMap (detectOne s))
  let a := s.active.getD ⟨0⟩
  all.filter (fun t => t.controller == a) ++ all.filter (fun t => t.controller != a)

/-- The frames that do not decide anything and whose work does not wait for triggers: the Cleanup
and the resolution of an item of the Chain. -/
def Frame.isResolution : Frame → Bool
  | .cleanup => true
  | .run .. => true
  | .finishSpell _ => true
  | .resolveChain => true
  | .combatDamage .. => true
  | .combatResolve .. => true
  | _ => false

/-- Put the triggers on the stack beneath the work that is still to do: just before the first frame
that is not resolution. Triggers already waiting there are joined. -/
def insertTriggers (pend : List PendTrigger) : List Frame → List Frame
  | [] => [.triggers pend]
  | f :: fs =>
    if f.isResolution then f :: insertTriggers pend fs
    else
      match f with
      | .triggers old => .triggers (old ++ pend) :: fs
      | _ => .triggers pend :: f :: fs

/-- The frames after inserting triggers are the old frames and `triggers` frames. -/
theorem insertTriggers_mem (pend : List PendTrigger) :
    ∀ (p : List Frame) {f : Frame}, f ∈ insertTriggers pend p →
      f ∈ p ∨ ∃ x, f = .triggers x
  | [], f, h => by
    simp only [insertTriggers, List.mem_singleton] at h
    exact Or.inr ⟨_, h⟩
  | g :: gs, f, h => by
    unfold insertTriggers at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases insertTriggers_mem pend gs h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
    · split at h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inl h

/-- Inserting triggers keeps the last frame, if it is not resolution and not a `triggers` frame. -/
theorem insertTriggers_getLast (pend : List PendTrigger) :
    ∀ (p : List Frame) {g : Frame}, p.getLast? = some g → g.isResolution = false →
      (∀ x, g ≠ .triggers x) → (insertTriggers pend p).getLast? = some g
  | [], g, h, _, _ => by simp at h
  | f :: fs, g, h, hr, hn => by
    cases fs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      unfold insertTriggers
      simp only [hr]
      cases f with
      | triggers x => exact absurd rfl (hn x)
      | _ => simp [List.getLast?_cons_cons]
    | cons y ys =>
      have h' : (y :: ys).getLast? = some g := by
        simpa [List.getLast?_cons_cons] using h
      have ih := insertTriggers_getLast pend (y :: ys) h' hr hn
      unfold insertTriggers
      split
      · have hne : insertTriggers pend (y :: ys) ≠ [] := by
          unfold insertTriggers; split <;> (try split) <;> simp
        cases hl : insertTriggers pend (y :: ys) with
        | nil => exact absurd hl hne
        | cons z zs =>
          rw [hl] at ih
          simpa [List.getLast?_cons_cons] using ih
      · split
        · simpa [List.getLast?_cons_cons] using h
        · simpa [List.getLast?_cons_cons] using h

/-- Inserting triggers does not change what the frames account for in the hands. -/
theorem insertTriggers_contrib (pend : List PendTrigger) (q : PlayerId) (contrib : Frame → Nat)
    (h0 : ∀ x, contrib (.triggers x) = 0) :
    ∀ p : List Frame, ((insertTriggers pend p).map contrib).sum = (p.map contrib).sum
  | [] => by simp [insertTriggers, h0]
  | f :: fs => by
    unfold insertTriggers
    split
    · simp [insertTriggers_contrib pend q contrib h0 fs]
    · split
      · simp [h0]
      · simp [h0]

/-- After a step: the abilities that fired wait on the stack. Not during the setup. -/
def GameState.withTriggers (s : GameState) (es : List Event) : GameState :=
  if s.phase != .setup && s.pending.all (fun f => !f.isSetup) then
    match s.detect es with
    | [] => s
    | pend => { s with pending := insertTriggers pend s.pending }
  else s

/-- The choices of the triggered ability that waits (CR 355). -/
def trigChoices (s : GameState) (t : PendTrigger) : List Choice :=
  match s.cards.find? t.card with
  | some d =>
    match d.allAbilities[t.idx]? with
    | some (Ability.triggered _ body _) => body.choices
    | _ => []
  | none => []

/-- Every legal pick for the ability's choices that the Pool of its controller can pay the Deflect
of (CR 355, 809). -/
def trigTuples (s : GameState) (t : PendTrigger) : List (List ObjId) :=
  (targetTuples s t.controller t.source (trigChoices s t)).filter
    (fun ts => s.deflectOk t.controller (s.poolOf t.controller) ts)

/-- The picks listed are exactly the legal ones that the Pool can pay for. -/
theorem mem_trigTuples (s : GameState) (t : PendTrigger) (ts : List ObjId) :
    ts ∈ trigTuples s t ↔ (targetsOk s t.controller t.source (trigChoices s t) ts &&
      s.deflectOk t.controller (s.poolOf t.controller) ts) = true := by
  unfold trigTuples
  rw [List.mem_filter, mem_targetTuples]
  simp [Bool.and_eq_true]

/-- The objects are a legal pick for the ability's choices, and the Pool pays the Deflect of them,
or the ability has no such pick and nothing is chosen (CR 355, 809). -/
def trigLegal (s : GameState) (t : PendTrigger) (ts : List ObjId) : Bool :=
  (targetsOk s t.controller t.source (trigChoices s t) ts &&
      s.deflectOk t.controller (s.poolOf t.controller) ts) ||
    (ts.isEmpty && (trigTuples s t).isEmpty)

/-- Every pick worth trying for the ability: the legal ones, or nothing if there is none. -/
def trigOptions (s : GameState) (t : PendTrigger) : List (List ObjId) :=
  match trigTuples s t with
  | [] => [[]]
  | l => l

/-- The picks listed are exactly the legal ones. -/
theorem mem_trigOptions (s : GameState) (t : PendTrigger) (ts : List ObjId) :
    ts ∈ trigOptions s t ↔ trigLegal s t ts = true := by
  unfold trigOptions trigLegal
  rw [Bool.or_eq_true, ← mem_trigTuples]
  cases hl : trigTuples s t with
  | nil => simp
  | cons x xs => simp

/-- An ability that waits has a legal pick. -/
theorem trigLegal_exists (s : GameState) (t : PendTrigger) : ∃ ts, trigLegal s t ts = true := by
  by_cases h : trigTuples s t = []
  · exact ⟨[], by simp [trigLegal, h]⟩
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
    have hok := (mem_trigTuples s t x).mp hx
    exact ⟨x, by simp [trigLegal, hok]⟩

/-- The Chain gets the ability: it is used (CR 371), and it goes on top as an object of its own,
controlled by the player, with the objects chosen. -/
def putTrigger (s : GameState) (t : PendTrigger) (ts : List ObjId) : GameState :=
  let s1 := s.modObj t.source (fun o => { o with used := o.used ++ [t.idx] })
  match addObject s1 (abilityItem t.card t.idx t.source t.controller (ts ++ t.subject.toList))
      .chain with
  | some r => r.1
  | none => s1

/-- Put the picked ability of the group on the Chain; an ability with choices and no pick is removed
(CR 355). -/
def putPick (s : GameState) (grp : List PendTrigger) (i : Nat) (ts : List ObjId) : GameState :=
  match grp[i]? with
  | some t => if ts.isEmpty && !(trigChoices s t).isEmpty then s else putTrigger s t ts
  | none => s

/-- The frames to put beneath the work after the abilities have gone on the Chain: the turn player
gets priority with the Chain, unless that is already so (CR 340). -/
def triggerFrames (s : GameState) (rest : List Frame) : List Frame :=
  match rest with
  | .chainPass .. :: _ => []
  | _ => if (s.zone .chain).isEmpty then [] else [.chainPass (s.active.getD ⟨0⟩) 0]

/-- The frames put under the work after the triggers are Chain priorities. -/
theorem triggerFrames_mem {s : GameState} {rest : List Frame} {f : Frame}
    (h : f ∈ triggerFrames s rest) : ∃ p n, f = .chainPass p n := by
  unfold triggerFrames at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [List.mem_singleton] at h
      exact ⟨_, _, h⟩

/-- One step of a `triggers` frame: with nothing left, the turn player gets priority; with one
ability and nothing to choose, it goes on the Chain; otherwise its player chooses (CR 383.3.d). The
state, and the frames to put above the rest of the stack. -/
def triggersStep (s : GameState) (pend : List PendTrigger) (rest : List Frame) :
    GameState × List Frame :=
  match pend with
  | [] => (s, triggerFrames s rest)
  | t :: ts =>
    let grp := ts.filter (fun u => u.controller == t.controller)
    let others := ts.filter (fun u => u.controller != t.controller)
    if grp.isEmpty && (trigChoices s t).isEmpty then (putTrigger s t [], [.triggers others])
    else (s, [.triggerOrder t.controller t grp others])

/-- Putting one ability on the Chain is a safe change. -/
theorem putTrigger_safe (s : GameState) (t : PendTrigger) (ts : List ObjId) :
    Safe s (putTrigger s t ts) := by
  have h1 : Safe s (s.modObj t.source (fun o => { o with used := o.used ++ [t.idx] })) :=
    Safe.modObj s t.source (fun _ => rfl) (fun _ => rfl)
  unfold putTrigger
  dsimp only
  split
  · rename_i r hr
    refine h1.trans ⟨fun hwf => addObject_wf hwf hr, fun hwf => addObject_physIds hwf hr rfl,
      fun hwf hown => addObject_ownerOk hwf hown hr, addObject_sameMeta hr⟩
  · exact h1

/-- Putting the picked ability on the Chain is a safe change. -/
theorem putPick_safe (s : GameState) (grp : List PendTrigger) (i : Nat) (ts : List ObjId) :
    Safe s (putPick s grp i ts) := by
  unfold putPick
  split
  · split
    · exact Safe.refl s
    · exact putTrigger_safe s _ ts
  · exact Safe.refl s

/-- A step of a `triggers` frame is a safe change, and the frames it puts are priorities, `triggers`
frames and choices of triggers. -/
theorem triggersStep_spec (s : GameState) (pend : List PendTrigger) (rest : List Frame) :
    Safe s (triggersStep s pend rest).1 ∧ ∀ g ∈ (triggersStep s pend rest).2,
      (∃ p n, g = .chainPass p n) ∨ (∃ x, g = .triggers x) ∨
        (∃ p t m o, g = .triggerOrder p t m o) := by
  unfold triggersStep
  split
  · refine ⟨Safe.refl s, fun g hg => ?_⟩
    obtain ⟨p, n, h⟩ := triggerFrames_mem hg
    exact Or.inl ⟨p, n, h⟩
  · dsimp only
    split
    · refine ⟨putTrigger_safe s _ [], fun g hg => ?_⟩
      simp only [List.mem_singleton] at hg
      exact Or.inr (Or.inl ⟨_, hg⟩)
    · refine ⟨Safe.refl s, fun g hg => ?_⟩
      simp only [List.mem_singleton] at hg
      exact Or.inr (Or.inr ⟨_, _, _, _, hg⟩)

/-- What a step of `withTriggers` does: nothing, or insert triggers where no setup frame is left
and the game is not in its setup. -/
theorem withTriggers_cases (s : GameState) (es : List Event) :
    s.withTriggers es = s ∨ ∃ pend, s.withTriggers es = { s with
        pending := insertTriggers pend s.pending } ∧ s.phase ≠ .setup ∧
      ∀ f ∈ s.pending, f.isSetup = false := by
  unfold GameState.withTriggers
  by_cases hg : (s.phase != .setup && s.pending.all (fun f => !f.isSetup)) = true
  · cases hd : s.detect es with
    | nil => simp [hg]
    | cons x xs =>
      right
      refine ⟨x :: xs, by simp [hg], ?_, ?_⟩
      · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg
        exact hg.1
      · simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
        exact hg.2
  · simp [hg]

/-- `withTriggers` changes the stack and nothing else. -/
theorem withTriggers_pending (s : GameState) (es : List Event) :
    ∃ p, s.withTriggers es = { s with pending := p } := by
  rcases withTriggers_cases s es with h | ⟨pend, h, -⟩
  · exact ⟨s.pending, by rw [h]⟩
  · exact ⟨_, h⟩

/-- Finding the triggers keeps the game well formed. -/
theorem withTriggers_wf {s : GameState} (es : List Event) (hwf : s.WF) :
    (s.withTriggers es).WF := by
  obtain ⟨p, h⟩ := withTriggers_pending s es
  rw [h]
  exact hwf.congr rfl rfl rfl rfl

/-- Finding the triggers keeps the physical cards. -/
theorem withTriggers_physIds (s : GameState) (es : List Event) :
    (s.withTriggers es).physIds = s.physIds := by
  obtain ⟨p, h⟩ := withTriggers_pending s es
  rw [h]
  rfl

/-- Finding the triggers keeps `OwnerOk`. -/
theorem withTriggers_ownerOk {s : GameState} (es : List Event) (hown : s.OwnerOk) :
    (s.withTriggers es).OwnerOk := by
  obtain ⟨p, h⟩ := withTriggers_pending s es
  rw [h]
  exact hown.congr rfl rfl

/-- With no event, nothing fires. -/
theorem withTriggers_nil (s : GameState) : s.withTriggers [] = s := by
  unfold GameState.withTriggers
  split
  · simp [GameState.detect, GameState.trimLimits]
  · rfl

/-- The frames a `triggers` step puts are not `setupHands`, are not setup frames. -/
theorem triggersStep_frames {s : GameState} {pend : List PendTrigger} {rest : List Frame}
    {g : Frame} (h : g ∈ (triggersStep s pend rest).2) :
    g ≠ .setupHands ∧ g.isSetup = false := by
  rcases (triggersStep_spec s pend rest).2 g h with
      ⟨p, n, rfl⟩ | ⟨x, rfl⟩ | ⟨p, t, m, o, rfl⟩ <;>
    exact ⟨by simp, rfl⟩

end Riftbound

end
