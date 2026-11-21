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
Triggers at a point of the turn and triggers of other objects are later.
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
  | .playCard .., .player p => playedOf p es
  | _, _ => []

/-- The ability can fire on the event: it is about the object itself, with no condition, every
time. -/
def trigOk (t : Trigger) (_body : EffectDef) : Bool :=
  t.subject == .self && t.condition == .always && t.occurrence == .every

/-- The ability can be used again this turn (CR 371, 386). -/
def limitOk (s : GameState) (src : ObjId) (idx : Nat) : Limit → Bool
  | .unlimited => true
  | .perTurn n => (s.obj? src).any (fun o => decide (o.used.count idx < n))

/-- The triggered abilities of the object `src`, controlled by `p`, that fire on the event. -/
def triggersOf (s : GameState) (src : ObjId) (p : PlayerId) (ev : TriggerEvent) :
    List PendTrigger :=
  match s.cardDef? src with
  | some d =>
    (List.range d.abilities.length).filterMap (fun (i : Nat) =>
      match d.abilities[i]? with
      | some (Ability.triggered t body lim) =>
        if t.event == ev && trigOk t body && limitOk s src i lim then
          some { source := src, card := d.id, idx := i, controller := p }
        else none
      | _ => none)
  | none => []

/-- The Units of the player at the Battlefield. -/
def GameState.trigUnitsAt (s : GameState) (bf : ObjId) (p : PlayerId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun u =>
    (s.obj? u).any (fun o => o.loc == some bf && o.controller == p))

/-- The Units at the Battlefield, of every player. -/
def GameState.trigAllUnitsAt (s : GameState) (bf : ObjId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun u => (s.obj? u).any (fun o => o.loc == some bf))

/-- The abilities that fire because of one event (CR 389). -/
def detectOne (s : GameState) : Event → List PendTrigger
  | .played p obj => triggersOf s obj p .play
  | .died obj p => triggersOf s obj p .die
  | .standardMoved u _ =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .move
    | none => []
  | .scored p bf conquer =>
    (s.trigUnitsAt bf p).flatMap
      (fun u => triggersOf s u p (if conquer then .conquer else .hold)) ++
    (s.zone (.player p .legendZone)).flatMap
      (fun l => triggersOf s l p (if conquer then .youConquer else .youHold)) ++
    triggersOf s bf p (if conquer then .youConquer else .youHold)
  | .combatStarted bf att =>
    (s.trigAllUnitsAt bf).flatMap (fun u =>
      match s.obj? u with
      | some o => triggersOf s u o.controller (if o.controller == att then .attack else .defend)
      | none => [])
  | _ => []

/-- The abilities that fire because of the events of a step, the turn player's first (CR 383.3). -/
def GameState.detect (s : GameState) (es : List Event) : List PendTrigger :=
  let all := es.flatMap (detectOne s)
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
    match d.abilities[t.idx]? with
    | some (Ability.triggered _ body _) => body.choices
    | _ => []
  | none => []

/-- The objects are a legal pick for the ability's choices, or the ability has no legal pick and
nothing is chosen (CR 355). -/
def trigLegal (s : GameState) (t : PendTrigger) (ts : List ObjId) : Bool :=
  targetsOk s t.controller t.source (trigChoices s t) ts ||
    (ts.isEmpty && (targetTuples s t.controller t.source (trigChoices s t)).isEmpty)

/-- Every pick worth trying for the ability: the legal ones, or nothing if there is none. -/
def trigOptions (s : GameState) (t : PendTrigger) : List (List ObjId) :=
  match targetTuples s t.controller t.source (trigChoices s t) with
  | [] => [[]]
  | l => l

/-- The picks listed are exactly the legal ones. -/
theorem mem_trigOptions (s : GameState) (t : PendTrigger) (ts : List ObjId) :
    ts ∈ trigOptions s t ↔ trigLegal s t ts = true := by
  unfold trigOptions trigLegal
  rw [Bool.or_eq_true, ← mem_targetTuples]
  cases hl : targetTuples s t.controller t.source (trigChoices s t) with
  | nil => simp
  | cons x xs => simp

/-- An ability that waits has a legal pick. -/
theorem trigLegal_exists (s : GameState) (t : PendTrigger) : ∃ ts, trigLegal s t ts = true := by
  by_cases h : targetTuples s t.controller t.source (trigChoices s t) = []
  · exact ⟨[], by simp [trigLegal, h]⟩
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
    have hok := (mem_targetTuples s t.controller t.source (trigChoices s t) x).mp hx
    exact ⟨x, by simp [trigLegal, hok]⟩

/-- The Chain gets the ability: it is used (CR 371), and it goes on top as an object of its own,
controlled by the player, with the objects chosen. -/
def putTrigger (s : GameState) (t : PendTrigger) (ts : List ObjId) : GameState :=
  let s1 := s.modObj t.source (fun o => { o with used := o.used ++ [t.idx] })
  match addObject s1 (abilityItem t.card t.idx t.source t.controller ts) .chain with
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
  · simp [GameState.detect]
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
