module

public import Riftbound.Rules.Chain

/-!
# Triggered abilities

A triggered ability fires when something it waits for happens (CR 382-385). The step that did it
leaves events; `detect` reads them and names the abilities that fire. They wait on the stack, in a
`triggers` frame beneath the work that is still to do, until a player would next receive priority
(CR 383.1); then each goes on the Chain as an object of its own, the turn player's first (CR 383.3).

This is the first model of triggers. The abilities that fire are those with the object itself as
subject, no condition, every time, and no choices (no targets). The player does not choose the
order of abilities of one player (CR 383.3.d): they go on the Chain in the order of the events and
of the objects. Triggers at a point of the turn and triggers of other objects are later.
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
time, and no choices. -/
def trigOk (t : Trigger) (body : EffectDef) : Bool :=
  t.subject == .self && t.condition == .always && t.occurrence == .every && body.choices.isEmpty

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

/-- The Chain gets the ability: it is used (CR 371), and it goes on top as an object of its own,
controlled by the player. -/
def putTrigger (s : GameState) (t : PendTrigger) : GameState :=
  let s1 := s.modObj t.source (fun o => { o with used := o.used ++ [t.idx] })
  match addObject s1 (abilityItem t.card t.idx t.source t.controller []) .chain with
  | some r => r.1
  | none => s1

/-- Put all the abilities on the Chain, in order. -/
def putAll (s : GameState) : List PendTrigger → GameState
  | [] => s
  | t :: ts => putAll (putTrigger s t) ts

/-- The frames to put beneath the work after the abilities have gone on the Chain: the turn player
gets priority with the Chain, unless that is already so (CR 340). -/
def triggerFrames (s : GameState) (rest : List Frame) : List Frame :=
  match rest with
  | .chainPass .. :: _ => []
  | _ => if (s.zone .chain).isEmpty then [] else [.chainPass (s.active.getD ⟨0⟩) 0]

/-- Putting one ability on the Chain is a safe change. -/
theorem putTrigger_safe (s : GameState) (t : PendTrigger) : Safe s (putTrigger s t) := by
  have h1 : Safe s (s.modObj t.source (fun o => { o with used := o.used ++ [t.idx] })) :=
    Safe.modObj s t.source (fun _ => rfl) (fun _ => rfl)
  unfold putTrigger
  dsimp only
  split
  · rename_i r hr
    refine h1.trans ⟨fun hwf => addObject_wf hwf hr, fun hwf => addObject_physIds hwf hr rfl,
      fun hwf hown => addObject_ownerOk hwf hown hr, addObject_sameMeta hr⟩
  · exact h1

/-- Putting all the abilities on the Chain is a safe change. -/
theorem putAll_safe : ∀ (ts : List PendTrigger) (s : GameState), Safe s (putAll s ts)
  | [], s => Safe.refl s
  | t :: ts, s => (putTrigger_safe s t).trans (putAll_safe ts _)

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

end Riftbound

end
