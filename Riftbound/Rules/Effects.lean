module

public import Riftbound.Rules.Play

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
    match moveObj s id (.player o.owner k) with
    | some r => (r.1, [Event.moved id r.2 (.player o.owner k)])
    | none => (s, [])
  | none => (s, [])

/-- Sending an object to a zone is a safe change. -/
theorem sendObj_safe (k : ZoneKind) (s : GameState) (id : ObjId) :
    Safe s (sendObj k s id).1 := by
  unfold sendObj
  split
  · split
    · rename_i r hm
      exact Safe.moveObj hm
    · exact Safe.refl s
  · exact Safe.refl s

/-- Kill an object: it goes to its owner's Trash. -/
def killObj (s : GameState) (id : ObjId) : GameState × List Event := sendObj .trash s id

/-- Killing an object is a safe change. -/
theorem killObj_safe (s : GameState) (id : ObjId) : Safe s (killObj s id).1 :=
  sendObj_safe .trash s id

/-- Deal `n` damage to an object (CR 142). An object whose damage reaches its Might is killed at
once. That is the state-based check of the cleanup (CR 417), done early: the cleanup itself comes
with combat (roadmap.md, M5). -/
def dealObj (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    let s1 := s.modObj id (fun o => { o with damage := o.damage + n })
    let ev := [Event.damaged id n]
    if 0 < o.damage + n && (s.mightOf id).any (fun m => decide (Might.eff m ≤ o.damage + n)) then
      let r := killObj s1 id
      (r.1, ev ++ r.2)
    else (s1, ev)
  | none => (s, [])

/-- Dealing damage is a safe change. -/
theorem dealObj_safe (n : Nat) (s : GameState) (id : ObjId) : Safe s (dealObj n s id).1 := by
  unfold dealObj
  split
  · rename_i o ho
    have h1 : Safe s (s.modObj id (fun o => { o with damage := o.damage + n })) :=
      Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
    split
    · exact h1.trans (killObj_safe _ id)
    · exact h1
  · exact Safe.refl s

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
  | some _ =>
    (s.modObj id (fun o => { o with exhausted := b }),
      [if b then Event.exhausted id else Event.readied id])
  | none => (s, [])

/-- Readying or exhausting is a safe change. -/
theorem setExhausted_safe (b : Bool) (s : GameState) (id : ObjId) :
    Safe s (setExhausted b s id).1 := by
  unfold setExhausted
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

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

/-- Do a game action that changes objects: the new state and the events. `none` if the action is
not understood yet, or what it names cannot be found. -/
def applyPrim (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) :
    Prim → Option (GameState × List Event)
  | .deal sel n => (n.evalS s p src env).bind (fun k => onSelected s p src env sel (dealObj k))
  | .heal sel n => (n.evalS s p src env).bind (fun k => onSelected s p src env sel (healOne k))
  | .kill sel => onSelected s p src env sel killObj
  | .ready sel => onSelected s p src env sel (setExhausted false)
  | .exhaust sel => onSelected s p src env sel (setExhausted true)
  | .banish sel => onSelected s p src env sel (sendObj .banishment)
  | .returnToHand sel => onSelected s p src env sel (sendObj .hand)
  | _ => none

/-- An action that is done is a safe change. -/
theorem applyPrim_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {pr : Prim}
    {r : GameState × List Event} (h : applyPrim s p src env pr = some r) : Safe s r.1 := by
  cases pr with
  | deal sel n =>
    simp only [applyPrim] at h
    cases hn : n.evalS s p src env with
    | none => simp [hn] at h
    | some k =>
      simp only [hn, Option.bind_some] at h
      exact onSelected_safe (dealObj_safe k) h
  | heal sel n =>
    simp only [applyPrim] at h
    cases hn : n.evalS s p src env with
    | none => simp [hn] at h
    | some k =>
      simp only [hn, Option.bind_some] at h
      exact onSelected_safe (healOne_safe k) h
  | kill sel => exact onSelected_safe killObj_safe h
  | ready sel => exact onSelected_safe (setExhausted_safe false) h
  | exhaust sel => exact onSelected_safe (setExhausted_safe true) h
  | banish sel => exact onSelected_safe (sendObj_safe .banishment) h
  | returnToHand sel => exact onSelected_safe (sendObj_safe .hand) h
  | _ => simp [applyPrim] at h

/-- Do the first effect of `e :: es`: the new state, the frames that replace the `run` frame, and
the events. An instruction that cannot be done is skipped (design.md §7.1). -/
def runEffect (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : GameState × List Frame × List Event :=
  let skip : GameState × List Frame × List Event := (s, [.run p src env es], [Event.skipped src])
  match e with
  | .nop => (s, [.run p src env es], [])
  | .seq l => (s, [.run p src env (l.append es)], [])
  | .bind v a e' =>
    match a.evalS s p src env with
    | some k => (s, [.run p src (env.bind v (.int k)) (.cons e' .nil), .run p src env es], [])
    | none => skip
  | .ifThen c t e' =>
    match c.eval s p src env with
    | some b => (s, [.run p src env (.cons (if b then t else e') es)], [])
    | none => skip
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
  | .prim (.draw sel n) =>
    match sel.resolve s p, n.evalS s p src env with
    | some ps, some k => (s, ps.map (fun q => Frame.draw q k) ++ [.run p src env es], [])
    | _, _ => skip
  | .prim pr =>
    match applyPrim s p src env pr with
    | some r => (r.1, [.run p src env es], r.2)
    | none => skip
  | _ => skip

/-- Doing an effect is a safe change of the state. -/
theorem runEffect_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : Safe s (runEffect s p src env e es).1 := by
  unfold runEffect
  split <;> (try split) <;> first
    | exact Safe.refl s
    | (rename_i r hr; exact applyPrim_safe hr)

/-- The frames that resolve the item on top of the Chain (CR 340): run its effect, then put it in
the Trash. Nothing to resolve when the Chain is empty. -/
def resolveFrames (s : GameState) (rest : List Frame) : List Frame :=
  match s.zone .chain with
  | item :: _ =>
    match s.obj? item, s.cardDef? item with
    | some o, some d =>
      .run o.controller item { slots := o.targets.map Value.obj }
        (match d.spellEffect with
          | some e => .cons e.body .nil
          | none => .nil) :: .finishSpell item :: rest
    | _, _ => .finishSpell item :: rest
  | [] => rest

/-- A Spell has resolved: it goes from the Chain to its owner's Trash (CR 359.3.d). Nothing
happens if it is no longer on the Chain. -/
def finishItem (s : GameState) (item : ObjId) : GameState × List Event :=
  match s.obj? item with
  | some o =>
    if item ∈ s.zone .chain then
      match moveObj s item (.player o.owner .trash) with
      | some r => (r.1, [Event.moved item r.2 (.player o.owner .trash)])
      | none => (s, [])
    else (s, [])
  | none => (s, [])

/-- Finishing an item either changes nothing, or moves it from the Chain to its owner's Trash. -/
theorem finishItem_cases (s : GameState) (item : ObjId) :
    (finishItem s item).1 = s ∨
      ∃ o s2 id', s.obj? item = some o ∧ item ∈ s.zone .chain ∧
        moveObj s item (.player o.owner .trash) = some (s2, id') ∧
          (finishItem s item).1 = s2 := by
  by_cases hex : ∃ o r, s.obj? item = some o ∧ item ∈ s.zone .chain ∧
      moveObj s item (.player o.owner .trash) = some r
  · obtain ⟨o, r, ho, hc, hm⟩ := hex
    right
    refine ⟨o, r.1, r.2, ho, hc, hm, ?_⟩
    simp [finishItem, ho, hc, hm]
  · left
    unfold finishItem
    split
    · rename_i o ho
      split
      · rename_i hc
        split
        · rename_i r hm
          exact absurd ⟨o, r, ho, hc, hm⟩ hex
        · rfl
      · rfl
    · rfl

/-- Finishing an item keeps the game well formed. -/
theorem finishItem_wf {s : GameState} (hwf : s.WF) (item : ObjId) : (finishItem s item).1.WF := by
  rcases finishItem_cases s item with h | ⟨o, s2, id', -, -, hm, h⟩
  · rw [h]; exact hwf
  · rw [h]; exact moveObj_wf hwf hm

/-- Finishing an item keeps the physical cards. -/
theorem finishItem_physIds {s : GameState} (hwf : s.WF) (item : ObjId) :
    (finishItem s item).1.physIds.Perm s.physIds := by
  rcases finishItem_cases s item with h | ⟨o, s2, id', -, -, hm, h⟩
  · rw [h]
  · rw [h]; exact moveObj_physIds hwf hm

/-- Finishing an item keeps `OwnerOk`. -/
theorem finishItem_ownerOk {s : GameState} (hwf : s.WF) (hown : s.OwnerOk) (item : ObjId) :
    (finishItem s item).1.OwnerOk := by
  rcases finishItem_cases s item with h | ⟨o, s2, id', -, -, hm, h⟩
  · rw [h]; exact hown
  · rw [h]; exact moveObj_ownerOk hwf hown hm

/-- Finishing an item changes only the zones, the objects and the counters. -/
theorem finishItem_sameMeta (s : GameState) (item : ObjId) : SameMeta s (finishItem s item).1 := by
  rcases finishItem_cases s item with h | ⟨o, s2, id', -, -, hm, h⟩
  · rw [h]; exact SameMeta.refl s
  · rw [h]; exact (moveObj_spec hm).choose_spec.choose_spec.other

/-- Resolving the Chain puts some frames on top of the stack below. -/
theorem resolveFrames_eq (s : GameState) (rest : List Frame) :
    ∃ pre, resolveFrames s rest = pre ++ rest ∧ ∀ g ∈ pre, g.isPlay = true := by
  unfold resolveFrames
  split
  · split
    · exact ⟨[.run _ _ _ _, .finishSpell _], rfl, by simp [Frame.isPlay]⟩
    · exact ⟨[.finishSpell _], rfl, by simp [Frame.isPlay]⟩
  · exact ⟨[], rfl, by simp⟩

end Riftbound

end
