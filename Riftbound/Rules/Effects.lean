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

namespace GameState

/-- The players of the game, in seat order. -/
def players (s : GameState) : List PlayerId := (List.range s.playerCount).map (fun i => ⟨i⟩)

/-- The player who gets priority after `p`: the next one in the turn order (CR 311). -/
def nextPlayer (s : GameState) (p : PlayerId) : PlayerId :=
  match s.turnOrder.idxOf? p with
  | some i => s.turnOrder.getD ((i + 1) % s.turnOrder.length) p
  | none => p

end GameState

/-- The players a selector of players names, seen by `self`. `none` if it cannot be known yet. -/
def PlayerSel.resolve (s : GameState) (self : PlayerId) : PlayerSel → Option (List PlayerId)
  | .you => some [self]
  | .opponent => (s.players.filter (· ≠ self)).head?.map (fun o => [o])
  | .eachPlayer => some s.players
  | .eachOpponent => some (s.players.filter (· ≠ self))
  | .chosen _ => none
  | .eventPlayer => none

/-- The number an amount stands for, if it can be computed from the variables alone. -/
def Amount.eval (env : Env) : Amount → Option Nat
  | .const n => some n
  | .var v =>
    match env.lookup v with
    | some (.int i) => some i.toNat
    | _ => none
  | .add a b => do pure ((← Amount.eval env a) + (← Amount.eval env b))
  | .sub a b => do pure ((← Amount.eval env a) - (← Amount.eval env b))
  | .mul a b => do pure ((← Amount.eval env a) * (← Amount.eval env b))
  | .min a b => do pure (Nat.min (← Amount.eval env a) (← Amount.eval env b))
  | .max a b => do pure (Nat.max (← Amount.eval env a) (← Amount.eval env b))
  | _ => none

/-- Do the first effect of `e :: es`: the frames that replace the `run` frame, and the events. An
instruction that cannot be done is skipped (design.md §7.1). -/
def runEffect (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : List Frame × List Event :=
  let skip : List Frame × List Event := ([.run p src env es], [Event.skipped src])
  match e with
  | .nop => ([.run p src env es], [])
  | .seq l => ([.run p src env (l.append es)], [])
  | .bind v a e' =>
    match a.eval env with
    | some k => ([.run p src (env.bind v (.int k)) (.cons e' .nil), .run p src env es], [])
    | none => skip
  | .prim (.draw sel n) =>
    match sel.resolve s p, n.eval env with
    | some ps, some k => (ps.map (fun q => Frame.draw q k) ++ [.run p src env es], [])
    | _, _ => skip
  | _ => skip

/-- The frames that resolve the item on top of the Chain (CR 340): run its effect, then put it in
the Trash. Nothing to resolve when the Chain is empty. -/
def resolveFrames (s : GameState) (rest : List Frame) : List Frame :=
  match s.zone .chain with
  | item :: _ =>
    match s.obj? item, s.cardDef? item with
    | some o, some d =>
      .run o.controller item Env.empty
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
        moveObj s item (.player o.owner .trash) = some (s2, id') ∧ (finishItem s item).1 = s2 := by
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
