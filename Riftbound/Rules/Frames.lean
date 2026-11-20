module

public import Riftbound.Rules.Reorder
public import Riftbound.Rules.Setup
public import Riftbound.Rules.Actions.Draw
public import Riftbound.Rules.Actions.Recycle
public import Riftbound.Rules.Actions.BurnOut

/-!
# Working through the frames

`microStep` advances one work frame by one step. `applyAction` applies the answer to the
decision frame on top of the stack. Neither checks that the answer is legal: that is `Legal`'s job
(`Riftbound.Spec.Legal`), and `step` asks it first (design.md §6.3).
-/

@[expose] public section

namespace Riftbound

/-- Move several objects to one zone, in order. Returns the new identifiers, in the same
order. -/
def moveAll (dst : Zone) (pos : Pos) : GameState → List ObjId →
    Option (GameState × List ObjId)
  | s, [] => some (s, [])
  | s, id :: ids => do
    let r ← moveObj s id dst pos
    let r2 ← moveAll dst pos r.1 ids
    pure (r2.1, r.2 :: r2.2)

/-- Unfold one step of `moveAll`. -/
theorem moveAll_cons {dst : Zone} {pos : Pos} {s s' : GameState} {id : ObjId}
    {ids : List ObjId} {news : List ObjId} (h : moveAll dst pos s (id :: ids) = some (s', news)) :
    ∃ r r2, moveObj s id dst pos = some r ∧ moveAll dst pos r.1 ids = some r2 ∧
      s' = r2.1 := by
  cases hr : moveObj s id dst pos with
  | none => simp [moveAll, hr] at h
  | some r =>
    cases hr2 : moveAll dst pos r.1 ids with
    | none => simp [moveAll, hr, hr2] at h
    | some r2 =>
      refine ⟨r, r2, rfl, hr2, ?_⟩
      simp [moveAll, hr, hr2] at h
      exact h.1.symm

/-- Moving several objects keeps the game well formed. -/
theorem moveAll_wf (dst : Zone) (pos : Pos) :
    ∀ (ids : List ObjId) {s s' : GameState} {news : List ObjId}, s.WF →
      moveAll dst pos s ids = some (s', news) → s'.WF
  | [], s, s', news, hwf, h => by
    rw [show moveAll dst pos s [] = some (s, []) from rfl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hwf
  | id :: ids, s, s', news, hwf, h => by
    obtain ⟨r, r2, hr, hr2, rfl⟩ := moveAll_cons h
    exact moveAll_wf dst pos ids (moveObj_wf hwf hr) hr2

/-- **I1** (moving several objects). -/
theorem moveAll_physIds (dst : Zone) (pos : Pos) :
    ∀ (ids : List ObjId) {s s' : GameState} {news : List ObjId}, s.WF →
      moveAll dst pos s ids = some (s', news) → s'.physIds.Perm s.physIds
  | [], s, s', news, hwf, h => by
    rw [show moveAll dst pos s [] = some (s, []) from rfl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  | id :: ids, s, s', news, hwf, h => by
    obtain ⟨r, r2, hr, hr2, rfl⟩ := moveAll_cons h
    exact (moveAll_physIds dst pos ids (moveObj_wf hwf hr) hr2).trans (moveObj_physIds hwf hr)

/-- Advance one work frame by one step. `none` if the top frame is not work. -/
def microStep (s : GameState) : Option (GameState × List Event) :=
  match s.pending with
  | .setupHands :: rest =>
    some ({ s with pending := s.turnOrder.map (fun p => Frame.draw p 4) ++
                                s.turnOrder.map (fun p => Frame.mulligan p []) ++ rest }, [])
  | .draw _ 0 :: rest => some ({ s with pending := rest }, [])
  | .draw p (n + 1) :: rest =>
    match drawOne s p with
    | some (s', es) => some ({ s' with pending := .draw p n :: rest }, es)
    | none => some ({ s with pending := .chanceBurnOut p :: .draw p (n + 1) :: rest }, [])
  | _ => none

/-- Apply an answer to the decision frame on top of the stack. The answer is assumed to be legal;
`none` if it does not fit the frame or a primitive cannot be done. -/
def applyAction (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match s.pending, a.kind with
  | .chanceShuffle z :: rest, .arrange l => some ({ s.reorder z l with pending := rest }, [])
  | .chanceBattlefield p :: rest, .pick i =>
    match (s.zone (.player p .outOfGame))[i]? with
    | some id =>
      (moveObj s id .battlefieldZone).map
        (fun r => ({ r.1 with pending := rest }, [Event.moved id r.2 .battlefieldZone]))
    | none => none
  | .chanceTurnOrder :: rest, .arrangePlayers l =>
    some ({ s with turnOrder := l, pending := rest }, [])
  | .mulligan p chosen :: rest, .mulliganPick c =>
    some ({ s with pending := .mulligan p (chosen ++ [c]) :: rest }, [])
  | .mulligan p chosen :: rest, .mulliganDone =>
    match chosen with
    | [] => some ({ s with pending := rest }, [])
    | _ :: _ =>
      (moveAll (.player p .setAside) .top s chosen).map
        (fun r => ({ r.1 with pending := .draw p chosen.length :: .chanceRecycle p r.2 :: rest },
                   []))
  | .chanceRecycle p _ :: rest, .arrange l =>
    (recycleAll p s l).map (fun s' => ({ s' with pending := rest }, []))
  | .chanceBurnOut p :: rest, .arrange l =>
    some ({ s with pending := .chooseBurnOut p l :: rest }, [])
  | .chooseBurnOut p order :: rest, .burnOutTarget opp =>
    (burnOut s p order opp).map (fun r => ({ r.1 with pending := rest }, r.2))
  | _, _ => none

/-- A step of work keeps the game well formed. -/
theorem microStep_wf {s s' : GameState} {es : List Event} (hwf : s.WF)
    (h : microStep s = some (s', es)) : s'.WF := by
  unfold microStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · rename_i p n rest hp
    split at h
    · rename_i s1 es1 hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr (drawOne_wf hwf hd) rfl rfl rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr hwf rfl rfl rfl rfl
  · exact absurd h (by simp)

/-- **I1** (work). A step of work keeps the physical cards. -/
theorem microStep_physIds {s s' : GameState} {es : List Event} (hwf : s.WF)
    (h : microStep s = some (s', es)) : s'.physIds.Perm s.physIds := by
  unfold microStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · rename_i p n rest hp
    split at h
    · rename_i s1 es1 hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      have hp := drawOne_physIds hwf hd
      rw [← h1]
      exact hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
  · exact absurd h (by simp)

end Riftbound

end
