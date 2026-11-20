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

/-- Advance one work frame by one step. `none` if the top frame is not work. -/
def microStep (s : GameState) : Option (GameState × List Event) :=
  match s.pending with
  | .setupHands :: rest =>
    some ({ s with pending := s.turnOrder.map (fun p => Frame.draw p 4) ++
                                s.turnOrder.map (fun p => Frame.mulligan p 0) ++ rest }, [])
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
    some ({ s with turnOrder := l, pending := .setupHands :: rest }, [])
  | .mulligan p n :: rest, .mulliganPick c =>
    (moveObj s c (.player p .setAside)).map
      (fun r => ({ r.1 with pending := .mulligan p (n + 1) :: rest },
                 [Event.moved c r.2 (.player p .setAside)]))
  | .mulligan p n :: rest, .mulliganDone =>
    match n with
    | 0 => some ({ s with pending := rest }, [])
    | k + 1 => some ({ s with pending := .draw p (k + 1) :: .chanceRecycle p :: rest }, [])
  | .chanceRecycle p :: rest, .arrange l =>
    (recycleAll p s l).map (fun s' => ({ s' with pending := rest }, []))
  | .chanceBurnOut p :: rest, .arrange l =>
    (recycleAll p s l).map
      (fun s' => ({ s' with pending := .chooseBurnOut p :: rest }, [Event.burnedOut p]))
  | .chooseBurnOut _ :: rest, .burnOutTarget opp =>
    some ({ s.gainPoints opp 1 with pending := rest }, [Event.pointsGained opp 1])
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
