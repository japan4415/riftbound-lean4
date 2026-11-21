module

public import Riftbound.Rules.Reorder
public import Riftbound.Rules.Setup
public import Riftbound.Rules.Objects
public import Riftbound.Rules.Resources
public import Riftbound.Rules.Play
public import Riftbound.Rules.Effects
public import Riftbound.Rules.Actions.Channel
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

/-- The player whose turn it is: the first player has turn 0, then the turn order goes round
(CR 118, 301). -/
def GameState.nextTurnPlayer (s : GameState) : PlayerId :=
  s.turnOrder.getD (s.turn % s.playerCount) ⟨0⟩

/-- The frames of a turn up to the Main Phase, where the turn player has priority (CR 315-316). -/
def turnFrames (tp : PlayerId) : List Frame :=
  [.phase .awaken, .phase .beginning, .phase .channel, .phase .draw, .phase .main, .priority tp]

/-- How many Runes the Channel Phase channels: two (CR 315.3), and one more for the second player
on their first turn in a 1v1 game (CR 487.7). -/
def GameState.channelCount (s : GameState) : Nat :=
  if s.playerCount = 2 ∧ s.turn = 2 then 3 else 2

/-- Advance one work frame by one step. `none` if the top frame is not work. -/
def microStep (s : GameState) : Option (GameState × List Event) :=
  match s.pending with
  | .setupHands :: rest =>
    some ({ s with pending := s.turnOrder.map (fun p => Frame.draw p 4) ++
                                s.turnOrder.map (fun p => Frame.mulligan p 0) ++
                                [Frame.beginTurn] ++ rest }, [])
  | .beginTurn :: rest =>
    let tp := s.nextTurnPlayer
    some ({ s with pending := turnFrames tp ++ rest, turn := s.turn + 1, active := some tp }, [])
  | .phase .awaken :: rest =>
    let s1 := s.mapObjects (readyOf (s.active.getD ⟨0⟩))
    some ({ s1 with phase := .awaken, pending := rest }, [])
  | .phase .channel :: rest =>
    let r := channel (s.active.getD ⟨0⟩) s.channelCount s
    some ({ r.1 with phase := .channel, pending := rest }, r.2)
  | .phase .draw :: rest =>
    some ({ s with phase := .draw, pending := .draw (s.active.getD ⟨0⟩) 1 :: rest }, [])
  | .phase .ending :: rest =>
    some ({ s.mapObjects healObj with phase := .ending, pending := rest, pools := {} }, [])
  | .phase .setup :: rest => some ({ s with pending := rest }, [])
  | .phase .beginning :: rest => some ({ s with phase := .beginning, pending := rest }, [])
  | .phase .main :: rest => some ({ s with phase := .main, pending := rest, pools := {} }, [])
  | .draw _ 0 :: rest => some ({ s with pending := rest }, [])
  | .draw p (n + 1) :: rest =>
    match drawOne s p with
    | some (s', es) => some ({ s' with pending := .draw p n :: rest }, es)
    | none => some ({ s with pending := .chanceBurnOut p :: .draw p (n + 1) :: rest }, [])
  | .resolveChain :: rest => some ({ s with pending := resolveFrames s rest }, [])
  | .run _ _ _ .nil :: rest => some ({ s with pending := rest }, [])
  | .run p src env (.cons e es) :: rest =>
    some ({ (runEffect s p src env e es).1 with
              pending := (runEffect s p src env e es).2.1 ++ rest },
      (runEffect s p src env e es).2.2)
  | .finishSpell item :: rest =>
    some ({ (finishItem s item).1 with pending := rest }, (finishItem s item).2)
  | _ => none

/-- The player who wins when `p` concedes a 1v1 game (CR 651.1). -/
def otherPlayer (p : PlayerId) : PlayerId := ⟨1 - p.n⟩

/-- Apply an answer to the decision frame on top of the stack. The answer is assumed to be legal;
`none` if it does not fit the frame or a primitive cannot be done. -/
def applyFrame (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match s.pending, a.kind with
  | .priority _ :: rest, .pass =>
    some ({ s with pending := .phase .ending :: .beginTurn :: rest }, [])
  | .priority p :: _, .runeAbility c ab => applyRune s p c ab
  | .priority p :: rest, .playCard c pay ts => applyPlayCard s p c pay ts rest
  | .chainPass p n :: rest, .pass =>
    if n + 1 < s.playerCount then
      some ({ s with pending := .chainPass (s.nextPlayer p) (n + 1) :: rest }, [])
    else some ({ s with pending := .resolveChain :: rest }, [])
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

/-- Apply an answer: a concession ends the game at any time (CR 649-651), any other answer goes to
the decision frame on top of the stack. -/
def applyAction (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match a.kind with
  | .concede =>
    match a.actor with
    | .player p => some ({ s with result := some (.won [otherPlayer p]), pending := [] }, [])
    | _ => none
  | _ => applyFrame s a

/-- An answer that is not a concession goes to the frame on top of the stack. -/
theorem applyAction_of_ne {s : GameState} {a : Action} (hk : a.kind ≠ .concede) :
    applyAction s a = applyFrame s a := by
  unfold applyAction
  split
  · exact absurd ‹a.kind = .concede› hk
  · rfl

/-- A concession by a player ends the game: the other player wins, and nothing is left to answer
(CR 651.1). -/
theorem applyAction_concede {s : GameState} {a : Action} {p : PlayerId} (hk : a.kind = .concede)
    (hp : a.actor = .player p) :
    applyAction s a =
      some ({ s with result := some (.won [otherPlayer p]), pending := [] }, []) := by
  unfold applyAction
  rw [hk]
  simp [hp]

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
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.wf_mapObjects hwf _).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (channel_wf _ _ hwf).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.wf_mapObjects hwf _).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
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
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((runEffect_safe _ _ _ _ _ _).wf hwf).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (finishItem_wf hwf _).congr rfl rfl rfl rfl
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
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.physIds_mapObjects s (fun o => readyOf_kind _ o)).symm ▸ List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hp := channel_physIds (s.active.getD ⟨0⟩) s.channelCount hwf
    exact hp
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.physIds_mapObjects s (fun o => healObj_kind o)).symm ▸ List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
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
      have hp' := drawOne_physIds hwf hd
      rw [← h1]
      exact hp'
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (runEffect_safe _ _ _ _ _ _).phys hwf
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact finishItem_physIds hwf _
  · exact absurd h (by simp)

end Riftbound

end
