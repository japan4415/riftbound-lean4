module

public import Riftbound.Rules.Move
public import Riftbound.State.Event

/-!
# Recycle

Recycle puts a card on the bottom of its owner's deck (CR 417). The owner is the player whose
zone the card goes to; `moveObj` sends a Non-Board destination to the owner's zone (CR 056).
-/

@[expose] public section

namespace Riftbound

/-- Put one object on the bottom of the owner's Main Deck (CR 417). -/
def recycleToMain (s : GameState) (p : PlayerId) (id : ObjId) : Option (GameState × ObjId) :=
  moveObj s id (.player p .mainDeck) .bottom

/-- Recycle the objects in the given order, one after the other. The objects still to be moved keep
their identifiers, because only the moved one is renamed. -/
def recycleAll (p : PlayerId) : GameState → List ObjId → Option GameState
  | s, [] => some s
  | s, id :: ids => do
    let r ← recycleToMain s p id
    recycleAll p r.1 ids

/-- Unfold one step of `recycleAll`. -/
theorem recycleAll_cons {p : PlayerId} {s s' : GameState} {id : ObjId} {ids : List ObjId}
    (h : recycleAll p s (id :: ids) = some s') :
    ∃ r, recycleToMain s p id = some r ∧ recycleAll p r.1 ids = some s' := by
  cases hr : recycleToMain s p id with
  | none => simp [recycleAll, hr] at h
  | some r =>
    refine ⟨r, rfl, ?_⟩
    simpa [recycleAll, hr] using h

/-- Recycling keeps the game well formed. -/
theorem recycleAll_wf (p : PlayerId) :
    ∀ (ids : List ObjId) {s s' : GameState}, s.WF → recycleAll p s ids = some s' → s'.WF
  | [], s, s', hwf, h => by
    rw [show recycleAll p s [] = some s from rfl] at h
    cases h
    exact hwf
  | id :: ids, s, s', hwf, h => by
    obtain ⟨r, hr, h⟩ := recycleAll_cons h
    exact recycleAll_wf p ids (moveObj_wf hwf hr) h

/-- **I1** (recycle). Recycling keeps the physical cards. -/
theorem recycleAll_physIds (p : PlayerId) :
    ∀ (ids : List ObjId) {s s' : GameState}, s.WF → recycleAll p s ids = some s' →
      s'.physIds.Perm s.physIds
  | [], s, s', hwf, h => by
    rw [show recycleAll p s [] = some s from rfl] at h
    cases h
    exact List.Perm.refl _
  | id :: ids, s, s', hwf, h => by
    obtain ⟨r, hr, h⟩ := recycleAll_cons h
    exact (recycleAll_physIds p ids (moveObj_wf hwf hr) h).trans (moveObj_physIds hwf hr)

/-- Recycling does not change the points. -/
theorem recycleAll_points (p : PlayerId) :
    ∀ (ids : List ObjId) {s s' : GameState}, recycleAll p s ids = some s' → s'.points = s.points
  | [], s, s', h => by
    rw [show recycleAll p s [] = some s from rfl] at h
    cases h
    rfl
  | id :: ids, s, s', h => by
    obtain ⟨r, hr, h⟩ := recycleAll_cons h
    obtain ⟨src, d, hs⟩ := moveObj_spec hr
    rw [recycleAll_points p ids h, hs.points]

/-- Recycling does not change the rules, the turn order or the stack of frames. -/
theorem recycleAll_meta (p : PlayerId) :
    ∀ (ids : List ObjId) {s s' : GameState}, recycleAll p s ids = some s' →
      s'.config = s.config ∧ s'.turnOrder = s.turnOrder ∧ s'.pending = s.pending
  | [], s, s', h => by
    rw [show recycleAll p s [] = some s from rfl] at h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  | id :: ids, s, s', h => by
    obtain ⟨r, hr, h⟩ := recycleAll_cons h
    obtain ⟨src, d, hs⟩ := moveObj_spec hr
    obtain ⟨c, t, pe⟩ := recycleAll_meta p ids h
    exact ⟨c.trans hs.config, t.trans hs.turnOrder, pe.trans hs.pending⟩

end Riftbound

end
