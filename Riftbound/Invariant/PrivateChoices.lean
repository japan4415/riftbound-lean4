module

public import Riftbound.Engine.Step

/-! # Privacy of hand-only decisions (I10) -/

@[expose] public section

namespace Riftbound

/-- Translate a hand choice when the same hand slots carry different engine identifiers. -/
def Action.renameHandPick (rename : ObjId → ObjId) (action : Action) : Action :=
  match action.kind with
  | .mulliganPick id => { action with kind := .mulliganPick (rename id) }
  | .discardPick id => { action with kind := .discardPick (rename id) }
  | _ => action

/-- A mulligan uses only its public pick count and the acting seat's own hand. With those
held fixed up to renaming and reordering, the same answers are legal in either state. -/
theorem legalFrameActions_mulligan_rename {s t : GameState} {p : PlayerId} {count : Nat}
    {tailS tailT : List Frame} (rename : ObjId → ObjId)
    (hs : s.pending = .mulligan p count :: tailS) (ht : t.pending = .mulligan p count :: tailT)
    (hand : (t.zone (.player p .hand)).Perm ((s.zone (.player p .hand)).map rename)) :
    (legalFrameActions t).Perm ((legalFrameActions s).map (Action.renameHandPick rename)) := by
  by_cases h : count < 2
  · have picks := hand.map (fun c => Action.mk (.player p) (.mulliganPick c))
    simpa [legalFrameActions, hs, ht, h, List.map_map, Function.comp_def, Action.renameHandPick]
      using picks.append_right [Action.mk (.player p) .mulliganDone]
  · simp [legalFrameActions, hs, ht, h, Action.renameHandPick]

/-- The ordinary discard decision also depends only on its count and the acting seat's hand. -/
theorem legalFrameActions_discard_rename {s t : GameState} {p : PlayerId} {count : Nat}
    {tailS tailT : List Frame} (rename : ObjId → ObjId)
    (hs : s.pending = .discard p count :: tailS) (ht : t.pending = .discard p count :: tailT)
    (hand : (t.zone (.player p .hand)).Perm ((s.zone (.player p .hand)).map rename)) :
    (legalFrameActions t).Perm ((legalFrameActions s).map (Action.renameHandPick rename)) := by
  have empty : t.zone (.player p .hand) = [] ↔ s.zone (.player p .hand) = [] := by
    simp [← List.length_eq_zero_iff, hand.length_eq]
  by_cases h : s.zone (.player p .hand) = [] ∨ count = 0
  · simp [legalFrameActions, hs, ht, empty, h, Action.renameHandPick]
  · have picks := hand.map (fun c => Action.mk (.player p) (.discardPick c))
    simpa [legalFrameActions, hs, ht, empty, h, List.map_map, Function.comp_def, Action.renameHandPick]
      using picks

end Riftbound

end
