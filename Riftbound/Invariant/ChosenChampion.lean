module

public import Riftbound.Rules.Effects
public import Riftbound.Rules.Setup

/-! # Physical identity of a registered Chosen Champion -/

@[expose] public section

namespace Riftbound

/-- Setup records the physical identifier allocated to the registered card. -/
theorem addChosenChampion_registered {db : CardDB} {p : PlayerId} {s next : GameState}
    {card : CardId} (placed : addChosenChampion db p s (some card) = some next) :
    next.chosenChampions[p.n]? = some ⟨s.nextId⟩ := by
  obtain ⟨board, _, rfl⟩ := Option.map_eq_some_iff.mp placed
  exact Std.ExtTreeMap.getElem?_insert_self

/-- A move preserves the card's Chosen Champion status even if it allocates a new object ID. -/
theorem GameState.chosenOf_moveObj {s next : GameState} {id moved : ObjId} {dst : Zone} {pos : Pos}
    (p : PlayerId) (move : moveObj s id dst pos = some (next, moved)) :
    next.chosenOf p moved = s.chosenOf p id := by
  obtain ⟨_, _, spec⟩ := moveObj_spec move
  have unchanged := spec.other
  unfold SameMeta at unchanged
  have registry := congrArg GameState.chosenChampions unchanged
  change next.chosenChampions = s.chosenChampions at registry
  unfold GameState.chosenOf
  rw [registry]
  split
  · rename_i phys _
    have kinds := congrArg (fun kind : Option ObjKind => kind.any (·.phys? == some phys)) spec.kind
    simpa only [GameState.obj?, Option.any_map, Function.comp_apply] using kinds
  · rfl

end Riftbound

end
