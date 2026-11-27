module

public import Riftbound.Tournament.OrderedReferences
public import Riftbound.Rules.Select

/-! # Ordered references in play history (I19) -/

@[expose] public section

namespace Riftbound

/-- Rename the object and timestamp references in a play record. -/
def CardPlay.renameReferences (object : ObjId → ObjId) (stamp : Nat → Nat) (play : CardPlay) :
    CardPlay :=
  { play with object := object play.object, stamp := play.stamp.map stamp }

/-- Rename a turn effect's target and creation timestamp. -/
def TurnFx.renameReferences (object : ObjId → ObjId) (stamp : Nat → Nat) (note : TurnFx) : TurnFx :=
  { note with target := note.target.map object, stamp := stamp note.stamp }

/-- Renaming object targets and timestamps preserves queries for the same kinds of turn
marks, including the company recorded immediately before a simultaneous death. -/
theorem GameState.hasTurnMark_rename {s t : GameState} {id : ObjId} {kind : TurnEffect}
    {seat : Option PlayerId} (object : ObjId → ObjId) (stamp : Nat → Nat)
    (injective : Function.Injective object) (turn : t.turn = s.turn)
    (notes : t.turnFx = s.turnFx.map (TurnFx.renameReferences object stamp)) :
    t.hasTurnMark (object id) kind seat = s.hasTurnMark id kind seat := by
  have sameTarget (target : Option ObjId) :
      (target.map object == some (object id)) = (target == some id) := by
    cases target with
    | none => rfl
    | some prior =>
      apply Bool.eq_iff_iff.mpr
      simp only [Option.map_some, beq_iff_eq, Option.some.injEq, injective.eq_iff]
  unfold GameState.hasTurnMark
  simp only [notes, List.any_map, List.findSome?_map, Function.comp_def, turn,
    TurnFx.renameReferences, sameTarget]

/-- The timestamps that a turn effect can compare against the finalization history. -/
def GameState.playTimestampReferences (s : GameState) : List Nat :=
  s.turnFx.map (·.stamp) ++ s.playLog.filterMap (·.stamp)

/-- Non-strict order is preserved as well, even when two references name the same timestamp. -/
theorem OrderedReferenceBijection.le_iff {left right : List Nat}
    (rename : OrderedReferenceBijection left right) {a b : Nat}
    (aMember : a ∈ left) (bMember : b ∈ left) :
    rename.forward a ≤ rename.forward b ↔ a ≤ b := by
  simpa only [Nat.not_lt] using not_congr (rename.order bMember aMember)

/-- The test used to consume a next-Spell discount survives the simultaneous renaming of
played objects, their finalization timestamps, and the timestamp at which the effect began. -/
theorem GameState.finalizedSince_rename {s t : GameState} {p : PlayerId} {kind : CardType}
    {stamp : Nat} (object : ObjId → ObjId)
    (rename : OrderedReferenceBijection s.playTimestampReferences t.playTimestampReferences)
    (turn : t.turn = s.turn)
    (plays : t.playLog = s.playLog.map (CardPlay.renameReferences object rename.forward))
    (threshold : stamp ∈ s.playTimestampReferences) :
    t.finalizedSince p kind (rename.forward stamp) = s.finalizedSince p kind stamp := by
  unfold GameState.finalizedSince
  rw [plays, List.any_map, turn]
  have same (play : CardPlay) (member : play ∈ s.playLog) :
      (play.stamp.map rename.forward).any (fun date => decide (rename.forward stamp ≤ date)) =
        play.stamp.any (fun date => decide (stamp ≤ date)) := by
    cases date : play.stamp with
    | none => simp
    | some value =>
      have valueMember : value ∈ s.playTimestampReferences :=
        List.mem_append_right _ (List.mem_filterMap.mpr ⟨play, member, date⟩)
      simp [rename.le_iff threshold valueMember]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Function.comp_def, CardPlay.renameReferences]
  constructor <;> rintro ⟨play, member, eligible⟩
  · refine ⟨play, member, ?_⟩
    simpa only [same play member] using eligible
  · refine ⟨play, member, ?_⟩
    simpa only [same play member] using eligible

/-- Counting finalizations never depends on the object references or timestamps. -/
theorem GameState.finalizedCount_rename {s t : GameState} {p : PlayerId}
    (object : ObjId → ObjId) (stamp : Nat → Nat) (turn : t.turn = s.turn)
    (plays : t.playLog = s.playLog.map (CardPlay.renameReferences object stamp)) :
    t.finalizedCount p = s.finalizedCount p := by
  simp [GameState.finalizedCount, plays, turn, List.countP_map, Function.comp_def,
    CardPlay.renameReferences]

private def spellCutNote (s : GameState) (p : PlayerId) (note : TurnFx) : Option Nat :=
  match note.kind with
  | .nextSpellCostMinus amount =>
    if note.turn == s.turn && note.who == p && !s.finalizedSince p .spell note.stamp then
      some amount
    else none
  | _ => none

private theorem GameState.spellCutFx_filterMap (s : GameState) (p : PlayerId) :
    s.spellCutFx p = s.turnFx.filterMap (spellCutNote s p) := by
  unfold GameState.spellCutFx GameState.fxOf
  rw [List.filterMap_map, List.filterMap_filter]
  apply filterMap_congr_mem
  intro note _
  cases kind : note.kind <;> simp [spellCutNote, kind]

/-- The discounts still waiting for this seat's next Spell are the same after renaming, including
the boundary case where a finalization has the same timestamp as an effect's creation. -/
theorem GameState.spellCutFx_rename {s t : GameState} {p : PlayerId}
    (object : ObjId → ObjId)
    (rename : OrderedReferenceBijection s.playTimestampReferences t.playTimestampReferences)
    (turn : t.turn = s.turn)
    (plays : t.playLog = s.playLog.map (CardPlay.renameReferences object rename.forward))
    (notes : t.turnFx = s.turnFx.map (TurnFx.renameReferences object rename.forward)) :
    t.spellCutFx p = s.spellCutFx p := by
  rw [GameState.spellCutFx_filterMap, GameState.spellCutFx_filterMap, notes, List.filterMap_map]
  apply filterMap_congr_mem
  intro note member
  have threshold : note.stamp ∈ s.playTimestampReferences :=
    List.mem_append_left _ (List.mem_map.mpr ⟨note, member, rfl⟩)
  have played := GameState.finalizedSince_rename (p := p) (kind := .spell)
    object rename turn plays threshold
  simp [spellCutNote, TurnFx.renameReferences, turn, played]

/-- Discounts tracked using the number of finalized cards do not read object or timestamp
references. -/
theorem GameState.nextCardDiscount_rename {s t : GameState} {p : PlayerId}
    (object : ObjId → ObjId) (stamp : Nat → Nat) (turn : t.turn = s.turn)
    (plays : t.playLog = s.playLog.map (CardPlay.renameReferences object stamp))
    (notes : t.turnFx = s.turnFx.map (TurnFx.renameReferences object stamp)) :
    t.nextCardDiscount p = s.nextCardDiscount p := by
  unfold GameState.nextCardDiscount
  rw [notes, List.foldl_map, turn, GameState.finalizedCount_rename object stamp turn plays]
  rfl

end Riftbound

end
