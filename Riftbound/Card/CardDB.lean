module

public import Riftbound.Card.CardDef

/-!
# The card database

The set of card definitions the engine runs against (design.md §3, P3). Theorems are stated
for every database that satisfies `CardDB.WF`. The table of custom handlers is added with the
effect IR (milestone M3b).
-/

@[expose] public section

namespace Riftbound

/-- A set of card definitions. -/
structure CardDB where
  /-- The definitions. -/
  cards : List CardDef
deriving Repr

namespace CardDB

/-- Look a card up by its identifier. -/
def find? (db : CardDB) (id : CardId) : Option CardDef :=
  db.cards.find? (fun c => c.id == id)

/-- Well-formedness of a database: identifiers are unique. Only decidable, static conditions
belong here (design.md §7.1). -/
def WF (db : CardDB) : Prop := (db.cards.map (·.id)).Nodup

instance (db : CardDB) : Decidable db.WF := by unfold WF; infer_instance

/-- A found card has the identifier that was asked for. -/
theorem find?_id {db : CardDB} {id : CardId} {c : CardDef} (h : db.find? id = some c) :
    c.id = id := by
  have := List.find?_some h
  simpa using this

/-- A found card belongs to the database. -/
theorem find?_mem {db : CardDB} {id : CardId} {c : CardDef} (h : db.find? id = some c) :
    c ∈ db.cards :=
  List.mem_of_find?_eq_some h

/-- Looking up by identifier in a list with unique identifiers finds each member. -/
theorem find?_of_mem_list {c : CardDef} :
    ∀ (l : List CardDef), (l.map (·.id)).Nodup → c ∈ l →
      l.find? (fun x => x.id == c.id) = some c
  | [], _, h => by simp at h
  | x :: xs, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hx : x.id = c.id
    · have hxc : x = c := by
        rcases List.mem_cons.mp h with h | h
        · exact h.symm
        · exact absurd (List.mem_map.mpr ⟨c, h, hx.symm⟩) hnd.1
      simp [hxc]
    · have hxs : c ∈ xs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd (by rw [h]) hx
        · exact h
      simp [hx, find?_of_mem_list xs hnd.2 hxs]

/-- In a well-formed database, a card is found by its own identifier. -/
theorem find?_of_mem {db : CardDB} (hwf : db.WF) {c : CardDef} (h : c ∈ db.cards) :
    db.find? c.id = some c :=
  find?_of_mem_list db.cards hwf h

end CardDB

end Riftbound

end
