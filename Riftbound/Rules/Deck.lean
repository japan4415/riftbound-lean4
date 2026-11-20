module

public import Riftbound.Card.CardDB
public import Riftbound.Core.Mode

/-!
# Deck building

The legality of a deck under the Core Rules (CR 101-103), written as a decidable predicate.
Each rule is a predicate of its own, so that the tournament formats can reuse the ones that
do not change (`Riftbound.Tournament.DeckLegality`).

The `Decidable` instance of `DeckValid` is the decision procedure: `decide (DeckValid ..)`
is the Boolean check, so no second, hand-written check has to be kept in step.
-/

@[expose] public section

namespace Riftbound

/-- A registered deck: the cards by identifier. -/
structure Deck where
  /-- The Champion Legend (CR 103.2). -/
  legend : CardId
  /-- The Chosen Champion (CR 103.3.a). It is one of the cards of `main`. -/
  chosenChampion : CardId
  /-- The Main Deck, including the Chosen Champion (CR 103.3). -/
  main : List CardId
  /-- The Rune Deck (CR 103.4). -/
  runes : List CardId
  /-- The Battlefields (CR 103.5). -/
  battlefields : List CardId
deriving DecidableEq, Repr

/-- A deck whose identifiers are resolved to card definitions. -/
structure Deck.Resolved where
  /-- The Legend. -/
  legend : CardDef
  /-- The Chosen Champion. -/
  chosenChampion : CardDef
  /-- The Main Deck, including the Chosen Champion. -/
  main : List CardDef
  /-- The Rune Deck. -/
  runes : List CardDef
  /-- The Battlefields. -/
  battlefields : List CardDef
deriving DecidableEq, Repr

/-- Resolve a deck against a database. `none` if some identifier is unknown. -/
def Deck.resolve (db : CardDB) (d : Deck) : Option Deck.Resolved := do
  let legend ← db.find? d.legend
  let chosenChampion ← db.find? d.chosenChampion
  let main ← d.main.mapM db.find?
  let runes ← d.runes.mapM db.find?
  let battlefields ← d.battlefields.mapM db.find?
  pure { legend, chosenChampion, main, runes, battlefields }

namespace Deck

/-- The two cards share a tag. The Chosen Champion and the Signature cards of a deck must
carry the Champion Tag of the Legend (CR 103.3.a, 103.3.d). This is the tag a Legend and its
Champion have in common. -/
def SharesTag (a b : CardDef) : Prop := ∃ t ∈ a.tags, t ∈ b.tags

instance (a b : CardDef) : Decidable (SharesTag a b) := by unfold SharesTag; infer_instance

/-- The Legend is a Legend card (CR 103.2). -/
def LegendOk (r : Resolved) : Prop := r.legend.hasType .legend = true

/-- The Chosen Champion is a Champion Unit that is not a Signature card, has the Champion Tag
of the Legend, and is in the Main Deck (CR 103.3.a). -/
def ChosenOk (r : Resolved) : Prop :=
  r.chosenChampion.IsChosenChampionCandidate ∧ SharesTag r.legend r.chosenChampion ∧
    r.chosenChampion ∈ r.main

/-- The Main Deck holds at least 40 cards (CR 103.3). -/
def MainSizeOk (r : Resolved) : Prop := 40 ≤ r.main.length

/-- Main Deck cards are Units, Gear or Spells (CR 103.3). -/
def MainTypesOk (cards : List CardDef) : Prop :=
  ∀ c ∈ cards, c.hasType .unit = true ∨ c.hasType .gear = true ∨ c.hasType .spell = true

/-- No card name appears more often than its limit (CR 103.3.b, 825). The Chosen Champion is
counted, because it is one of the cards. -/
def CopyLimitOk (cards : List CardDef) : Prop :=
  ∀ c ∈ cards, cards.countP (fun x => x.nameKey == c.nameKey) ≤ c.copyLimit

/-- At most three Signature cards in total, all with the Champion Tag of the Legend
(CR 103.3.d). -/
def SignatureOk (r : Resolved) : Prop :=
  (r.main.filter (·.hasSupertype .signature)).length ≤ 3 ∧
    ∀ c ∈ r.main, c.hasSupertype .signature = true → SharesTag r.legend c

/-- Every domain on a Main Deck or Rune Deck card is in the Domain Identity, which is the
domains of the Legend (CR 103.2.b). A card of a single domain needs that domain; a card of
several domains needs all of them; a card without a domain fits anywhere. -/
def IdentityOk (r : Resolved) : Prop :=
  ∀ c ∈ r.main ++ r.runes, ∀ d ∈ c.domains, d ∈ r.legend.domains

/-- The Rune Deck holds exactly 12 Runes (CR 103.4). -/
def RuneDeckOk (r : Resolved) : Prop :=
  r.runes.length = 12 ∧ ∀ c ∈ r.runes, c.hasType .rune = true

/-- The Battlefields: the number the mode asks for, all Battlefield cards, and with two or
more required, all different names (CR 103.5). -/
def BattlefieldsOk (mode : Mode) (r : Resolved) : Prop :=
  r.battlefields.length = mode.deckBattlefields ∧
    (∀ c ∈ r.battlefields, c.hasType .battlefield = true) ∧
    (2 ≤ mode.deckBattlefields → (r.battlefields.map (·.nameKey)).Nodup)

instance (r : Resolved) : Decidable (LegendOk r) := by unfold LegendOk; infer_instance
instance (r : Resolved) : Decidable (ChosenOk r) := by unfold ChosenOk; infer_instance
instance (r : Resolved) : Decidable (MainSizeOk r) := by unfold MainSizeOk; infer_instance
instance (l : List CardDef) : Decidable (MainTypesOk l) := by unfold MainTypesOk; infer_instance
instance (l : List CardDef) : Decidable (CopyLimitOk l) := by unfold CopyLimitOk; infer_instance
instance (r : Resolved) : Decidable (SignatureOk r) := by unfold SignatureOk; infer_instance
instance (r : Resolved) : Decidable (IdentityOk r) := by unfold IdentityOk; infer_instance
instance (r : Resolved) : Decidable (RuneDeckOk r) := by unfold RuneDeckOk; infer_instance
instance (m : Mode) (r : Resolved) : Decidable (BattlefieldsOk m r) := by
  unfold BattlefieldsOk; infer_instance

/-- A resolved deck is legal under the Core Rules (CR 101-103). -/
def Resolved.Valid (mode : Mode) (r : Resolved) : Prop :=
  LegendOk r ∧ ChosenOk r ∧ MainSizeOk r ∧ MainTypesOk r.main ∧ CopyLimitOk r.main ∧
    SignatureOk r ∧ IdentityOk r ∧ RuneDeckOk r ∧ BattlefieldsOk mode r

instance (mode : Mode) (r : Resolved) : Decidable (r.Valid mode) := by
  unfold Resolved.Valid; infer_instance

end Deck

/-- A deck is legal under the Core Rules (CR 101-103) in `mode`. -/
def DeckValid (db : CardDB) (mode : Mode) (d : Deck) : Prop :=
  match d.resolve db with
  | some r => r.Valid mode
  | none => False

instance (db : CardDB) (mode : Mode) (d : Deck) : Decidable (DeckValid db mode d) := by
  unfold DeckValid
  split <;> infer_instance

/-- A deck with an unknown card is not legal. -/
theorem DeckValid.resolve_isSome {db : CardDB} {mode : Mode} {d : Deck}
    (h : DeckValid db mode d) : (d.resolve db).isSome = true := by
  unfold DeckValid at h
  split at h <;> simp_all

/-- A legal deck is a legal resolved deck. -/
theorem DeckValid.exists_resolved {db : CardDB} {mode : Mode} {d : Deck}
    (h : DeckValid db mode d) : ∃ r, d.resolve db = some r ∧ r.Valid mode := by
  unfold DeckValid at h
  split at h
  · rename_i r hr
    exact ⟨r, hr, h⟩
  · exact h.elim

/-- A legal resolved deck is a legal deck. -/
theorem DeckValid.of_resolved {db : CardDB} {mode : Mode} {d : Deck} {r : Deck.Resolved}
    (hr : d.resolve db = some r) (h : r.Valid mode) : DeckValid db mode d := by
  unfold DeckValid
  rw [hr]
  exact h

namespace Deck.Resolved

/-- A legal deck has at least 40 Main Deck cards (CR 103.3). -/
theorem main_length_ge {mode : Mode} {r : Resolved} (h : r.Valid mode) : 40 ≤ r.main.length :=
  h.2.2.1

/-- A legal deck has exactly 12 Runes (CR 103.4). -/
theorem runes_length {mode : Mode} {r : Resolved} (h : r.Valid mode) : r.runes.length = 12 :=
  h.2.2.2.2.2.2.2.1.1

/-- A legal deck contains its Chosen Champion (CR 103.3.a). -/
theorem chosenChampion_mem {mode : Mode} {r : Resolved} (h : r.Valid mode) :
    r.chosenChampion ∈ r.main :=
  h.2.1.2.2

/-- A card that is not Unique appears at most three times (CR 103.3.b). -/
theorem count_le_three {mode : Mode} {r : Resolved} (h : r.Valid mode) {c : CardDef}
    (hc : c ∈ r.main) (hu : c.hasKeyword .unique = false) :
    r.main.countP (fun x => x.nameKey == c.nameKey) ≤ 3 := by
  have := h.2.2.2.2.1 c hc
  rwa [CardDef.copyLimit_of_not_unique hu] at this

/-- A Unique card appears at most once (CR 825). -/
theorem count_le_one_of_unique {mode : Mode} {r : Resolved} (h : r.Valid mode) {c : CardDef}
    (hc : c ∈ r.main) (hu : c.hasKeyword .unique = true) :
    r.main.countP (fun x => x.nameKey == c.nameKey) ≤ 1 := by
  have := h.2.2.2.2.1 c hc
  rwa [CardDef.copyLimit_of_unique hu] at this

end Deck.Resolved

end Riftbound

end
