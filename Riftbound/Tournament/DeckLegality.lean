module

public import Riftbound.Rules.Deck
public import Riftbound.Tournament.Format

/-!
# Deck legality in the tournament formats

Constructed (TR 402, 403, 601) and Limited (TR 602). A Constructed deck is also a legal deck
under the Core Rules (`constructedDeckValid_deckValid`, theorem I13 in roadmap.md).

The rules of Sealed and Draft are taken from tournament-model.md §2.2 and simplified in two
places that are listed in tournament-model.md §7: the Domain Identity is any three domains
(the variant of one domain plus the Legend's is left out), and the Main Deck count includes the
Chosen Champion.
-/

@[expose] public section

namespace Riftbound

/-- Which cards a format allows: the legal sets and the banned cards (TR 601.2-3, 602.1). -/
structure LegalityEnv where
  /-- The sets whose cards are legal. -/
  legalSets : List SetCode
  /-- Banned cards. -/
  banned : List CardId
deriving DecidableEq, Repr

/-- A card is legal in Constructed: not banned, and printed in a legal set (TR 601.2-3). -/
def CardLegal (env : LegalityEnv) (c : CardDef) : Prop :=
  c.id ∉ env.banned ∧ ∃ s ∈ c.sets, s ∈ env.legalSets

instance (env : LegalityEnv) (c : CardDef) : Decidable (CardLegal env c) := by
  unfold CardLegal; infer_instance

/-- A card is not banned (TR 602.1.b). -/
def NotBanned (env : LegalityEnv) (c : CardDef) : Prop := c.id ∉ env.banned

instance (env : LegalityEnv) (c : CardDef) : Decidable (NotBanned env c) := by
  unfold NotBanned; infer_instance

/-! ## Constructed -/

/-- A Constructed deck: the deck and its sideboard (TR 601.1.c). -/
structure ConstructedDeck where
  /-- The Legend, Main Deck, Rune Deck and Battlefields. -/
  deck : Deck
  /-- The sideboard. -/
  sideboard : List CardId
deriving DecidableEq, Repr

namespace Deck

/-- Constructed Battlefields: exactly three Battlefield cards with different names
(TR 402.1, 601.1.b). -/
def ConstructedBattlefieldsOk (r : Resolved) : Prop :=
  r.battlefields.length = 3 ∧ (∀ c ∈ r.battlefields, c.hasType .battlefield = true) ∧
    (r.battlefields.map (·.nameKey)).Nodup

instance (r : Resolved) : Decidable (ConstructedBattlefieldsOk r) := by
  unfold ConstructedBattlefieldsOk; infer_instance

/-- A resolved Constructed deck is legal (TR 402.1, 601.1). The rules of Core Rules deck
building that the format does not change are used as they are; the Main Deck is exactly 40
cards, the name limits count the Main Deck and the sideboard together (TR 601.1.c), the
sideboard has at most 10 cards that could go in the Main Deck, and every card is legal. -/
def Resolved.ConstructedValid (env : LegalityEnv) (r : Resolved) (side : List CardDef) : Prop :=
  LegendOk r ∧ ChosenOk r ∧ r.main.length = 40 ∧ MainTypesOk r.main ∧
    CopyLimitOk (r.main ++ side) ∧ SignatureOk r ∧ IdentityOk r ∧ RuneDeckOk r ∧
    ConstructedBattlefieldsOk r ∧
    side.length ≤ 10 ∧ MainTypesOk side ∧ DomainsIn r.legend.domains side ∧
    (∀ c ∈ r.legend :: (r.main ++ side ++ r.runes ++ r.battlefields), CardLegal env c)

instance (env : LegalityEnv) (r : Resolved) (side : List CardDef) :
    Decidable (r.ConstructedValid env side) := by
  unfold Resolved.ConstructedValid; infer_instance

end Deck

/-- A Constructed deck is legal in the format with `env` (TR 402, 403, 601). -/
def ConstructedDeckValid (db : CardDB) (env : LegalityEnv) (cd : ConstructedDeck) : Prop :=
  match cd.deck.resolve db, cd.sideboard.mapM db.find? with
  | some r, some side => r.ConstructedValid env side
  | _, _ => False

instance (db : CardDB) (env : LegalityEnv) (cd : ConstructedDeck) :
    Decidable (ConstructedDeckValid db env cd) := by
  unfold ConstructedDeckValid
  split <;> infer_instance

namespace Deck

/-- Counting a name in the Main Deck never exceeds counting it in the Main Deck and the
sideboard together. -/
theorem copyLimitOk_of_append {main side : List CardDef}
    (h : CopyLimitOk (main ++ side)) : CopyLimitOk main := by
  intro c hc
  rcases h c (List.mem_append_left side hc) with hu | hn
  · exact Or.inl hu
  · rw [List.countP_append] at hn
    exact Or.inr (by omega)

/-- **I13.** A legal Constructed deck, without its sideboard, is legal under the Core Rules in
every mode that asks for three Battlefields (for example 1v1 Duel). The Battlefield count is
the mode's (CR 103.5), so the theorem is stated for modes that agree with Constructed. -/
theorem Resolved.valid_of_constructedValid {env : LegalityEnv} {r : Resolved}
    {side : List CardDef} (mode : Mode) (hm : mode.deckBattlefields = 3)
    (h : r.ConstructedValid env side) : r.Valid mode := by
  obtain ⟨hl, hc, hsz, hty, hcp, hsig, hid, hrune, ⟨hb1, hb2, hb3⟩, -⟩ := h
  refine ⟨hl, hc, ?_, hty, copyLimitOk_of_append hcp, hsig, hid, hrune, ?_⟩
  · unfold MainSizeOk; omega
  · refine ⟨by omega, hb2, fun _ => hb3⟩

end Deck

/-- **I13.** A deck that is legal in Constructed is legal under the Core Rules, in every mode
that asks for three Battlefields (TR 402.1, 601) and (CR 103). -/
theorem constructedDeckValid_deckValid {db : CardDB} {env : LegalityEnv} {cd : ConstructedDeck}
    (mode : Mode) (hm : mode.deckBattlefields = 3)
    (h : ConstructedDeckValid db env cd) : DeckValid db mode cd.deck := by
  unfold ConstructedDeckValid at h
  split at h
  · rename_i r side hr hs
    exact DeckValid.of_resolved hr (Deck.Resolved.valid_of_constructedValid mode hm h)
  · exact h.elim

/-- **I13** for 1v1 Duel. -/
theorem constructedDeckValid_deckValid_duel {db : CardDB} {env : LegalityEnv}
    {cd : ConstructedDeck} (h : ConstructedDeckValid db env cd) :
    DeckValid db Mode.duel cd.deck :=
  constructedDeckValid_deckValid Mode.duel rfl h

/-! ## Limited (Sealed and Draft) -/

/-- A Limited deck (TR 602.4). The Domain Identity is declared; the Legend and the Chosen
Champion are optional (TR 602.4.a.5). -/
structure LimitedDeck where
  /-- The declared Domain Identity: three domains (TR 602.4.a.3). -/
  identity : List Domain
  /-- The Legend, if the deck uses one. -/
  legend : Option CardId
  /-- The Chosen Champion, if the deck uses one. It is one of the cards of `main`. -/
  chosenChampion : Option CardId
  /-- The Main Deck, including the Chosen Champion if there is one. -/
  main : List CardId
  /-- The Rune Deck. -/
  runes : List CardId
  /-- The Battlefields. -/
  battlefields : List CardId
deriving DecidableEq, Repr

/-- A Limited deck whose identifiers are resolved. -/
structure LimitedDeck.Resolved where
  /-- The declared Domain Identity. -/
  identity : List Domain
  /-- The Legend, if any. -/
  legend : Option CardDef
  /-- The Chosen Champion, if any. -/
  chosenChampion : Option CardDef
  /-- The Main Deck. -/
  main : List CardDef
  /-- The Rune Deck. -/
  runes : List CardDef
  /-- The Battlefields. -/
  battlefields : List CardDef
deriving DecidableEq, Repr

/-- Resolve a Limited deck. `none` if some identifier is unknown. -/
def LimitedDeck.resolve (db : CardDB) (d : LimitedDeck) : Option LimitedDeck.Resolved := do
  let legend ← d.legend.mapM db.find?
  let chosenChampion ← d.chosenChampion.mapM db.find?
  let main ← d.main.mapM db.find?
  let runes ← d.runes.mapM db.find?
  let battlefields ← d.battlefields.mapM db.find?
  pure { identity := d.identity, legend, chosenChampion, main, runes, battlefields }

/-- A resolved Limited deck is legal (TR 602.4) with at least `minMain` Main Deck cards:
three different Domain Identity domains; every Main Deck and Rune Deck card fits the identity;
exactly 12 Runes; a Legend and a Chosen Champion that are what they should be, if present; no
card is banned. There is no limit on how many copies of a name the deck holds
(TR 602.4.a.6). -/
def LimitedDeck.Resolved.Valid (env : LegalityEnv) (minMain : Nat)
    (r : LimitedDeck.Resolved) : Prop :=
  r.identity.Nodup ∧ r.identity.length = 3 ∧ minMain ≤ r.main.length ∧
    Deck.MainTypesOk r.main ∧ Deck.DomainsIn r.identity (r.main ++ r.runes) ∧
    r.runes.length = 12 ∧ (∀ c ∈ r.runes, c.hasType .rune = true) ∧
    (∀ l ∈ r.legend.toList, l.hasType .legend = true) ∧
    (∀ c ∈ r.chosenChampion.toList, c.IsChosenChampionCandidate ∧ c ∈ r.main) ∧
    (∀ b ∈ r.battlefields, b.hasType .battlefield = true) ∧
    (∀ c ∈ r.legend.toList ++ r.main ++ r.runes ++ r.battlefields, NotBanned env c)

instance LimitedDeck.Resolved.decidableValid (env : LegalityEnv) (n : Nat)
    (r : LimitedDeck.Resolved) : Decidable (r.Valid env n) := by
  unfold LimitedDeck.Resolved.Valid; infer_instance

/-- A Limited deck is legal with at least `minMain` Main Deck cards (TR 602.4). -/
def LimitedDeckValid (db : CardDB) (env : LegalityEnv) (minMain : Nat) (d : LimitedDeck) :
    Prop :=
  match d.resolve db with
  | some r => r.Valid env minMain
  | none => False

instance (db : CardDB) (env : LegalityEnv) (n : Nat) (d : LimitedDeck) :
    Decidable (LimitedDeckValid db env n d) := by
  unfold LimitedDeckValid
  split <;> infer_instance

/-- A Sealed deck is legal: at least 25 Main Deck cards (TR 602.4.a). -/
def SealedDeckValid (db : CardDB) (env : LegalityEnv) (d : LimitedDeck) : Prop :=
  LimitedDeckValid db env 25 d

/-- A Draft deck is legal: at least 20 Main Deck cards (TR 602.4.b). -/
def DraftDeckValid (db : CardDB) (env : LegalityEnv) (d : LimitedDeck) : Prop :=
  LimitedDeckValid db env 20 d

instance (db : CardDB) (env : LegalityEnv) (d : LimitedDeck) :
    Decidable (SealedDeckValid db env d) := by
  unfold SealedDeckValid; infer_instance

instance (db : CardDB) (env : LegalityEnv) (d : LimitedDeck) :
    Decidable (DraftDeckValid db env d) := by
  unfold DraftDeckValid; infer_instance

/-- The sizes in the Limited formats agree with `Format.limitedMinMain`. -/
theorem limitedMinMain_sealed : Format.limitedMinMain .sealed = some 25 := rfl

/-- The Draft Main Deck size agrees with `Format.limitedMinMain`. -/
theorem limitedMinMain_draft : Format.limitedMinMain .draft = some 20 := rfl

/-- A Sealed deck is also a Draft deck as far as the size goes: Sealed asks for more cards. -/
theorem draftDeckValid_of_sealedDeckValid {db : CardDB} {env : LegalityEnv} {d : LimitedDeck}
    (h : SealedDeckValid db env d) : DraftDeckValid db env d := by
  unfold SealedDeckValid LimitedDeckValid at h
  unfold DraftDeckValid LimitedDeckValid
  split at h
  · obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, by omega, h4⟩
  · exact h.elim

end Riftbound

end
