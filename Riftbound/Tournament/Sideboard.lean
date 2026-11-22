module

public import Riftbound.Tournament.DeckLegality
public import Riftbound.Tournament.Match

/-!
# Sideboarding (TR 403)

Between the games of a Constructed match the players may exchange cards of the Main Deck for cards
of the sideboard, one for one (TR 403.4). The Chosen Champion may be changed too (TR 403.4.a); the
Runes, the Legend and the Battlefields may not (TR 403.4.b). The first game of a match, and the game
after a draw, are played with the deck as it is (TR 403.5) (TR 403.10); see
`MatchState.sideboardAllowed`.

The deck after the exchange has to be legal. What the exchange cannot break is proved here: the
number of cards of the Main Deck, the size of the sideboard, the limit on the copies of a name
(it counts the Main Deck and the sideboard together) (TR 601.1.c), and the legality of every card.
What it can break is listed: the types, the Chosen Champion, the Signature cards, and the Domain
Identity.
-/

@[expose] public section

namespace Riftbound

/-- The exchange of the sideboard (TR 403.4): some cards leave the Main Deck and the same number of
cards come in from the sideboard, and the cards that left go to the sideboard. Cards are told apart
as a multiset: the order of a list means nothing here. -/
def IsSwap (main side main' side' : List CardDef) : Prop :=
  ∃ keep outs rest ins, main.Perm (keep ++ outs) ∧ side.Perm (rest ++ ins) ∧
    main'.Perm (keep ++ ins) ∧ side'.Perm (rest ++ outs) ∧ outs.length = ins.length

/-- Not exchanging anything is an exchange. -/
theorem IsSwap.refl (main side : List CardDef) : IsSwap main side main side :=
  ⟨main, [], side, [], by simp, by simp, by simp, by simp, rfl⟩

namespace IsSwap

/-- **The cards of the Main Deck and the sideboard together do not change** (TR 403.4, 601.1.c):
every card that is in one is in the other, with the same counts. -/
theorem pool {main side main' side' : List CardDef} (h : IsSwap main side main' side') :
    (main' ++ side').Perm (main ++ side) := by
  obtain ⟨keep, outs, rest, ins, h1, h2, h3, h4, -⟩ := h
  have a : (main' ++ side').Perm ((keep ++ ins) ++ (rest ++ outs)) := h3.append h4
  have b : (main ++ side).Perm ((keep ++ outs) ++ (rest ++ ins)) := h1.append h2
  have c : ((keep ++ ins) ++ (rest ++ outs)).Perm ((keep ++ outs) ++ (rest ++ ins)) :=
    List.perm_iff_count.mpr fun x => by simp only [List.count_append]; omega
  exact a.trans (c.trans b.symm)

/-- **The Main Deck keeps its size**, one for one (TR 403.4). -/
theorem main_length {main side main' side' : List CardDef} (h : IsSwap main side main' side') :
    main'.length = main.length := by
  obtain ⟨keep, outs, rest, ins, h1, h2, h3, h4, hl⟩ := h
  rw [h3.length_eq, h1.length_eq]
  simp [hl]

/-- **The sideboard keeps its size**, one for one (TR 403.4). -/
theorem side_length {main side main' side' : List CardDef} (h : IsSwap main side main' side') :
    side'.length = side.length := by
  obtain ⟨keep, outs, rest, ins, h1, h2, h3, h4, hl⟩ := h
  rw [h4.length_eq, h2.length_eq]
  simp [hl]

end IsSwap

namespace Deck

/-- The limit on the copies of a name does not depend on the order of the cards. -/
theorem copyLimitOk_perm {l l' : List CardDef} (hp : l.Perm l') (h : CopyLimitOk l) :
    CopyLimitOk l' := by
  intro c hc
  have := h c (hp.mem_iff.mpr hc)
  rwa [hp.countP_eq] at this

/-- A Constructed deck with its Main Deck and Chosen Champion changed. -/
def Resolved.withMain (r : Resolved) (main' : List CardDef) (champion' : CardDef) : Resolved :=
  { r with main := main', chosenChampion := champion' }

/-- **What an exchange cannot break** (TR 403.4, 403.4.c, 601.1.c): from a legal Constructed deck
and an exchange of the sideboard, the new deck is legal as soon as the parts that the exchange can
change are in order: the Chosen Champion, which may be changed (TR 403.4.a), the types, the
Signature cards, and the Domain Identity of the Main Deck and the sideboard. The size of the Main
Deck, the size of the sideboard, the limit on the copies of a name, the legality of every card, and
the Legend, the Runes and the Battlefields (TR 403.4.b) need no check. -/
theorem Resolved.constructedValid_swap {env : LegalityEnv} {r : Resolved}
    {side main' side' : List CardDef} {champion' : CardDef} (h : r.ConstructedValid env side)
    (hs : IsSwap r.main side main' side')
    (hchosen : ChosenOk (r.withMain main' champion')) (hty : MainTypesOk main')
    (hsig : SignatureOk (r.withMain main' champion'))
    (hid : IdentityOk (r.withMain main' champion')) (hty2 : MainTypesOk side')
    (hdom : DomainsIn r.legend.domains side') :
    (r.withMain main' champion').ConstructedValid env side' := by
  obtain ⟨hl, -, hsz, -, hcp, -, -, hrune, hbf, hside, -, -, hlegal⟩ := h
  have hmem : ∀ c, c ∈ main' ++ side' → c ∈ r.main ++ side :=
    fun c hc => hs.pool.mem_iff.mp hc
  refine ⟨hl, hchosen, ?_, hty, ?_, hsig, hid, hrune, hbf, ?_, hty2, hdom, ?_⟩
  · show main'.length = 40
    rw [hs.main_length]; exact hsz
  · exact copyLimitOk_perm hs.pool.symm hcp
  · rw [hs.side_length]; exact hside
  · intro c hc
    apply hlegal
    simp only [Resolved.withMain, List.mem_cons, List.mem_append] at hc ⊢
    rcases hc with hc | ((hc | hc) | hc) | hc
    · exact Or.inl hc
    · rcases List.mem_append.mp (hmem c (List.mem_append.mpr (Or.inl hc))) with h1 | h1
      · exact Or.inr (Or.inl (Or.inl (Or.inl h1)))
      · exact Or.inr (Or.inl (Or.inl (Or.inr h1)))
    · rcases List.mem_append.mp (hmem c (List.mem_append.mpr (Or.inr hc))) with h1 | h1
      · exact Or.inr (Or.inl (Or.inl (Or.inl h1)))
      · exact Or.inr (Or.inl (Or.inl (Or.inr h1)))
    · exact Or.inr (Or.inl (Or.inr hc))
    · exact Or.inr (Or.inr hc)

end Deck

/-- The exchange is made when the match allows it (TR 403.5, 403.10) and it is an exchange of the
sideboard (TR 403.4). -/
def SideboardStep (m : MatchState) (main side main' side' : List CardDef) : Prop :=
  m.sideboardAllowed = true ∧ IsSwap main side main' side'

/-- **No exchange before the first game of the match, nor after a draw** (TR 403.5, 403.10). -/
theorem not_sideboardStep_start (target : Nat) (main side main' side' : List CardDef) :
    ¬ SideboardStep (MatchState.start target) main side main' side' := by
  intro h
  have := h.1
  rw [MatchState.sideboard_not_first] at this
  exact absurd this (by simp)

/-- No exchange after a draw. -/
theorem not_sideboardStep_draw {m : MatchState} (hd : m.last = some .draw)
    (main side main' side' : List CardDef) : ¬ SideboardStep m main side main' side' := by
  intro h
  have := h.1
  rw [MatchState.sideboard_not_after_draw hd] at this
  exact absurd this (by simp)

end Riftbound

end
