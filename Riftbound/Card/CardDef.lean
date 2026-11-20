module

public import Riftbound.Core.Ids
public import Riftbound.Core.Domain
public import Riftbound.Core.CardType
public import Riftbound.Core.Cost
public import Riftbound.Core.Might
public import Riftbound.Core.Keyword
public import Riftbound.Card.IR.Ability

/-!
# Card definitions

The static data of a logical card (card-data.md §4): the metadata, and the effects written in the
effect IR (`Riftbound.Card.IR`).
-/

@[expose] public section

namespace Riftbound

/-- How far the implementation of a card has come (roadmap.md, "ImplStatus"). -/
inductive ImplStatus where
  /-- Metadata only. -/
  | todo
  /-- The effect is transcribed into the IR; its meaning is not yet checked. -/
  | drafted
  /-- Partly implemented. The reason is written in the card's docstring. -/
  | «partial»
  /-- Implemented in every mode that exists, as the card text says. -/
  | full
deriving DecidableEq, Repr, Hashable

/-- The definition of one logical card. -/
structure CardDef where
  /-- The logical card's identifier. -/
  id : CardId
  /-- The short name (CR 132). -/
  name : String
  /-- The subtitle (CR 132). The name of the card is the short name with the subtitle. -/
  subtitle : Option String := none
  /-- The card types. A card can have several (CR 177). -/
  types : List CardType
  /-- The supertypes (CR 133.7). -/
  supertypes : List Supertype := []
  /-- The tags (CR 133.8). -/
  tags : List Tag := []
  /-- The domains (CR 134). Empty for a card without a domain. -/
  domains : List Domain := []
  /-- The printed cost, if the card has one. -/
  cost : Option Cost := none
  /-- The printed Might (CR 143), if the card has one. -/
  might : Option Int := none
  /-- The Might bonus of an Equipment (CR 137), if any. -/
  mightBonus : Option Int := none
  /-- The printed keywords. -/
  keywords : List KeywordInst := []
  /-- The abilities of the card (CR 361): passive, replacement, activated and triggered. The
  abilities that a printed keyword stands for are not here (design.md §7.4). -/
  abilities : List Ability := []
  /-- What a Spell does: the choices made when it is played, and the effect (CR 355, 359.3). -/
  spellEffect : Option EffectDef := none
  /-- The sets the card has been printed in. -/
  sets : List SetCode := []
  /-- The implementation status. -/
  status : ImplStatus := .todo
deriving DecidableEq, Repr

namespace CardDef

/-- The identity of a card's name: short name and subtitle together (CR 103.3.b, 132). Two
cards have the same name exactly when their name keys are equal. -/
def nameKey (c : CardDef) : String × Option String := (c.name, c.subtitle)

/-- The card has the type `t`. -/
def hasType (c : CardDef) (t : CardType) : Bool := c.types.contains t

/-- The card has the supertype `s`. -/
def hasSupertype (c : CardDef) (s : Supertype) : Bool := c.supertypes.contains s

/-- The card prints the keyword `k`. -/
def hasKeyword (c : CardDef) (k : Keyword) : Bool := c.keywords.any (·.keyword == k)

/-- A Champion Unit that is not a Signature card: what a Chosen Champion must be
(CR 103.3.a). -/
def IsChosenChampionCandidate (c : CardDef) : Prop :=
  c.hasType .unit = true ∧ c.hasSupertype .champion = true ∧ c.hasSupertype .signature = false

instance (c : CardDef) : Decidable c.IsChosenChampionCandidate := by
  unfold IsChosenChampionCandidate; infer_instance

/-- The number of copies of a card allowed in a deck: a Unique card is limited to one
(CR 825), any other to three (CR 103.3.b). -/
def copyLimit (c : CardDef) : Nat := if c.hasKeyword .unique then 1 else 3

/-- A Unique card is limited to one copy (CR 825). -/
theorem copyLimit_of_unique {c : CardDef} (h : c.hasKeyword .unique = true) :
    c.copyLimit = 1 := by
  simp [copyLimit, h]

/-- A card that is not Unique is limited to three copies (CR 103.3.b). -/
theorem copyLimit_of_not_unique {c : CardDef} (h : c.hasKeyword .unique = false) :
    c.copyLimit = 3 := by
  simp [copyLimit, h]

end CardDef

end Riftbound

end
