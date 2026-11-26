module

/-!
# Card types, supertypes and tags

Card types, supertypes and tags (CR 133, 140-178).
Tokens are not cards (CR 185.1) and have no `CardType`.
-/

@[expose] public section

namespace Riftbound

/-- A card type (CR 133). A card can have several types (CR 177-178). -/
inductive CardType where
  /-- Unit (CR 143-144). -/
  | unit
  /-- Gear (CR 149-150). -/
  | gear
  /-- Spell (CR 155). -/
  | spell
  /-- Rune (CR 161). Rune Deck only. -/
  | rune
  /-- Battlefield (CR 170-171). -/
  | battlefield
  /-- Legend (CR 174-175). -/
  | legend
deriving DecidableEq, Repr, Hashable

/-- A card type that can be guessed for a card from the Main Deck. -/
inductive CardTypeGuess where
  /-- The player guesses Unit. -/
  | unit
  /-- The player guesses Gear. -/
  | gear
  /-- The player guesses Spell. -/
  | spell
deriving DecidableEq, Repr, Hashable

/-- The three possible answers to a Main Deck card-type guess. -/
def CardTypeGuess.choices : List CardTypeGuess := [.unit, .gear, .spell]

/-- A supertype (CR 133.7). -/
inductive Supertype where
  /-- Champion. Units only. -/
  | champion
  /-- Signature. -/
  | signature
deriving DecidableEq, Repr, Hashable

/-- A tag (CR 133.8, 763.1). Tags have no rules meaning in general; the exceptions
are matched by name. The set of tags is open, so a tag is its name. -/
structure Tag where
  /-- The tag's name as printed. -/
  name : String
deriving DecidableEq, Repr, Hashable

end Riftbound

end
