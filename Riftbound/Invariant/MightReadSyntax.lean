module

public import Riftbound.Rules.Select

/-!
# Reads used by Might-related passive abilities

These checks recognize the expressions used by the passive modifiers that affect Might, including
the modifiers that grant Tank, Assault or Shield. In particular a selector in this fragment reads
the Board or a player's Trash, without counting objects on the Chain.
-/

@[expose] public section

namespace Riftbound.MightRead

/-- Places supported by the invariance proof for Might-related selectors. -/
def place : Place → Bool
  | .anywhere | .here | .inTrash => true
  | _ => false

/-- Filters that read the printed traits, the Board, or the supplied Might environment. -/
def filter : Filter → Bool
  | .at_ .self | .alone | .attacker | .buffed | .defender | .empowered | .exhausted
  | .hasKeyword .. | .mighty | .notSelf | .ofSupertype .. | .ofType .. | .onBattlefield
  | .sameNameAsSource | .stunned | .tag .. | .token => true
  | .either a b => filter a && filter b
  | _ => false

/-- Every filter in a selector must be supported. -/
def filters : FilterList → Bool
  | .nil => true
  | .cons f fs => filter f && filters fs

/-- Select the source, or all matching objects at a supported place. -/
def selector : Selector → Bool
  | .self => true
  | .pick .all _ where_ fs => place where_ && filters fs
  | _ => false

/-- Amount expressions supported by the proof for a Might-related modifier. -/
def amount : Amount → Bool
  | .const .. | .empowerCount | .points .you | .powerSpent | .xp => true
  | .count sel => selector sel
  | .mul a b => amount a && amount b
  | _ => false

/-- Conditions supported by the proof for a Might-related passive ability. -/
def condition : Condition → Bool
  | .always | .discardedThisTurn | .noted .. | .spentOnSpell .. => true
  | .and a b => condition a && condition b
  | .cmp _ a b => amount a && amount b
  | .empowered sel | .exists sel => selector sel
  | .matches sel f => selector sel && filter f
  | _ => false

/-- The keywords whose presence or amount can affect the observed Might. -/
def keyword (k : Keyword) : Bool := [.assault, .shield, .tank].contains k

/-- Whether the modifier can contribute to Might or to a keyword used to compute it. -/
def relevant : StaticMod → Bool
  | .mightPlus .. | .mightPlusWithKeyword .. | .mightMinus .. | .mightMinusMin .. | .assaultCount .. => true
  | .keyword _ k | .keywordHere k | .equipEach k => keyword k.keyword
  | _ => false

/-- Check the selectors and amount expressions used by a Might-related modifier. -/
def modifier : StaticMod → Bool
  | .mightPlus sel a | .mightMinus sel a | .mightMinusMin sel a _ => selector sel && amount a
  | .mightPlusWithKeyword sel k a => selector sel && k == .tank && amount a
  | .assaultCount sel | .keyword sel _ => selector sel
  | _ => true

/-- Only passives that can affect Might need their condition and relevant modifiers checked. -/
def ability : Ability → Bool
  | .passive c ms => (ms.filter relevant).all modifier && (!(ms.any relevant) || condition c)
  | _ => true

/-- Check both the printed and animated types of a card. The animation's Might value does not
affect which abilities its definition contains. -/
def card (d : CardDef) : Bool :=
  d.allAbilities.all ability && (d.withUnitGearMight 0).allAbilities.all ability

/-- Every registered passive that can affect Might uses the supported read expressions. -/
def database (db : CardDB) : Prop := db.cards.all card = true

instance (db : CardDB) : Decidable (database db) := by
  unfold database
  infer_instance

end Riftbound.MightRead

end
