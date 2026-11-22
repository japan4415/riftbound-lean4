module

public import Riftbound.Core.Ids
public import Riftbound.Core.Domain
public import Riftbound.Core.CardType
public import Riftbound.Core.Cost
public import Riftbound.Core.Might
public import Riftbound.Core.Keyword
public import Riftbound.Card.IR.Ability
public import Riftbound.Card.IR.Build
public import Riftbound.Card.IR.Check

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
  /-- For an Equipment: the abilities the Unit it is attached to has (CR 137): the text the card
  gives. They are not abilities of the card itself. -/
  grants : List Ability := []
  /-- What a Spell does: the choices made when it is played, and the effect (CR 355, 359.3). -/
  spellEffect : Option EffectDef := none
  /-- The cost the player may pay more when they play the card: "you may pay ... as an additional
  cost to play me" (CR 357.2). -/
  additionalCost : Option Cost := none
  /-- The sets the card has been printed in. -/
  sets : List SetCode := []
  /-- The implementation status. -/
  status : ImplStatus := .todo
deriving DecidableEq, Repr

namespace CardDef

/-- What playing the card from hiding does (CR 811): a Spell does its effect and goes to the Trash,
a Unit or a Gear is played. It does so only if the card is still hidden: the ability can be used
again while it is on the Chain. -/
def hiddenPlay (c : CardDef) : EffectDef :=
  let gate (e : Effect) : Effect :=
    .ifThen (.matches .self .hidden)
      (.seq (.cons (.prim (.turnEffect .hiddenPlayed)) (.cons e .nil))) .nop
  if c.types.contains .spell then
    let e := c.spellEffect.getD (EffectDef.of [] .nop)
    EffectDef.mk e.choices (gate (.seq (.cons e.body (.cons (.prim (.bin .self)) .nil))))
  else EffectDef.of [] (gate (.prim (.play .self)))

/-- The abilities that the printed keywords of the card stand for (design.md §7.4): Equip is an
activated ability, "pay the cost: attach this to a unit you control" (CR 137, 825), and Hunt X
fires when the Unit conquers or holds: the player gains X XP (CR 823). -/
def keywordAbilities (c : CardDef) : List Ability :=
  c.keywords.filterMap (fun k =>
    match k.keyword, k.arg with
    | .equip, .cost cost =>
      some (.activated [.pay cost] .normal
        (EffectDef.of [Choice.targetOf .one .friendly .anywhere [.ofType .unit]]
          (.prim (.attach .self (.slot 0)))) .unlimited)
    | _, _ => none) ++
  c.keywords.flatMap (fun k =>
    match k.keyword, k.arg with
    | .hidden, _ =>
      -- Hide: pay one Power of any domain, to hide the card at a Battlefield its player controls;
      -- play: from the turn after, as a Reaction, without paying (CR 811)
      [.activated [.fromHand, .pay ⟨0, [.any]⟩] .normal
        (EffectDef.of [Choice.targetOf .one .any .anywhere [.ofType .battlefield, .controlled]]
          (.ifThen (.matches (.slot 0) .controlled) (.prim (.hideAt .self (.slot 0))) .nop))
        .unlimited,
       -- the card must still be hidden when the ability resolves: it can be used again while it
       -- is on the Chain
       .activated [.fromHidden] .reaction c.hiddenPlay .unlimited]
    | .vision, _ =>
      [.triggered (Trigger.onSelf .play)
        (EffectDef.of [] (.may (.prim (.recycleTop .you)))) .unlimited]
    | .hunt, .amount n =>
      [.triggered (Trigger.onSelf .conquer) (EffectDef.of [] (.prim (.gainXP .you (.const n))))
        .unlimited,
       .triggered (Trigger.onSelf .hold) (EffectDef.of [] (.prim (.gainXP .you (.const n))))
        .unlimited]
    | _, _ => [])

/-- The abilities of the card itself: the written ones, and those of its keywords. -/
def fullAbilities (c : CardDef) : List Ability := c.abilities ++ c.keywordAbilities

/-- The abilities of the card itself, and then the abilities it gives to the Unit it is attached
to. The place of an ability in this list is what a trigger on the Chain remembers. -/
def allAbilities (c : CardDef) : List Ability := c.fullAbilities ++ c.grants

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

/-- The effects of the card refer only to what is there: bound variables, declared choices, and
`it` and the replaced event where they mean something (`Riftbound.Card.IR.Check`). -/
def StaticOk (c : CardDef) : Prop :=
  c.abilities.all Ability.ok = true ∧ c.grants.all Ability.ok = true ∧
    (match c.spellEffect with
      | none => true
      | some d => d.ok {}) = true

instance (c : CardDef) : Decidable c.StaticOk := by unfold StaticOk; infer_instance

/-- A card with no effect refers to nothing, so it passes the check. -/
theorem staticOk_of_no_effects {c : CardDef} (h1 : c.abilities = []) (h2 : c.spellEffect = none)
    (h3 : c.grants = []) : c.StaticOk := by
  simp [StaticOk, h1, h2, h3]

end CardDef

end Riftbound

end
