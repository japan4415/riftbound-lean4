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

/-- An additional cost to play a card that is paid by an action instead of Energy or Power. -/
inductive PlayExtra where
  /-- A friendly gear returns to its owner's hand. -/
  | returnGear
  /-- A friendly Unit returns to its owner's hand. -/
  | returnUnit
  /-- A friendly gear is killed. -/
  | killGear
  /-- A friendly Unit or Gear is killed. -/
  | killUnitOrGear
  /-- The player's Legend is exhausted. -/
  | exhaustLegend
  /-- A ready friendly Unit is exhausted. -/
  | exhaustUnit
  /-- A friendly Bird, Cat, Dog or Poro is killed. -/
  | killPet
  /-- A friendly Unit is killed (for a Spell: the first object it chooses; its first choice must be
  a friendly Unit). -/
  | killUnit
  /-- The player spends this much of their own XP. -/
  | spendXP (n : Nat)
  /-- For a Spell: spending this much XP lifts the first target's Might cap (Conscription). -/
  | spendXPOver (n : Nat) (cap : Nat)
deriving DecidableEq, Repr, Hashable

/-- The Spell picks the object for this cost separately from its effect's choices (CR 355, 357). -/
def PlayExtra.separateSpellObject : PlayExtra → Bool
  | .returnUnit | .exhaustUnit => true
  | _ => false

/-- Whether this cost asks for a permanent to die. -/
def PlayExtra.kills : PlayExtra → Bool
  | .killGear | .killUnitOrGear | .killUnit | .killPet => true
  | _ => false

/-- What the additional cost of a card (its `playExtra`) takes off the cost of the card when it is
done as the card is played. -/
inductive PaidCut where
  /-- The card costs this much less Energy (Poppy). -/
  | energy (n : Nat)
  /-- The card costs as much less Energy as the object the cost is done to costs, and as many Power
  symbols less as it has (Atakhan). -/
  | killed
deriving DecidableEq, Repr, Hashable

/-- A Show Off requirement for one object (CR 832). -/
structure ShowOffRequirement where
  /-- Qualities the shown card or object must have. -/
  filters : FilterList := .nil
  /-- The requirement specifies a card, excluding tokens (CR 185). -/
  cardsOnly : Bool := false
deriving DecidableEq, Repr

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
  /-- Requirements for the optional object shown off during this card's finalization (CR 832). -/
  showOffRequirement : Option ShowOffRequirement := none
  /-- The abilities of the card (CR 361): passive, replacement, activated and triggered. The
  abilities that a printed keyword stands for are not here (design.md §7.4). -/
  abilities : List Ability := []
  /-- Abilities this card gives to other objects, through attachment or a resolving effect
  (CR 137, 479.3). They are not abilities of the card itself. -/
  grants : List Ability := []
  /-- What a Spell does: the choices made when it is played, and the effect (CR 355, 359.3). -/
  spellEffect : Option EffectDef := none
  /-- The cost the player may pay more when they play the card: "you may pay ... as an additional
  cost to play me" (CR 357.2). -/
  additionalCost : Option Cost := none
  /-- This Spell declares an additional cost of any amount of Power (CR 355.1, 356.4.f). -/
  variablePower : Bool := false
  /-- Electing the zero-resource entry option makes this Unit enter ready and unable to move
  for the rest of the turn. The play's cost choices carry the election. -/
  electReadyEntryNoMove : Bool := false
  /-- The player may discard a card as an additional cost to play this card (CR 357.2). -/
  discardToPlay : Bool := false
  /-- What else the player does as an additional cost to play the card (not Energy or Power): what
  it is, and whether it must be done ("as an additional cost to play me, ..." or "you may ...").
  The object it is done to is chosen as the card is played. -/
  playExtra : Option (PlayExtra × Bool) := none
  /-- What the additional cost `playExtra` takes off the cost of the card, if it is done. -/
  paidCut : Option PaidCut := none
  /-- The maximum number of instances of Empowered this object can have (CR 442). -/
  empowerLimit : Nat := 1
  /-- The card's text waives the number of copies allowed in a deck (CR 002, 103.3.b). -/
  unlimitedCopies : Bool := false
  /-- How many additional Legends this card permits its player to register (CR 103.1). -/
  reserveLegendLimit : Nat := 0
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
    EffectDef.of e.choices (gate (.seq (.cons e.body (.cons (.prim (.bin .self)) .nil))))
  else if c.types.contains .unit then
    -- a Unit played from hiding enters the Battlefield where it was hidden (CR 811)
    EffectDef.of [] (gate (.prim (.playTo .self (.locationOf .self))))
  else EffectDef.of [] (gate (.prim (.play .self)))

/-- Hide: hide the card at a Battlefield its player controls (CR 811). Hiding is free this turn
after Guerilla Warfare: what was paid comes back (`refund`: a Power, or the Energy of the other
Hide). -/
def hideEffectWith (refund : Prim) : EffectDef :=
  EffectDef.of [Choice.targetOf .one .any .anywhere
    [.ofType .battlefield, .controlled, .hideRoom]]
    (.ifThen (.matches (.slot 0) .controlled)
      (.seqOf [
        .ifThen (.and (.noted .hideFree)
            (.cmp .ge (.count (Selector.all .friendly .inHand [.sameAs .self])) (.const 1)))
          (.prim refund) .nop,
        .prim (.hideAt .self (.slot 0))])
      .nop)

/-- Hide for one Power of any domain. -/
def hideEffect : EffectDef := hideEffectWith (.addPower .you (.const 1) none none)

/-- Hide for one Energy (with Swift Scout): the Energy comes back, if hiding is free. -/
def hideEnergyEffect : EffectDef :=
  let e := hideEffectWith (.addEnergy .you (.const 1) none)
  EffectDef.of e.choices (.ifThen .hidesWithEnergy e.body .nop)

/-- The Equip cost the card prints, if it has one. -/
def equipCost (c : CardDef) : Option Cost :=
  c.keywords.findSome? (fun k =>
    match k.keyword, k.arg with
    | .equip, .cost cost | .equip, .costOrExhaustUnit cost => some cost
    | _, _ => none)

/-- Whether the Equipment lets its controller exhaust a Unit to pay its Equip cost. -/
def equipCanExhaust (c : CardDef) : Bool :=
  c.keywords.any (fun k => match k.keyword, k.arg with
    | .equip, .costOrExhaustUnit _ => true
    | _, _ => false)

/-- Keyword effects that need an effective value captured when they trigger. -/
def keywordTrigger : Keyword → Option Ability
  | .disarm => some (.triggered (Trigger.onSelf .attack)
      (EffectDef.of [Choice.targetOf .one .enemy .here [.ofType .unit]]
        (.grant (.slot 0) (.mightMinus .it .eventAmount) .thisTurn)) .unlimited)
  | _ => none

/-- The abilities that the printed keywords of the card stand for (design.md §7.4): Equip is an
activated ability, "pay the cost: attach this to a unit you control" (CR 137, 825), and Hunt X
fires when the Unit conquers or holds: the player gains X XP (CR 823). -/
def printedKeywordAbilities (c : CardDef) : List Ability :=
  let equipAbility (cost : AbilityCost) : Ability :=
    .activated [cost] .normal
      (EffectDef.of [Choice.targetOf .one .you .anywhere [.ofType .unit]]
        (.prim (.attach .self (.slot 0)))) .unlimited
  c.keywords.flatMap (fun k =>
    match k.keyword, k.arg with
    | .equip, .cost cost => [equipAbility (.pay cost)]
    | .equip, .costOrExhaustUnit cost =>
      [equipAbility (.pay cost), equipAbility (.exhaustFriendly (.ofList [.ofType .unit]))]
    | _, _ => []) ++
  c.keywords.flatMap (fun k =>
    match k.keyword, k.arg with
    -- Backline: the Unit must be assigned combat damage last (CR 826)
    | .backline, _ => [.passive .always [.assignedLast]]
    -- Deploy: the Gear is killed when an opponent holds its Battlefield (CR 830).
    | .deploy, _ =>
      [.triggered (Trigger.onSelf .opponentHoldsHere)
        (EffectDef.of [] (.prim (.kill .self))) .unlimited]
    -- Quick-Draw: when the card is played, attach it to a unit its player controls (CR 819)
    | .quickDraw, _ =>
      [.triggered (Trigger.onSelf .play)
        (EffectDef.of [Choice.targetOf .one .you .anywhere [.ofType .unit]]
          (.prim (.attach .self (.slot 0)))) .unlimited]
    -- Weaponmaster: when the Unit is played, its player may Equip one of their Equipment to it
    -- for one Power less, even if it is attached already (CR 821)
    | .weaponmaster, _ =>
      [.triggered { event := .play, optional := true }
        (EffectDef.of [Choice.targetOf .one .you .anywhere [.tag ⟨"Equipment"⟩]]
          (.equipWithCost (.slot 0) .self 1)) .unlimited]
    | .hidden, _ =>
      -- Hide: pay one Power of any domain, to hide the card at a Battlefield its player controls;
      -- play: from the turn after, as a Reaction, without paying (CR 811)
      [.activated [.fromHand, .pay ⟨0, [.any]⟩] .normal hideEffect .unlimited,
       -- the card must still be hidden when the ability resolves: it can be used again while it
       -- is on the Chain
       .activated [.fromHidden] .reaction c.hiddenPlay .unlimited,
       -- with Swift Scout: hide for one Energy instead (the passive of the Legend is asked)
       .activated [.fromHand, .pay ⟨1, []⟩] .normal
         hideEnergyEffect .unlimited]
    | .empower, .cost cost =>
      -- Untranscribed cards may qualify the printed cost, so they are not playable from metadata.
      if c.status == .todo || c.abilities.any Ability.isEmpower then [] else
        [.empower [.pay cost] c.empowerLimit]
    | .vision, _ =>
      [.triggered (Trigger.onSelf .play)
        (EffectDef.of [] (.seqOf [.prim (.lookTop 1), .may (.prim (.recycleTop .you))]))
        .unlimited]
    | .hunt, .amount n =>
      [.triggered (Trigger.onSelf .conquer) (EffectDef.of [] (.prim (.gainXP .you (.const n))))
        .unlimited,
       .triggered (Trigger.onSelf .hold) (EffectDef.of [] (.prim (.gainXP .you (.const n))))
        .unlimited]
    | _, _ => [])

/-- A Unit can be played from the Champion Zone: the ability pays its cost and plays it. The cost
is the printed one: the reductions that a play from the hand gets are not applied. -/
def championPlay (c : CardDef) : List Ability :=
  match c.cost with
  | some cost =>
    if c.types.contains .unit then
      [.activated [.fromChampionZone, .pay cost] .normal
        (EffectDef.of [] (.prim (.play .self))) .unlimited]
    else []
  | none => []

/-- A Legend can use the ability a Battlefield its player controls gives it: Exhaust, attach an
Equipment its player controls to a Unit they control (Forge of the Fluft). -/
def legendAbilities (c : CardDef) : List Ability :=
  if c.types.contains .legend then
    [.activated [.exhaustSelf] .normal
      (EffectDef.of [Choice.targetOf .one .friendly .anywhere [.tag ⟨"Equipment"⟩],
          Choice.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.ifThen (.exists (Selector.all .friendly .atBattlefield
            [.ofType .battlefield, .controlled, .givesLegendsAttach]))
          (.prim (.attach (.slot 0) (.slot 1))) .nop)) .unlimited]
  else []

/-- The abilities from the card's copyable rules text, including printed keywords (CR 479.1). -/
def textAbilities (c : CardDef) : List Ability := c.abilities ++ c.printedKeywordAbilities

/-- Whether this Equipment copies the Unit's text to its own Effect Text when attaching. -/
def copiesUnitText (c : CardDef) : Bool :=
  c.abilities.any (fun
    | .passive .always mods => mods.contains .copiesUnitText
    | _ => false)

/-- The abilities from keywords and the implicit abilities of Champion Zone cards and Legends. -/
def keywordAbilities (c : CardDef) : List Ability :=
  c.printedKeywordAbilities ++ c.championPlay ++ c.legendAbilities

/-- The abilities of the card itself: the written ones, and those of its keywords. -/
def fullAbilities (c : CardDef) : List Ability := c.abilities ++ c.keywordAbilities

/-- The abilities of the card itself, then the abilities it grants. The place of an ability in
this list is what a trigger on the Chain remembers. -/
def allAbilities (c : CardDef) : List Ability := c.fullAbilities ++ c.grants

/-- The identity of a card's name: short name and subtitle together (CR 103.3.b, 132). Two
cards have the same name exactly when their name keys are equal. -/
def nameKey (c : CardDef) : String × Option String := (c.name, c.subtitle)

/-- The card has the type `t`. -/
def hasType (c : CardDef) (t : CardType) : Bool := c.types.contains t

/-- Identify token definitions, including the four Origins tokens numbered with the main set
(CR 179, 185). -/
def isTokenCard (c : CardDef) : Bool :=
  c.id.code.startsWith "TKN-" || (c.id.code.splitOn "-T").length > 1 ||
    ["OGN-271", "OGN-272", "OGN-273", "OGN-274"].contains c.id.code

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

/-- The default deck limit: a Unique card is limited to one copy, other cards to three
(CR 103.3.b, 825). -/
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
