module

public import Riftbound.Card.CardDef

/-!
# Unleashed (UNL)

The cards first printed in Unleashed. Each card has a generated block (the official text and
the metadata) and, right after it, the part written by hand (the effect and the
implementation status). `scripts/gen_lean.py` rewrites the generated blocks only
(docs/card-data.md §4.1).
-/

@[expose] public section

namespace RiftboundCards.Unleashed

open Riftbound

/-- Look at the top `n` cards of the Main Deck, may reveal one that has the properties and draw it,
and recycle the rest. A bonus for revealing a matching card follows the recycle. -/
def lookDraw (n : Nat) (fs : List Filter) (bonus : Option (Filter × Effect) := none) : Effect :=
  let eligible := Filter.lookedAt :: fs
  let picked := Selector.var pickVar
  let take := Effect.seqOf [.prim (.reveal picked), .prim (.drawLooked picked), .recycleLooked]
  let afterPick := match bonus with
    | none => take
    | some (property, effect) =>
      let qualified := Selector.all .friendly .inMainDeck [.sameAs picked, property]
      .ifThen (.cmp .gt (.count qualified) (.const 0)) (.seqOf [take, effect]) take
  let choose := Effect.chooseObject .friendly .inMainDeck (.ofList eligible) afterPick
  .lookAtTop n (.ifThen (.cmp .gt (.count (.all .friendly .inMainDeck eligible)) (.const 0))
    (.eitherOf (.ofList [choose, .recycleLooked])) .recycleLooked)

/-- The card is a Bird, a Cat, a Dog or a Poro. -/
def petFilter : Filter :=
  .either (.tag ⟨"Bird"⟩) (.either (.tag ⟨"Cat"⟩) (.either (.tag ⟨"Dog"⟩) (.tag ⟨"Poro"⟩)))

/-- Ivern buffs a friendly Unit after recycling if the revealed Unit is a pet. -/
def ivernLook : Effect :=
  lookDraw 3 [.ofType .unit]
    (some (petFilter, .prim (.buff (Selector.one .friendly .anywhere [.ofType .unit]))))

/-- Predict 1: look at the top card of the Main Deck, and may recycle it. -/
def predict1 : Effect := .seqOf [.prim (.lookTop 1), .may (.prim (.recycleTop .you))]

/-- Open the private Predict decision and resolve the kept and recycled cards. -/
def predict2 : Effect := .prim (.predict (.const 2))

/-- Ready up to two runes. -/
def readyTwoRunes : Effect :=
  .seqOf [.may (.prim (.ready (Selector.one .friendly .atBase [.ofType .rune, .exhausted]))),
    .may (.prim (.ready (Selector.one .friendly .atBase [.ofType .rune, .exhausted])))]

/-- Another friendly Dragon. -/
def otherDragon : Selector := Selector.all .friendly .anywhere [.ofType .unit, .tag ⟨"Dragon"⟩, .notSelf]

/-- A friendly unit other than the one the ability belongs to. -/
def otherFriendlyUnit : Selector := Selector.all .friendly .anywhere [.ofType .unit, .notSelf]

/-- A mode that has not been chosen yet (Curtain Call): it is noted, then done. -/
def freshMode (k : Nat) (e : Effect) : Effect :=
  .ifThen (.not (.marked (.modeUsed k))) (.seqOf [.prim (.markOn .self (.modeUsed k)), e]) .nop

/-- The names of the tags the cards of the game have. -/
def allTagNames : List String :=
  ["Ahri", "Akali", "Akshan", "Ambessa", "Anivia", "Annie",
  "Aphelios", "Ashe", "Azir", "Bandle City", "Bard", "Bilgewater",
  "Bird", "Blitzcrank", "Caitlyn", "Cat", "Darius", "Demacia",
  "Demon", "Device", "Diana", "Dog", "Dr. Mundo", "Dragon",
  "Draven", "Ekko", "Elite", "Equipment", "Evelynn", "Ezreal",
  "Fae", "Fiora", "Fizz", "Freljord", "Galio", "Gangplank",
  "Garen", "Graves", "Heimerdinger", "Hwei", "Icathia", "Illaoi",
  "Ionia", "Irelia", "Ivern", "Ixtal", "Janna", "Jarvan IV",
  "Jax", "Jayce", "Jhin", "Jinx", "K'Sante", "Kai'Sa",
  "Karthus", "Katarina", "Kathkan", "Kayle", "Kayn", "Kennen",
  "Kha'Zix", "Kog'Maw", "LeBlanc", "Lee Sin", "Leona", "Lillia",
  "Lucian", "Lulu", "Lux", "Malzahar", "Master Yi", "Mech",
  "Mel", "Miss Fortune", "Mordekaiser", "Morgana", "Mount Targon", "Nami",
  "Nasus", "Neeko", "Nidalee", "Nilah", "Nocturne", "Noxus",
  "Orianna", "Ornn", "Piltover", "Pirate", "Poppy", "Poro",
  "Pyke", "Qiyana", "Recruit", "Rek'Sai", "Rell", "Renata Glasc",
  "Renekton", "Rengar", "Riven", "Rumble", "Sentinel", "Seraphine",
  "Sett", "Shadow Isles", "Shen", "Shurima", "Sivir", "Sona",
  "Soraka", "Spider", "Spirit", "Swain", "Syndra", "Taric",
  "Teemo", "The Void", "Trifarian", "Tryndamere", "Twisted Fate", "Udyr",
  "Vayne", "Vex", "Vi", "Viktor", "Volibear", "Warwick",
  "Xerath", "Xin Zhao", "Yasuo", "Yone", "Yordle", "Yuumi",
  "Zaun", "Zed", "Ziggs", "Zilean"]

/-- Name a tag: the object gains it (The List), one of all the tags that there are. -/
def nameATag : Effect :=
  .eitherOf (EffectList.ofList (allTagNames.map (fun t => Effect.prim (.gainTag .self t))))

/-- Dancing Grenade: deal 2 to a unit, and 1 more for each time it has dealt damage this turn; the
controller of the unit may play the spell again for one Power, and so on (`n` more times). -/
def grenade (n bonus : Nat) : Effect :=
  .seqOf [.prim (.deal (Selector.one .any .anywhere [.ofType .unit]) (.const (2 + bonus))),
    match n with
    | 0 => .nop
    | n + 1 =>
      .eachPlayer .eachOpponent
        (.ifThen (.canPay ⟨0, [.any]⟩)
          (.may (.seqOf [.prim (.pay ⟨0, [.any]⟩), grenade n (bonus + 1)])) .nop)]

/-- The number of the tags Bird, Cat, Dog and Poro that the player's units have among them. -/
def petTags : Amount :=
  .add (.add (.min (.const 1) (.count (Selector.all .friendly .anywhere [.ofType .unit, .tag ⟨"Bird"⟩])))
      (.min (.const 1) (.count (Selector.all .friendly .anywhere [.ofType .unit, .tag ⟨"Cat"⟩]))))
    (.add (.min (.const 1) (.count (Selector.all .friendly .anywhere [.ofType .unit, .tag ⟨"Dog"⟩])))
      (.min (.const 1) (.count (Selector.all .friendly .anywhere [.ofType .unit, .tag ⟨"Poro"⟩]))))

-- BEGIN GENERATED UNL-001
/--
**Arena Kingpin** — Unit · Fury · Energy 5 · Might 3
Printings: UNL-001/219

> I enter ready.
> :rb_exhaust:: Give a unit +3 :rb_might: this turn.
-/
def UNL_001.meta : CardDef :=
  { id := ⟨"UNL-001"⟩,
    name := "Arena Kingpin",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨5, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Arena Kingpin. -/
def UNL_001 : CardDef :=
  { UNL_001.meta with
    abilities := [.passive .always [.entersReady .self],
      .activated [.exhaustSelf] .normal
        (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-002
/--
**Inferna** — Unit · Fury · Energy 2 · Might 1
Printings: UNL-002/219

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> [Assault 2] (+2 :rb_might: while I'm an attacker.)
-/
def UNL_002.meta : CardDef :=
  { id := ⟨"UNL-002"⟩,
    name := "Inferna",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .ambush },
      { keyword := .assault, arg := .amount 2 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Inferna. -/
def UNL_002 : CardDef :=
  { UNL_002.meta with
    status := .full }

-- BEGIN GENERATED UNL-003
/--
**Mischievous Marai** — Unit · Fury · Energy 2 · Might 2
Printings: UNL-003/219

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me to a battlefield, deal 2 to an enemy unit here.
-/
def UNL_003.meta : CardDef :=
  { id := ⟨"UNL-003"⟩,
    name := "Mischievous Marai",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Mischievous Marai. -/
def UNL_003 : CardDef :=
  { UNL_003.meta with
    abilities := [.triggered { event := .play, condition := .matches .self .onBattlefield }
      (.of [.targetOf .one .enemy .here [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 2)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-004
/--
**Prepared Neophyte** — Unit · Fury · Energy 3 · Might 1
Printings: UNL-004/219

> If you've spent :rb_energy_4: or more to play a spell this turn, I have +4 :rb_might:.
-/
def UNL_004.meta : CardDef :=
  { id := ⟨"UNL-004"⟩,
    name := "Prepared Neophyte",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 1,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Prepared Neophyte. -/
def UNL_004 : CardDef :=
  { UNL_004.meta with
    -- +4 Might while I have spent 4 Energy or more to play a spell this turn
    abilities := [.passive (.spentOnSpell 4) [.mightPlus .self (.const 4)]],
    status := .full }

-- BEGIN GENERATED UNL-005
/--
**Revna the Lorekeeper** — Unit · Fury · Energy 7 + Power 1 · Might 7
Printings: UNL-005/219

> [Ganking] (I can move from battlefield to battlefield.)
> When you play a spell, if you spent :rb_energy_4: or more, ready me.
-/
def UNL_005.meta : CardDef :=
  { id := ⟨"UNL-005"⟩,
    name := "Revna the Lorekeeper",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.fury],
    cost := some ⟨7, [.domain .fury]⟩,
    might := some 7,
    keywords := [{ keyword := .ganking }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Revna the Lorekeeper. -/
def UNL_005 : CardDef :=
  { UNL_005.meta with
    abilities := [.triggered
      { event := .play, subject := Selector.all .you .anywhere [.ofType .spell],
        condition := .cmp .ge .eventAmount (.const 4) }
      (.of [] (.prim (.ready .self))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-006
/--
**Sharkling** — Unit · Fury · Energy 3 · Might 1
Printings: UNL-006/219

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> [Assault 4] (+4 :rb_might: while I'm an attacker.)
-/
def UNL_006.meta : CardDef :=
  { id := ⟨"UNL-006"⟩,
    name := "Sharkling",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 1,
    keywords := [{ keyword := .accelerate },
      { keyword := .assault, arg := .amount 4 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Sharkling. -/
def UNL_006 : CardDef :=
  { UNL_006.meta with
    status := .full }

-- BEGIN GENERATED UNL-007
/--
**Smite** — Spell · Fury · Energy 2 + Power 1
Printings: UNL-007/219

> [Action] (Play on your turn or in showdowns.)
> Deal 3 to a unit at a battlefield. If it would die this turn, banish it instead.
-/
def UNL_007.meta : CardDef :=
  { id := ⟨"UNL-007"⟩,
    name := "Smite",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Smite. -/
def UNL_007 : CardDef :=
  { UNL_007.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit, .onBattlefield]]
      (.seqOf [.prim (.markOn (.slot 0) .banishInstead), .prim (.deal (.slot 0) (.const 3))])),
    status := .full }

-- BEGIN GENERATED UNL-008
/--
**Towering Pairofant** — Unit · Fury · Energy 6 · Might 6
Printings: UNL-008/219

> [Assault] (+1 :rb_might: while I'm an attacker.)
> If a unit died this turn, I enter ready.
-/
def UNL_008.meta : CardDef :=
  { id := ⟨"UNL-008"⟩,
    name := "Towering Pairofant",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.fury],
    cost := some ⟨6, []⟩,
    might := some 6,
    keywords := [{ keyword := .assault, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Towering Pairofant. -/
def UNL_008 : CardDef :=
  { UNL_008.meta with
    -- if a unit died this turn, I enter ready
    abilities := [.passive (.or (.friendlyNoted .unitDied) .enemyUnitDied) [.entersReady .self]],
    status := .full }

-- BEGIN GENERATED UNL-009
/--
**Upstage Comedy** — Spell · Fury · Energy 2
Printings: UNL-009/219

> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Ready a unit.
-/
def UNL_009.meta : CardDef :=
  { id := ⟨"UNL-009"⟩,
    name := "Upstage Comedy",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Upstage Comedy. -/
def UNL_009 : CardDef :=
  { UNL_009.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.prim (.ready (.slot 0)))),
    status := .full }

-- BEGIN GENERATED UNL-010
/--
**Vault Breaker** — Spell · Fury · Energy 1 + Power 1
Printings: UNL-010/219

> [Action] (Play on your turn or in showdowns.)
> Give a unit [Assault 2] and [Ganking] this turn. (+2 :rb_might: while it's an attacker. It can
> move from battlefield to battlefield.)
-/
def UNL_010.meta : CardDef :=
  { id := ⟨"UNL-010"⟩,
    name := "Vault Breaker",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨1, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Vault Breaker. -/
def UNL_010 : CardDef :=
  { UNL_010.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.grant (.slot 0) (.keyword .it { keyword := .assault, arg := .amount 2 }) .thisTurn,
        .grant (.slot 0) (.keyword .it { keyword := .ganking }) .thisTurn])),
    status := .full }

-- BEGIN GENERATED UNL-011
/--
**Fresh Beans** — Gear · Fury · Energy 2
Printings: UNL-011/219

> When you play a unit during a showdown, you may exhaust this to draw 1.
-/
def UNL_011.meta : CardDef :=
  { id := ⟨"UNL-011"⟩,
    name := "Fresh Beans",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Fresh Beans. -/
def UNL_011 : CardDef :=
  let drawOn (event : TriggerEvent) : Ability :=
    .triggered {
      event, subject := Selector.all .you .anywhere [.ofType .unit],
      condition := .showdownNow, optional := true, cost := .exhaustSelf }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited
  { UNL_011.meta with
    abilities := [drawOn .play, drawOn .playToken],
    status := .full }

-- BEGIN GENERATED UNL-012
/--
**Lord Broadmane** — Unit · Fury · Energy 5 + Power 1 · Might 5
Printings: UNL-012/219

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> When you play me, give your other units here [Assault] this turn. (+1 :rb_might: while they're
> attackers.)
-/
def UNL_012.meta : CardDef :=
  { id := ⟨"UNL-012"⟩,
    name := "Lord Broadmane",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 5,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Lord Broadmane. -/
def UNL_012 : CardDef :=
  { UNL_012.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.grant (Selector.all .you .here [.ofType .unit, .notSelf])
        (.keyword .it { keyword := .assault }) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-013
/--
**Lotus Trap** — Spell · Fury · Energy 2
Printings: UNL-013/219

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a unit. Double all damage that would be dealt to it this turn.
-/
def UNL_013.meta : CardDef :=
  { id := ⟨"UNL-013"⟩,
    name := "Lotus Trap",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Lotus Trap. -/
def UNL_013 : CardDef :=
  { UNL_013.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.prim (.markOn (.slot 0) .doubleDamage))),
    status := .full }

-- BEGIN GENERATED UNL-014
/--
**Monster Harpoon** — Spell · Fury · Energy 1 + Power 1
Printings: UNL-014/219

> [Action] (Play on your turn or in showdowns.)
> Deal 2 to a unit at a battlefield. If you control a facedown card, deal 4 to it instead.
-/
def UNL_014.meta : CardDef :=
  { id := ⟨"UNL-014"⟩,
    name := "Monster Harpoon",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨1, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Monster Harpoon. -/
def UNL_014 : CardDef :=
  { UNL_014.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.ifThen .hasHidden
        (.prim (.deal (.slot 0) (.const 4))) (.prim (.deal (.slot 0) (.const 2))))),
    status := .full }

-- BEGIN GENERATED UNL-015
/--
**Right of Conquest** — Spell · Fury · Energy 3 + Power 1
Printings: UNL-015/219

> Draw 1, then draw 1 for each battlefield you or allies control.
-/
def UNL_015.meta : CardDef :=
  { id := ⟨"UNL-015"⟩,
    name := "Right of Conquest",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Right of Conquest. -/
def UNL_015 : CardDef :=
  { UNL_015.meta with
    spellEffect := some (.of [] (.seqOf [.prim (.draw .you (.const 1)),
      .repeatN (.count (Selector.all .any .anywhere [.ofType .battlefield, .not .openBf, .not .controlledByOpponent]))
        (.prim (.draw .you (.const 1)))])),
    status := .full }

-- BEGIN GENERATED UNL-016
/--
**Scorchclaw** — Unit · Fury · Energy 3 + Power 1 · Might 3
Printings: UNL-016/219

> [Hunt 2] (When I conquer or hold, gain 2 XP.)
> [Level 3][>] I have +1 :rb_might: and enter ready. (While you have 3+ XP, get the effect.)
-/
def UNL_016.meta : CardDef :=
  { id := ⟨"UNL-016"⟩,
    name := "Scorchclaw",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    might := some 3,
    keywords := [{ keyword := .hunt, arg := .amount 2 },
      { keyword := .level, arg := .amount 3 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Scorchclaw. -/
def UNL_016 : CardDef :=
  { UNL_016.meta with
    abilities := [.passive (.cmp .ge .xp (.const 3)) [.mightPlus .self (.const 1), .entersReady .self]],
    status := .full }

-- BEGIN GENERATED UNL-017
/--
**Square Up** — Spell · Fury · Energy 4
Printings: UNL-017/219

> [Repeat] — Discard 1 (You may pay the additional cost to repeat this spell's effect.)
> Give a unit [Assault 4] this turn. (+4 :rb_might: while it's an attacker.)
-/
def UNL_017.meta : CardDef :=
  { id := ⟨"UNL-017"⟩,
    name := "Square Up",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    keywords := [{ keyword := .repeat_ }],
    sets := [⟨"UNL"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Square Up. -/
def UNL_017 : CardDef :=
  { UNL_017.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.grant (.slot 0) (.keyword .it { keyword := .assault, arg := .amount 4 }) .thisTurn,
        .ifThen (.cmp .ge (.handSize .you) (.const 1))
          (.may (.seqOf [.prim (.discard .you (.const 1)),
            .grant (.slot 0) (.keyword .it { keyword := .assault, arg := .amount 4 }) .thisTurn]))
          .nop])),
    status := .drafted }

-- BEGIN GENERATED UNL-018
/--
**Yeti Brawler** — Unit · Fury · Energy 6 · Might 6
Printings: UNL-018/219

> When I conquer, if you assigned 3 or more excess damage, play two Gold gear tokens exhausted.
> (They have "[Reaction][>] Kill this, :rb_exhaust:: [Add] :rb_rune_rainbow:.")
-/
def UNL_018.meta : CardDef :=
  { id := ⟨"UNL-018"⟩,
    name := "Yeti Brawler",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨6, []⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Yeti Brawler. -/
def UNL_018 : CardDef :=
  { UNL_018.meta with
    abilities := [.triggered { event := .conquer, condition := .excessAtLeast 3 }
      (.of [] (.prim (.create "Gold" (.const 2) .atBase false))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-019
/--
**Blighted Battleaxe** — Gear · Fury · Energy 4 · Might 4
Printings: UNL-019/219

> [Equip] :rb_energy_1::rb_rune_fury: (:rb_energy_1::rb_rune_fury:: Attach this to a unit you
> control.)

Effect (given to the unit it is attached to):

> At the end of your turn, if I didn't conquer this turn, unattach this and deal 4 to me.
-/
def UNL_019.meta : CardDef :=
  { id := ⟨"UNL-019"⟩,
    name := "Blighted Battleaxe",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    mightBonus := some 4,
    keywords := [{ keyword := .equip, arg := .cost ⟨1, [.domain .fury]⟩ }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Blighted Battleaxe. -/
def UNL_019 : CardDef :=
  { UNL_019.meta with
    grants := [
      .triggered (.onSelf .conquer) (.of [] (.prim (.markOn .self .conqueredHere))) .unlimited,
      .triggered
        { condition := .not (.marked .conqueredHere), event := .at_ .endOfTurn }
        (.of [] (.seqOf [
          .prim (.detach (Selector.all .any .anywhere [.attachedTo .self, .named "Blighted Battleaxe"])),
          .prim (.deal .self (.const 4))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-020
/--
**Dancing Grenade** — Spell · Fury · Energy 2 + Power 1
Printings: UNL-020/219

> Deal 2 to a unit. Its controller may play this spell again for :rb_rune_rainbow:. If they do,
> this deals 1 additional Bonus Damage for each time this spell has dealt damage this turn.
-/
def UNL_020.meta : CardDef :=
  { id := ⟨"UNL-020"⟩,
    name := "Dancing Grenade",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Dancing Grenade. -/
def UNL_020 : CardDef :=
  { UNL_020.meta with
    spellEffect := some (.of [] (grenade 3 0)),
    status := .drafted }

-- BEGIN GENERATED UNL-021
/--
**Grim Apothecary** — Unit · Fury · Energy 3 · Might 3
Printings: UNL-021/219

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> When you play me, you may return a friendly unit at a battlefield to its owner's hand.
-/
def UNL_021.meta : CardDef :=
  { id := ⟨"UNL-021"⟩,
    name := "Grim Apothecary",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Grim Apothecary. -/
def UNL_021 : CardDef :=
  { UNL_021.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.may (.prim (.returnToHand (Selector.one .friendly .atBattlefield [.ofType .unit])))))
        .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-022
/--
**Jhin, Murderous Artist** — Unit · Fury · Energy 4 + Power 1 · Might 4
Printings: UNL-022/219, UNL-022a/219

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> [Ganking] (I can move from battlefield to battlefield.)
> When I move, [Add] :rb_energy_1::rb_rune_rainbow:. (Abilities that add resources can't be
> reacted to.)
-/
def UNL_022.meta : CardDef :=
  { id := ⟨"UNL-022"⟩,
    name := "Jhin",
    subtitle := some "Murderous Artist",
    types := [.unit],
    tags := [⟨"Jhin"⟩, ⟨"Ionia"⟩],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    might := some 4,
    keywords := [{ keyword := .deflect, arg := .amount 1 },
      { keyword := .ganking }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Jhin. -/
def UNL_022 : CardDef :=
  { UNL_022.meta with
    abilities := [.triggered (.onSelf .move)
      (.of [] (.seqOf [.prim (.addEnergy .you (.const 1) none),
        .prim (.addPower .you (.const 1) none none)])) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-023
/--
**Katarina, Reckless** — Unit · Fury · Energy 5 + Power 1 · Might 5
Printings: UNL-023/219

> When you hide a card, ready me.
> When you play a card from face down, deal 2 to an enemy unit.
-/
def UNL_023.meta : CardDef :=
  { id := ⟨"UNL-023"⟩,
    name := "Katarina",
    subtitle := some "Reckless",
    types := [.unit],
    tags := [⟨"Katarina"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Katarina. -/
def UNL_023 : CardDef :=
  { UNL_023.meta with
    abilities := [
      .triggered (.onSelf .hide) (.of [] (.prim (.ready .self))) .unlimited,
      .triggered (.onSelf .playHidden)
        (.of [.targetOf .one .enemy .anywhere [.ofType .unit]] (.prim (.deal (.slot 0) (.const 2))))
        .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-024
/--
**Rengar, Unseen** — Unit · Fury · Energy 4 + Power 1 · Might 4
Printings: UNL-024/219, UNL-024a/219

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> [Assault 2] (+2 :rb_might: while I'm an attacker.)
> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> [Ganking] (I can move from battlefield to battlefield.)
-/
def UNL_024.meta : CardDef :=
  { id := ⟨"UNL-024"⟩,
    name := "Rengar",
    subtitle := some "Unseen",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Rengar"⟩, ⟨"Ixtal"⟩],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    might := some 4,
    keywords := [{ keyword := .accelerate },
      { keyword := .assault, arg := .amount 2 },
      { keyword := .deflect, arg := .amount 1 },
      { keyword := .ganking }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Rengar, Unseen. -/
def UNL_024 : CardDef :=
  { UNL_024.meta with
    status := .full }

-- BEGIN GENERATED UNL-025
/--
**Undying Legion** — Unit · Fury · Energy 3 · Might 3
Printings: UNL-025/219

> [Legion][>] You may play me from your trash for :rb_energy_3::rb_rune_fury:. (Get the effect
> if you've played another card this turn.)
-/
def UNL_025.meta : CardDef :=
  { id := ⟨"UNL-025"⟩,
    name := "Undying Legion",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .legion }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Undying Legion. -/
def UNL_025 : CardDef :=
  { UNL_025.meta with
    abilities := [.activated [.fromTrash, .pay ⟨3, [.domain .fury]⟩] .normal
      (.of [] (.ifThen .playedAnother (.prim (.play .self)) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-026
/--
**Xerath, Freed** — Unit · Fury · Energy 5 · Might 5
Printings: UNL-026/219

> :rb_rune_fury:, :rb_exhaust:: Deal 3 to a unit. Use this ability only while I'm at a
> battlefield.
-/
def UNL_026.meta : CardDef :=
  { id := ⟨"UNL-026"⟩,
    name := "Xerath",
    subtitle := some "Freed",
    types := [.unit],
    tags := [⟨"Shurima"⟩, ⟨"Xerath"⟩],
    domains := [.fury],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Xerath. -/
def UNL_026 : CardDef :=
  { UNL_026.meta with
    abilities := [.activated [.pay ⟨0, [.domain .fury]⟩, .exhaustSelf, .fromBattlefield] .normal
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 3))))
        .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-027
/--
**Inviolus Vox** — Unit · Fury · Energy 8 + Power 2 · Might 8
Printings: UNL-027/219

> When I conquer, give a friendly unit +8 :rb_might: this turn.
-/
def UNL_027.meta : CardDef :=
  { id := ⟨"UNL-027"⟩,
    name := "Inviolus Vox",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Mount Targon"⟩],
    domains := [.fury],
    cost := some ⟨8, [.domain .fury, .domain .fury]⟩,
    might := some 8,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Inviolus Vox. -/
def UNL_027 : CardDef :=
  { UNL_027.meta with
    abilities := [.triggered (.onSelf .conquer)
        (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 8)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-028
/--
**Pyke, Dockside Butcher** — Unit · Fury · Energy 3 · Might 2
Printings: UNL-028/219, UNL-028a/219

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Ganking] (I can move from battlefield to battlefield.)
> You may pay :rb_rune_fury: as an additional cost to play me.
> When you play me, if you paid the additional cost, ready me and give me +2 :rb_might: this
> turn.
-/
def UNL_028.meta : CardDef :=
  { id := ⟨"UNL-028"⟩,
    name := "Pyke",
    subtitle := some "Dockside Butcher",
    types := [.unit],
    tags := [⟨"Pyke"⟩, ⟨"Bilgewater"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 2,
    keywords := [{ keyword := .hidden },
      { keyword := .ganking }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Pyke. -/
def UNL_028 : CardDef :=
  { UNL_028.meta with
    additionalCost := some ⟨0, [.domain .fury]⟩,
    abilities := [.triggered { event := .play, condition := .paid }
      (.of [] (.seqOf [.prim (.ready .self),
        .grant .self (.mightPlus .it (.const 2)) .thisTurn])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-029
/--
**Red Brambleback** — Unit · Fury · Energy 4 + Power 1 · Might 4
Printings: UNL-029/219, UNL-029a/219

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> Your conquer effects for conquering here trigger an additional time.
> When I conquer, [Buff] a friendly unit. (Give it a +1 :rb_might: buff if it doesn't have one.)
-/
def UNL_029.meta : CardDef :=
  { id := ⟨"UNL-029"⟩,
    name := "Red Brambleback",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    might := some 4,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Red Brambleback. -/
def UNL_029 : CardDef :=
  { UNL_029.meta with
    abilities := [.passive .always [.triggersExtra .conquer .here],
      .triggered (.onSelf .conquer)
        (.of [] (.prim (.buff (Selector.one .friendly .anywhere [.ofType .unit])))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-030
/--
**Vi, Hotheaded** — Unit · Fury · Energy 4 · Might 3
Printings: UNL-030/219, UNL-030a/219

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> :rb_energy_2::rb_rune_fury:: Double my Might this turn.
-/
def UNL_030.meta : CardDef :=
  { id := ⟨"UNL-030"⟩,
    name := "Vi",
    subtitle := some "Hotheaded",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Vi"⟩, ⟨"Zaun"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 3,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Vi. -/
def UNL_030 : CardDef :=
  { UNL_030.meta with
    abilities := [.activated [.pay ⟨2, [.domain .fury]⟩] .normal
      (.of [] (.grant .self (.mightPlus .it (.mightOf .self)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-031
/--
**Combat Experience** — Spell · Calm · Energy 1
Printings: UNL-031/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a unit +1 :rb_might: this turn.
> [Level 6][>] Give it +3 :rb_might: this turn instead. (While you have 6+ XP, get the effect.)
-/
def UNL_031.meta : CardDef :=
  { id := ⟨"UNL-031"⟩,
    name := "Combat Experience",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction },
      { keyword := .level, arg := .amount 6 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Combat Experience. -/
def UNL_031 : CardDef :=
  { UNL_031.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.ifThen (.cmp .ge .xp (.const 6))
        (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)
        (.grant (.slot 0) (.mightPlus .it (.const 1)) .thisTurn))),
    status := .drafted }

-- BEGIN GENERATED UNL-032
/--
**Double Trouble** — Spell · Calm · Energy 2
Printings: UNL-032/219

> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Look at the top 3 cards of your Main Deck. You may reveal a unit from among them and draw it.
> Recycle the rest.
-/
def UNL_032.meta : CardDef :=
  { id := ⟨"UNL-032"⟩,
    name := "Double Trouble",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Double Trouble. -/
def UNL_032 : CardDef :=
  { UNL_032.meta with
    spellEffect := some (.of [] (lookDraw 3 [.ofType .unit])),
    status := .drafted }

-- BEGIN GENERATED UNL-033
/--
**Frisky Hunter** — Unit · Calm · Energy 4 · Might 3
Printings: UNL-033/219

> When you play me, play a 1 :rb_might: Bird unit token with [Deflect] here. (Opponents must pay
> :rb_rune_rainbow: to choose it with a spell or ability.)
-/
def UNL_033.meta : CardDef :=
  { id := ⟨"UNL-033"⟩,
    name := "Frisky Hunter",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Zaun"⟩],
    domains := [.calm],
    cost := some ⟨4, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Frisky Hunter. -/
def UNL_033 : CardDef :=
  { UNL_033.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.create "Bird" (.const 1) .here false))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-034
/--
**Herald of Spring** — Unit · Calm · Energy 4 + Power 1 · Might 4
Printings: UNL-034/219

> [Hunt] (When I conquer or hold, gain 1 XP.)
> When you play me, gain 2 XP.
-/
def UNL_034.meta : CardDef :=
  { id := ⟨"UNL-034"⟩,
    name := "Herald of Spring",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    might := some 4,
    keywords := [{ keyword := .hunt, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Herald of Spring. -/
def UNL_034 : CardDef :=
  { UNL_034.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.gainXP .you (.const 2)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-035
/--
**Monch** — Unit · Calm · Energy 6 · Might 6
Printings: UNL-035/219

> If an opponent controls a stunned unit, I cost :rb_energy_2: less and enter ready.
-/
def UNL_035.meta : CardDef :=
  { id := ⟨"UNL-035"⟩,
    name := "Monch",
    types := [.unit],
    tags := [⟨"Bandle City"⟩],
    domains := [.calm],
    cost := some ⟨6, []⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Monch. -/
def UNL_035 : CardDef :=
  { UNL_035.meta with
    abilities := [.passive (.exists (Selector.all .enemy .anywhere [.ofType .unit, .stunned]))
      [.costMinus .self (.const 2), .entersReady .self]],
    status := .drafted }

-- BEGIN GENERATED UNL-036
/--
**Mutated Mouser** — Unit · Calm · Energy 2 · Might 1
Printings: UNL-036/219

> [Shield 2] (+2 :rb_might: while I'm a defender.)
> [Tank] (I must be assigned combat damage first.)
-/
def UNL_036.meta : CardDef :=
  { id := ⟨"UNL-036"⟩,
    name := "Mutated Mouser",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Bilgewater"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .shield, arg := .amount 2 },
      { keyword := .tank }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Mutated Mouser. -/
def UNL_036 : CardDef :=
  { UNL_036.meta with
    status := .full }

-- BEGIN GENERATED UNL-037
/--
**Shadow Watcher** — Unit · Calm · Energy 4 + Power 1 · Might 5
Printings: UNL-037/219

> If a friendly unit died during your Beginning Phase this turn, I enter ready.
-/
def UNL_037.meta : CardDef :=
  { id := ⟨"UNL-037"⟩,
    name := "Shadow Watcher",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Shadow Watcher. -/
def UNL_037 : CardDef :=
  { UNL_037.meta with
    abilities := [.passive (.and (.friendlyNoted .diedInBeginning) .yourTurn) [.entersReady .self]],
    status := .full }

-- BEGIN GENERATED UNL-038
/--
**Skyward Strike** — Spell · Calm · Energy 2 + Power 1
Printings: UNL-038/219

> Move an enemy unit.
> [Level 6][>] [Stun] an enemy unit. (While you have 6+ XP, get the effect. A stunned unit
> doesn't deal combat damage this turn.)
-/
def UNL_038.meta : CardDef :=
  { id := ⟨"UNL-038"⟩,
    name := "Skyward Strike",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, [.domain .calm]⟩,
    keywords := [{ keyword := .level, arg := .amount 6 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Skyward Strike. -/
def UNL_038 : CardDef :=
  { UNL_038.meta with
    spellEffect := some (.of [.targetOf .one .enemy .anywhere [.ofType .unit]]
      (.seqOf [.eitherOf (.cons (.prim (.move (.slot 0) .base))
            (.cons (.prim (.move (.slot 0) (.at_ (Selector.one .any .anywhere [.ofType .battlefield]))))
              .nil)),
        .ifThen (.cmp .ge .xp (.const 6)) (.prim (.stun (Selector.one .enemy .anywhere [.ofType .unit]))) .nop])),
    status := .drafted }

-- BEGIN GENERATED UNL-039
/--
**Soul Sword** — Gear · Calm · Energy 1 · Might 1
Printings: UNL-039/219

> [Equip] :rb_rune_calm: (:rb_rune_calm:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Level 3][>] I have an additional +1 :rb_might:. (While you have 3+ XP, get the effect.)
-/
def UNL_039.meta : CardDef :=
  { id := ⟨"UNL-039"⟩,
    name := "Soul Sword",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .calm]⟩ }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Soul Sword. -/
def UNL_039 : CardDef :=
  { UNL_039.meta with
    grants := [.passive (.cmp .ge .xp (.const 3)) [.mightPlus .self (.const 1)]],
    status := .full }

-- BEGIN GENERATED UNL-040
/--
**Wuju Apprentice** — Unit · Calm · Energy 2 · Might 2
Printings: UNL-040/219

> [Hunt] (When I conquer or hold, gain 1 XP.)
> [Level 6][>] When you play me, draw 1. (While you have 6+ XP, get the effect.)
-/
def UNL_040.meta : CardDef :=
  { id := ⟨"UNL-040"⟩,
    name := "Wuju Apprentice",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .hunt, arg := .amount 1 },
      { keyword := .level, arg := .amount 6 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Wuju Apprentice. -/
def UNL_040 : CardDef :=
  { UNL_040.meta with
    abilities := [.triggered { event := .play, condition := .cmp .ge .xp (.const 6) }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-041
/--
**Allay, Eager Admirer** — Unit · Calm · Energy 3 · Might 3
Printings: UNL-041/219

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> While I'm at a battlefield, your other units here have [Deflect].
-/
def UNL_041.meta : CardDef :=
  { id := ⟨"UNL-041"⟩,
    name := "Allay, Eager Admirer",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Allay, Eager Admirer. -/
def UNL_041 : CardDef :=
  { UNL_041.meta with
    abilities := [.passive (.matches .self .onBattlefield)
      [.keyword (Selector.all .friendly .here [.ofType .unit, .notSelf]) { keyword := .deflect }]],
    status := .drafted }

-- BEGIN GENERATED UNL-042
/--
**Back Off** — Spell · Calm · Energy 3
Printings: UNL-042/219

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> [Stun] a unit. (It doesn't deal combat damage this turn.)
> If you played this from your hand, draw 1.
-/
def UNL_042.meta : CardDef :=
  { id := ⟨"UNL-042"⟩,
    name := "Back Off",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Back Off. -/
def UNL_042 : CardDef :=
  { UNL_042.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.prim (.stun (.slot 0)),
        .ifThen (.not (.matches .self .playedFromElsewhere)) (.prim (.draw .you (.const 1))) .nop])),
    status := .full }

-- BEGIN GENERATED UNL-043
/--
**Enthusiastic Promoter** — Unit · Calm · Energy 3 · Might 2
Printings: UNL-043/219

> [Backline] (I must be assigned combat damage last.)
> When I hold, [Buff] all units here. (Give each a +1 :rb_might: buff if it doesn't have one.)
-/
def UNL_043.meta : CardDef :=
  { id := ⟨"UNL-043"⟩,
    name := "Enthusiastic Promoter",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 2,
    keywords := [{ keyword := .backline }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Enthusiastic Promoter. -/
def UNL_043 : CardDef :=
  { UNL_043.meta with
    abilities := [.triggered (.onSelf .hold)
      (.of [] (.prim (.buff (Selector.all .any .here [.ofType .unit])))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-044
/--
**Flurry of Feathers** — Spell · Calm · Energy 4 + Power 2
Printings: UNL-044/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose one —Counter a spell.Play four 1 :rb_might: Bird unit tokens with [Deflect]. (Opponents
> must pay :rb_rune_rainbow: to choose them with a spell or ability.)
-/
def UNL_044.meta : CardDef :=
  { id := ⟨"UNL-044"⟩,
    name := "Flurry of Feathers",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm, .domain .calm]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Flurry of Feathers chooses a mode and its targets when played. -/
def UNL_044 : CardDef :=
  { UNL_044.meta with
    spellEffect := some { body := .nop, modes := [
      ⟨"Counter a spell", [.targetOf .one .any .onChain [.ofType .spell]],
        .prim (.counter (.slot 0)), none⟩,
      ⟨"Play four Birds", [], .repeatN (.const 4) (.prim (.playUnitToken "Bird")), none⟩] },
    status := .full }

-- BEGIN GENERATED UNL-045
/--
**Forgotten Signpost** — Gear · Calm · Energy 2
Printings: UNL-045/219

> [Action][>] Exhaust a unit you control, :rb_exhaust:: Move a different unit you control to the
> location of the unit you exhausted to pay for this ability.
-/
def UNL_045.meta : CardDef :=
  { id := ⟨"UNL-045"⟩,
    name := "Forgotten Signpost",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Forgotten Signpost. -/
def UNL_045 : CardDef :=
  { UNL_045.meta with
    abilities := [.activated [.exhaustSelf] .action
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .ready],
          .targetOf .one .friendly .anywhere [.ofType .unit, .not (.sameAs (.slot 0))]]
        (.seqOf [.prim (.exhaust (.slot 0)),
          .ifThen (.matches (.slot 0) .onBattlefield)
            (.prim (.move (.slot 1) (.at_ (.locationOf (.slot 0)))))
            (.prim (.move (.slot 1) .base))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-046
/--
**Friendship** — Spell · Calm · Energy 1
Printings: UNL-046/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a unit. Give it +1 :rb_might: this turn for each of the following tags among your units
> — Bird, Cat, Dog, and Poro.
-/
def UNL_046.meta : CardDef :=
  { id := ⟨"UNL-046"⟩,
    name := "Friendship",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Friendship. -/
def UNL_046 : CardDef :=
  { UNL_046.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it petTags) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED UNL-047
/--
**Mosstomper** — Unit · Calm · Energy 3 + Power 1 · Might 3
Printings: UNL-047/219

> [Hunt 2] (When I conquer or hold, gain 2 XP.)
> [Level 3][>] I have +1 :rb_might: and [Deflect]. (While you have 3+ XP, get the effect.
> Opponents must pay :rb_rune_rainbow: to choose a [Deflect] unit with a spell or ability.)
-/
def UNL_047.meta : CardDef :=
  { id := ⟨"UNL-047"⟩,
    name := "Mosstomper",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Ixtal"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 3,
    keywords := [{ keyword := .hunt, arg := .amount 2 },
      { keyword := .level, arg := .amount 3 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Mosstomper. -/
def UNL_047 : CardDef :=
  { UNL_047.meta with
    abilities := [.passive (.cmp .ge .xp (.const 3))
      [.mightPlus .self (.const 1), .keyword .self { keyword := .deflect }]],
    status := .drafted }

-- BEGIN GENERATED UNL-048
/--
**Trevor Snoozebottom** — Unit · Calm · Energy 3 · Might 3
Printings: UNL-048/219

> [Shield] (+1 :rb_might: while I'm a defender.)
> When I hold, play a ready 3 :rb_might: Sprite unit token with [Temporary] here. (Kill it at
> the start of its controller's next Beginning Phase, before scoring.)
-/
def UNL_048.meta : CardDef :=
  { id := ⟨"UNL-048"⟩,
    name := "Trevor Snoozebottom",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .shield, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Trevor Snoozebottom. -/
def UNL_048 : CardDef :=
  { UNL_048.meta with
    abilities := [.triggered (.onSelf .hold)
        (.of []
        (.prim (.create "Sprite" (.const 1) .here true))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-049
/--
**Honeyfruit** — Gear · Calm · Energy 2
Printings: UNL-049/219

> This enters exhausted.
> [Reaction][>] :rb_exhaust:: [Add] :rb_rune_rainbow:. (Abilities that add resources can't be
> reacted to.)
> [Level 6][>] [>>][Reaction][>] :rb_exhaust:: [Add] :rb_energy_1::rb_rune_rainbow:. (Use this
> ability only while you have 6+ XP.)
-/
def UNL_049.meta : CardDef :=
  { id := ⟨"UNL-049"⟩,
    name := "Honeyfruit",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .level, arg := .amount 6 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Honeyfruit adds both resources immediately when its controller chooses the Level 6 ability. -/
def UNL_049 : CardDef :=
  { UNL_049.meta with
    abilities := [.passive .always [.entersExhausted],
      .activated [.exhaustSelf] .reaction (.of [] (.prim (.addPower .you (.const 1) none none))) .unlimited,
      .activated [.exhaustSelf] .reaction
        (.of [] (.ifThen (.cmp .ge .xp (.const 6))
          (.seqOf [.prim (.addEnergy .you (.const 1) none), .prim (.addPower .you (.const 1) none none)])
          .nop)) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-050
/--
**Iascylla** — Unit · Calm · Energy 7 + Power 1 · Might 6
Printings: UNL-050/219

> When I hold, at the start of your next Main Phase, you may move an enemy unit to this
> battlefield.
-/
def UNL_050.meta : CardDef :=
  { id := ⟨"UNL-050"⟩,
    name := "Iascylla",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.calm],
    cost := some ⟨7, [.domain .calm]⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Iascylla. -/
def UNL_050 : CardDef :=
  { UNL_050.meta with
    abilities := [
      .triggered (.onSelf .hold) (.of [] (.prim (.markOn .self (.armed 1)))) .unlimited,
      .triggered { event := .at_ .startOfMain, condition := .marked (.armed 1) }
        (.of [] (.may (.prim (.move (Selector.one .enemy .anywhere [.ofType .unit])
          (.at_ (Selector.all .any .here [.ofType .battlefield])))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-051
/--
**Ivern, Nurturer** — Unit · Calm · Energy 5 + Power 1 · Might 4
Printings: UNL-051/219, UNL-051a/219

> When you play me or when I hold, look at the top 3 cards of your Main Deck. You may reveal a
> unit from among them and draw it. Recycle the rest. Then if you revealed a Bird, Cat, Dog, or
> Poro, do this: [Buff] a friendly unit. (Give it a +1 :rb_might: buff if it doesn't have one.)
-/
def UNL_051.meta : CardDef :=
  { id := ⟨"UNL-051"⟩,
    name := "Ivern",
    subtitle := some "Nurturer",
    types := [.unit],
    tags := [⟨"Ivern"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 4,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Ivern. -/
def UNL_051 : CardDef :=
  { UNL_051.meta with
    abilities := [.triggered (.onSelf .play)
        (.of [] ivernLook) .unlimited,
      .triggered (.onSelf .hold)
        (.of [] ivernLook) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-052
/--
**Nami, Headstrong** — Unit · Calm · Energy 3 · Might 3
Printings: UNL-052/219

> You may pay :rb_rune_calm: as an additional cost to play me.
> When you play me, if you paid the additional cost, [Stun] an enemy unit. (It doesn't deal
> combat damage this turn.)
> When I hold, the next time you play a unit this turn, ready it and [Buff] it.
-/
def UNL_052.meta : CardDef :=
  { id := ⟨"UNL-052"⟩,
    name := "Nami",
    subtitle := some "Headstrong",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩, ⟨"Nami"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Nami. -/
def UNL_052 : CardDef :=
  { UNL_052.meta with
    additionalCost := some ⟨0, [.domain .calm]⟩,
    abilities := [
      .triggered { event := .play, condition := .paid }
        (.of [.targetOf .one .enemy .anywhere [.ofType .unit]] (.prim (.stun (.slot 0)))) .unlimited,
      .triggered (.onSelf .hold)
        (.of [] (.seqOf [.prim (.turnEffect .nextUnitReady), .prim (.turnEffect .nextUnitBuffed)]))
        .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-053
/--
**Scuttle Crab** — Unit · Calm · Energy 2 · Might 0
Printings: UNL-053/219

> (Units with 0 :rb_might: can conquer and hold.)
> When you play me, draw 1.
> [Deathknell][>] Choose an opponent. They reveal their hand. You can look at their facedown
> cards this turn. Gain 1 XP. (When I die, get the effects.)
-/
def UNL_053.meta : CardDef :=
  { id := ⟨"UNL-053"⟩,
    name := "Scuttle Crab",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 0,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Scuttle Crab. -/
def UNL_053 : CardDef :=
  { UNL_053.meta with
    abilities := [.triggered (.onSelf .play) (.of [] (.prim (.draw .you (.const 1)))) .unlimited,
      .triggered (.onSelf .deathknell)
        { playerTarget := some .enemy
          body := .revealHand (.chosen 0)
            (.seqOf [.prim (.allowFacedownInspection (.chosen 0)), .prim (.gainXP .you (.const 1))]) }
        .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-054
/--
**Tricksy Tentacles** — Spell · Calm · Energy 4 + Power 1
Printings: UNL-054/219

> Move any number of enemy units with the same controller and a total Might of 8 or less to a
> single location.
-/
def UNL_054.meta : CardDef :=
  { id := ⟨"UNL-054"⟩,
    name := "Tricksy Tentacles",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Tricksy Tentacles. -/
def UNL_054 : CardDef :=
  { UNL_054.meta with
    spellEffect := some {
      choices := [.targetOf (.combinedMightFromOneController 8) .enemy .anywhere [.ofType .unit]]
      moveChoice := some ⟨0, true, .nil⟩
      recheckTargets := true
      body := .prim (.move (.slotsFrom 0) .declared) },
    status := .full }

-- BEGIN GENERATED UNL-055
/--
**Vex, Mocking** — Unit · Calm · Energy 5 + Power 1 · Might 5
Printings: UNL-055/219, UNL-055a/219

> [Shield] (+1 :rb_might: while I'm a defender.)
> [Tank] (I must be assigned combat damage first.)
> When you [Stun] an enemy unit at a battlefield, you may move me to that battlefield.
-/
def UNL_055.meta : CardDef :=
  { id := ⟨"UNL-055"⟩,
    name := "Vex",
    subtitle := some "Mocking",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Yordle"⟩, ⟨"Vex"⟩, ⟨"Shadow Isles"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 5,
    keywords := [{ keyword := .shield, arg := .amount 1 },
      { keyword := .tank }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Vex. -/
def UNL_055 : CardDef :=
  { UNL_055.meta with
    abilities := [.triggered
      { event := .stunByYou, subject := Selector.all .enemy .anywhere [.ofType .unit, .onBattlefield],
        optional := true }
      (.of [] (.prim (.move .self (.at_
        (.all .any .atBattlefield [.ofType .battlefield, .atEventBattlefield none]))))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-056
/--
**Yuumi, Magical Cat** — Unit · Calm · Energy 3 + Power 1 · Might 1
Printings: UNL-056/219

> When I attack or defend, give one of your other units here +3 :rb_might: and [Tank] this turn.
> (It must be assigned combat damage first.)
-/
def UNL_056.meta : CardDef :=
  { id := ⟨"UNL-056"⟩,
    name := "Yuumi",
    subtitle := some "Magical Cat",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Cat"⟩, ⟨"Bandle City"⟩, ⟨"Yuumi"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 1,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Yuumi. -/
def UNL_056 : CardDef :=
  { UNL_056.meta with
    abilities := [.triggered (.onSelf .attack)
        (.of [.targetOf .one .you .here [.ofType .unit, .notSelf]]
          (.seqOf [.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn,
            .grant (.slot 0) (.keyword .it { keyword := .tank }) .thisTurn])) .unlimited,
      .triggered (.onSelf .defend)
        (.of [.targetOf .one .you .here [.ofType .unit, .notSelf]]
          (.seqOf [.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn,
            .grant (.slot 0) (.keyword .it { keyword := .tank }) .thisTurn])) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-057
/--
**Alpha Wildclaw** — Unit · Calm · Energy 6 + Power 2 · Might 7
Printings: UNL-057/219

> [Tank] (I must be assigned combat damage first.)
> Your units here with less Might than me can't be chosen by enemy spells and abilities.
-/
def UNL_057.meta : CardDef :=
  { id := ⟨"UNL-057"⟩,
    name := "Alpha Wildclaw",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Freljord"⟩],
    domains := [.calm],
    cost := some ⟨6, [.domain .calm, .domain .calm]⟩,
    might := some 7,
    keywords := [{ keyword := .tank }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Alpha Wildclaw. -/
def UNL_057 : CardDef :=
  { UNL_057.meta with
    abilities := [.passive .always
      [.cant (Selector.all .you .here [.ofType .unit, .mightLtOf .self]) .beChosen]],
    status := .full }

-- BEGIN GENERATED UNL-058
/--
**Lillia, Protector of Dreams** — Unit · Calm · Energy 5 · Might 4
Printings: UNL-058/219, UNL-058a/219

> When you play a token unit, give me +1 :rb_might: this turn.
> Your token units have [Tank]. (They must be assigned combat damage first.)
-/
def UNL_058.meta : CardDef :=
  { id := ⟨"UNL-058"⟩,
    name := "Lillia",
    subtitle := some "Protector of Dreams",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Lillia"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨5, []⟩,
    might := some 4,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Lillia. -/
def UNL_058 : CardDef :=
  { UNL_058.meta with
    abilities := [.triggered
        { event := .playToken, subject := Selector.all .you .anywhere [.ofType .unit] }
        (.of [] (.grant .self (.mightPlus .it (.const 1)) .thisTurn)) .unlimited,
      .passive .always
        [.keyword (Selector.all .you .anywhere [.ofType .unit, .token]) { keyword := .tank }]],
    status := .full }

-- BEGIN GENERATED UNL-059
/--
**Master Yi, Unstoppable** — Unit · Calm · Energy 12 + Power 3 · Might 12
Printings: UNL-059/219, UNL-059a/219

> [Level 3][>] I cost :rb_energy_2::rb_rune_calm: less. (While you have 3+ XP, get the effect.)
> [Level 6][>] I cost :rb_energy_4::rb_rune_calm::rb_rune_calm: less instead.
> [Level 11][>] I cost :rb_energy_6::rb_rune_calm::rb_rune_calm::rb_rune_calm: less instead.
> [Level 16][>] I can't be chosen by enemy spells and abilities.
-/
def UNL_059.meta : CardDef :=
  { id := ⟨"UNL-059"⟩,
    name := "Master Yi",
    subtitle := some "Unstoppable",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Master Yi"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨12, [.domain .calm, .domain .calm, .domain .calm]⟩,
    might := some 12,
    keywords := [{ keyword := .level, arg := .amount 3 },
      { keyword := .level, arg := .amount 6 },
      { keyword := .level, arg := .amount 11 },
      { keyword := .level, arg := .amount 16 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Master Yi. -/
def UNL_059 : CardDef :=
  { UNL_059.meta with
    abilities := [
      .passive (.and (.cmp .ge .xp (.const 3)) (.not (.cmp .ge .xp (.const 6))))
        [.costMinus .self (.const 2), .costPower .self (.const 1) (some .calm) false],
      .passive (.and (.cmp .ge .xp (.const 6)) (.not (.cmp .ge .xp (.const 11))))
        [.costMinus .self (.const 4), .costPower .self (.const 2) (some .calm) false],
      .passive (.cmp .ge .xp (.const 11))
        [.costMinus .self (.const 6), .costPower .self (.const 3) (some .calm) false],
      .passive (.cmp .ge .xp (.const 16)) [.cant .self .beChosen]],
    status := .full }

-- BEGIN GENERATED UNL-060
/--
**Vilemaw** — Unit · Calm · Energy 8 + Power 2 · Might 8
Printings: UNL-060/219, UNL-060a/219

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> Enemy units here with less Might than me don't deal combat damage.
> When I hold, draw 1.
-/
def UNL_060.meta : CardDef :=
  { id := ⟨"UNL-060"⟩,
    name := "Vilemaw",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Spider"⟩],
    domains := [.calm],
    cost := some ⟨8, [.domain .calm, .domain .calm]⟩,
    might := some 8,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Vilemaw. -/
def UNL_060 : CardDef :=
  { UNL_060.meta with
    abilities := [
      .passive .always
        [.noCombatDamageFor (Selector.all .enemy .here [.ofType .unit, .mightLtOf .self])],
      .triggered (.onSelf .hold) (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-061
/--
**Downstage Dramatics** — Spell · Mind · Energy 2
Printings: UNL-061/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Draw 1.
-/
def UNL_061.meta : CardDef :=
  { id := ⟨"UNL-061"⟩,
    name := "Downstage Dramatics",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction },
      { keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Downstage Dramatics. -/
def UNL_061 : CardDef :=
  { UNL_061.meta with
    spellEffect := some (.of []
      (.prim (.draw .you (.const 1)))),
    status := .full }

-- BEGIN GENERATED UNL-062
/--
**Dramatic Visionary** — Unit · Mind · Energy 4 · Might 4
Printings: UNL-062/219

> [Deathknell][>] [Predict 2]. (When I die, look at the top two cards of your Main Deck. Recycle
> any of them and put the rest back in any order.)
-/
def UNL_062.meta : CardDef :=
  { id := ⟨"UNL-062"⟩,
    name := "Dramatic Visionary",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Dramatic Visionary. -/
def UNL_062 : CardDef :=
  { UNL_062.meta with
    abilities := [.triggered (.onSelf .die) (.of [] predict2) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-063
/--
**Eclipse** — Spell · Mind · Energy 3
Printings: UNL-063/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a unit -4 :rb_might: this turn.
> [Predict]. (Look at the top card of your Main Deck. You may recycle it.)
-/
def UNL_063.meta : CardDef :=
  { id := ⟨"UNL-063"⟩,
    name := "Eclipse",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Eclipse. -/
def UNL_063 : CardDef :=
  { UNL_063.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.grant (.slot 0) (.mightMinus .it (.const 4)) .thisTurn, predict1])),
    status := .drafted }

-- BEGIN GENERATED UNL-064
/--
**Fate Weaver** — Unit · Mind · Energy 5 · Might 4
Printings: UNL-064/219

> When you play me, look at the top 4 cards of your Main Deck. You may reveal a spell with
> Energy cost :rb_energy_4: or more from among them and draw it. Recycle the rest.
-/
def UNL_064.meta : CardDef :=
  { id := ⟨"UNL-064"⟩,
    name := "Fate Weaver",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    might := some 4,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Fate Weaver. -/
def UNL_064 : CardDef :=
  { UNL_064.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (lookDraw 4 [.ofType .spell, .cost .ge (.const 4)])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-065
/--
**Icevale Archer** — Unit · Mind · Energy 2 · Might 2
Printings: UNL-065/219

> When I attack, you may pay :rb_energy_1: to give a unit here -1 :rb_might: this turn.
-/
def UNL_065.meta : CardDef :=
  { id := ⟨"UNL-065"⟩,
    name := "Icevale Archer",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Icevale Archer. -/
def UNL_065 : CardDef :=
  { UNL_065.meta with
    abilities := [.triggered { Trigger.onSelf .attack with optional := true, cost := .energy 1 }
      { choices := [.targetOf .one .any .here [.ofType .unit]]
        recheckTargets := true
        body := .grant (.slot 0) (.mightMinus .it (.const 1)) .thisTurn } .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-066
/--
**Moonlight Affliction** — Spell · Mind · Energy 7
Printings: UNL-066/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a unit -10 :rb_might: this turn.
-/
def UNL_066.meta : CardDef :=
  { id := ⟨"UNL-066"⟩,
    name := "Moonlight Affliction",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨7, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Moonlight Affliction. -/
def UNL_066 : CardDef :=
  { UNL_066.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.mightMinus .it (.const 10)) .thisTurn)),
    status := .full }

-- BEGIN GENERATED UNL-067
/--
**Ruined Rex** — Unit · Mind · Energy 6 + Power 1 · Might 6
Printings: UNL-067/219

> [Deathknell][>] Deal 4 to an enemy unit. (When I die, get the effect.)
-/
def UNL_067.meta : CardDef :=
  { id := ⟨"UNL-067"⟩,
    name := "Ruined Rex",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind]⟩,
    might := some 6,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Ruined Rex. -/
def UNL_067 : CardDef :=
  { UNL_067.meta with
    abilities := [.triggered (.onSelf .die)
        (.of [.targetOf .one .enemy .anywhere [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 4)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-068
/--
**Spectral Centaur** — Unit · Mind · Energy 6 · Might 5
Printings: UNL-068/219

> When another friendly unit dies, give me +2 :rb_might: this turn.
-/
def UNL_068.meta : CardDef :=
  { id := ⟨"UNL-068"⟩,
    name := "Spectral Centaur",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.mind],
    cost := some ⟨6, []⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Spectral Centaur. -/
def UNL_068 : CardDef :=
  { UNL_068.meta with
    abilities := [.triggered
      { event := .die, subject := Selector.all .friendly .anywhere [.ofType .unit, .notSelf] }
      (.of [] (.grant .self (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-069
/--
**Sprite Burst** — Spell · Mind · Energy 5
Printings: UNL-069/219

> Play two ready 3 :rb_might: Sprite unit tokens with [Temporary]. (Kill each at the start of
> its controller's Beginning Phase, before scoring.)
-/
def UNL_069.meta : CardDef :=
  { id := ⟨"UNL-069"⟩,
    name := "Sprite Burst",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Sprite Burst. -/
def UNL_069 : CardDef :=
  { UNL_069.meta with
    spellEffect := some (.of []
      (.repeatN (.const 2) (.prim (.playReadyUnitToken "Sprite")))),
    status := .full }

-- BEGIN GENERATED UNL-070
/--
**Turn to Dust** — Spell · Mind · Energy 2
Printings: UNL-070/219

> Give a gear [Temporary]. (Kill it at the start of its controller's Beginning Phase, before
> scoring.)
-/
def UNL_070.meta : CardDef :=
  { id := ⟨"UNL-070"⟩,
    name := "Turn to Dust",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Turn to Dust. -/
def UNL_070 : CardDef :=
  { UNL_070.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .gear]]
      (.grant (.slot 0) (.keyword .it { keyword := .temporary }) .permanent)),
    status := .full }

-- BEGIN GENERATED UNL-071
/--
**Chakram Dancer** — Unit · Mind · Energy 3 · Might 3
Printings: UNL-071/219

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> When you play me, give your other units here [Shield] this turn. (+1 :rb_might: while they're
> defenders.)
-/
def UNL_071.meta : CardDef :=
  { id := ⟨"UNL-071"⟩,
    name := "Chakram Dancer",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Chakram Dancer. -/
def UNL_071 : CardDef :=
  { UNL_071.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.grant (Selector.all .friendly .here [.ofType .unit, .notSelf])
        (.keyword .it { keyword := .shield }) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-072
/--
**Crescent Strike** — Spell · Mind · Energy 3 + Power 1
Printings: UNL-072/219

> [Action] (Play on your turn or in showdowns.)
> Choose a battlefield and an enemy unit there. Deal 4 to that unit and 1 to each other enemy
> unit there.
-/
def UNL_072.meta : CardDef :=
  { id := ⟨"UNL-072"⟩,
    name := "Crescent Strike",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Crescent Strike. -/
def UNL_072 : CardDef :=
  { UNL_072.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .battlefield],
        .targetOf .one .enemy .anywhere [.ofType .unit, .at_ (.slot 0)]]
      (.seqOf [.prim (.deal (.slot 1) (.const 4)),
        .prim (.deal (Selector.all .enemy .anywhere
          [.ofType .unit, .at_ (.slot 0), .not (.sameAs (.slot 1))]) (.const 1))])),
    status := .drafted }

-- BEGIN GENERATED UNL-073
/--
**Deadly Flourish** — Spell · Mind · Energy 4
Printings: UNL-073/219

> Deal 3 to an enemy unit. When it dies this turn, play a Gold gear token exhausted. (It has
> "[Reaction][>] Kill this, :rb_exhaust:: [Add] :rb_rune_rainbow:.")
-/
def UNL_073.meta : CardDef :=
  { id := ⟨"UNL-073"⟩,
    name := "Deadly Flourish",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Deadly Flourish. -/
def UNL_073 : CardDef :=
  { UNL_073.meta with
    abilities := [.triggered (.onSelf .die) (.of [] (.prim (.create "Gold" (.const 1) .atBase false)))
      .unlimited],
    spellEffect := some (.of [.targetOf .one .enemy .anywhere [.ofType .unit]]
      (.seqOf [.prim (.delayUntilDeath (.slot 0) 0),
        .prim (.deal (.slot 0) (.const 3))])),
    status := .full }

-- BEGIN GENERATED UNL-074
/--
**Frigid Jewel** — Gear · Mind · Energy 2
Printings: UNL-074/219

> When you draw your second card each turn, give a friendly unit +2 :rb_might: this turn.
-/
def UNL_074.meta : CardDef :=
  { id := ⟨"UNL-074"⟩,
    name := "Frigid Jewel",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Frigid Jewel. -/
def UNL_074 : CardDef :=
  { UNL_074.meta with
    abilities := [.triggered { condition := .drewCards 2, event := .draw }
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-075
/--
**Gustwalker** — Unit · Mind · Energy 3 + Power 1 · Might 3
Printings: UNL-075/219

> [Hunt 2] (When I conquer or hold, gain 2 XP.)
> [Level 3][>] I have +1 :rb_might: and [Ganking]. (While you have 3+ XP, get the effect. A
> [Ganking] unit can move from battlefield to battlefield.)
-/
def UNL_075.meta : CardDef :=
  { id := ⟨"UNL-075"⟩,
    name := "Gustwalker",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    might := some 3,
    keywords := [{ keyword := .hunt, arg := .amount 2 },
      { keyword := .level, arg := .amount 3 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Gustwalker. -/
def UNL_075 : CardDef :=
  { UNL_075.meta with
    abilities := [.passive (.cmp .ge .xp (.const 3))
      [.mightPlus .self (.const 1), .keyword .self { keyword := .ganking }]],
    status := .drafted }

-- BEGIN GENERATED UNL-076
/--
**Petal Pixie** — Unit · Mind · Energy 2 · Might 2
Printings: UNL-076/219

> I have +1 :rb_might: for each of your units with [Temporary] at my battlefield.
-/
def UNL_076.meta : CardDef :=
  { id := ⟨"UNL-076"⟩,
    name := "Petal Pixie",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Petal Pixie. -/
def UNL_076 : CardDef :=
  { UNL_076.meta with
    abilities := [.passive .always [.mightPlus .self
      (.count (Selector.all .friendly .here [.ofType .unit, .hasKeyword .temporary]))]],
    status := .drafted }

-- BEGIN GENERATED UNL-077
/--
**Soul Shepherd** — Unit · Mind · Energy 5 · Might 3
Printings: UNL-077/219

> Your token units have +1 :rb_might:.
-/
def UNL_077.meta : CardDef :=
  { id := ⟨"UNL-077"⟩,
    name := "Soul Shepherd",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Soul Shepherd. -/
def UNL_077 : CardDef :=
  { UNL_077.meta with
    abilities := [.passive .always
      [.mightPlus (Selector.all .friendly .anywhere [.ofType .unit, .token]) (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED UNL-078
/--
**Sprite Fountain** — Gear · Mind · Energy 2 + Power 1
Printings: UNL-078/219

> [Temporary] (Kill this at the start of its controller's Beginning Phase, before scoring.)
> When you play this, play a ready 3 :rb_might: Sprite unit token with [Temporary] to your base.
> [Deathknell][>] Repeat this gear's play effect. (When this dies, get the effect.)
-/
def UNL_078.meta : CardDef :=
  { id := ⟨"UNL-078"⟩,
    name := "Sprite Fountain",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨2, [.domain .mind]⟩,
    keywords := [{ keyword := .temporary },
      { keyword := .deathknell }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Sprite Fountain. -/
def UNL_078 : CardDef :=
  { UNL_078.meta with
    abilities := [.triggered (.onSelf .play)
        (.of [] (.prim (.create "Sprite" (.const 1) .atBase true))) .unlimited,
      .triggered (.onSelf .deathknell)
        (.of [] (.prim (.create "Sprite" (.const 1) .atBase true))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-079
/--
**Diana, Lunari** — Unit · Mind · Energy 3 · Might 3
Printings: UNL-079/219, UNL-079a/219

> When a showdown begins here, you may pay :rb_energy_1: to [Predict], then reveal the top card
> of your Main Deck. If it's a spell, draw it. (To Predict, look at the top card of your Main
> Deck. You may recycle it.)
-/
def UNL_079.meta : CardDef :=
  { id := ⟨"UNL-079"⟩,
    name := "Diana",
    subtitle := some "Lunari",
    types := [.unit],
    tags := [⟨"Diana"⟩, ⟨"Mount Targon"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Diana. -/
def UNL_079 : CardDef :=
  { UNL_079.meta with
    abilities := [.triggered { Trigger.onSelf .showdownStart with optional := true, cost := .energy 1 }
      (.of [] (.seqOf [.prim (.predict (.const 1)),
        .revealDeckTops .you
          (.ifThen (.cmp .gt (.count (Selector.all .you .inMainDeck [.top 1, .ofType .spell])) (.const 0))
            (.prim (.draw .you (.const 1))) .nop)])) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-080
/--
**Hwei, Brooding Painter** — Unit · Mind · Energy 5 + Power 1 · Might 5
Printings: UNL-080/219

> When I move, draw 1, then discard 1. Then, do the following based on the discarded card's
> type:Spell — Draw 1.Gear — Ready up to 2 runes.Unit — Give me +3 :rb_might: this turn.
-/
def UNL_080.meta : CardDef :=
  { id := ⟨"UNL-080"⟩,
    name := "Hwei",
    subtitle := some "Brooding Painter",
    types := [.unit],
    tags := [⟨"Ionia"⟩, ⟨"Hwei"⟩],
    domains := [.mind],
    cost := some ⟨5, [.domain .mind]⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Hwei's discard can trigger all the effects corresponding to that card's types. -/
def UNL_080 : CardDef :=
  { UNL_080.meta with
    abilities := [.triggered (.onSelf .move)
      (.of [] (.seqOf [.prim (.draw .you (.const 1)),
        .prim (.discardWithTypeTriggers (.one .friendly .inHand [])
          [(.spell, 1), (.gear, 2), (.unit, 3)])])) .unlimited,
      .triggered (.onSelf .linkedDiscardType)
        (.of [] (.prim (.draw .you (.const 1)))) .unlimited,
      .triggered (.onSelf .linkedDiscardType)
        (.of [] readyTwoRunes) .unlimited,
      .triggered (.onSelf .linkedDiscardType)
        (.of [] (.grant .self (.mightPlus .it (.const 3)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-081
/--
**Keeper of Masks** — Unit · Mind · Energy 2 · Might 1
Printings: UNL-081/219

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Temporary] (Kill me at the start of my controller's Beginning Phase, before scoring.)
> When you play me, play two Reflection unit tokens here. Then do this: They become copies of
> me.
-/
def UNL_081.meta : CardDef :=
  { id := ⟨"UNL-081"⟩,
    name := "Keeper of Masks",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .hidden },
      { keyword := .temporary }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Keeper of Masks. -/
def UNL_081 : CardDef :=
  { UNL_081.meta with
    abilities := [
      .triggered (.onSelf .play) (.of [] (.playUnitTokensThen "Reflection" 2 .here false 1))
        .unlimited,
      .triggered (.onSelf (.linkedUnitTokens false))
        (.of [] (.prim (.becomeCopy .eventObjects .self))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-082
/--
**Lillia, Fae Fawn** — Unit · Mind · Energy 3 · Might 3
Printings: UNL-082/219, UNL-082a/219

> [Accelerate] (You may pay :rb_energy_1::rb_rune_mind: as an additional cost to have me enter
> ready.)
> When I move from a location, play a 3 :rb_might: Sprite unit token with [Temporary] there.
> (Kill it at the start of its controller's Beginning Phase, before scoring.)
-/
def UNL_082.meta : CardDef :=
  { id := ⟨"UNL-082"⟩,
    name := "Lillia",
    subtitle := some "Fae Fawn",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Lillia"⟩, ⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Lillia. -/
def UNL_082 : CardDef :=
  { UNL_082.meta with
    abilities := [.triggered (.onSelf .moveFrom)
      (.of [] (.prim (.createAtPrev "Sprite" (.const 1) false))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-083
/--
**Smoke and Mirrors** — Spell · Mind · Energy 2
Printings: UNL-083/219

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Choose a unit you control and another unit you control at a different location. If at least
> one of them has [Temporary], move each to the other's location. Draw 1.
-/
def UNL_083.meta : CardDef :=
  { id := ⟨"UNL-083"⟩,
    name := "Smoke and Mirrors",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Smoke and Mirrors. -/
def UNL_083 : CardDef :=
  { UNL_083.meta with
    spellEffect := some (.of [.targetOf .one .you .anywhere [.ofType .unit],
        .targetOf .one .you .anywhere [.ofType .unit, .not (.at_ (.slot 0))]]
      (.seqOf [.ifThen (.or (.matches (.slot 0) (.hasKeyword .temporary))
          (.matches (.slot 1) (.hasKeyword .temporary)))
          (.prim (.swapPlaces (.slot 0) (.slot 1))) .nop,
        .prim (.draw .you (.const 1))])),
    status := .full }

-- BEGIN GENERATED UNL-084
/--
**Sprite Queen** — Unit · Mind · Energy 7 + Power 1 · Might 6
Printings: UNL-084/219

> When you play me or at the start of your Beginning Phase, play a ready 3 :rb_might: Sprite
> unit token with [Temporary] to your base. (Kill them at the start of their controller's next
> Beginning Phase, before scoring.)
-/
def UNL_084.meta : CardDef :=
  { id := ⟨"UNL-084"⟩,
    name := "Sprite Queen",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨7, [.domain .mind]⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Sprite Queen. -/
def UNL_084 : CardDef :=
  { UNL_084.meta with
    abilities := [.triggered (.onSelf .play)
        (.of [] (.prim (.create "Sprite" (.const 1) .atBase true))) .unlimited,
      .triggered { event := .at_ .beginning }
        (.of [] (.prim (.create "Sprite" (.const 1) .atBase true))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-085
/--
**Sumpworks Map** — Gear · Mind · Energy 2
Printings: UNL-085/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> [Temporary] (Kill this at the start of its controller's Beginning Phase, before scoring.)
> When an opponent scores, draw 1.
-/
def UNL_085.meta : CardDef :=
  { id := ⟨"UNL-085"⟩,
    name := "Sumpworks Map",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction },
      { keyword := .temporary }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Sumpworks Map. -/
def UNL_085 : CardDef :=
  { UNL_085.meta with
    abilities := [.triggered (.onSelf .opponentScores) (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-086
/--
**Zilean, Time Mage** — Unit · Mind · Energy 5 + Power 1 · Might 5
Printings: UNL-086/219

> Once each turn, if you would play a token unit while I'm at a battlefield, you may play that
> token and an additional copy of it instead.
-/
def UNL_086.meta : CardDef :=
  { id := ⟨"UNL-086"⟩,
    name := "Zilean",
    subtitle := some "Time Mage",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Icathia"⟩, ⟨"Zilean"⟩],
    domains := [.mind],
    cost := some ⟨5, [.domain .mind]⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Zilean. -/
def UNL_086 : CardDef :=
  { UNL_086.meta with
    abilities := [.passive (.matches .self .onBattlefield) [.duplicateUnitTokenOnce]],
    status := .full }

-- BEGIN GENERATED UNL-087
/--
**Blue Sentinel** — Unit · Mind · Energy 4 + Power 1 · Might 4
Printings: UNL-087/219, UNL-087a/219

> [Shield 2] (+2 :rb_might: while I'm a defender.)
> Your hold effects for holding here trigger an additional time.
> When I hold, [Add] :rb_rune_rainbow: at the start of your next Main Phase. (Abilities that add
> resources can't be reacted to.)
-/
def UNL_087.meta : CardDef :=
  { id := ⟨"UNL-087"⟩,
    name := "Blue Sentinel",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 4,
    keywords := [{ keyword := .shield, arg := .amount 2 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Blue Sentinel. -/
def UNL_087 : CardDef :=
  { UNL_087.meta with
    abilities := [
      .passive .always [.triggersExtra .hold .here],
      .triggered (.onSelf .hold) (.of [] (.prim (.markOn .self (.armed 1)))) .unlimited,
      .triggered { event := .at_ .startOfMain, condition := .marked (.armed 1) }
        (.of [] (.prim (.addPower .you (.const 1) none none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-088
/--
**Gutter Palace** — Gear · Mind · Energy 4
Printings: UNL-088/219

> At the start of your Beginning Phase, if you have exactly 4 cards in hand and exactly 4 units
> at battlefields, you win the game.
> Discard 1, :rb_exhaust:: Play a 1 :rb_might: Bird unit token with [Deflect]. (Opponents must
> pay :rb_rune_rainbow: to choose it with a spell or ability.)
-/
def UNL_088.meta : CardDef :=
  { id := ⟨"UNL-088"⟩,
    name := "Gutter Palace",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Gutter Palace checks its controller's hand and deployed Units at Beginning. -/
def UNL_088 : CardDef :=
  { UNL_088.meta with
    abilities := [
      .triggered
        { condition := .and (.cmp .eq (.handSize .you) (.const 4))
            (.cmp .eq (.count (Selector.all .you .atBattlefield [.ofType .unit])) (.const 4)),
          event := .at_ .beginning }
        (.of [] (.prim (.win .you))) .unlimited,
      .activated [.discard 1, .exhaustSelf] .normal
        (.of [] (.prim (.playUnitToken "Bird"))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-089
/--
**Jhin, Meticulous Killer** — Unit · Mind · Energy 4 · Might 4
Printings: UNL-089/219, UNL-089a/219

> [Vision] (When you play me, look at the top card of your Main Deck. You may recycle it.)
> If you've spent :rb_energy_4: or more to play a spell this turn, you may play me for
> :rb_rune_mind:.
-/
def UNL_089.meta : CardDef :=
  { id := ⟨"UNL-089"⟩,
    name := "Jhin",
    subtitle := some "Meticulous Killer",
    types := [.unit],
    tags := [⟨"Jhin"⟩, ⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .vision }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Jhin. -/
def UNL_089 : CardDef :=
  { UNL_089.meta with
    abilities := [.passive (.spentOnSpell 4)
      [.costMinus .self (.const 4), .costPower .self (.const 1) (some .mind) true]],
    status := .drafted }

-- BEGIN GENERATED UNL-090
/--
**LeBlanc, Everywhere at Once** — Unit · Mind · Energy 4 · Might 4
Printings: UNL-090/219, UNL-090a/219

> [Backline] (I must be assigned combat damage last.)
> Your [Temporary] effects at my battlefield don't trigger.
-/
def UNL_090.meta : CardDef :=
  { id := ⟨"UNL-090"⟩,
    name := "LeBlanc",
    subtitle := some "Everywhere at Once",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Noxus"⟩, ⟨"LeBlanc"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .backline }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- LeBlanc. -/
def UNL_090 : CardDef :=
  { UNL_090.meta with
    abilities := [.passive .always [.ignoreKeyword .temporary .here]],
    status := .full }

-- BEGIN GENERATED UNL-091
/--
**Concentrate** — Spell · Body · Energy 5
Printings: UNL-091/219

> Draw 2.
> [Level 6][>] This costs :rb_energy_2: less. (While you have 6+ XP, get the effect.)
> [Level 11][>] This costs :rb_energy_4: less instead.
-/
def UNL_091.meta : CardDef :=
  { id := ⟨"UNL-091"⟩,
    name := "Concentrate",
    types := [.spell],
    domains := [.body],
    cost := some ⟨5, []⟩,
    keywords := [{ keyword := .level, arg := .amount 6 },
      { keyword := .level, arg := .amount 11 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Concentrate. -/
def UNL_091 : CardDef :=
  { UNL_091.meta with
    abilities := [
      .passive (.and (.cmp .ge .xp (.const 6)) (.not (.cmp .ge .xp (.const 11))))
        [.costMinus .self (.const 2)],
      .passive (.cmp .ge .xp (.const 11)) [.costMinus .self (.const 4)]],
    spellEffect := some (.of [] (.prim (.draw .you (.const 2)))),
    status := .full }

-- BEGIN GENERATED UNL-092
/--
**Demacian Diplomat** — Unit · Body · Energy 2 · Might 2
Printings: UNL-092/219

> When you play me, gain 1 XP.
-/
def UNL_092.meta : CardDef :=
  { id := ⟨"UNL-092"⟩,
    name := "Demacian Diplomat",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Demacian Diplomat. -/
def UNL_092 : CardDef :=
  { UNL_092.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.gainXP .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-093
/--
**Dragonsoul Sage** — Unit · Body · Energy 2 · Might 1
Printings: UNL-093/219

> [Reaction][>] :rb_exhaust:: [Add] :rb_energy_1:. (Abilities that add resources can't be
> reacted to.)
-/
def UNL_093.meta : CardDef :=
  { id := ⟨"UNL-093"⟩,
    name := "Dragonsoul Sage",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 1,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Dragonsoul Sage. -/
def UNL_093 : CardDef :=
  { UNL_093.meta with
    abilities := [.activated [.exhaustSelf] .reaction
        (.of []
        (.prim (.addEnergy .you (.const 1) none))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-094
/--
**Gemhand Hunter** — Unit · Body · Energy 2 · Might 2
Printings: UNL-094/219

> [Hunt] (When I conquer or hold, gain 1 XP.)
> [Level 6][>] I have +1 :rb_might:. (While you have 6+ XP, get the effect.)
-/
def UNL_094.meta : CardDef :=
  { id := ⟨"UNL-094"⟩,
    name := "Gemhand Hunter",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Mount Targon"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .hunt, arg := .amount 1 },
      { keyword := .level, arg := .amount 6 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Gemhand Hunter. -/
def UNL_094 : CardDef :=
  { UNL_094.meta with
    abilities := [.passive (.cmp .ge .xp (.const 6)) [.mightPlus .self (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED UNL-095
/--
**Grim Resolve** — Spell · Body · Energy 2
Printings: UNL-095/219

> [Action] (Play on your turn or in showdowns.)
> Give a friendly unit +3 :rb_might: this turn. When it wins a combat this turn, gain 2 XP.
-/
def UNL_095.meta : CardDef :=
  { id := ⟨"UNL-095"⟩,
    name := "Grim Resolve",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Grim Resolve. -/
def UNL_095 : CardDef :=
  { UNL_095.meta with
    abilities := [.triggered (.onSelf .winCombat) (.of [] (.prim (.gainXP .you (.const 2)))) .unlimited],
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
      (.seqOf [.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn,
        .prim (.markOn (.slot 0) (.grantsAbility "UNL-095" 0))])),
    status := .drafted }

-- BEGIN GENERATED UNL-096
/--
**Hunter's Machete** — Gear · Body · Energy 3 · Might 2
Printings: UNL-096/219

> [Equip] :rb_rune_body: (:rb_rune_body:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Hunt] (When I conquer or hold, gain 1 XP.)
-/
def UNL_096.meta : CardDef :=
  { id := ⟨"UNL-096"⟩,
    name := "Hunter's Machete",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .body]⟩ }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Hunter's Machete. -/
def UNL_096 : CardDef :=
  { UNL_096.meta with
    grants := [.triggered (.onSelf .conquer) (.of [] (.prim (.gainXP .you (.const 1)))) .unlimited,
      .triggered (.onSelf .hold) (.of [] (.prim (.gainXP .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-097
/--
**Kinkou Initiate** — Unit · Body · Energy 3 · Might 3
Printings: UNL-097/219

> When you play me, draw 1 if your other units have total Might 5 or more.
-/
def UNL_097.meta : CardDef :=
  { id := ⟨"UNL-097"⟩,
    name := "Kinkou Initiate",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Kinkou Initiate. -/
def UNL_097 : CardDef :=
  { UNL_097.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.ifThen (.cmp .ge (.mightOf otherFriendlyUnit) (.const 5))
        (.prim (.draw .you (.const 1))) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-098
/--
**Targonian Visionary** — Unit · Body · Energy 6 · Might 6
Printings: UNL-098/219

> [Level 11][>] I have +4 :rb_might:. (While you have 11+ XP, get the effect.)
-/
def UNL_098.meta : CardDef :=
  { id := ⟨"UNL-098"⟩,
    name := "Targonian Visionary",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.body],
    cost := some ⟨6, []⟩,
    might := some 6,
    keywords := [{ keyword := .level, arg := .amount 11 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Targonian Visionary. -/
def UNL_098 : CardDef :=
  { UNL_098.meta with
    abilities := [.passive (.cmp .ge .xp (.const 11)) [.mightPlus .self (.const 4)]],
    status := .drafted }

-- BEGIN GENERATED UNL-099
/--
**Towering Combatant** — Unit · Body · Energy 4 · Might 3
Printings: UNL-099/219

> [Shield 2] (+2 :rb_might: while I'm a defender.)
> [Tank] (I must be assigned combat damage first.)
-/
def UNL_099.meta : CardDef :=
  { id := ⟨"UNL-099"⟩,
    name := "Towering Combatant",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 3,
    keywords := [{ keyword := .shield, arg := .amount 2 },
      { keyword := .tank }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Towering Combatant. -/
def UNL_099 : CardDef :=
  { UNL_099.meta with
    status := .full }

-- BEGIN GENERATED UNL-100
/--
**Voracious Gromp** — Unit · Body · Energy 5 · Might 5
Printings: UNL-100/219

> [Hunt 3] (When I conquer or hold, gain 3 XP.)
-/
def UNL_100.meta : CardDef :=
  { id := ⟨"UNL-100"⟩,
    name := "Voracious Gromp",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .hunt, arg := .amount 3 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Voracious Gromp. -/
def UNL_100 : CardDef :=
  { UNL_100.meta with
    status := .full }

-- BEGIN GENERATED UNL-101
/--
**Call to Battle** — Spell · Body · Energy 3
Printings: UNL-101/219

> Move a unit you control to a battlefield you control. Then, choose an opponent. They move a
> unit they control to the same battlefield.
-/
def UNL_101.meta : CardDef :=
  { id := ⟨"UNL-101"⟩,
    name := "Call to Battle",
    types := [.spell],
    domains := [.body],
    cost := some ⟨3, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Call to Battle. -/
def UNL_101 : CardDef :=
  { UNL_101.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .any .anywhere [.ofType .battlefield, .controlled]]
      (.seqOf [.prim (.move (.slot 0) (.at_ (.slot 1))),
        .eachPlayer .eachOpponent
          (.prim (.move (Selector.one .friendly .anywhere [.ofType .unit]) (.at_ (.slot 1))))])),
    status := .drafted }

-- BEGIN GENERATED UNL-102
/--
**Crowd Favorite** — Unit · Body · Energy 3 · Might 3
Printings: UNL-102/219

> [Hunt] (When I conquer or hold, gain 1 XP.)
> Spend 2 XP: [Buff] me. (Give me a +1 :rb_might: buff if I don't have one.)
-/
def UNL_102.meta : CardDef :=
  { id := ⟨"UNL-102"⟩,
    name := "Crowd Favorite",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .hunt, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Crowd Favorite. -/
def UNL_102 : CardDef :=
  { UNL_102.meta with
    abilities := [.activated [.spendXP 2] .normal (.of [] (.prim (.buff .self))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-103
/--
**Disposal Order** — Spell · Body · Energy 2
Printings: UNL-103/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose one —Choose up to 3 cards from opponents' trashes. Their owners recycle them.Draw 1.
-/
def UNL_103.meta : CardDef :=
  { id := ⟨"UNL-103"⟩,
    name := "Disposal Order",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Disposal Order. -/
def UNL_103 : CardDef :=
  { UNL_103.meta with
    spellEffect := some { body := .nop, recheckTargets := true, modes := [
      ⟨"相手の Trash から最大3枚を Recycle", [.targetOf (.upTo 3) .enemy .inTrash [.physicalCard]],
        .recycleTrashTargets, none⟩,
      ⟨"1枚引く", [], .prim (.draw .you (.const 1)), none⟩] },
    status := .full }

-- BEGIN GENERATED UNL-104
/--
**Gentle Gemdragon** — Unit · Body · Energy 8 · Might 8
Printings: UNL-104/219

> When you play me or another Dragon, ready up to 2 runes.
-/
def UNL_104.meta : CardDef :=
  { id := ⟨"UNL-104"⟩,
    name := "Gentle Gemdragon",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Mount Targon"⟩],
    domains := [.body],
    cost := some ⟨8, []⟩,
    might := some 8,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Gentle Gemdragon. -/
def UNL_104 : CardDef :=
  { UNL_104.meta with
    abilities := [
      .triggered (.onSelf .play)
        (.of [] readyTwoRunes)
        .unlimited,
      .triggered { event := .play, subject := otherDragon }
        (.of [] readyTwoRunes)
        .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-105
/--
**Imposing Challenger** — Unit · Body · Energy 5 · Might 5
Printings: UNL-105/219

> When I move, you may move an enemy unit here with less Might than me to a different
> battlefield.
-/
def UNL_105.meta : CardDef :=
  { id := ⟨"UNL-105"⟩,
    name := "Imposing Challenger",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.body],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Imposing Challenger. -/
def UNL_105 : CardDef :=
  { UNL_105.meta with
    abilities := [.triggered (.onSelf .move)
      (.of [.targetOf .one .enemy .here [.ofType .unit, .mightLtOf .self],
          .targetOf .one .any .anywhere [.ofType .battlefield, .not (.at_ .self)]]
        (.may (.prim (.move (.slot 0) (.at_ (.slot 1)))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-106
/--
**Repulse** — Spell · Body · Energy 1 + Power 1
Printings: UNL-106/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a friendly unit at a battlefield. Counter an enemy spell or ability that chooses it and
> no other friendly unit.
-/
def UNL_106.meta : CardDef :=
  { id := ⟨"UNL-106"⟩,
    name := "Repulse",
    types := [.spell],
    domains := [.body],
    cost := some ⟨1, [.domain .body]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Repulse counters an item that chooses this friendly Unit and no other friendly Unit. -/
def UNL_106 : CardDef :=
  { UNL_106.meta with
    spellEffect := some {
      choices := [.targetOf .one .friendly .anywhere [.ofType .unit, .onBattlefield],
        .targetOf .one .enemy .onChainAll [.choosesOnly (.slot 0)]]
      body := .ifThen (.matches (.slot 0) .onBattlefield) (.prim (.counter (.slot 1))) .nop
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED UNL-107
/--
**Stare Down** — Spell · Body · Energy 2
Printings: UNL-107/219

> Choose a friendly unit and a battlefield. Move all enemy units at that battlefield with less
> Might than the chosen unit to their base. Gain 1 XP.
-/
def UNL_107.meta : CardDef :=
  { id := ⟨"UNL-107"⟩,
    name := "Stare Down",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Stare Down. -/
def UNL_107 : CardDef :=
  { UNL_107.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .any .anywhere [.ofType .battlefield]]
      (.seqOf [.prim (.move (Selector.all .enemy .anywhere
          [.ofType .unit, .at_ (.slot 1), .mightLtOf (.slot 0)]) .base),
        .prim (.gainXP .you (.const 1))])),
    status := .drafted }

-- BEGIN GENERATED UNL-108
/--
**Wily Newtfish** — Unit · Body · Energy 4 · Might 4
Printings: UNL-108/219

> If you've gained XP this turn, I have +1 :rb_might: and [Ganking]. (I can move from
> battlefield to battlefield.)
-/
def UNL_108.meta : CardDef :=
  { id := ⟨"UNL-108"⟩,
    name := "Wily Newtfish",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Wily Newtfish. -/
def UNL_108 : CardDef :=
  { UNL_108.meta with
    abilities := [.passive (.noted .gainedXP)
      [.mightPlus .self (.const 1), .keyword .self { keyword := .ganking }]],
    status := .full }

-- BEGIN GENERATED UNL-109
/--
**Blood Rose** — Gear · Body · Energy 1
Printings: UNL-109/219

> When you play a unit, you may pay :rb_energy_1: to gain 1 XP.
> Spend 3 XP, :rb_exhaust:: Ready a unit.
-/
def UNL_109.meta : CardDef :=
  { id := ⟨"UNL-109"⟩,
    name := "Blood Rose",
    types := [.gear],
    domains := [.body],
    cost := some ⟨1, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Blood Rose. -/
def UNL_109 : CardDef :=
  { UNL_109.meta with
    abilities := [
      .triggered
        { event := .play
          subject := Selector.all .you .anywhere [.ofType .unit]
          optional := true, cost := .energy 1 }
        (.of [] (.prim (.gainXP .you (.const 1)))) .unlimited,
      .activated [.spendXP 3, .exhaustSelf] .normal
        { choices := [.targetOf .one .any .anywhere [.ofType .unit]]
          recheckTargets := true
          body := .prim (.ready (.slot 0)) } .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-110
/--
**Clash of Giants** — Spell · Body · Energy 6 + Power 2
Printings: UNL-110/219

> Choose two units. They deal damage equal to their Mights to each other.
-/
def UNL_110.meta : CardDef :=
  { id := ⟨"UNL-110"⟩,
    name := "Clash of Giants",
    types := [.spell],
    domains := [.body],
    cost := some ⟨6, [.domain .body, .domain .body]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Clash of Giants. -/
def UNL_110 : CardDef :=
  { UNL_110.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit],
        .targetOf .one .any .anywhere [.ofType .unit, .not (.sameAs (.slot 0))]]
      (.prim (.exchangeDamage (.slot 0) (.slot 1)))),
    status := .full }

-- BEGIN GENERATED UNL-111
/--
**Determined Sentry** — Unit · Body · Energy 1 · Might 1
Printings: UNL-111/219

> I can't move to base.
-/
def UNL_111.meta : CardDef :=
  { id := ⟨"UNL-111"⟩,
    name := "Determined Sentry",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.body],
    cost := some ⟨1, []⟩,
    might := some 1,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Determined Sentry. -/
def UNL_111 : CardDef :=
  { UNL_111.meta with
    abilities := [.passive .always [.noMoveToBase]],
    status := .full }

-- BEGIN GENERATED UNL-112
/--
**Irresistible Faefolk** — Unit · Body · Energy 2 · Might 1
Printings: UNL-112/219

> When I move to a battlefield, you may move an enemy unit to that battlefield.
-/
def UNL_112.meta : CardDef :=
  { id := ⟨"UNL-112"⟩,
    name := "Irresistible Faefolk",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Ionia"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 1,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Irresistible Faefolk can move an enemy Unit to the Battlefield it moved to. -/
def UNL_112 : CardDef :=
  { UNL_112.meta with
    abilities := [.triggered { Trigger.onSelf .moveToBattlefield with optional := true }
      (.of [.targetOf .one .enemy .anywhere [.ofType .unit]]
        (.prim (.move (.slot 0) (.at_
          (.all .any .atBattlefield [.ofType .battlefield, .atEventBattlefield none]))))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-113
/--
**Master Yi, Tempered** — Unit · Body · Energy 4 · Might 4
Printings: UNL-113/219, UNL-113a/219

> [Hunt 2] (When I conquer or hold, gain 2 XP.)
> [Level 6][>] I have [Deflect] and [Ganking]. (While you have 6+ XP, opponents must pay
> :rb_rune_rainbow: to choose me with a spell or ability and I can move from battlefield to
> battlefield.)
-/
def UNL_113.meta : CardDef :=
  { id := ⟨"UNL-113"⟩,
    name := "Master Yi",
    subtitle := some "Tempered",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Master Yi"⟩, ⟨"Ionia"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .hunt, arg := .amount 2 },
      { keyword := .level, arg := .amount 6 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Master Yi. -/
def UNL_113 : CardDef :=
  { UNL_113.meta with
    abilities := [.passive (.cmp .ge .xp (.const 6))
      [.keyword .self { keyword := .deflect }, .keyword .self { keyword := .ganking }]],
    status := .drafted }

-- BEGIN GENERATED UNL-114
/--
**Nidalee, Cat Form** — Unit · Body · Energy 3 + Power 1 · Might 4
Printings: UNL-114/219

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> When I win a combat, draw 1. (I win if I remain after combat.)
-/
def UNL_114.meta : CardDef :=
  { id := ⟨"UNL-114"⟩,
    name := "Nidalee",
    subtitle := some "Cat Form",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Ixtal"⟩, ⟨"Nidalee"⟩],
    domains := [.body],
    cost := some ⟨3, [.domain .body]⟩,
    might := some 4,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Nidalee. -/
def UNL_114 : CardDef :=
  { UNL_114.meta with
    abilities := [.triggered (.onSelf .winCombat) (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-115
/--
**Nilah, Joyful Ascetic** — Unit · Body · Energy 3 + Power 1 · Might 4
Printings: UNL-115/219

> [Accelerate] (You may pay :rb_energy_1::rb_rune_body: as an additional cost to have me enter
> ready.)
> [Ganking] (I can move from battlefield to battlefield.)
> When I move, gain 1 XP.
-/
def UNL_115.meta : CardDef :=
  { id := ⟨"UNL-115"⟩,
    name := "Nilah",
    subtitle := some "Joyful Ascetic",
    types := [.unit],
    tags := [⟨"Nilah"⟩, ⟨"Kathkan"⟩, ⟨"Demon"⟩],
    domains := [.body],
    cost := some ⟨3, [.domain .body]⟩,
    might := some 4,
    keywords := [{ keyword := .accelerate },
      { keyword := .ganking }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Nilah, Joyful Ascetic. -/
def UNL_115 : CardDef :=
  { UNL_115.meta with
    abilities := [.triggered (.onSelf .move)
        (.of []
        (.prim (.gainXP .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-116
/--
**Poppy, Paragon** — Unit · Body · Energy 5 · Might 5
Printings: UNL-116/219, UNL-116a/219

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> When you play me, if an opponent's score is within 3 points of the Victory Score, ready me and
> gain 3 XP.
-/
def UNL_116.meta : CardDef :=
  { id := ⟨"UNL-116"⟩,
    name := "Poppy",
    subtitle := some "Paragon",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Demacia"⟩, ⟨"Poppy"⟩],
    domains := [.body],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Poppy. -/
def UNL_116 : CardDef :=
  { UNL_116.meta with
    abilities := [.triggered { event := .play, condition := .opponentNearVictory 3 }
      (.of [] (.seqOf [.prim (.ready .self), .prim (.gainXP .you (.const 3))])) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-117
/--
**Arachnoid Horror** — Unit · Body · Energy 6 + Power 1 · Might 6
Printings: UNL-117/219

> [Hunt 2] (When I conquer or hold, gain 2 XP.)
> I can be played to an occupied battlefield if an enemy unit is alone there.
> Friendly units can be played to an occupied battlefield if an enemy unit is alone there.
-/
def UNL_117.meta : CardDef :=
  { id := ⟨"UNL-117"⟩,
    name := "Arachnoid Horror",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Spider"⟩],
    domains := [.body],
    cost := some ⟨6, [.domain .body]⟩,
    might := some 6,
    keywords := [{ keyword := .hunt, arg := .amount 2 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Arachnoid Horror. -/
def UNL_117 : CardDef :=
  { UNL_117.meta with
    abilities := [.passive .always [.playToBf [.enemyAlone], .playToBfAll [.enemyAlone]]],
    status := .full }

-- BEGIN GENERATED UNL-118
/--
**Elder Dragon** — Unit · Body · Energy 12 + Power 4 · Might 10
Printings: UNL-118/219, UNL-118a/219

> Any amount of your damage is enough to kill enemy units.
> When you play me, choose up to one enemy unit at each location. Deal 1 to them.
-/
def UNL_118.meta : CardDef :=
  { id := ⟨"UNL-118"⟩,
    name := "Elder Dragon",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Demacia"⟩],
    domains := [.body],
    cost := some ⟨12, [.domain .body, .domain .body, .domain .body, .domain .body]⟩,
    might := some 10,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Elder Dragon. -/
def UNL_118 : CardDef :=
  { UNL_118.meta with
    abilities := [.passive .always [.anyDamageKills],
      .triggered (.onSelf .play)
        (.of [.targetOf .onePerLocation .enemy .anywhere [.ofType .unit]]
          (.prim (.deal (.slotsFrom 0) (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-119
/--
**Kha'Zix, Evolving Hunter** — Unit · Body · Energy 5 + Power 1 · Might 5
Printings: UNL-119/219, UNL-119a/219, VEN-180/166

> [Hunt] (When I conquer or hold, gain 1 XP.)
> When I attack, you may spend 3 XP to deal damage equal to my Might to an enemy unit here.
-/
def UNL_119.meta : CardDef :=
  { id := ⟨"UNL-119"⟩,
    name := "Kha'Zix",
    subtitle := some "Evolving Hunter",
    types := [.unit],
    tags := [⟨"Kha'Zix"⟩, ⟨"The Void"⟩],
    domains := [.body],
    cost := some ⟨5, [.domain .body]⟩,
    might := some 5,
    keywords := [{ keyword := .hunt, arg := .amount 1 }],
    sets := [⟨"UNL"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Kha'Zix. -/
def UNL_119 : CardDef :=
  { UNL_119.meta with
    abilities := [.triggered { Trigger.onSelf .attack with optional := true, cost := .spendXP 3 }
      { choices := [.targetOf .one .enemy .here [.ofType .unit]]
        recheckTargets := true
        body := .prim (.deal (.slot 0) (.mightOf .self)) } .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-120
/--
**Rengar, Trophy Hunter** — Unit · Body · Energy 5 + Power 1 · Might 6
Printings: UNL-120/219, UNL-120a/219, VEN-179/166

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> I can be played to a battlefield where there are enemy units (even if you don't have units
> there).
-/
def UNL_120.meta : CardDef :=
  { id := ⟨"UNL-120"⟩,
    name := "Rengar",
    subtitle := some "Trophy Hunter",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Rengar"⟩, ⟨"Ixtal"⟩],
    domains := [.body],
    cost := some ⟨5, [.domain .body]⟩,
    might := some 6,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Rengar. -/
def UNL_120 : CardDef :=
  { UNL_120.meta with
    -- Official Unleashed errata extends both the location and timing permissions of Ambush.
    abilities := [.passive .always [.ambushToBf [.enemyOccupied]]],
    status := .full }

-- BEGIN GENERATED UNL-121
/--
**Bewitching Spirit** — Unit · Chaos · Energy 3 · Might 2
Printings: UNL-121/219

> When you play me, choose a player. They discard 1.
-/
def UNL_121.meta : CardDef :=
  { id := ⟨"UNL-121"⟩,
    name := "Bewitching Spirit",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 2,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Bewitching Spirit. -/
def UNL_121 : CardDef :=
  { UNL_121.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.eitherOf (EffectList.ofList
        [.prim (.discard .you (.const 1)), .prim (.discard .opponent (.const 1))]))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-122
/--
**Crescent Guardian** — Unit · Chaos · Energy 4 · Might 4
Printings: UNL-122/219

> If you've played a spell this turn, you may pay :rb_rune_chaos: as an additional cost to play
> me. If you do, I enter ready.
-/
def UNL_122.meta : CardDef :=
  { id := ⟨"UNL-122"⟩,
    name := "Crescent Guardian",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Crescent Guardian. -/
def UNL_122 : CardDef :=
  { UNL_122.meta with
    additionalCost := some ⟨0, [.domain .chaos]⟩,
    abilities := [.triggered { event := .play, condition := .and .paid (.spentOnSpell 0) }
      (.of [] (.prim (.ready .self))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-123
/--
**Evershade Stalker** — Unit · Chaos · Energy 3 · Might 3
Printings: UNL-123/219

> When you play me, discard 1, then draw 1.
-/
def UNL_123.meta : CardDef :=
  { id := ⟨"UNL-123"⟩,
    name := "Evershade Stalker",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Evershade Stalker. -/
def UNL_123 : CardDef :=
  { UNL_123.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.seqOf [.prim (.discard .you (.const 1)),
          .prim (.draw .you (.const 1))])) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-124
/--
**Isolate** — Spell · Chaos · Energy 2
Printings: UNL-124/219

> Move an enemy unit from a battlefield to its base. Then, if there's an enemy unit alone at
> that battlefield, draw 1.
-/
def UNL_124.meta : CardDef :=
  { id := ⟨"UNL-124"⟩,
    name := "Isolate",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Isolate. -/
def UNL_124 : CardDef :=
  { UNL_124.meta with
    spellEffect := some (.of [.targetOf .one .enemy .anywhere [.ofType .unit, .onBattlefield]]
      (.bind ⟨"n"⟩ (.count (Selector.all .enemy .anywhere [.ofType .unit, .at_ (.slot 0)]))
        (.seqOf [.prim (.move (.slot 0) .base),
          .ifThen (.and (.cmp .eq (.var ⟨"n"⟩) (.const 2)) (.not (.matches (.slot 0) .onBattlefield)))
            (.prim (.draw .you (.const 1))) .nop]))),
    status := .drafted }

-- BEGIN GENERATED UNL-125
/--
**Lunar Boon** — Spell · Chaos · Energy 3
Printings: UNL-125/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Discard 1, then draw 2.
-/
def UNL_125.meta : CardDef :=
  { id := ⟨"UNL-125"⟩,
    name := "Lunar Boon",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Lunar Boon. -/
def UNL_125 : CardDef :=
  { UNL_125.meta with
    spellEffect := some (.of []
      (.seqOf [.prim (.discard .you (.const 1)),
        .prim (.draw .you (.const 2))])),
    status := .full }

-- BEGIN GENERATED UNL-126
/--
**Megatusk** — Unit · Chaos · Energy 6 · Might 6
Printings: UNL-126/219

> Spend 3 XP: Give your units here [Ganking] this turn. (We can move from battlefield to
> battlefield.)
-/
def UNL_126.meta : CardDef :=
  { id := ⟨"UNL-126"⟩,
    name := "Megatusk",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨6, []⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Megatusk. -/
def UNL_126 : CardDef :=
  { UNL_126.meta with
    abilities := [.activated [.spendXP 3] .normal
      (.of [] (.grant (Selector.all .you .here [.ofType .unit])
        (.keyword .it { keyword := .ganking }) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-127
/--
**Mister Root** — Unit · Chaos · Energy 2 · Might 1
Printings: UNL-127/219

> [Accelerate] (You may pay :rb_energy_1::rb_rune_chaos: as an additional cost to have me enter
> ready.)
> When I move to a battlefield, gain 2 XP.
-/
def UNL_127.meta : CardDef :=
  { id := ⟨"UNL-127"⟩,
    name := "Mister Root",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Mister Root. -/
def UNL_127 : CardDef :=
  { UNL_127.meta with
    abilities := [.triggered { event := .move, condition := .matches .self .onBattlefield }
      (.of [] (.prim (.gainXP .you (.const 2)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-128
/--
**Star-Crossed** — Spell · Chaos · Energy 3 + Power 1
Printings: UNL-128/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Return a friendly unit and an enemy unit to their owners' hands.
-/
def UNL_128.meta : CardDef :=
  { id := ⟨"UNL-128"⟩,
    name := "Star-Crossed",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Star-Crossed. -/
def UNL_128 : CardDef :=
  { UNL_128.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .enemy .anywhere [.ofType .unit]]
      (.seqOf [.prim (.returnToHand (.slot 0)), .prim (.returnToHand (.slot 1))])),
    status := .drafted }

-- BEGIN GENERATED UNL-129
/--
**Vicious Snapjaws** — Unit · Chaos · Energy 5 · Might 5
Printings: UNL-129/219

> When another friendly unit dies, gain 1 XP.
-/
def UNL_129.meta : CardDef :=
  { id := ⟨"UNL-129"⟩,
    name := "Vicious Snapjaws",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Vicious Snapjaws. -/
def UNL_129 : CardDef :=
  { UNL_129.meta with
    abilities := [.triggered
      { event := .die, subject := Selector.all .friendly .anywhere [.ofType .unit, .notSelf] }
      (.of [] (.prim (.gainXP .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-130
/--
**Walking Roost** — Unit · Chaos · Energy 5 · Might 6
Printings: UNL-130/219

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> When you play me, choose an opponent. They play a 1 :rb_might: Bird unit token with [Deflect].
-/
def UNL_130.meta : CardDef :=
  { id := ⟨"UNL-130"⟩,
    name := "Walking Roost",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨5, []⟩,
    might := some 6,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Walking Roost targets one opponent, who chooses where to play the Bird. -/
def UNL_130 : CardDef :=
  { UNL_130.meta with
    abilities := [.triggered (.onSelf .play)
      { playerTarget := some .enemy, body := .eachPlayer (.chosen 0) (.prim (.playUnitToken "Bird")) }
      .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-131
/--
**Abandon** — Spell · Chaos · Energy 2
Printings: UNL-131/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Counter a spell. Return it to its owner's hand instead of putting it in their trash.
> [Predict]. (Look at the top card of your Main Deck. You may recycle it.)
-/
def UNL_131.meta : CardDef :=
  { id := ⟨"UNL-131"⟩,
    name := "Abandon",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Abandon. -/
def UNL_131 : CardDef :=
  { UNL_131.meta with
    spellEffect := some (.of [.targetOf .one .any .onChain [.ofType .spell]]
      (.seqOf [.prim (.counterToHand (.slot 0)), .prim (.predict (.const 1))])),
    status := .full }

-- BEGIN GENERATED UNL-132
/--
**Angler Beast** — Unit · Chaos · Energy 5 + Power 1 · Might 5
Printings: UNL-132/219

> When you play me, return all units with 2 :rb_might: or less to their owners' hands.
-/
def UNL_132.meta : CardDef :=
  { id := ⟨"UNL-132"⟩,
    name := "Angler Beast",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨5, [.domain .chaos]⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Angler Beast. -/
def UNL_132 : CardDef :=
  { UNL_132.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.prim (.returnToHand (Selector.all .any .anywhere
        [.ofType .unit, .might .le (.const 2)])))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-133
/--
**Blast Cone** — Gear · Chaos · Energy 4 + Power 1
Printings: UNL-133/219

> When you play this, you may move an enemy unit.
> When you move an enemy unit, you may exhaust this to [Stun] it. (It doesn't deal combat damage
> this turn.)
-/
def UNL_133.meta : CardDef :=
  { id := ⟨"UNL-133"⟩,
    name := "Blast Cone",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Blast Cone. -/
def UNL_133 : CardDef :=
  { UNL_133.meta with
    abilities := [
      .triggered (.onSelf .play)
        (.of [.targetOf (.upTo 1) .enemy .anywhere [.ofType .unit]]
          (.eitherOf (.cons (.prim (.move (.slot 0) .base))
            (.cons (.prim (.move (.slot 0) (.at_ (Selector.one .any .anywhere [.ofType .battlefield]))))
              .nil)))) .unlimited,
      .triggered
        { subject := Selector.all .enemy .anywhere [.ofType .unit], event := .movedByYou }
        (.of [] (.ifThen (.matches .self .ready)
          (.may (.seqOf [.prim (.exhaust .self), .prim (.stun (.slot 0))])) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-134
/--
**Existential Dread** — Spell · Chaos · Energy 1 + Power 1
Printings: UNL-134/219

> [Action] (Play on your turn or in showdowns.)
> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> [Stun] an attacking enemy unit. If it's already stunned, return it to its owner's hand
> instead. (A stunned unit doesn't deal combat damage this turn.)
-/
def UNL_134.meta : CardDef :=
  { id := ⟨"UNL-134"⟩,
    name := "Existential Dread",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨1, [.domain .chaos]⟩,
    keywords := [{ keyword := .action },
      { keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Existential Dread. -/
def UNL_134 : CardDef :=
  { UNL_134.meta with
    spellEffect := some (.of [.targetOf .one .enemy .anywhere [.ofType .unit, .attacker]]
      (.ifThen (.matches (.slot 0) .stunned) (.prim (.returnToHand (.slot 0)))
        (.prim (.stun (.slot 0))))),
    status := .drafted }

-- BEGIN GENERATED UNL-135
/--
**Insightful Investigator** — Unit · Chaos · Energy 3 · Might 3
Printings: UNL-135/219

> When you play me, choose an opponent. They reveal their hand. You may pay 2 XP to choose a
> card from their hand. If you do, they discard that card and draw 1.
-/
def UNL_135.meta : CardDef :=
  { id := ⟨"UNL-135"⟩,
    name := "Insightful Investigator",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Insightful Investigator. -/
def UNL_135 : CardDef :=
  let revealed := [Filter.ownedByPlayerTarget 0, .revealedByEffect]
  { UNL_135.meta with
    abilities := [.triggered (.onSelf .play)
      { playerTarget := some .enemy
        body := .revealHand (.chosen 0)
          (.ifThen (.and (.cmp .ge .xp (.const 2))
              (.cmp .gt (.count (Selector.all .any .inHand revealed)) (.const 0)))
            (.may (.seqOf [.prim (.spendXP .you (.const 2)),
              .chooseObject .any .inHand (.ofList revealed)
                (.eachPlayer (.chosen 0) (.seqOf [.prim (.discardCard (.var pickVar)),
                  .prim (.draw .you (.const 1))]))])) .nop) } .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-136
/--
**Scryer's Bloom** — Gear · Chaos · Energy 1
Printings: UNL-136/219

> This enters exhausted.
> Kill this, :rb_energy_1:, :rb_exhaust:: [Predict 2], then draw 1. Gain 1 XP.  (To Predict 2,
> look at the top two cards of your Main Deck. Recycle any of them and put the rest back in any
> order.)
-/
def UNL_136.meta : CardDef :=
  { id := ⟨"UNL-136"⟩,
    name := "Scryer's Bloom",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Scryer's Bloom. -/
def UNL_136 : CardDef :=
  { UNL_136.meta with
    abilities := [.passive .always [.entersExhausted],
      .activated [.pay ⟨1, []⟩, .exhaustSelf, .killSelf] .normal
        (.of [] (.seqOf [predict2, .prim (.draw .you (.const 1)),
          .prim (.gainXP .you (.const 1))])) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-137
/--
**Sinister Poro** — Unit · Chaos · Energy 2 + Power 1 · Might 1
Printings: UNL-137/219

> When I attack, you may pay :rb_energy_1: to move an enemy unit here to its base.
-/
def UNL_137.meta : CardDef :=
  { id := ⟨"UNL-137"⟩,
    name := "Sinister Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩, ⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨2, [.domain .chaos]⟩,
    might := some 1,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Sinister Poro. -/
def UNL_137 : CardDef :=
  { UNL_137.meta with
    abilities := [.triggered { Trigger.onSelf .attack with optional := true, cost := .energy 1 }
      { choices := [.targetOf .one .enemy .here [.ofType .unit]]
        recheckTargets := true
        body := .prim (.move (.slot 0) .base) } .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-138
/--
**The List** — Gear · Chaos · Energy 1
Printings: UNL-138/219

> As you play this, name a tag. (For example, Miss Fortune, Demacia, and Poro are tags.)
> :rb_exhaust:: Give a unit with the named tag -2 :rb_might: this turn.
-/
def UNL_138.meta : CardDef :=
  { id := ⟨"UNL-138"⟩,
    name := "The List",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- The List. -/
def UNL_138 : CardDef :=
  { UNL_138.meta with
    abilities := [
      .triggered (.onSelf .play) (.of [] nameATag) .unlimited,
      .activated [.exhaustSelf] .normal
        (.of [.targetOf .one .any .anywhere [.ofType .unit, .sharesGainedTag]]
          (.grant (.slot 0) (.mightMinus .it (.const 2)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-139
/--
**Bone Skewer** — Spell · Chaos · Energy 2 + Power 1
Printings: UNL-139/219

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> Choose a battlefield. An opponent reveals their hand. You may choose a unit from it. They play
> that unit to that battlefield, ignoring any and all costs. When they do, [Stun] it. (It
> doesn't deal combat damage this turn.)
-/
def UNL_139.meta : CardDef :=
  { id := ⟨"UNL-139"⟩,
    name := "Bone Skewer",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, [.domain .chaos]⟩,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Bone Skewer. -/
def UNL_139 : CardDef :=
  { UNL_139.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .battlefield]]
      (.eachPlayer .eachOpponent
        (.seqOf [.prim (.playTo (Selector.one .friendly .inHand [.ofType .unit]) (.slot 0)),
          .prim (.stun (Selector.all .any .anywhere [.ofType .unit, .playedLast]))]))),
    status := .drafted }

-- BEGIN GENERATED UNL-140
/--
**Conscription** — Spell · Chaos · Energy 5 + Power 2
Printings: UNL-140/219

> You may spend 5 XP as an additional cost to play this.
> Choose an enemy unit at a battlefield with 3 :rb_might: or less. If you paid the additional
> cost, choose any enemy unit at a battlefield instead. Take control of it, exhaust it, and
> recall it.
-/
def UNL_140.meta : CardDef :=
  { id := ⟨"UNL-140"⟩,
    name := "Conscription",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨5, [.domain .chaos, .domain .chaos]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Conscription. -/
def UNL_140 : CardDef :=
  { UNL_140.meta with
    spellEffect := some { EffectDef.of [.targetOf .one .enemy .atBattlefield [.ofType .unit]]
      (.seqOf [.prim (.takeControl (.slot 0)), .prim (.exhaust (.slot 0)),
        .prim (.recall (.slot 0) false)]) with
      recheckTargets := true },
    playExtra := some (.spendXPOver 5 3, false),
    status := .full }

-- BEGIN GENERATED UNL-141
/--
**Evelynn, Entrancing** — Unit · Chaos · Energy 2 · Might 2
Printings: UNL-141/219

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Backline] (I must be assigned combat damage last.)
> When you play me from face down on your turn, you may move an enemy unit at a different
> location to my battlefield.
-/
def UNL_141.meta : CardDef :=
  { id := ⟨"UNL-141"⟩,
    name := "Evelynn",
    subtitle := some "Entrancing",
    types := [.unit],
    tags := [⟨"Evelynn"⟩, ⟨"Demon"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .hidden },
      { keyword := .backline }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Evelynn. -/
def UNL_141 : CardDef :=
  { UNL_141.meta with
    abilities := [.triggered { event := .play, condition := .and .fromHidden .yourTurn }
      (.of [] (.may (.prim (.move
        (Selector.one .enemy .anywhere [.ofType .unit, .not (.at_ .self)])
        (.at_ (.locationOf .self)))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-142
/--
**Heedless Resurrection** — Spell · Chaos · Energy 2 + Power 1
Printings: UNL-142/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> As an additional cost to play this, kill a friendly unit.
> Play a unit from your trash that costs no more Energy and no more Power than the killed unit,
> ignoring its cost.
-/
def UNL_142.meta : CardDef :=
  { id := ⟨"UNL-142"⟩,
    name := "Heedless Resurrection",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, [.domain .chaos]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Heedless Resurrection. -/
def UNL_142 : CardDef :=
  { UNL_142.meta with
    spellEffect := some { EffectDef.of [.targetOf .one .you .inTrash [.ofType .unit]]
      (.playCard (.slot 0) .ignoreBase) with recheckTargets := true },
    playExtra := some (.killUnitForTarget, true),
    status := .full }

-- BEGIN GENERATED UNL-143
/--
**Kha'Zix, Mutating Horror** — Unit · Chaos · Energy 4 + Power 1 · Might 4
Printings: UNL-143/219, UNL-143a/219

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> When I attack or defend, if an enemy unit is alone here, give me +2 :rb_might: this turn and
> gain 2 XP.
-/
def UNL_143.meta : CardDef :=
  { id := ⟨"UNL-143"⟩,
    name := "Kha'Zix",
    subtitle := some "Mutating Horror",
    types := [.unit],
    tags := [⟨"Kha'Zix"⟩, ⟨"The Void"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    might := some 4,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Kha'Zix. -/
def UNL_143 : CardDef :=
  let isolated := Condition.cmp .eq (.count (Selector.all .enemy .here [.ofType .unit])) (.const 1)
  let reward := EffectDef.of [] (.seqOf [
    .grant .self (.mightPlus .it (.const 2)) .thisTurn, .prim (.gainXP .you (.const 2))])
  { UNL_143.meta with
    abilities := [
      .triggered { event := .attack, condition := isolated } reward .unlimited,
      .triggered { event := .defend, condition := isolated } reward .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-144
/--
**Maduli the Gatekeeper** — Unit · Chaos · Energy 7 + Power 1 · Might 6
Printings: UNL-144/219

> I can't be readied.
> :rb_rune_chaos:: Move me to an occupied enemy battlefield if my Might is greater than the
> total Might of enemy units there.
-/
def UNL_144.meta : CardDef :=
  { id := ⟨"UNL-144"⟩,
    name := "Maduli the Gatekeeper",
    types := [.unit],
    tags := [⟨"Bandle City"⟩],
    domains := [.chaos],
    cost := some ⟨7, [.domain .chaos]⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Maduli the Gatekeeper. -/
def UNL_144 : CardDef :=
  { UNL_144.meta with
    abilities := [
      .triggered (.onSelf .play) (.of [] (.prim (.gainTag .self "!cantReady"))) .unlimited,
      .activated [.pay ⟨0, [.domain .chaos]⟩] .normal
        (.of [.targetOf .one .any .atBattlefield [.ofType .battlefield, .enemyOccupied]]
          (.ifThen (.cmp .gt (.mightOf .self)
              (.mightOf (Selector.all .enemy .anywhere [.ofType .unit, .at_ (.slot 0)])))
            (.prim (.move .self (.at_ (.slot 0)))) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-145
/--
**Pyke, Returned** — Unit · Chaos · Energy 3 · Might 3
Printings: UNL-145/219, UNL-145a/219

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Backline] (I must be assigned combat damage last.)
> Once each turn, when an enemy unit dies while I'm at a battlefield, play a Gold gear token
> exhausted. (It has "[Reaction][>] Kill this, :rb_exhaust:: [Add] :rb_rune_rainbow:.")
-/
def UNL_145.meta : CardDef :=
  { id := ⟨"UNL-145"⟩,
    name := "Pyke",
    subtitle := some "Returned",
    types := [.unit],
    tags := [⟨"Pyke"⟩, ⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .hidden },
      { keyword := .backline }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Pyke. -/
def UNL_145 : CardDef :=
  { UNL_145.meta with
    abilities := [.triggered
      { event := .die, subject := Selector.all .enemy .anywhere [.ofType .unit],
        condition := .matches .self .onBattlefield }
      (.of [] (.prim (.create "Gold" (.const 1) .atBase false))) (.perTurn 1)],
    status := .drafted }

-- BEGIN GENERATED UNL-146
/--
**Syndra, Transcendent** — Unit · Chaos · Energy 6 + Power 1 · Might 6
Printings: UNL-146/219

> While I'm in a showdown, your spells have [Repeat] :rb_energy_2::rb_rune_chaos:. (You may pay
> the additional cost to repeat the spell's effect.)
-/
def UNL_146.meta : CardDef :=
  { id := ⟨"UNL-146"⟩,
    name := "Syndra",
    subtitle := some "Transcendent",
    types := [.unit],
    tags := [⟨"Ionia"⟩, ⟨"Syndra"⟩],
    domains := [.chaos],
    cost := some ⟨6, [.domain .chaos]⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Syndra. -/
def UNL_146 : CardDef :=
  { UNL_146.meta with
    abilities := [.passive .inShowdown [.grantRepeat ⟨2, [.domain .chaos]⟩]],
    status := .drafted }

-- BEGIN GENERATED UNL-147
/--
**Baron Nashor** — Unit · Chaos · Energy 10 + Power 3 · Might 12
Printings: UNL-147/219, UNL-147a/219, UNL-238/219

> As you play me, add the Baron Pit battlefield token to the board if it's not there already. If
> you do, I enter there. (It has "Units can move here from anywhere.")
> I can't be chosen by enemy spells and abilities.
> Other friendly units have +2 :rb_might:.
-/
def UNL_147.meta : CardDef :=
  { id := ⟨"UNL-147"⟩,
    name := "Baron Nashor",
    types := [.unit],
    tags := [⟨"The Void"⟩],
    domains := [.chaos],
    cost := some ⟨10, [.domain .chaos, .domain .chaos, .domain .chaos]⟩,
    might := some 12,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Baron Nashor. -/
def UNL_147 : CardDef :=
  { UNL_147.meta with
    abilities := [
      .triggered (.onSelf .play)
        (.of [] (.ifThen (.not (.exists (Selector.all .any .anywhere [.named "Baron Pit"])))
          (.seqOf [.prim (.addBattlefield "Baron Pit"),
            .prim (.move .self (.at_ (Selector.one .any .anywhere [.named "Baron Pit"])))]) .nop))
        .unlimited,
      .passive .always [.cant .self .beChosen],
      .passive .always [.mightPlus otherFriendlyUnit (.const 2)]],
    status := .drafted }

-- BEGIN GENERATED UNL-148
/--
**Cursed Sarcophagus** — Gear · Chaos · Energy 4 + Power 1
Printings: UNL-148/219

> When you play this, banish all units from your trash.
> :rb_exhaust:: Play a unit banished with this. (You must pay its costs.)
-/
def UNL_148.meta : CardDef :=
  { id := ⟨"UNL-148"⟩,
    name := "Cursed Sarcophagus",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Cursed Sarcophagus. -/
def UNL_148 : CardDef :=
  { UNL_148.meta with
    abilities := [
      .triggered (.onSelf .play)
        (.of [] (.prim (.moveAll .friendly .inTrash (FilterList.ofList [.ofType .unit])
          .inBanishment true))) .unlimited,
      .activated [.exhaustSelf] .normal
        (.of [] (.prim (.playReduced
          (Selector.one .friendly .inBanishment [.ofType .unit, .banishedWithMe]) (.const 0) none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-149
/--
**Diana, No Longer Human** — Unit · Chaos · Energy 4 + Power 1 · Might 3
Printings: UNL-149/219, UNL-149a/219, VEN-183/166

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> When you play a spell, give me +2 :rb_might: this turn.
-/
def UNL_149.meta : CardDef :=
  { id := ⟨"UNL-149"⟩,
    name := "Diana",
    subtitle := some "No Longer Human",
    types := [.unit],
    tags := [⟨"Diana"⟩, ⟨"Mount Targon"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    might := some 3,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Diana. -/
def UNL_149 : CardDef :=
  { UNL_149.meta with
    abilities := [.triggered
      { event := .play, subject := Selector.all .you .anywhere [.ofType .spell] }
      (.of [] (.grant .self (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-150
/--
**Vex, Apathetic** — Unit · Chaos · Energy 4 · Might 4
Printings: UNL-150/219, UNL-150a/219

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> When an opponent plays a unit while I'm at a battlefield, [Stun] it. They can't move it this
> turn. (It doesn't deal combat damage this turn.)
-/
def UNL_150.meta : CardDef :=
  { id := ⟨"UNL-150"⟩,
    name := "Vex",
    subtitle := some "Apathetic",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Yordle"⟩, ⟨"Vex"⟩, ⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Vex stuns units her opponents play and prevents those players from moving them this turn. -/
def UNL_150 : CardDef :=
  { UNL_150.meta with
    abilities := [.triggered
      { subject := Selector.all .enemy .anywhere [.ofType .unit],
        condition := .matches .self .onBattlefield, event := .playIncludingTokens }
      (.of [] (.seqOf [.prim (.stun (.slot 0)),
        .eachPlayer (.playedBy 0) (.prim (.markOn (.slot 0) .cannotMoveByPlayer))])) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-151
/--
**Bandle Soldier** — Unit · Order · Energy 4 + Power 1 · Might 5
Printings: UNL-151/219

> [Level 3][>] I enter ready. (While you have 3+ XP, get the effect.)
-/
def UNL_151.meta : CardDef :=
  { id := ⟨"UNL-151"⟩,
    name := "Bandle Soldier",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order]⟩,
    might := some 5,
    keywords := [{ keyword := .level, arg := .amount 3 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Bandle Soldier. -/
def UNL_151 : CardDef :=
  { UNL_151.meta with
    abilities := [.passive (.cmp .ge .xp (.const 3)) [.entersReady .self]],
    status := .full }

-- BEGIN GENERATED UNL-152
/--
**Black Rose Dignitary** — Unit · Order · Energy 3 · Might 2
Printings: UNL-152/219

> [Assault] (+1 :rb_might: while I'm an attacker.)
> [Deathknell][>] Channel 1 rune exhausted. (When I die, get the effect.)
-/
def UNL_152.meta : CardDef :=
  { id := ⟨"UNL-152"⟩,
    name := "Black Rose Dignitary",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 2,
    keywords := [{ keyword := .assault, arg := .amount 1 },
      { keyword := .deathknell }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Black Rose Dignitary. -/
def UNL_152 : CardDef :=
  { UNL_152.meta with
    abilities := [.triggered (.onSelf .die)
        (.of []
        (.prim (.channel .you (.const 0) (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-153
/--
**Carrion Dredger** — Unit · Order · Energy 2 · Might 1
Printings: UNL-153/219

> [Deathknell][>] Play a 1 :rb_might: Bird unit token with [Deflect] to your base. (When I die,
> get the effect. Opponents must pay :rb_rune_rainbow: to choose a [Deflect] unit with a spell
> or ability.)
-/
def UNL_153.meta : CardDef :=
  { id := ⟨"UNL-153"⟩,
    name := "Carrion Dredger",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Zaun"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Carrion Dredger. -/
def UNL_153 : CardDef :=
  { UNL_153.meta with
    abilities := [.triggered (.onSelf .deathknell)
      (.of [] (.prim (.create "Bird" (.const 1) .atBase false))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-154
/--
**Crimson Pigeons** — Unit · Order · Energy 3 · Might 3
Printings: UNL-154/219

> I have +2 :rb_might: while I'm attacking with another unit.
-/
def UNL_154.meta : CardDef :=
  { id := ⟨"UNL-154"⟩,
    name := "Crimson Pigeons",
    types := [.unit],
    tags := [⟨"Bird"⟩, ⟨"Noxus"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Crimson Pigeons. -/
def UNL_154 : CardDef :=
  { UNL_154.meta with
    abilities := [.passive
      (.and (.matches .self .attacker) (.exists (Selector.all .friendly .anywhere
        [.ofType .unit, .attacker, .notSelf]))) [.mightPlus .self (.const 2)]],
    status := .drafted }

-- BEGIN GENERATED UNL-155
/--
**Heroic Charge** — Spell · Order · Energy 3
Printings: UNL-155/219

> [Action] (Play on your turn or in showdowns.)
> Give a friendly unit +1 :rb_might: this turn and [Stun] an enemy unit at its location. (A
> stunned unit doesn't deal combat damage this turn.)
-/
def UNL_155.meta : CardDef :=
  { id := ⟨"UNL-155"⟩,
    name := "Heroic Charge",
    types := [.spell],
    domains := [.order],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Heroic Charge. -/
def UNL_155 : CardDef :=
  { UNL_155.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .enemy .anywhere [.ofType .unit, .at_ (.slot 0)]]
      (.seqOf [.grant (.slot 0) (.mightPlus .it (.const 1)) .thisTurn, .prim (.stun (.slot 1))])),
    status := .full }

-- BEGIN GENERATED UNL-156
/--
**Loyal Poro** — Unit · Order · Energy 3 · Might 3
Printings: UNL-156/219

> [Deathknell][>] If I didn't die alone, draw 1. (When I die, get the effect. I wasn't alone if
> there were other friendly units here.)
-/
def UNL_156.meta : CardDef :=
  { id := ⟨"UNL-156"⟩,
    name := "Loyal Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩, ⟨"Freljord"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Loyal Poro. -/
def UNL_156 : CardDef :=
  { UNL_156.meta with
    abilities := [.triggered (.onSelf .die)
      (.of [] (.ifThen (.not (.marked .diedAlone)) (.prim (.draw .you (.const 1))) .nop)) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-157
/--
**Scrutinizing Sergeant** — Unit · Order · Energy 6 · Might 6
Printings: UNL-157/219

> When you play me, gain 1 XP for each friendly unit.
-/
def UNL_157.meta : CardDef :=
  { id := ⟨"UNL-157"⟩,
    name := "Scrutinizing Sergeant",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨6, []⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Scrutinizing Sergeant. -/
def UNL_157 : CardDef :=
  { UNL_157.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.prim (.gainXP .you (.count (Selector.all .friendly .anywhere [.ofType .unit])))))
      .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-158
/--
**Shepherd's Heirloom** — Gear · Order · Energy 2 · Might 2
Printings: UNL-158/219

> When you play this, gain 1 XP.
> [Equip] — Spend 1 XP (Pay the cost: Attach this to a unit you control.)
-/
def UNL_158.meta : CardDef :=
  { id := ⟨"UNL-158"⟩,
    name := "Shepherd's Heirloom",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip }],
    sets := [⟨"UNL"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Shepherd's Heirloom. -/
def UNL_158 : CardDef :=
  { UNL_158.meta with
    equipXP := some 1,
    abilities := [.triggered (.onSelf .play) (.of [] (.prim (.gainXP .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-159
/--
**Soul Harvest** — Spell · Order · Energy 2 + Power 1
Printings: UNL-159/219

> Kill a unit at a battlefield with 3 :rb_might: or less.
-/
def UNL_159.meta : CardDef :=
  { id := ⟨"UNL-159"⟩,
    name := "Soul Harvest",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Soul Harvest. -/
def UNL_159 : CardDef :=
  { UNL_159.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere
        [.ofType .unit, .onBattlefield, .might .le (.const 3)]]
      (.prim (.kill (.slot 0)))),
    status := .full }

-- BEGIN GENERATED UNL-160
/--
**Ultrasoft Poro** — Unit · Order · Energy 5 · Might 5
Printings: UNL-160/219

> :rb_exhaust:: Play two 1 :rb_might: Bird unit tokens with [Deflect]. Use this ability only
> while I'm at a battlefield. (Opponents must pay :rb_rune_rainbow: to choose a [Deflect] unit
> with a spell or ability.)
-/
def UNL_160.meta : CardDef :=
  { id := ⟨"UNL-160"⟩,
    name := "Ultrasoft Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩, ⟨"Freljord"⟩],
    domains := [.order],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Ultrasoft Poro. -/
def UNL_160 : CardDef :=
  { UNL_160.meta with
    abilities := [.activated [.exhaustSelf, .fromBattlefield] .normal
      (.of [] (.repeatN (.const 2) (.prim (.playUnitToken "Bird")))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-161
/--
**Divining Shells** — Gear · Order · Energy 2
Printings: UNL-161/219

> [Vision] (When you play this, look at the top card of your Main Deck. You may recycle it.)
> [Action][>] Kill this, :rb_exhaust:: Give a unit +2 :rb_might: this turn.
-/
def UNL_161.meta : CardDef :=
  { id := ⟨"UNL-161"⟩,
    name := "Divining Shells",
    types := [.gear],
    domains := [.order],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .vision }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Divining Shells pays its Kill and Exhaust when activating the Might bonus. -/
def UNL_161 : CardDef :=
  { UNL_161.meta with
    abilities := [.activated [.killSelf, .exhaustSelf] .action
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-162
/--
**Enthralling Protector** — Unit · Order · Energy 2 · Might 2
Printings: UNL-162/219

> [Hunt] (When I conquer or hold, gain 1 XP.)
> Spend 2 XP: [Buff] me. (Give me a +1 :rb_might: buff if I don't have one.)
-/
def UNL_162.meta : CardDef :=
  { id := ⟨"UNL-162"⟩,
    name := "Enthralling Protector",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .hunt, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Enthralling Protector. -/
def UNL_162 : CardDef :=
  { UNL_162.meta with
    abilities := [.activated [.spendXP 2] .normal (.of [] (.prim (.buff .self))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-163
/--
**Mageseeker Investigator** — Unit · Order · Energy 4 · Might 4
Printings: UNL-163/219

> Opponents must pay :rb_rune_rainbow: for each unit beyond the first to move multiple units to
> my battlefield at the same time.
-/
def UNL_163.meta : CardDef :=
  { id := ⟨"UNL-163"⟩,
    name := "Mageseeker Investigator",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Mageseeker Investigator charges opponents one Power per extra Unit in a simultaneous arrival. -/
def UNL_163 : CardDef :=
  { UNL_163.meta with
    abilities := [.passive .always [.moveExtraUnitPowerHere 1]],
    status := .full }

-- BEGIN GENERATED UNL-164
/--
**Safety Inspector** — Unit · Order · Energy 5 + Power 1 · Might 3
Printings: UNL-164/219

> You may spend 3 XP as an additional cost to play me.
> When you play me, each player must kill one of their units. If you paid my additional cost,
> you don't kill a unit this way.
-/
def UNL_164.meta : CardDef :=
  { id := ⟨"UNL-164"⟩,
    name := "Safety Inspector",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Safety Inspector. -/
def UNL_164 : CardDef :=
  { UNL_164.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.ifThen .paid
        (.eachPlayer .eachOtherPlayer (.prim (.kill (Selector.one .you .anywhere [.ofType .unit]))))
        (.eachPlayer .eachPlayer (.prim (.kill (Selector.one .you .anywhere [.ofType .unit])))))) .unlimited],
    playExtra := some (.spendXP 3, false),
    status := .full }

-- BEGIN GENERATED UNL-165
/--
**Shadow's Call** — Spell · Order · Energy 2
Printings: UNL-165/219

> Choose a friendly unit without [Temporary]. Give it [Temporary]. Draw 2. (Kill it at the start
> of its controller's Beginning Phase, before scoring.)
-/
def UNL_165.meta : CardDef :=
  { id := ⟨"UNL-165"⟩,
    name := "Shadow's Call",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Shadow's Call. -/
def UNL_165 : CardDef :=
  { UNL_165.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere
        [.ofType .unit, .not (.hasKeyword .temporary)]]
      (.seqOf [.grant (.slot 0) (.keyword .it { keyword := .temporary }) .permanent,
        .prim (.draw .you (.const 2))])),
    status := .drafted }

-- BEGIN GENERATED UNL-166
/--
**Stalking Wolf** — Unit · Order · Energy 4 + Power 1 · Might 6
Printings: UNL-166/219

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> As an additional cost to play me, kill a Bird, Cat, Dog, or Poro you control. You may [Ambush]
> me to its battlefield, even if you don't have other units there.
-/
def UNL_166.meta : CardDef :=
  { id := ⟨"UNL-166"⟩,
    name := "Stalking Wolf",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Freljord"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order]⟩,
    might := some 6,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Stalking Wolf. -/
def UNL_166 : CardDef :=
  { UNL_166.meta with
    playExtra := some (.killPet, true),
    status := .full }

-- BEGIN GENERATED UNL-167
/--
**Starhound** — Unit · Order · Energy 5 + Power 1 · Might 6
Printings: UNL-167/219

> When you play me, return a Bird, Cat, Dog, or Poro from your trash to your hand.
-/
def UNL_167.meta : CardDef :=
  { id := ⟨"UNL-167"⟩,
    name := "Starhound",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Mount Targon"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Starhound. -/
def UNL_167 : CardDef :=
  { UNL_167.meta with
    abilities := [.triggered (.onSelf .play)
      { EffectDef.of [.targetOf .one .you .inTrash [petFilter]]
        (.prim (.returnToHand (.slot 0))) with recheckTargets := true }
      .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-168
/--
**Undying Loyalty** — Spell · Order · Energy 2 + Power 1
Printings: UNL-168/219

> This costs :rb_energy_2: less if you choose a Bird, Cat, Dog, or Poro.
> Play a unit with cost no more than :rb_energy_2: and no more than :rb_rune_rainbow: from your
> trash, ignoring its cost.
-/
def UNL_168.meta : CardDef :=
  { id := ⟨"UNL-168"⟩,
    name := "Undying Loyalty",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Undying Loyalty. -/
def UNL_168 : CardDef :=
  { UNL_168.meta with
    chosenEnergyDiscount := some (.ofList [petFilter], 2),
    spellEffect := some { EffectDef.of
      [.targetOf .one .you .inTrash [.ofType .unit, .cost .le (.const 2), .powerCost .le (.const 1)]]
      (.playCard (.slot 0) .ignoreBase) with recheckTargets := true },
    status := .full }

-- BEGIN GENERATED UNL-169
/--
**Ashe, Focused** — Unit · Order · Energy 5 + Power 1 · Might 4
Printings: UNL-169/219

> When you play me, choose an opponent. They reveal their hand. Choose a card revealed this way
> and banish it. When they hold, return it to their hand (even if I'm no longer on the board).
-/
def UNL_169.meta : CardDef :=
  { id := ⟨"UNL-169"⟩,
    name := "Ashe",
    subtitle := some "Focused",
    types := [.unit],
    tags := [⟨"Freljord"⟩, ⟨"Ashe"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 4,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Ashe. -/
def UNL_169 : CardDef :=
  { UNL_169.meta with
    abilities := [
      .triggered (.onSelf .play)
        (.of [] (.prim (.banishWith (Selector.one .enemy .inHand [])))) .unlimited,
      .triggered (.onSelf .opponentHolds)
        (.of [] (.prim (.moveAll .enemy .inBanishment (FilterList.ofList [.banishedWithMe])
          .inHand false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-170
/--
**Atakhan** — Unit · Order · Energy 10 + Power 3 · Might 7
Printings: UNL-170/219

> You may kill a friendly unit as an additional cost to play me. If you do, I cost :rb_energy_1:
> less for each Energy it costs and :rb_rune_order: less for each Power it costs.
> [Ganking] (I can move from battlefield to battlefield.)
> When I attack, the defender must kill one of their units here.
-/
def UNL_170.meta : CardDef :=
  { id := ⟨"UNL-170"⟩,
    name := "Atakhan",
    types := [.unit],
    tags := [⟨"Noxus"⟩, ⟨"Demon"⟩],
    domains := [.order],
    cost := some ⟨10, [.domain .order, .domain .order, .domain .order]⟩,
    might := some 7,
    keywords := [{ keyword := .ganking }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Atakhan. -/
def UNL_170 : CardDef :=
  { UNL_170.meta with
    abilities := [.triggered (.onSelf .attack)
      (.of [] (.eachPlayer .eachOpponent
        (.prim (.kill (Selector.one .friendly .here [.ofType .unit]))))) .unlimited],
    -- the additional cost: kill a friendly unit; the card costs as much less as that unit costs
    playExtra := some (.killUnit, false),
    paidCut := some .killed,
    status := .drafted }

-- BEGIN GENERATED UNL-171
/--
**Galio, Indefatigable** — Unit · Order · Energy 3 + Power 1 · Might 6
Printings: UNL-171/219

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> [Tank] (I must be assigned combat damage first.)
> I don't deal combat damage.
-/
def UNL_171.meta : CardDef :=
  { id := ⟨"UNL-171"⟩,
    name := "Galio",
    subtitle := some "Indefatigable",
    types := [.unit],
    tags := [⟨"Demacia"⟩, ⟨"Galio"⟩],
    domains := [.order],
    cost := some ⟨3, [.domain .order]⟩,
    might := some 6,
    keywords := [{ keyword := .deflect, arg := .amount 1 },
      { keyword := .tank }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Galio. -/
def UNL_171 : CardDef :=
  { UNL_171.meta with
    abilities := [.passive .always [.noCombatDamage]],
    status := .drafted }

-- BEGIN GENERATED UNL-172
/--
**LeBlanc, Fragmented** — Unit · Order · Energy 3 + Power 1 · Might 3
Printings: UNL-172/219, UNL-172a/219

> [Assault] (+1 :rb_might: while I'm an attacker.)
> [Deathknell][>] Draw 1. If it's your Beginning Phase, draw 2 instead. (When I die, get the
> effect.)
-/
def UNL_172.meta : CardDef :=
  { id := ⟨"UNL-172"⟩,
    name := "LeBlanc",
    subtitle := some "Fragmented",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Noxus"⟩, ⟨"LeBlanc"⟩],
    domains := [.order],
    cost := some ⟨3, [.domain .order]⟩,
    might := some 3,
    keywords := [{ keyword := .assault, arg := .amount 1 },
      { keyword := .deathknell }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- LeBlanc. -/
def UNL_172 : CardDef :=
  { UNL_172.meta with
    abilities := [.triggered (.onSelf .die)
      (.of [] (.ifThen (.and .yourTurn .beginningPhase) (.prim (.draw .you (.const 2)))
        (.prim (.draw .you (.const 1))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-173
/--
**Sacrifice** — Spell · Order · Energy 1
Printings: UNL-173/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> As an additional cost to play this, kill a friendly [Mighty] unit. (A unit is Mighty while it
> has 5+ :rb_might:.)
> Draw 2 and channel 1 rune exhausted.
-/
def UNL_173.meta : CardDef :=
  { id := ⟨"UNL-173"⟩,
    name := "Sacrifice",
    types := [.spell],
    domains := [.order],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Sacrifice. -/
def UNL_173 : CardDef :=
  { UNL_173.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .mighty]]
      (.seqOf [.prim (.draw .you (.const 2)),
        .prim (.channel .you (.const 0) (.const 1))])),
    -- the Mighty unit killed as the additional cost is the first thing the spell chooses
    playExtra := some (.killUnit, true),
    status := .drafted }

-- BEGIN GENERATED UNL-174
/--
**Shard of Undoing** — Gear · Order · Energy 6
Printings: UNL-174/219

> The first time a friendly unit dies during your Beginning Phase each turn, each opponent must
> kill one of their units.
-/
def UNL_174.meta : CardDef :=
  { id := ⟨"UNL-174"⟩,
    name := "Shard of Undoing",
    types := [.gear],
    domains := [.order],
    cost := some ⟨6, []⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Shard of Undoing. -/
def UNL_174 : CardDef :=
  { UNL_174.meta with
    abilities := [.triggered
      { event := .die, subject := Selector.all .friendly .anywhere [.ofType .unit],
        condition := .and .yourTurn .beginningPhase }
      (.of [] (.eachPlayer .eachOpponent
        (.prim (.kill (Selector.one .friendly .anywhere [.ofType .unit]))))) (.perTurn 1)],
    status := .drafted }

-- BEGIN GENERATED UNL-175
/--
**Tactical Retreat** — Spell · Order · Energy 2
Printings: UNL-175/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a friendly unit. The next time it would die this turn, heal it, exhaust it, and recall
> it instead. (Send it to base. This isn't a move.)
-/
def UNL_175.meta : CardDef :=
  { id := ⟨"UNL-175"⟩,
    name := "Tactical Retreat",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Tactical Retreat. -/
def UNL_175 : CardDef :=
  { UNL_175.meta with
    -- the next time the unit would die this turn, it is healed, exhausted and recalled instead
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
      (.prim (.markOn (.slot 0) .saveOnce))),
    status := .full }

-- BEGIN GENERATED UNL-176
/--
**Vi, Peacekeeper** — Unit · Order · Energy 5 + Power 1 · Might 5
Printings: UNL-176/219, UNL-176a/219

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> When I attack, [Stun] an enemy unit here. (It doesn't deal combat damage this turn.)
-/
def UNL_176.meta : CardDef :=
  { id := ⟨"UNL-176"⟩,
    name := "Vi",
    subtitle := some "Peacekeeper",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Vi"⟩, ⟨"Piltover"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 5,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Vi, Peacekeeper. -/
def UNL_176 : CardDef :=
  { UNL_176.meta with
    abilities := [.triggered (.onSelf .attack)
        (.of [.targetOf .one .enemy .here [.ofType .unit]]
        (.prim (.stun (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-177
/--
**Ivern, Friend to All** — Unit · Order · Energy 6 · Might 6
Printings: UNL-177/219, UNL-177a/219

> As you play me, choose Bird, Cat, Dog, or Poro. I gain that tag.
> When I conquer or hold, score 1 point if your units have all of the following tags among them
> — Bird, Cat, Dog, and Poro.
-/
def UNL_177.meta : CardDef :=
  { id := ⟨"UNL-177"⟩,
    name := "Ivern",
    subtitle := some "Friend to All",
    types := [.unit],
    tags := [⟨"Ivern"⟩, ⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨6, []⟩,
    might := some 6,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Ivern. -/
def UNL_177 : CardDef :=
  { UNL_177.meta with
    abilities := [
      .triggered (.onSelf .play)
        (.of [] (.eitherOf (EffectList.ofList
          [.prim (.gainTag .self "Bird"), .prim (.gainTag .self "Cat"),
           .prim (.gainTag .self "Dog"), .prim (.gainTag .self "Poro")]))) .unlimited,
      .triggered (.onSelf .conquer)
        (.of [] (.ifThen (.cmp .eq petTags (.const 4)) (.prim (.score .you (.const 1))) .nop))
        .unlimited,
      .triggered (.onSelf .hold)
        (.of [] (.ifThen (.cmp .eq petTags (.const 4)) (.prim (.score .you (.const 1))) .nop))
        .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-178
/--
**Poppy, Defender of the Meek** — Unit · Order · Energy 6 + Power 1 · Might 5
Printings: UNL-178/219, UNL-178a/219

> You may spend 3 XP as an additional cost to play me. If you do, I cost :rb_energy_3: less.
> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> [Tank] (I must be assigned combat damage first.)
-/
def UNL_178.meta : CardDef :=
  { id := ⟨"UNL-178"⟩,
    name := "Poppy",
    subtitle := some "Defender of the Meek",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Demacia"⟩, ⟨"Poppy"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order]⟩,
    might := some 5,
    keywords := [{ keyword := .ambush },
      { keyword := .tank }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Poppy. -/
def UNL_178 : CardDef :=
  { UNL_178.meta with
    -- the additional cost: spend 3 XP, and the card costs 3 Energy less
    playExtra := some (.spendXP 3, false),
    paidCut := some (.energy 3),
    status := .full }

-- BEGIN GENERATED UNL-179
/--
**Rift Herald** — Unit · Order · Energy 8 + Power 1 · Might 7
Printings: UNL-179/219, UNL-179a/219

> When I move to a battlefield, look at the top 3 cards of your Main Deck. You may reveal a unit
> from among them and draw it. Recycle the rest.
> [Deathknell][>] Play a unit from your hand to your base, ignoring its Energy cost. (When I
> die, get the effect. You must still pay its Power cost.)
-/
def UNL_179.meta : CardDef :=
  { id := ⟨"UNL-179"⟩,
    name := "Rift Herald",
    types := [.unit],
    tags := [⟨"The Void"⟩],
    domains := [.order],
    cost := some ⟨8, [.domain .order]⟩,
    might := some 7,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Rift Herald. -/
def UNL_179 : CardDef :=
  { UNL_179.meta with
    abilities := [
      .triggered { condition := .matches .self .onBattlefield, event := .move }
        (.of [] (lookDraw 3 [.ofType .unit])) .unlimited,
      .triggered (.onSelf .die)
        -- The player may decline to act on a specific card type in their private hand (CR 128.6).
        (.of [] (.may (.playCard (.one .friendly .inHand [.ofType .unit]) .ignoreEnergy
          (baseOnly := true)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-180
/--
**The Ruination** — Spell · Order · Energy 9 + Power 3
Printings: UNL-180/219

> Kill all units.
-/
def UNL_180.meta : CardDef :=
  { id := ⟨"UNL-180"⟩,
    name := "The Ruination",
    types := [.spell],
    domains := [.order],
    cost := some ⟨9, [.domain .order, .domain .order, .domain .order]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- The Ruination. -/
def UNL_180 : CardDef :=
  { UNL_180.meta with
    spellEffect := some (.of []
      (.prim (.kill (Selector.all .any .anywhere [.ofType .unit])))),
    status := .full }

-- BEGIN GENERATED UNL-181
/--
**Virtuoso** — Legend · Fury/Mind
Printings: UNL-181/219, UNL-226*/219, UNL-226/219

> When you play a spell, if you spent :rb_energy_4: or more, you may banish it. Then, if there
> are four spells banished with me, put each in its trash, channel 4 runes, and draw 1.
-/
def UNL_181.meta : CardDef :=
  { id := ⟨"UNL-181"⟩,
    name := "Virtuoso",
    types := [.legend],
    tags := [⟨"Jhin"⟩],
    domains := [.fury, .mind],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Virtuoso. -/
def UNL_181 : CardDef :=
  { UNL_181.meta with
    abilities := [.triggered
      { condition := .cmp .ge .eventAmount (.const 4),
        subject := Selector.all .you .anywhere [.ofType .spell], event := .play }
      (.of [] (.may (.seqOf [.prim (.banishWith (.slot 0)),
        .ifThen (.cmp .ge (.count (Selector.all .friendly .inBanishment
          [.ofType .spell, .banishedWithMe])) (.const 4))
          (.seqOf [.prim (.moveAll .friendly .inBanishment
              (FilterList.ofList [.ofType .spell, .banishedWithMe]) .inTrash false),
            .prim (.channel .you (.const 4) (.const 0)), .prim (.draw .you (.const 1))]) .nop]))
      ) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-182
/--
**Curtain Call** — Spell · Fury/Mind · Energy 4
Printings: UNL-182/219

> [Repeat] — :rb_energy_1: / :rb_rune_rainbow: / :rb_energy_1::rb_rune_rainbow: (You may pay
> each additional cost to repeat this spell's effect.)
> Choose one you haven't already chosen —Draw 1.Deal 2 to a unit at a battlefield.Deal 3 to a
> unit at a base.Give a unit at a battlefield -4 :rb_might: this turn.
-/
def UNL_182.meta : CardDef :=
  { id := ⟨"UNL-182"⟩,
    name := "Curtain Call",
    types := [.spell],
    tags := [⟨"Jhin"⟩],
    domains := [.fury, .mind],
    cost := some ⟨4, []⟩,
    keywords := [{ keyword := .repeat_ }],
    sets := [⟨"UNL"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Curtain Call. -/
def UNL_182 : CardDef :=
  { UNL_182.meta with
    keywords := [{ keyword := .repeat_, arg := .cost ⟨1, []⟩ },
      { keyword := .repeat_, arg := .cost ⟨0, [.any]⟩ },
      { keyword := .repeat_, arg := .cost ⟨1, [.any]⟩ }],
    spellEffect := some (.of [] (.eitherOf (EffectList.ofList
      [freshMode 0 (.prim (.draw .you (.const 1))),
       freshMode 1 (.prim (.deal (Selector.one .any .atBattlefield [.ofType .unit]) (.const 2))),
       freshMode 2 (.prim (.deal (Selector.one .any .atBase [.ofType .unit]) (.const 3))),
       freshMode 3 (.grant (Selector.one .any .atBattlefield [.ofType .unit])
         (.mightMinus .it (.const 4)) .thisTurn)]))),
    status := .drafted }

-- BEGIN GENERATED UNL-183
/--
**Pridestalker** — Legend · Fury/Body
Printings: UNL-183/219, UNL-227*/219, UNL-227/219

> When you play a unit, give a unit +1 :rb_might: this turn.
-/
def UNL_183.meta : CardDef :=
  { id := ⟨"UNL-183"⟩,
    name := "Pridestalker",
    types := [.legend],
    tags := [⟨"Rengar"⟩],
    domains := [.fury, .body],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Pridestalker. -/
def UNL_183 : CardDef :=
  { UNL_183.meta with
    abilities := [.triggered
      { event := .play, subject := Selector.all .you .anywhere [.ofType .unit] }
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 1)) .thisTurn)) .unlimited,
      .triggered
      { event := .playToken, subject := Selector.all .you .anywhere [.ofType .unit] }
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 1)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-184
/--
**Thrill of the Hunt** — Spell · Fury/Body · Energy 2 + Power 1
Printings: UNL-184/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Banish a friendly unit, then its owner plays it to any battlefield, ignoring its cost.
-/
def UNL_184.meta : CardDef :=
  { id := ⟨"UNL-184"⟩,
    name := "Thrill of the Hunt",
    types := [.spell],
    tags := [⟨"Rengar"⟩],
    domains := [.fury, .body],
    cost := some ⟨2, [.any]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Thrill of the Hunt. -/
def UNL_184 : CardDef :=
  { UNL_184.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
      (.prim (.banishReplay (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED UNL-185
/--
**Bloodharbor Ripper** — Legend · Fury/Chaos
Printings: UNL-185/219, UNL-228*/219, UNL-228/219

> :rb_energy_1:, :rb_exhaust:: Return a friendly unit at a battlefield to its owner's hand. Play
> a Gold gear token exhausted. (It has "[Reaction][>] Kill this, :rb_exhaust:: [Add]
> :rb_rune_rainbow:.")
-/
def UNL_185.meta : CardDef :=
  { id := ⟨"UNL-185"⟩,
    name := "Bloodharbor Ripper",
    types := [.legend],
    tags := [⟨"Pyke"⟩],
    domains := [.fury, .chaos],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Bloodharbor Ripper. -/
def UNL_185 : CardDef :=
  { UNL_185.meta with
    abilities := [.activated [.pay ⟨1, []⟩, .exhaustSelf] .normal
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .onBattlefield]]
        (.seqOf [.prim (.returnToHand (.slot 0)), .prim (.create "Gold" (.const 1) .atBase false)]))
      .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-186
/--
**Death from Below** — Spell · Fury/Chaos · Energy 4 + Power 1
Printings: UNL-186/219

> Kill a unit at a battlefield. Then, if it had 3 :rb_might: or less, you may play this from
> your trash for :rb_rune_rainbow:.
-/
def UNL_186.meta : CardDef :=
  { id := ⟨"UNL-186"⟩,
    name := "Death from Below",
    types := [.spell],
    tags := [⟨"Pyke"⟩],
    domains := [.fury, .chaos],
    cost := some ⟨4, [.any]⟩,
    sets := [⟨"UNL"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Death from Below. -/
def UNL_186 : CardDef :=
  { UNL_186.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.bind ⟨"m"⟩ (.mightOf (.slot 0))
        (.seqOf [.prim (.kill (.slot 0)),
          .ifThen (.cmp .le (.var ⟨"m"⟩) (.const 3))
            (.ifThen (.canPay ⟨0, [.any]⟩)
              (.may (.seqOf [.prim (.pay ⟨0, [.any]⟩),
                .prim (.kill (Selector.one .any .atBattlefield [.ofType .unit]))])) .nop)
            .nop]))),
    status := .drafted }

-- BEGIN GENERATED UNL-187
/--
**Piltover Enforcer** — Legend · Fury/Order
Printings: UNL-187/219, UNL-229*/219, UNL-229/219

> When you conquer, if you assigned 3 or more excess damage, you may exhaust me to ready a unit.
-/
def UNL_187.meta : CardDef :=
  { id := ⟨"UNL-187"⟩,
    name := "Piltover Enforcer",
    types := [.legend],
    tags := [⟨"Vi"⟩],
    domains := [.fury, .order],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Piltover Enforcer chooses the Unit and pays Exhaust during trigger finalization. -/
def UNL_187 : CardDef :=
  { UNL_187.meta with
    abilities := [.triggered
      { event := .youConquer, condition := .excessAtLeast 3, optional := true, cost := .exhaustSelf }
      { choices := [.targetOf .one .any .anywhere [.ofType .unit]]
        recheckTargets := true
        body := .prim (.ready (.slot 0)) } .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-188
/--
**Hextech Gauntlets** — Gear · Fury/Order · Energy 3 · Might 3
Printings: UNL-188/219

> [Equip] :rb_energy_3::rb_rune_rainbow:. This ability's Energy cost is reduced by the Might of
> the unit you choose. (Pay the cost: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I conquer, if you assigned 3 or more excess damage, draw 1.
-/
def UNL_188.meta : CardDef :=
  { id := ⟨"UNL-188"⟩,
    name := "Hextech Gauntlets",
    types := [.gear],
    supertypes := [.signature],
    tags := [⟨"Vi"⟩, ⟨"Equipment"⟩],
    domains := [.fury, .order],
    cost := some ⟨3, []⟩,
    might := some 3,
    mightBonus := some 3,
    keywords := [{ keyword := .equip, arg := .cost ⟨3, [.any]⟩ }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Hextech Gauntlets discounts the Equip cost by the chosen Unit's current Might. -/
def UNL_188 : CardDef :=
  { UNL_188.meta with
    equipEnergyDiscount := some (.mightOf (.slot 0)),
    grants := [.triggered { condition := .excessAtLeast 3, event := .conquer }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-189
/--
**Bashful Bloom** — Legend · Calm/Mind
Printings: UNL-189/219, UNL-230*/219, UNL-230/219

> :rb_energy_4:, :rb_exhaust:: Play a ready 3 :rb_might: Sprite unit token with [Temporary].
> This ability costs :rb_energy_1: less for each friendly unit with [Temporary].
-/
def UNL_189.meta : CardDef :=
  { id := ⟨"UNL-189"⟩,
    name := "Bashful Bloom",
    types := [.legend],
    tags := [⟨"Lillia"⟩],
    domains := [.calm, .mind],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Bashful Bloom counts friendly Temporary Units when declaring its activation. -/
def UNL_189 : CardDef :=
  { UNL_189.meta with
    abilities := [.activated [.pay ⟨4, []⟩, .exhaustSelf,
        .energyDiscount .always (.count (Selector.all .friendly .anywhere [.ofType .unit, .hasKeyword .temporary]))]
      .normal (.of [] (.prim (.playReadyUnitToken "Sprite"))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-190
/--
**Lilting Lullaby** — Spell · Calm/Mind · Energy 2 + Power 2
Printings: UNL-190/219

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Counter a spell. Its controller can't play spells this turn.
-/
def UNL_190.meta : CardDef :=
  { id := ⟨"UNL-190"⟩,
    name := "Lilting Lullaby",
    types := [.spell],
    tags := [⟨"Lillia"⟩],
    domains := [.calm, .mind],
    cost := some ⟨2, [.any, .any]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"UNL"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Lilting Lullaby. -/
def UNL_190 : CardDef :=
  { UNL_190.meta with
    spellEffect := some (.of [.targetOf .one .any .onChain [.ofType .spell]]
      (.seqOf [.prim (.counter (.slot 0)), .prim (.turnEffect .opponentsNoSpells)])),
    status := .drafted }

-- BEGIN GENERATED UNL-191
/--
**Wuju Master** — Legend · Calm/Body
Printings: UNL-191/219, UNL-231*/219, UNL-231/219

> [Level 6][>] Your units have +1 :rb_might:. (While you have 6+ XP, get the effect.)
> [Level 11][>] Your units enter ready.
-/
def UNL_191.meta : CardDef :=
  { id := ⟨"UNL-191"⟩,
    name := "Wuju Master",
    types := [.legend],
    tags := [⟨"Master Yi"⟩],
    domains := [.calm, .body],
    keywords := [{ keyword := .level, arg := .amount 6 },
      { keyword := .level, arg := .amount 11 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Wuju Master. -/
def UNL_191 : CardDef :=
  { UNL_191.meta with
    abilities := [
      .passive (.cmp .ge .xp (.const 6))
        [.mightPlus (Selector.all .you .anywhere [.ofType .unit]) (.const 1)],
      .passive (.cmp .ge .xp (.const 11))
        [.entersReady (Selector.all .you .anywhere [.ofType .unit])]],
    status := .drafted }

-- BEGIN GENERATED UNL-192
/--
**Alpha Strike** — Spell · Calm/Body · Energy 3 + Power 1
Printings: UNL-192/219

> [Action] (Play on your turn or in showdowns.)
> Choose a friendly unit. It deals damage equal to its Might split among enemy units at
> battlefields. Then for each unit this kills, do this: Gain 1 XP.
-/
def UNL_192.meta : CardDef :=
  { id := ⟨"UNL-192"⟩,
    name := "Alpha Strike",
    types := [.spell],
    supertypes := [.signature],
    tags := [⟨"Master Yi"⟩],
    domains := [.calm, .body],
    cost := some ⟨3, [.own]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Alpha Strike divides the chosen Unit's damage and gains XP for each actual kill. -/
def UNL_192 : CardDef :=
  { UNL_192.meta with
    spellEffect := some {
      choices := [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf (.splitByMight 0) .enemy .atBattlefield [.ofType .unit]]
      body := .splitUnitDamage (.slot 0) (.slotsFrom 1) 0
      recheckTargets := true },
    abilities := [.triggered (.onSelf .linkedDamageKill)
      (.of [] (.prim (.gainXP .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-193
/--
**Gloomist** — Legend · Calm/Chaos
Printings: UNL-193/219, UNL-232*/219, UNL-232/219

> When you or an ally hold, you may exhaust me to draw 1.
-/
def UNL_193.meta : CardDef :=
  { id := ⟨"UNL-193"⟩,
    name := "Gloomist",
    types := [.legend],
    tags := [⟨"Vex"⟩],
    domains := [.calm, .chaos],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Gloomist. -/
def UNL_193 : CardDef :=
  { UNL_193.meta with
    abilities := [.triggered
      { event := .hold, subject := Selector.all .friendly .anywhere [.ofType .battlefield],
        optional := true, cost := .exhaustSelf }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-194
/--
**Shadow** — Unit · Calm/Chaos · Energy 3 · Might 3
Printings: UNL-194/219

> If you play me to a battlefield, I enter ready.
> [Action][>] :rb_energy_1::rb_rune_rainbow:, :rb_exhaust:: [Stun] an enemy unit attacking here.
> (It doesn't deal combat damage this turn.)
-/
def UNL_194.meta : CardDef :=
  { id := ⟨"UNL-194"⟩,
    name := "Shadow",
    types := [.unit],
    supertypes := [.signature],
    tags := [⟨"Vex"⟩, ⟨"Shadow Isles"⟩],
    domains := [.calm, .chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Shadow. -/
def UNL_194 : CardDef :=
  { UNL_194.meta with
    abilities := [
      .passive .always [.entersReadyAtBattlefield],
      .activated [.pay ⟨1, [.any]⟩, .exhaustSelf] .action
        (.of [.targetOf .one .enemy .anywhere [.ofType .unit, .attacker, .at_ .self]]
          (.prim (.stun (.slot 0)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-195
/--
**Green Father** — Legend · Calm/Order
Printings: UNL-195/219, UNL-233*/219, UNL-233/219

> When you conquer or hold, you may exhaust me to replace that battlefield with a Brush
> battlefield token. (Bird, Cat, Dog, Poro, and Ivern units have +1 :rb_might: in Brush. It can
> be swapped back when scored.)
-/
def UNL_195.meta : CardDef :=
  { id := ⟨"UNL-195"⟩,
    name := "Green Father",
    types := [.legend],
    tags := [⟨"Ivern"⟩],
    domains := [.calm, .order],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Green Father. -/
def UNL_195 : CardDef :=
  { UNL_195.meta with
    abilities := [
      .triggered (.onSelf .youConquer)
        (.of [] (.ifThen .legendReady (.may (.seqOf [.prim (.exhaust .self),
          .prim (.replaceBattlefield (Selector.one .any .anywhere
            [.ofType .battlefield, .scoredByMine]) "Brush")])) .nop)) .unlimited,
      .triggered (.onSelf .youHold)
        (.of [] (.ifThen .legendReady (.may (.seqOf [.prim (.exhaust .self),
          .prim (.replaceBattlefield (Selector.one .any .anywhere
            [.ofType .battlefield, .scoredByMine]) "Brush")])) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-196
/--
**Daisy!** — Unit · Calm/Order · Energy 9 + Power 2 · Might 8
Printings: UNL-196/219

> I enter ready.
> Reduce my cost by :rb_energy_1: for each of the following tags among your units — Bird, Cat,
> Dog, and Poro.
> When I attack while your units have all 4 tags, [Stun] an enemy unit here. (It doesn't deal
> combat damage this turn.)
-/
def UNL_196.meta : CardDef :=
  { id := ⟨"UNL-196"⟩,
    name := "Daisy!",
    types := [.unit],
    tags := [⟨"Ivern"⟩, ⟨"Ionia"⟩],
    domains := [.calm, .order],
    cost := some ⟨9, [.any, .any]⟩,
    might := some 8,
    sets := [⟨"UNL"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Daisy!. -/
def UNL_196 : CardDef :=
  { UNL_196.meta with
    abilities := [
      .passive .always [.entersReady .self, .costMinus .self petTags],
      .triggered (.onSelf .attack)
        (.of [] (.ifThen (.cmp .eq petTags (.const 4))
          (.prim (.stun (Selector.one .enemy .here [.ofType .unit]))) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-197
/--
**Scorn of the Moon** — Legend · Mind/Chaos
Printings: UNL-197/219, UNL-234*/219, UNL-234/219

> [Reaction][>] :rb_exhaust:: [Add] :rb_energy_1:. Spend this Energy only during showdowns.
> (Abilities that add resources can't be reacted to.)
-/
def UNL_197.meta : CardDef :=
  { id := ⟨"UNL-197"⟩,
    name := "Scorn of the Moon",
    types := [.legend],
    tags := [⟨"Diana"⟩],
    domains := [.mind, .chaos],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Scorn of the Moon. -/
def UNL_197 : CardDef :=
  { UNL_197.meta with
    abilities := [.activated [.exhaustSelf] .reaction
      (.of [] (.ifThen .showdownNow (.prim (.addEnergy .you (.const 1) none)) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-198
/--
**Moonfall** — Spell · Mind/Chaos · Energy 3 + Power 1
Printings: UNL-198/219

> [Action] (Play on your turn or in showdowns.)
> Choose a battlefield where you have units. You may move up to one enemy unit to that
> battlefield. Then give enemy units there -2 :rb_might: this turn.
-/
def UNL_198.meta : CardDef :=
  { id := ⟨"UNL-198"⟩,
    name := "Moonfall",
    types := [.spell],
    tags := [⟨"Diana"⟩],
    domains := [.mind, .chaos],
    cost := some ⟨3, [.any]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"UNL"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Moonfall. -/
def UNL_198 : CardDef :=
  let toMove := Selector.all .enemy .anywhere
    [.ofType .unit, .sameAs (.slot 1), .not (.at_ (.slot 0))]
  { UNL_198.meta with
    spellEffect := some (.of
      [.targetOf .one .any .anywhere [.ofType .battlefield, .myUnitsHere],
        .targetOf (.upTo 1) .enemy .anywhere [.ofType .unit, .not (.at_ (.slot 0))]]
      (.seqOf [.ifThen (.exists toMove) (.may (.prim (.move toMove (.at_ (.slot 0))))) .nop,
        .grant (Selector.all .enemy .anywhere [.ofType .unit, .at_ (.slot 0)])
          (.mightMinus .it (.const 2)) .thisTurn])),
    status := .drafted }

-- BEGIN GENERATED UNL-199
/--
**Deceiver** — Legend · Mind/Order
Printings: UNL-199/219, UNL-235*/219, UNL-235/219

> When you conquer or hold, you may discard 1 and exhaust me to play a ready Reflection unit
> token there. Then do this: It becomes a copy of another unit there. Give it [Temporary].
-/
def UNL_199.meta : CardDef :=
  { id := ⟨"UNL-199"⟩,
    name := "Deceiver",
    types := [.legend],
    tags := [⟨"LeBlanc"⟩],
    domains := [.mind, .order],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Deceiver. -/
def UNL_199 : CardDef :=
  let offer (event : TriggerEvent) : Ability :=
    .triggered { event, optional := true, cost := .discardAndExhaust 1 }
      (.of [] (.playUnitTokensThen "Reflection" 1 .here true 2)) .unlimited
  { UNL_199.meta with
    abilities := [
      offer .youConquer, offer .youHold,
      .triggered (.onSelf (.linkedUnitTokens false))
        (.of [.targetOf .one .any .anywhere
          [.ofType .unit, .atEventBattlefield none, .not (.inTriggerGroup [])]]
          (.seqOf [.prim (.becomeCopy .eventObjects (.slot 0)),
            .grant .eventObjects (.keyword .it { keyword := .temporary }) .permanent])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-200
/--
**Mirror Image** — Spell · Mind/Order · Energy 3 + Power 2
Printings: UNL-200/219

> Choose a unit. Play a ready Reflection unit token to your base. Then do this: It becomes a
> copy of that unit. Give it [Temporary]. (Kill it at the start of its controller's Beginning
> Phase, before scoring.)
-/
def UNL_200.meta : CardDef :=
  { id := ⟨"UNL-200"⟩,
    name := "Mirror Image",
    types := [.spell],
    supertypes := [.signature],
    tags := [⟨"LeBlanc"⟩],
    domains := [.mind, .order],
    cost := some ⟨3, [.own, .own]⟩,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Mirror Image. -/
def UNL_200 : CardDef :=
  { UNL_200.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.playUnitTokensThen "Reflection" 1 .atBase true 0 (some (.slot 0)))),
    abilities := [.triggered (.onSelf (.linkedUnitTokens true))
      (.of [] (.seqOf [.prim (.becomeCopy .eventObjects (.slot 0)),
        .grant .eventObjects (.keyword .it { keyword := .temporary }) .permanent])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-201
/--
**Voidreaver** — Legend · Body/Chaos
Printings: UNL-201/219, UNL-236*/219, UNL-236/219

> When you win a combat, gain 1 XP.
> Spend 1 XP, :rb_exhaust:: [Buff] a unit.
> Spend 2 XP, :rb_exhaust:: Move an exhausted friendly unit from a battlefield to its base.
-/
def UNL_201.meta : CardDef :=
  { id := ⟨"UNL-201"⟩,
    name := "Voidreaver",
    types := [.legend],
    tags := [⟨"Kha'Zix"⟩],
    domains := [.body, .chaos],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Voidreaver. -/
def UNL_201 : CardDef :=
  { UNL_201.meta with
    abilities := [
      .triggered (.onSelf .winCombat) (.of [] (.prim (.gainXP .you (.const 1)))) .unlimited,
      .activated [.spendXP 1, .exhaustSelf] .normal
        { choices := [.targetOf .one .any .anywhere [.ofType .unit]]
          recheckTargets := true
          body := .prim (.buff (.slot 0)) } .unlimited,
      .activated [.spendXP 2, .exhaustSelf] .normal
        { choices := [.targetOf .one .friendly .atBattlefield [.ofType .unit, .exhausted]]
          recheckTargets := true
          body := .prim (.move (.slot 0) .base) } .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-202
/--
**Void Assault** — Spell · Body/Chaos · Energy 2 + Power 1
Printings: UNL-202/219

> Move a friendly unit, then move an enemy unit. (If they both move to a battlefield you don't
> control, you're the attacker.)
-/
def UNL_202.meta : CardDef :=
  { id := ⟨"UNL-202"⟩,
    name := "Void Assault",
    types := [.spell],
    tags := [⟨"Kha'Zix"⟩],
    domains := [.body, .chaos],
    cost := some ⟨2, [.any]⟩,
    sets := [⟨"UNL"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Void Assault. -/
def UNL_202 : CardDef :=
  { UNL_202.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .enemy .anywhere [.ofType .unit]]
      (.seqOf [.eitherOf (.cons (.prim (.move (.slot 0) .base))
            (.cons (.prim (.move (.slot 0) (.at_ (Selector.one .any .anywhere [.ofType .battlefield]))))
              .nil)),
        .eitherOf (.cons (.prim (.move (.slot 1) .base))
            (.cons (.prim (.move (.slot 1) (.at_ (Selector.one .any .anywhere [.ofType .battlefield]))))
              .nil))])),
    status := .drafted }

-- BEGIN GENERATED UNL-203
/--
**Keeper of the Hammer** — Legend · Body/Order
Printings: UNL-203/219, UNL-237*/219, UNL-237/219

> When you hold, gain 1 XP.
> Spend 3 XP, :rb_exhaust:: Draw 1.
-/
def UNL_203.meta : CardDef :=
  { id := ⟨"UNL-203"⟩,
    name := "Keeper of the Hammer",
    types := [.legend],
    tags := [⟨"Poppy"⟩],
    domains := [.body, .order],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Keeper of the Hammer. -/
def UNL_203 : CardDef :=
  { UNL_203.meta with
    abilities := [.triggered (.onSelf .youHold) (.of [] (.prim (.gainXP .you (.const 1)))) .unlimited,
      .activated [.spendXP 3, .exhaustSelf] .normal
        (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-204
/--
**Keeper's Verdict** — Spell · Body/Order · Energy 2 + Power 2
Printings: UNL-204/219

> [Action] (Play on your turn or in showdowns.)
> Choose an enemy unit at a battlefield. Its owner places it on the top or bottom of their Main
> Deck.
-/
def UNL_204.meta : CardDef :=
  { id := ⟨"UNL-204"⟩,
    name := "Keeper's Verdict",
    types := [.spell],
    tags := [⟨"Poppy"⟩],
    domains := [.body, .order],
    cost := some ⟨2, [.any, .any]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"UNL"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Keeper's Verdict. -/
def UNL_204 : CardDef :=
  { UNL_204.meta with
    spellEffect := some (.of [.targetOf .one .enemy .anywhere [.ofType .unit, .onBattlefield]]
      (.eachPlayer (.controllerOf 0)
        (.eitherOf (EffectList.ofList [.prim (.topdeck (.slot 0)), .prim (.recycle (.slot 0))])))),
    status := .drafted }

-- BEGIN GENERATED UNL-205
/--
**Abandoned Hall** — Battlefield · Colorless
Printings: UNL-205/219

> When a player plays a spell, they may give a unit they control here +1 :rb_might: this turn.
-/
def UNL_205.meta : CardDef :=
  { id := ⟨"UNL-205"⟩,
    name := "Abandoned Hall",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Abandoned Hall. -/
def UNL_205 : CardDef :=
  { UNL_205.meta with
    abilities := [.triggered
      { subject := Selector.all .any .anywhere [.ofType .spell], event := .play }
      (.of [] (.may (.grant (Selector.one .friendly .anywhere [.ofType .unit, .at_ .self])
        (.mightPlus .it (.const 1)) .thisTurn))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-206
/--
**Altar of Blood** — Battlefield · Colorless
Printings: UNL-206/219

> If a unit here would die during combat, its controller may pay
> :rb_rune_rainbow::rb_rune_rainbow::rb_rune_rainbow: to heal it, exhaust it, and recall it
> instead.
-/
def UNL_206.meta : CardDef :=
  { id := ⟨"UNL-206"⟩,
    name := "Altar of Blood",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Altar of Blood. -/
def UNL_206 : CardDef :=
  { UNL_206.meta with
    abilities := [.triggered
      { condition := .and .inCombat (.canPay ⟨0, [.any, .any, .any]⟩),
        subject := Selector.all .any .anywhere [.ofType .unit, .at_ .self], event := .die }
      (.of [] (.may (.seqOf [.prim (.pay ⟨0, [.any, .any, .any]⟩),
        .prim (.play (Selector.one .friendly .inTrash [.sameAs (.slot 0)]))]))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-207
/--
**Amateur Recital** — Battlefield · Colorless
Printings: UNL-207/219

> When you hold here, you may move a unit at a battlefield to its base.
-/
def UNL_207.meta : CardDef :=
  { id := ⟨"UNL-207"⟩,
    name := "Amateur Recital",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Amateur Recital chooses a Unit at a Battlefield when the Hold ability is finalized. -/
def UNL_207 : CardDef :=
  { UNL_207.meta with
    abilities := [.triggered { event := .youHold, optional := true }
      { choices := [.targetOf .one .any .anywhere [.ofType .unit, .onBattlefield]]
        body := .prim (.move (.slot 0) .base)
        recheckTargets := true } .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-208
/--
**Black Flame Altar** — Battlefield · Colorless
Printings: UNL-208/219

> Units here with [Temporary] have [Shield]. (+1 :rb_might: while they're defenders.)
-/
def UNL_208.meta : CardDef :=
  { id := ⟨"UNL-208"⟩,
    name := "Black Flame Altar",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Black Flame Altar. -/
def UNL_208 : CardDef :=
  { UNL_208.meta with
    abilities := [.passive .always
      [.keyword (Selector.all .any .here [.ofType .unit, .hasKeyword .temporary])
        { keyword := .shield }]],
    status := .drafted }

-- BEGIN GENERATED UNL-209
/--
**Dusk Rose Lab** — Battlefield · Colorless
Printings: UNL-209/219

> At the start of your Beginning Phase, you may kill a unit you control here to draw 1. (This
> happens before scoring.)
-/
def UNL_209.meta : CardDef :=
  { id := ⟨"UNL-209"⟩,
    name := "Dusk Rose Lab",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Dusk Rose Lab. -/
def UNL_209 : CardDef :=
  { UNL_209.meta with
    abilities := [.triggered
      { event := .at_ .beginning, condition := .iControlHere, optional := true,
        cost := .killControlled 1 (.ofList [.ofType .unit, .at_ .self]) }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-210
/--
**Forbidding Waste** — Battlefield · Colorless
Printings: UNL-210/219

> While a unit here is defending alone, it has -2 :rb_might:. (It's alone if there are no other
> friendly units here.)
-/
def UNL_210.meta : CardDef :=
  { id := ⟨"UNL-210"⟩,
    name := "Forbidding Waste",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Forbidding Waste. -/
def UNL_210 : CardDef :=
  { UNL_210.meta with
    abilities := [.passive .always
      [.mightMinus (Selector.all .any .here [.ofType .unit, .defender, .alone]) (.const 2)]],
    status := .full }

-- BEGIN GENERATED UNL-211
/--
**Forgotten Library** — Battlefield · Colorless
Printings: UNL-211/219

> While you control this battlefield, when you play a spell, if you spent :rb_energy_4: or more,
> [Predict]. (Look at the top card of your Main Deck. You may recycle it.)
-/
def UNL_211.meta : CardDef :=
  { id := ⟨"UNL-211"⟩,
    name := "Forgotten Library",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Forgotten Library. -/
def UNL_211 : CardDef :=
  { UNL_211.meta with
    abilities := [.triggered
      { condition := .and .iControlHere (.cmp .ge .eventAmount (.const 4)),
        subject := Selector.all .you .anywhere [.ofType .spell], event := .play }
      (.of [] (.prim (.predict (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-212
/--
**Frozen Fortress** — Battlefield · Colorless
Printings: UNL-212/219

> At the start of each player's Beginning Phase, deal 1 to each unit here. (This happens before
> scoring.)
-/
def UNL_212.meta : CardDef :=
  { id := ⟨"UNL-212"⟩,
    name := "Frozen Fortress",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Frozen Fortress. -/
def UNL_212 : CardDef :=
  { UNL_212.meta with
    abilities := [.triggered { event := .battlefieldBeginning }
      (.of [] (.prim (.deal (Selector.all .any .here [.ofType .unit]) (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-213
/--
**Gardens of Becoming** — Battlefield · Colorless
Printings: UNL-213/219

> Units here have ":rb_exhaust:: Gain 1 XP."
-/
def UNL_213.meta : CardDef :=
  { id := ⟨"UNL-213"⟩,
    name := "Gardens of Becoming",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Gardens of Becoming. -/
def UNL_213 : CardDef :=
  { UNL_213.meta with
    abilities := [.activated [] .normal
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .ready, .at_ .self]]
        (.seqOf [.prim (.exhaust (.slot 0)), .prim (.gainXP .you (.const 1))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-214
/--
**Ripper's Bay** — Battlefield · Colorless
Printings: UNL-214/219

> When a unit here is returned to a player's hand, that player may pay :rb_energy_1: to channel
> 1 rune exhausted.
-/
def UNL_214.meta : CardDef :=
  { id := ⟨"UNL-214"⟩,
    name := "Ripper's Bay",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Ripper's Bay. -/
def UNL_214 : CardDef :=
  { UNL_214.meta with
    abilities := [.triggered
      { subject := Selector.all .any .anywhere [.movedFromHere, .inHandZone], event := .leave }
      (.of [] (.ifThen (.canPay ⟨1, []⟩)
        (.may (.seqOf [.prim (.pay ⟨1, []⟩), .prim (.channel .you (.const 0) (.const 1))])) .nop))
      .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-215
/--
**Star Spring** — Battlefield · Colorless
Printings: UNL-215/219

> The first time a player plays a non-token unit here each turn, they may move another unit they
> control here to its base.
-/
def UNL_215.meta : CardDef :=
  { id := ⟨"UNL-215"⟩,
    name := "Star Spring",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Star Spring. -/
def UNL_215 : CardDef :=
  { UNL_215.meta with
    abilities := [.triggered
      { subject := Selector.all .any .anywhere [.ofType .unit, .at_ .self, .not .token],
        event := .play }
      (.of [] (.may (.prim (.move (Selector.one .friendly .anywhere
        [.ofType .unit, .at_ .self, .not (.sameAs (.slot 0))]) .base)))) (.perTurn 1)],
    status := .drafted }

-- BEGIN GENERATED UNL-216
/--
**The Academy** — Battlefield · Colorless
Printings: UNL-216/219

> When you hold here, give your next spell this turn [Repeat] equal to its base cost. (You may
> pay the additional cost to repeat the spell's effect.)
-/
def UNL_216.meta : CardDef :=
  { id := ⟨"UNL-216"⟩,
    name := "The Academy",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- The Academy. -/
def UNL_216 : CardDef :=
  { UNL_216.meta with
    abilities := [.triggered (.onSelf .youHold)
      (.of [] (.prim (.turnEffect .nextSpellRepeat))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-217
/--
**Trapping Grounds** — Battlefield · Colorless
Printings: UNL-217/219

> When you conquer here, if you assigned 3 or more excess damage, play a 1 :rb_might: Bird unit
> token with [Deflect].
-/
def UNL_217.meta : CardDef :=
  { id := ⟨"UNL-217"⟩,
    name := "Trapping Grounds",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Trapping Grounds. -/
def UNL_217 : CardDef :=
  { UNL_217.meta with
    abilities := [.triggered { event := .youConquer, condition := .excessAtLeast 3 }
      (.of [] (.prim (.playUnitToken "Bird"))) .unlimited],
    status := .full }

-- BEGIN GENERATED UNL-218
/--
**Valley of Idols** — Battlefield · Colorless
Printings: UNL-218/219

> When a player plays a unit here, they may pay :rb_energy_1: to [Buff] it. (Give it a +1
> :rb_might: buff if it doesn't have one.)
-/
def UNL_218.meta : CardDef :=
  { id := ⟨"UNL-218"⟩,
    name := "Valley of Idols",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Valley of Idols. -/
def UNL_218 : CardDef :=
  { UNL_218.meta with
    abilities := [.triggered
      { subject := Selector.all .any .anywhere [.ofType .unit, .at_ .self], event := .play }
      (.of [] (.ifThen (.canPay ⟨1, []⟩)
        (.may (.seqOf [.prim (.pay ⟨1, []⟩), .prim (.buff (.slot 0))])) .nop)) .unlimited,
      .triggered
      { subject := Selector.all .any .anywhere [.ofType .unit, .at_ .self], event := .playToken }
      (.of [] (.ifThen (.canPay ⟨1, []⟩)
        (.may (.seqOf [.prim (.pay ⟨1, []⟩), .prim (.buff (.slot 0))])) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-219
/--
**Vaults of Helia** — Battlefield · Colorless
Printings: UNL-219/219

> When you hold here, your non-token units cost :rb_energy_1: more to play this turn.
-/
def UNL_219.meta : CardDef :=
  { id := ⟨"UNL-219"⟩,
    name := "Vaults of Helia",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Vaults of Helia. -/
def UNL_219 : CardDef :=
  { UNL_219.meta with
    abilities := [.triggered (.onSelf .youHold)
      (.of [] (.prim (.turnEffect (.unitsCostMore 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-T01
/--
**Baron Pit** — Battlefield · Colorless
Printings: UNL-T01

> (You can't start the game with a token battlefield.)
> Units can move here from anywhere.
-/
def UNL_T01.meta : CardDef :=
  { id := ⟨"UNL-T01"⟩,
    name := "Baron Pit",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Baron Pit. -/
def UNL_T01 : CardDef :=
  { UNL_T01.meta with
    abilities := [.passive .always [.movesHereFromAnywhere]],
    status := .drafted }

-- BEGIN GENERATED UNL-T02
/--
**Bird** — Unit · Colorless · Might 1
Printings: UNL-T02

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
-/
def UNL_T02.meta : CardDef :=
  { id := ⟨"UNL-T02"⟩,
    name := "Bird",
    types := [.unit],
    tags := [⟨"Bird"⟩],
    might := some 1,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Bird. -/
def UNL_T02 : CardDef :=
  { UNL_T02.meta with
    status := .full }

-- BEGIN GENERATED UNL-T03
/--
**Brush** — Battlefield · Colorless
Printings: UNL-T03

> Bird, Cat, Dog, Poro, and Ivern units here have +1 :rb_might:.
> When you score here, you may replace this with the battlefield it replaced.
-/
def UNL_T03.meta : CardDef :=
  { id := ⟨"UNL-T03"⟩,
    name := "Brush",
    types := [.battlefield],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Brush. -/
def UNL_T03 : CardDef :=
  { UNL_T03.meta with
    abilities := [
      .passive .always [.mightPlus (Selector.all .any .here
        [.ofType .unit, .either petFilter (.tag ⟨"Ivern"⟩)]) (.const 1)],
      .triggered (.onSelf .youConquer) (.of [] (.may (.prim (.restoreBattlefield .self)))) .unlimited,
      .triggered (.onSelf .youHold) (.of [] (.may (.prim (.restoreBattlefield .self)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED UNL-T04
/--
**Buff** — Token · Colorless · Might 1
Printings: UNL-T04

> A unit may have no more than one buff at a time.
-/
def UNL_T04.meta : CardDef :=
  { id := ⟨"UNL-T04"⟩,
    name := "Buff",
    types := [],
    might := some 1,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Buff. -/
def UNL_T04 : CardDef :=
  { UNL_T04.meta with
    status := .drafted }

-- BEGIN GENERATED UNL-T06
/--
**Reflection** — Unit · Colorless · Might 0
Printings: UNL-T06

> (I become a copy of something when played. I don't get that card's play effects.)
-/
def UNL_T06.meta : CardDef :=
  { id := ⟨"UNL-T06"⟩,
    name := "Reflection",
    types := [.unit],
    might := some 0,
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- Reflection. -/
def UNL_T06 : CardDef :=
  { UNL_T06.meta with
    status := .full }

-- BEGIN GENERATED UNL-T08
/--
**XP Tracker** — Token · Colorless
Printings: UNL-T08

> Track gained XP here.
> Some cards get bonuses based on your [Level].
> Some cards can spend XP for powerful effects.
-/
def UNL_T08.meta : CardDef :=
  { id := ⟨"UNL-T08"⟩,
    name := "XP Tracker",
    types := [],
    sets := [⟨"UNL"⟩] }
-- END GENERATED

/-- XP Tracker. -/
def UNL_T08 : CardDef :=
  { UNL_T08.meta with
    status := .drafted }

-- BEGIN GENERATED LIST
/-- The cards first printed in Unleashed. -/
def cards : List CardDef :=
  [UNL_001,
    UNL_002,
    UNL_003,
    UNL_004,
    UNL_005,
    UNL_006,
    UNL_007,
    UNL_008,
    UNL_009,
    UNL_010,
    UNL_011,
    UNL_012,
    UNL_013,
    UNL_014,
    UNL_015,
    UNL_016,
    UNL_017,
    UNL_018,
    UNL_019,
    UNL_020,
    UNL_021,
    UNL_022,
    UNL_023,
    UNL_024,
    UNL_025,
    UNL_026,
    UNL_027,
    UNL_028,
    UNL_029,
    UNL_030,
    UNL_031,
    UNL_032,
    UNL_033,
    UNL_034,
    UNL_035,
    UNL_036,
    UNL_037,
    UNL_038,
    UNL_039,
    UNL_040,
    UNL_041,
    UNL_042,
    UNL_043,
    UNL_044,
    UNL_045,
    UNL_046,
    UNL_047,
    UNL_048,
    UNL_049,
    UNL_050,
    UNL_051,
    UNL_052,
    UNL_053,
    UNL_054,
    UNL_055,
    UNL_056,
    UNL_057,
    UNL_058,
    UNL_059,
    UNL_060,
    UNL_061,
    UNL_062,
    UNL_063,
    UNL_064,
    UNL_065,
    UNL_066,
    UNL_067,
    UNL_068,
    UNL_069,
    UNL_070,
    UNL_071,
    UNL_072,
    UNL_073,
    UNL_074,
    UNL_075,
    UNL_076,
    UNL_077,
    UNL_078,
    UNL_079,
    UNL_080,
    UNL_081,
    UNL_082,
    UNL_083,
    UNL_084,
    UNL_085,
    UNL_086,
    UNL_087,
    UNL_088,
    UNL_089,
    UNL_090,
    UNL_091,
    UNL_092,
    UNL_093,
    UNL_094,
    UNL_095,
    UNL_096,
    UNL_097,
    UNL_098,
    UNL_099,
    UNL_100,
    UNL_101,
    UNL_102,
    UNL_103,
    UNL_104,
    UNL_105,
    UNL_106,
    UNL_107,
    UNL_108,
    UNL_109,
    UNL_110,
    UNL_111,
    UNL_112,
    UNL_113,
    UNL_114,
    UNL_115,
    UNL_116,
    UNL_117,
    UNL_118,
    UNL_119,
    UNL_120,
    UNL_121,
    UNL_122,
    UNL_123,
    UNL_124,
    UNL_125,
    UNL_126,
    UNL_127,
    UNL_128,
    UNL_129,
    UNL_130,
    UNL_131,
    UNL_132,
    UNL_133,
    UNL_134,
    UNL_135,
    UNL_136,
    UNL_137,
    UNL_138,
    UNL_139,
    UNL_140,
    UNL_141,
    UNL_142,
    UNL_143,
    UNL_144,
    UNL_145,
    UNL_146,
    UNL_147,
    UNL_148,
    UNL_149,
    UNL_150,
    UNL_151,
    UNL_152,
    UNL_153,
    UNL_154,
    UNL_155,
    UNL_156,
    UNL_157,
    UNL_158,
    UNL_159,
    UNL_160,
    UNL_161,
    UNL_162,
    UNL_163,
    UNL_164,
    UNL_165,
    UNL_166,
    UNL_167,
    UNL_168,
    UNL_169,
    UNL_170,
    UNL_171,
    UNL_172,
    UNL_173,
    UNL_174,
    UNL_175,
    UNL_176,
    UNL_177,
    UNL_178,
    UNL_179,
    UNL_180,
    UNL_181,
    UNL_182,
    UNL_183,
    UNL_184,
    UNL_185,
    UNL_186,
    UNL_187,
    UNL_188,
    UNL_189,
    UNL_190,
    UNL_191,
    UNL_192,
    UNL_193,
    UNL_194,
    UNL_195,
    UNL_196,
    UNL_197,
    UNL_198,
    UNL_199,
    UNL_200,
    UNL_201,
    UNL_202,
    UNL_203,
    UNL_204,
    UNL_205,
    UNL_206,
    UNL_207,
    UNL_208,
    UNL_209,
    UNL_210,
    UNL_211,
    UNL_212,
    UNL_213,
    UNL_214,
    UNL_215,
    UNL_216,
    UNL_217,
    UNL_218,
    UNL_219,
    UNL_T01,
    UNL_T02,
    UNL_T03,
    UNL_T04,
    UNL_T06,
    UNL_T08]
-- END GENERATED LIST

end RiftboundCards.Unleashed

end
