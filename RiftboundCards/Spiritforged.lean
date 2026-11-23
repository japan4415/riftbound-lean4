module

public import Riftbound.Card.CardDef

/-!
# Spiritforged (SFD)

The cards first printed in Spiritforged. Each card has a generated block (the official text and
the metadata) and, right after it, the part written by hand (the effect and the
implementation status). `scripts/gen_lean.py` rewrites the generated blocks only
(docs/card-data.md §4.1).
-/

@[expose] public section

namespace RiftboundCards.Spiritforged

open Riftbound

-- BEGIN GENERATED SFD-001
/--
**Against the Odds** — Spell · Fury · Energy 2
Printings: SFD-001/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a friendly unit at a battlefield +2 :rb_might: this turn for each enemy unit there.
-/
def SFD_001.meta : CardDef :=
  { id := ⟨"SFD-001"⟩,
    name := "Against the Odds",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Against the Odds. -/
def SFD_001 : CardDef :=
  { SFD_001.meta with

    spellEffect := some (.of [.targetOf .one .friendly .atBattlefield [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it (.mul (.const 2)
        (.count (Selector.all .enemy .atBattlefield [.ofType .unit, .at_ (.slot 0)]))))
        .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED SFD-002
/--
**Armed Assailant** — Unit · Fury · Energy 6 + Power 1 · Might 6
Printings: SFD-002/221

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
-/
def SFD_002.meta : CardDef :=
  { id := ⟨"SFD-002"⟩,
    name := "Armed Assailant",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨6, [.domain .fury]⟩,
    might := some 6,
    keywords := [{ keyword := .accelerate },
      { keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Armed Assailant. -/
def SFD_002 : CardDef :=
  { SFD_002.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-003
/--
**Blood Rush** — Spell · Fury · Energy 1
Printings: SFD-003/221

> [Action] (Play on your turn or in showdowns.)
> [Repeat] :rb_energy_1: (You may pay the additional cost to repeat this spell's effect.)
> Give a unit [Assault 2]. (+2 :rb_might: while it's an attacker.)
-/
def SFD_003.meta : CardDef :=
  { id := ⟨"SFD-003"⟩,
    name := "Blood Rush",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .action },
      { keyword := .repeat_, arg := .cost ⟨1, []⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Blood Rush. -/
def SFD_003 : CardDef :=
  { SFD_003.meta with

    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.keyword .it ⟨.assault, .amount 2⟩) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED SFD-004
/--
**Bushwhack** — Spell · Fury · Energy 2 + Power 1
Printings: SFD-004/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> Friendly units enter ready this turn. Play a Gold gear token exhausted.
-/
def SFD_004.meta : CardDef :=
  { id := ⟨"SFD-004"⟩,
    name := "Bushwhack",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Bushwhack. -/
def SFD_004 : CardDef :=
  { SFD_004.meta with

    spellEffect := some (.of [] (.seqOf [.prim (.turnEffect .unitsReady),
      .prim (.create "Gold" (.const 1) .atBase false)])),
    status := .drafted }

-- BEGIN GENERATED SFD-005
/--
**Detonate** — Spell · Fury · Energy 1 + Power 1
Printings: SFD-005/221

> Kill a gear. Its controller draws 2.
-/
def SFD_005.meta : CardDef :=
  { id := ⟨"SFD-005"⟩,
    name := "Detonate",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨1, [.domain .fury]⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Detonate. -/
def SFD_005 : CardDef :=
  { SFD_005.meta with

    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .gear]]
      (.ifThen (.exists (Selector.all .friendly .anywhere [.sameAs (.slot 0)]))
        (.seqOf [.prim (.kill (.slot 0)), .prim (.draw .you (.const 2))])
        (.ifThen (.exists (Selector.all .enemy .anywhere [.sameAs (.slot 0)]))
          (.seqOf [.prim (.kill (.slot 0)), .prim (.draw .opponent (.const 2))]) .nop))),
    status := .drafted }

-- BEGIN GENERATED SFD-006
/--
**Eager Drakehound** — Unit · Fury · Energy 3 + Power 1 · Might 3
Printings: SFD-006/221

> I enter ready.
-/
def SFD_006.meta : CardDef :=
  { id := ⟨"SFD-006"⟩,
    name := "Eager Drakehound",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Dragon"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Eager Drakehound. -/
def SFD_006 : CardDef :=
  { SFD_006.meta with
    abilities := [.passive .always [.entersReady .self]],
    status := .drafted }

-- BEGIN GENERATED SFD-007
/--
**Gem Jammer** — Unit · Fury · Energy 2 · Might 2
Printings: SFD-007/221

> When you play me, give a unit [Ganking] this turn. (It can move from battlefield to
> battlefield.)
-/
def SFD_007.meta : CardDef :=
  { id := ⟨"SFD-007"⟩,
    name := "Gem Jammer",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Bandle City"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Gem Jammer. -/
def SFD_007 : CardDef :=
  { SFD_007.meta with

    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.keyword .it { keyword := .ganking }) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-008
/--
**Sentinel Adept** — Unit · Fury · Energy 3 · Might 3
Printings: SFD-008/221

> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
-/
def SFD_008.meta : CardDef :=
  { id := ⟨"SFD-008"⟩,
    name := "Sentinel Adept",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Sentinel"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Sentinel Adept. -/
def SFD_008 : CardDef :=
  { SFD_008.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-009
/--
**Serrated Dirk** — Gear · Fury · Energy 1 · Might 0
Printings: SFD-009/221

> [Equip] :rb_rune_fury: (:rb_rune_fury:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Assault 2] (+2 :rb_might: while I'm an attacker.)
-/
def SFD_009.meta : CardDef :=
  { id := ⟨"SFD-009"⟩,
    name := "Serrated Dirk",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.fury],
    cost := some ⟨1, []⟩,
    might := some 0,
    mightBonus := some 0,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .fury]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Serrated Dirk. -/
def SFD_009 : CardDef :=
  { SFD_009.meta with
    grants := [.passive .always [.keyword .self { keyword := .assault, arg := .amount 2 }]],
    status := .drafted }

-- BEGIN GENERATED SFD-010
/--
**Void Drone** — Unit · Fury · Energy 3 · Might 3
Printings: SFD-010/221

> I cost :rb_energy_2: less to play from anywhere other than your hand.
-/
def SFD_010.meta : CardDef :=
  { id := ⟨"SFD-010"⟩,
    name := "Void Drone",
    types := [.unit],
    tags := [⟨"The Void"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Void Drone: the effect is not written yet. -/
def SFD_010 : CardDef := SFD_010.meta

-- BEGIN GENERATED SFD-011
/--
**Angle Shot** — Spell · Fury · Energy 2
Printings: SFD-011/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a unit and an Equipment with the same controller. Attach that Equipment to that unit or
> detach that Equipment from that unit. Draw 1.
-/
def SFD_011.meta : CardDef :=
  { id := ⟨"SFD-011"⟩,
    name := "Angle Shot",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Angle Shot: the effect is not written yet. -/
def SFD_011 : CardDef := SFD_011.meta

-- BEGIN GENERATED SFD-012
/--
**Battering Ram** — Unit · Fury · Energy 5 · Might 5
Printings: SFD-012/221

> I cost :rb_energy_1: less for each card you've played this turn, to a minimum of
> :rb_energy_1:.
-/
def SFD_012.meta : CardDef :=
  { id := ⟨"SFD-012"⟩,
    name := "Battering Ram",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Battering Ram. -/
def SFD_012 : CardDef :=
  { SFD_012.meta with

    abilities := [.passive .always [.costMinusMin .self .cardsPlayed 1]],
    status := .drafted }

-- BEGIN GENERATED SFD-013
/--
**Blast Corps Cadet** — Unit · Fury · Energy 2 · Might 2
Printings: SFD-013/221

> You may pay :rb_energy_1::rb_rune_fury: as an additional cost to play me.
> When you play me, if you paid the additional cost, deal 2 to a unit at a battlefield.
-/
def SFD_013.meta : CardDef :=
  { id := ⟨"SFD-013"⟩,
    name := "Blast Corps Cadet",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Blast Corps Cadet. -/
def SFD_013 : CardDef :=
  { SFD_013.meta with
    additionalCost := some ⟨1, [.domain .fury]⟩,
    abilities := [.triggered { Trigger.onSelf .play with condition := .paid }
        (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 2)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-014
/--
**Minotaur Reckoner** — Unit · Fury · Energy 5 · Might 5
Printings: SFD-014/221

> Units can't move to base.
-/
def SFD_014.meta : CardDef :=
  { id := ⟨"SFD-014"⟩,
    name := "Minotaur Reckoner",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Minotaur Reckoner: the effect is not written yet. -/
def SFD_014 : CardDef := SFD_014.meta

-- BEGIN GENERATED SFD-015
/--
**Perched Grimwyrm** — Unit · Fury · Energy 4 · Might 5
Printings: SFD-015/221

> Play me only to a battlefield you conquered this turn. (You can't play me anywhere else.)
-/
def SFD_015.meta : CardDef :=
  { id := ⟨"SFD-015"⟩,
    name := "Perched Grimwyrm",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Shadow Isles"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Perched Grimwyrm: the effect is not written yet. -/
def SFD_015 : CardDef := SFD_015.meta

-- BEGIN GENERATED SFD-016
/--
**Recurve Bow** — Gear · Fury · Energy 2 · Might 0
Printings: SFD-016/221

> [Equip] :rb_rune_fury: (:rb_rune_fury:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I attack or defend, deal 2 to an enemy unit here.
-/
def SFD_016.meta : CardDef :=
  { id := ⟨"SFD-016"⟩,
    name := "Recurve Bow",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 0,
    mightBonus := some 0,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .fury]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Recurve Bow. -/
def SFD_016 : CardDef :=
  { SFD_016.meta with
    grants := [.triggered (.onSelf .attack)
        (.of [.targetOf .one .enemy .here [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 2)))) .unlimited,
      .triggered (.onSelf .defend)
        (.of [.targetOf .one .enemy .here [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 2)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-017
/--
**Sudden Storm** — Spell · Fury · Energy 3
Printings: SFD-017/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Deal 2 to a unit at a battlefield. If it's attacking, deal 4 to it instead.
-/
def SFD_017.meta : CardDef :=
  { id := ⟨"SFD-017"⟩,
    name := "Sudden Storm",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Sudden Storm. -/
def SFD_017 : CardDef :=
  { SFD_017.meta with

    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.ifThen (.matches (.slot 0) .attacker) (.prim (.deal (.slot 0) (.const 4)))
        (.prim (.deal (.slot 0) (.const 2))))),
    status := .drafted }

-- BEGIN GENERATED SFD-018
/--
**Void Hatchling** — Unit · Fury · Energy 2 · Might 2
Printings: SFD-018/221

> If you would reveal cards from a deck, look at the top card first. You may recycle it. Then
> reveal those cards.
-/
def SFD_018.meta : CardDef :=
  { id := ⟨"SFD-018"⟩,
    name := "Void Hatchling",
    types := [.unit],
    tags := [⟨"The Void"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Void Hatchling: the effect is not written yet. -/
def SFD_018 : CardDef := SFD_018.meta

-- BEGIN GENERATED SFD-019
/--
**Assembly Rig** — Gear · Fury · Energy 4
Printings: SFD-019/221

> :rb_energy_1::rb_rune_fury:, Recycle a unit from your trash, :rb_exhaust:: Play a 3 :rb_might:
> Mech unit token to your base.
-/
def SFD_019.meta : CardDef :=
  { id := ⟨"SFD-019"⟩,
    name := "Assembly Rig",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Assembly Rig: the effect is not written yet. -/
def SFD_019 : CardDef := SFD_019.meta

-- BEGIN GENERATED SFD-020
/--
**Draven, Vanquisher** — Unit · Fury · Energy 4 · Might 4
Printings: SFD-020/221, SFD-020a/221

> When I win a combat, play a Gold gear token exhausted.
> When I attack or defend, you may pay :rb_rune_fury:. If you do, give me +2 :rb_might: this
> turn.
-/
def SFD_020.meta : CardDef :=
  { id := ⟨"SFD-020"⟩,
    name := "Draven",
    subtitle := some "Vanquisher",
    types := [.unit],
    tags := [⟨"Draven"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Draven, Vanquisher. -/
def SFD_020 : CardDef :=
  { SFD_020.meta with

    abilities := [.triggered (.onSelf .winCombat)
        (.of [] (.prim (.create "Gold" (.const 1) .atBase false))) .unlimited,
      .triggered (.onSelf .attack)
        (.of [] (.ifThen (.canPay ⟨0, [.domain .fury]⟩)
          (.may (.seqOf [.prim (.pay ⟨0, [.domain .fury]⟩),
            .grant .self (.mightPlus .it (.const 2)) .thisTurn])) .nop)) .unlimited,
      .triggered (.onSelf .defend)
        (.of [] (.ifThen (.canPay ⟨0, [.domain .fury]⟩)
          (.may (.seqOf [.prim (.pay ⟨0, [.domain .fury]⟩),
            .grant .self (.mightPlus .it (.const 2)) .thisTurn])) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-021
/--
**Ferrous Forerunner** — Unit · Fury · Energy 6 + Power 1 · Might 6
Printings: SFD-021/221

> [Deathknell] — Play two 3 :rb_might: Mech unit tokens to your base. (When I die, get the
> effect.)
-/
def SFD_021.meta : CardDef :=
  { id := ⟨"SFD-021"⟩,
    name := "Ferrous Forerunner",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.fury],
    cost := some ⟨6, [.domain .fury]⟩,
    might := some 6,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Ferrous Forerunner. -/
def SFD_021 : CardDef :=
  { SFD_021.meta with
    abilities := [.triggered (.onSelf .die)
        (.of []
        (.prim (.create "Mech" (.const 2) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-022
/--
**Long Sword** — Gear · Fury · Energy 2 + Power 1 · Might 2
Printings: SFD-022/221

> [Quick-Draw] (This has [Reaction]. When you play it, attach it to a unit you control.)
> [Equip] :rb_rune_fury: (:rb_rune_fury:: Attach this to a unit you control.)
-/
def SFD_022.meta : CardDef :=
  { id := ⟨"SFD-022"⟩,
    name := "Long Sword",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .quickDraw },
      { keyword := .equip, arg := .cost ⟨0, [.domain .fury]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Long Sword. -/
def SFD_022 : CardDef :=
  { SFD_022.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-023
/--
**Piercing Light** — Spell · Fury · Energy 2 + Power 1
Printings: SFD-023/221

> [Repeat] :rb_energy_2::rb_rune_fury: (You may pay the additional cost to repeat this spell's
> effect.)
> Deal 2 to a unit at a battlefield, then deal 2 to up to one other unit.
-/
def SFD_023.meta : CardDef :=
  { id := ⟨"SFD-023"⟩,
    name := "Piercing Light",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    keywords := [{ keyword := .repeat_, arg := .cost ⟨2, [.domain .fury]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Piercing Light. -/
def SFD_023 : CardDef :=
  { SFD_023.meta with

    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.seqOf [.prim (.deal (.slot 0) (.const 2)),
        .may (.prim (.deal (Selector.one .any .anywhere [.ofType .unit, .not (.sameAs (.slot 0))])
          (.const 2)))])),
    status := .drafted }

-- BEGIN GENERATED SFD-024
/--
**Rell, Magnetic** — Unit · Fury · Energy 4 · Might 4
Printings: SFD-024/221

> [Tank] (I must be assigned combat damage first.)
> When I attack, you may play an Equipment with Energy cost no more than :rb_energy_2:, ignoring
> its cost, and attach it to me.
-/
def SFD_024.meta : CardDef :=
  { id := ⟨"SFD-024"⟩,
    name := "Rell",
    subtitle := some "Magnetic",
    types := [.unit],
    tags := [⟨"Rell"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .tank }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Rell, Magnetic: the effect is not written yet. -/
def SFD_024 : CardDef := SFD_024.meta

-- BEGIN GENERATED SFD-025
/--
**Rengar, Pouncing** — Unit · Fury · Energy 3 + Power 1 · Might 3
Printings: SFD-025/221

> [Reaction] (Play any time, even before spells and abilities resolve, including to a
> battlefield you control.)
> [Assault 2] (+2 :rb_might: while I'm an attacker.)
> I can be played to a battlefield you're attacking.
-/
def SFD_025.meta : CardDef :=
  { id := ⟨"SFD-025"⟩,
    name := "Rengar",
    subtitle := some "Pouncing",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Rengar"⟩, ⟨"Ixtal"⟩],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    might := some 3,
    keywords := [{ keyword := .reaction },
      { keyword := .assault, arg := .amount 2 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Rengar, Pouncing: the effect is not written yet. -/
def SFD_025 : CardDef := SFD_025.meta

-- BEGIN GENERATED SFD-026
/--
**Rumble, Hotheaded** — Unit · Fury · Energy 4 · Might 4
Printings: SFD-026/221, SFD-026a/221

> Your Mechs each have [Assault]. (+1 :rb_might: while we're attackers.)
> When I conquer, you may recycle another friendly unit to play a Mech from your trash. Reduce
> its Energy cost by the Might of the unit you recycled.
-/
def SFD_026.meta : CardDef :=
  { id := ⟨"SFD-026"⟩,
    name := "Rumble",
    subtitle := some "Hotheaded",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Yordle"⟩, ⟨"Rumble"⟩, ⟨"Bandle City"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Rumble, Hotheaded: the effect is not written yet. -/
def SFD_026 : CardDef := SFD_026.meta

-- BEGIN GENERATED SFD-027
/--
**Dunebreaker** — Unit · Fury · Energy 7 + Power 1 · Might 7
Printings: SFD-027/221

> If you have two or fewer cards in your hand, I enter ready.
> When I hold, draw 2.
-/
def SFD_027.meta : CardDef :=
  { id := ⟨"SFD-027"⟩,
    name := "Dunebreaker",
    types := [.unit],
    tags := [⟨"The Void"⟩],
    domains := [.fury],
    cost := some ⟨7, [.domain .fury]⟩,
    might := some 7,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Dunebreaker. -/
def SFD_027 : CardDef :=
  { SFD_027.meta with

    abilities := [
      -- the card is still in the hand as it enters: "two or fewer" other cards is three here
      .passive (.cmp .le (.handSize .you) (.const 3)) [.entersReady .self],
      .triggered (.onSelf .hold) (.of [] (.prim (.draw .you (.const 2)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-028
/--
**Lucian, Gunslinger** — Unit · Fury · Energy 3 · Might 2
Printings: SFD-028/221, SFD-028a/221

> [Assault] (+1 :rb_might: while I'm an attacker.)
> When I attack, deal damage equal to my [Assault] to an enemy unit here.
-/
def SFD_028.meta : CardDef :=
  { id := ⟨"SFD-028"⟩,
    name := "Lucian",
    subtitle := some "Gunslinger",
    types := [.unit],
    tags := [⟨"Lucian"⟩, ⟨"Demacia"⟩, ⟨"Sentinel"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 2,
    keywords := [{ keyword := .assault, arg := .amount 1 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Lucian, Gunslinger: the effect is not written yet. -/
def SFD_028 : CardDef := SFD_028.meta

-- BEGIN GENERATED SFD-029
/--
**Rek'Sai, Breacher** — Unit · Fury · Energy 3 · Might 3
Printings: SFD-029/221, SFD-029a/221

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> [Assault] (+1 :rb_might: while I'm an attacker.)
> Friendly units played from anywhere other than a player's hand have [Accelerate].
-/
def SFD_029.meta : CardDef :=
  { id := ⟨"SFD-029"⟩,
    name := "Rek'Sai",
    subtitle := some "Breacher",
    types := [.unit],
    tags := [⟨"Rek'Sai"⟩, ⟨"The Void"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .accelerate },
      { keyword := .assault, arg := .amount 1 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Rek'Sai, Breacher: the effect is not written yet. -/
def SFD_029 : CardDef := SFD_029.meta

-- BEGIN GENERATED SFD-030
/--
**Skyfall of Areion** — Gear · Fury · Energy 3 · Might 2
Printings: SFD-030/221

> [Equip] :rb_energy_1::rb_rune_fury: (:rb_energy_1::rb_rune_fury:: Attach this to a unit you
> control.)

Effect (given to the unit it is attached to):

> My hold effects are also conquer effects, and vice versa.
-/
def SFD_030.meta : CardDef :=
  { id := ⟨"SFD-030"⟩,
    name := "Skyfall of Areion",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip, arg := .cost ⟨1, [.domain .fury]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Skyfall of Areion: the effect is not written yet. -/
def SFD_030 : CardDef := SFD_030.meta

-- BEGIN GENERATED SFD-031
/--
**Desert's Call** — Spell · Calm · Energy 2
Printings: SFD-031/221

> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Play a 2 :rb_might: Sand Soldier unit token.
-/
def SFD_031.meta : CardDef :=
  { id := ⟨"SFD-031"⟩,
    name := "Desert's Call",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Desert's Call. -/
def SFD_031 : CardDef :=
  { SFD_031.meta with
    spellEffect := some (.of []
      (.prim (.create "Sand Soldier" (.const 1) .atBase false))),
    status := .drafted }

-- BEGIN GENERATED SFD-032
/--
**Disarming Rake** — Unit · Calm · Energy 3 + Power 1 · Might 2
Printings: SFD-032/221

> When you play me, you may kill a gear.
-/
def SFD_032.meta : CardDef :=
  { id := ⟨"SFD-032"⟩,
    name := "Disarming Rake",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Disarming Rake. -/
def SFD_032 : CardDef :=
  { SFD_032.meta with

    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .anywhere [.ofType .gear]] (.may (.prim (.kill (.slot 0)))))
      .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-033
/--
**Doran's Shield** — Gear · Calm · Energy 1 · Might 1
Printings: SFD-033/221

> [Equip] :rb_rune_calm: (:rb_rune_calm:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Tank] (I must be assigned combat damage first.)
-/
def SFD_033.meta : CardDef :=
  { id := ⟨"SFD-033"⟩,
    name := "Doran's Shield",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .calm]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Doran's Shield. -/
def SFD_033 : CardDef :=
  { SFD_033.meta with
    grants := [.passive .always [.keyword .self { keyword := .tank }]],
    status := .drafted }

-- BEGIN GENERATED SFD-034
/--
**Feral Strength** — Spell · Calm · Energy 2
Printings: SFD-034/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Give a unit +2 :rb_might: this turn.
-/
def SFD_034.meta : CardDef :=
  { id := ⟨"SFD-034"⟩,
    name := "Feral Strength",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction },
      { keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Feral Strength. -/
def SFD_034 : CardDef :=
  { SFD_034.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED SFD-035
/--
**Guardian of the Passage** — Unit · Calm · Energy 6 · Might 6
Printings: SFD-035/221

> When I hold, you may return a unit or gear from your trash to your hand.
-/
def SFD_035.meta : CardDef :=
  { id := ⟨"SFD-035"⟩,
    name := "Guardian of the Passage",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.calm],
    cost := some ⟨6, []⟩,
    might := some 6,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Guardian of the Passage. -/
def SFD_035 : CardDef :=
  { SFD_035.meta with

    abilities := [.triggered (.onSelf .hold)
      (.of [] (.may (.prim (.returnToHand
        (Selector.one .friendly .inTrash [.not (.ofType .spell)]))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-036
/--
**Lonely Poro** — Unit · Calm · Energy 2 · Might 2
Printings: SFD-036/221, UNL-221/219

> [Deathknell] — If I died alone, draw 1. (When I die, get the effect. I'm alone if there are no
> other friendly units here.)
-/
def SFD_036.meta : CardDef :=
  { id := ⟨"SFD-036"⟩,
    name := "Lonely Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩, ⟨"Freljord"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"SFD"⟩, ⟨"UNL"⟩] }
-- END GENERATED

/-- Lonely Poro: the effect is not written yet. -/
def SFD_036 : CardDef := SFD_036.meta

-- BEGIN GENERATED SFD-037
/--
**Navori Scout** — Unit · Calm · Energy 4 · Might 4
Printings: SFD-037/221

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
-/
def SFD_037.meta : CardDef :=
  { id := ⟨"SFD-037"⟩,
    name := "Navori Scout",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Navori Scout. -/
def SFD_037 : CardDef :=
  { SFD_037.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-038
/--
**Ribbon Dancer** — Unit · Calm · Energy 3 · Might 3
Printings: SFD-038/221

> When I move to a battlefield, give another friendly unit +1 :rb_might: this turn.
-/
def SFD_038.meta : CardDef :=
  { id := ⟨"SFD-038"⟩,
    name := "Ribbon Dancer",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Ribbon Dancer. -/
def SFD_038 : CardDef :=
  { SFD_038.meta with

    abilities := [.triggered { event := .move, condition := .matches .self .onBattlefield }
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .notSelf]]
        (.grant (.slot 0) (.mightPlus .it (.const 1)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-039
/--
**Royal Entourage** — Unit · Calm · Energy 3 + Power 1 · Might 4
Printings: SFD-039/221

> When you play me, ready or exhaust a legend.
-/
def SFD_039.meta : CardDef :=
  { id := ⟨"SFD-039"⟩,
    name := "Royal Entourage",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Royal Entourage: the effect is not written yet. -/
def SFD_039 : CardDef := SFD_039.meta

-- BEGIN GENERATED SFD-040
/--
**Thwonk!** — Spell · Calm · Energy 2
Printings: SFD-040/221

> [Action] (Play on your turn or in showdowns.)
> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Stun an attacking unit. (It doesn't deal combat damage this turn.)
-/
def SFD_040.meta : CardDef :=
  { id := ⟨"SFD-040"⟩,
    name := "Thwonk!",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action },
      { keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Thwonk!. -/
def SFD_040 : CardDef :=
  { SFD_040.meta with

    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit, .attacker]]
      (.prim (.stun (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED SFD-041
/--
**Apprentice Smith** — Unit · Calm · Energy 2 · Might 2
Printings: SFD-041/221

> When I move, reveal the top card of your Main Deck. If it's a gear, draw it. Otherwise,
> recycle it.
-/
def SFD_041.meta : CardDef :=
  { id := ⟨"SFD-041"⟩,
    name := "Apprentice Smith",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Apprentice Smith: the effect is not written yet. -/
def SFD_041 : CardDef := SFD_041.meta

-- BEGIN GENERATED SFD-042
/--
**Brutalizer** — Gear · Calm · Energy 2 · Might 1
Printings: SFD-042/221

> [Equip] :rb_rune_calm: (:rb_rune_calm:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> If this was attached to me this turn, I have an additional +2 :rb_might:.
-/
def SFD_042.meta : CardDef :=
  { id := ⟨"SFD-042"⟩,
    name := "Brutalizer",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .calm]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Brutalizer: the effect is not written yet. -/
def SFD_042 : CardDef := SFD_042.meta

-- BEGIN GENERATED SFD-043
/--
**Emperor's Divide** — Spell · Calm · Energy 2
Printings: SFD-043/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Move any number of friendly units at a battlefield to their base.
-/
def SFD_043.meta : CardDef :=
  { id := ⟨"SFD-043"⟩,
    name := "Emperor's Divide",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Emperor's Divide. -/
def SFD_043 : CardDef :=
  { SFD_043.meta with

    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .battlefield]]
      (.forEach (Selector.all .friendly .atBattlefield [.ofType .unit, .at_ (.slot 0)])
        (.may (.prim (.move .it .base))))),
    status := .drafted }

-- BEGIN GENERATED SFD-044
/--
**Legion Quartermaster** — Unit · Calm · Energy 3 · Might 4
Printings: SFD-044/221

> As an additional cost to play me, return a friendly gear to its owner's hand.
-/
def SFD_044.meta : CardDef :=
  { id := ⟨"SFD-044"⟩,
    name := "Legion Quartermaster",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Legion Quartermaster: the effect is not written yet. -/
def SFD_044 : CardDef := SFD_044.meta

-- BEGIN GENERATED SFD-045
/--
**Not So Fast** — Spell · Calm · Energy 2 + Power 1
Printings: SFD-045/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Counter an enemy spell or ability that chooses a friendly unit or gear.
-/
def SFD_045.meta : CardDef :=
  { id := ⟨"SFD-045"⟩,
    name := "Not So Fast",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, [.domain .calm]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Not So Fast: the effect is not written yet. -/
def SFD_045 : CardDef := SFD_045.meta

-- BEGIN GENERATED SFD-046
/--
**Poro Snax** — Gear · Calm · Energy 1 + Power 1
Printings: SFD-046/221

> When you play this, draw 1.
> :rb_energy_1::rb_rune_calm:, :rb_exhaust:, Kill this: Draw 1.
-/
def SFD_046.meta : CardDef :=
  { id := ⟨"SFD-046"⟩,
    name := "Poro Snax",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨1, [.domain .calm]⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Poro Snax: the effect is not written yet. -/
def SFD_046 : CardDef := SFD_046.meta

-- BEGIN GENERATED SFD-047
/--
**Simian Ancestor** — Unit · Calm · Energy 5 + Power 1 · Might 5
Printings: SFD-047/221

> When you buff me, ready me.
-/
def SFD_047.meta : CardDef :=
  { id := ⟨"SFD-047"⟩,
    name := "Simian Ancestor",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Simian Ancestor. -/
def SFD_047 : CardDef :=
  { SFD_047.meta with

    abilities := [.triggered (.onSelf .buff) (.of [] (.prim (.ready .self))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-048
/--
**Stellacorn Herder** — Unit · Calm · Energy 4 · Might 3
Printings: SFD-048/221

> When I move, draw 1.
-/
def SFD_048.meta : CardDef :=
  { id := ⟨"SFD-048"⟩,
    name := "Stellacorn Herder",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.calm],
    cost := some ⟨4, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Stellacorn Herder. -/
def SFD_048 : CardDef :=
  { SFD_048.meta with
    abilities := [.triggered (.onSelf .move)
        (.of []
        (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-049
/--
**Aphelios, Exalted** — Unit · Calm · Energy 4 + Power 1 · Might 4
Printings: SFD-049/221, SFD-224*/221, SFD-224/221, RAD-179/167

> When you attach an Equipment to me, choose one that hasn't been chosen this turn —Ready 2
> runes.Channel 1 rune exhausted.Buff a friendly unit.
-/
def SFD_049.meta : CardDef :=
  { id := ⟨"SFD-049"⟩,
    name := "Aphelios",
    subtitle := some "Exalted",
    types := [.unit],
    tags := [⟨"Aphelios"⟩, ⟨"Mount Targon"⟩],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    might := some 4,
    sets := [⟨"SFD"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Aphelios, Exalted: the effect is not written yet. -/
def SFD_049 : CardDef := SFD_049.meta

-- BEGIN GENERATED SFD-050
/--
**Azir, Ascendant** — Unit · Calm · Energy 6 + Power 1 · Might 6
Printings: SFD-050/221, SFD-050a/221

> :rb_rune_calm:: [Action] — Choose a unit you control. Move me to its location and it to my
> original location. If it's equipped, you may attach one of its Equipment to me. Use only once
> per turn.
-/
def SFD_050.meta : CardDef :=
  { id := ⟨"SFD-050"⟩,
    name := "Azir",
    subtitle := some "Ascendant",
    types := [.unit],
    tags := [⟨"Bird"⟩, ⟨"Azir"⟩, ⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨6, [.domain .calm]⟩,
    might := some 6,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Azir, Ascendant: the effect is not written yet. -/
def SFD_050 : CardDef := SFD_050.meta

-- BEGIN GENERATED SFD-051
/--
**Guardian Angel** — Gear · Calm · Energy 2 · Might 1
Printings: SFD-051/221

> [Equip] :rb_rune_calm: (:rb_rune_calm:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> If I would die, kill Guardian Angel instead. Heal me, exhaust me, and recall me.
-/
def SFD_051.meta : CardDef :=
  { id := ⟨"SFD-051"⟩,
    name := "Guardian Angel",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .calm]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Guardian Angel: the effect is not written yet. -/
def SFD_051 : CardDef := SFD_051.meta

-- BEGIN GENERATED SFD-052
/--
**Heart of Dark Ice** — Gear · Calm · Energy 3 + Power 1
Printings: SFD-052/221

> :rb_exhaust:: Give a unit +3 :rb_might: this turn.
-/
def SFD_052.meta : CardDef :=
  { id := ⟨"SFD-052"⟩,
    name := "Heart of Dark Ice",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Heart of Dark Ice. -/
def SFD_052 : CardDef :=
  { SFD_052.meta with
    abilities := [.activated [.exhaustSelf] .normal
        (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-053
/--
**Janna, Savior** — Unit · Calm · Energy 3 + Power 1 · Might 3
Printings: SFD-053/221

> [Reaction] (Play any time, even before spells and abilities resolve, including to a
> battlefield you control.)
> When you play me, heal your units here, then move an enemy unit from here to its base.
-/
def SFD_053.meta : CardDef :=
  { id := ⟨"SFD-053"⟩,
    name := "Janna",
    subtitle := some "Savior",
    types := [.unit],
    tags := [⟨"Janna"⟩, ⟨"Zaun"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 3,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Janna, Savior. -/
def SFD_053 : CardDef :=
  { SFD_053.meta with

    abilities := [.triggered (.onSelf .play)
      (.of [] (.seqOf [
        .prim (.heal (Selector.all .friendly .anywhere [.ofType .unit, .at_ .self]) (.const 99)),
        .prim (.move (Selector.one .enemy .anywhere [.ofType .unit, .at_ .self]) .base)]))
      .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-054
/--
**Jax, Unmatched** — Unit · Calm · Energy 5 + Power 1 · Might 5
Printings: SFD-054/221, SFD-054a/221

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> Each Equipment in your hand has [Quick-Draw]. (It gains [Reaction]. When you play it, attach
> it to a unit you control.)
-/
def SFD_054.meta : CardDef :=
  { id := ⟨"SFD-054"⟩,
    name := "Jax",
    subtitle := some "Unmatched",
    types := [.unit],
    tags := [⟨"Jax"⟩, ⟨"Icathia"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 5,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Jax, Unmatched: the effect is not written yet. -/
def SFD_054 : CardDef := SFD_054.meta

-- BEGIN GENERATED SFD-055
/--
**Needlessly Large Yordle** — Unit · Calm · Energy 10 + Power 3 · Might 5
Printings: SFD-055/221

> [Shield 5] (+5 :rb_might: while I'm a defender.)
> [Tank] (I must be assigned combat damage first.)
> I cost :rb_energy_2::rb_rune_calm: less for each point you scored from holding this turn.
-/
def SFD_055.meta : CardDef :=
  { id := ⟨"SFD-055"⟩,
    name := "Needlessly Large Yordle",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.calm],
    cost := some ⟨10, [.domain .calm, .domain .calm, .domain .calm]⟩,
    might := some 5,
    keywords := [{ keyword := .shield, arg := .amount 5 },
      { keyword := .tank }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Needlessly Large Yordle: the effect is not written yet. -/
def SFD_055 : CardDef := SFD_055.meta

-- BEGIN GENERATED SFD-056
/--
**Sterak's Gage** — Gear · Calm · Energy 3 + Power 2 · Might 3
Printings: SFD-056/221

> [Quick-Draw] (This has [Reaction]. When you play it, attach it to a unit you control.)
> [Equip] :rb_rune_calm: (:rb_rune_calm:: Attach this to a unit you control.)
-/
def SFD_056.meta : CardDef :=
  { id := ⟨"SFD-056"⟩,
    name := "Sterak's Gage",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm, .domain .calm]⟩,
    might := some 3,
    mightBonus := some 3,
    keywords := [{ keyword := .quickDraw },
      { keyword := .equip, arg := .cost ⟨0, [.domain .calm]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Sterak's Gage. -/
def SFD_056 : CardDef :=
  { SFD_056.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-057
/--
**Irelia, Fervent** — Unit · Calm · Energy 5 · Might 4
Printings: SFD-057/221, SFD-057a/221, SFD-225*/221, SFD-225/221, VEN-174/166

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> When you choose or ready me, give me +1 :rb_might: this turn.
-/
def SFD_057.meta : CardDef :=
  { id := ⟨"SFD-057"⟩,
    name := "Irelia",
    subtitle := some "Fervent",
    types := [.unit],
    tags := [⟨"Irelia"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨5, []⟩,
    might := some 4,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"SFD"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Irelia, Fervent: the effect is not written yet. -/
def SFD_057 : CardDef := SFD_057.meta

-- BEGIN GENERATED SFD-058
/--
**Ornn, Blacksmith** — Unit · Calm · Energy 5 + Power 1 · Might 5
Printings: SFD-058/221, SFD-058a/221

> When you play me or when I hold, look at the top 4 cards of your Main Deck. You may reveal a
> gear from among them and draw it. Then recycle the rest.
-/
def SFD_058.meta : CardDef :=
  { id := ⟨"SFD-058"⟩,
    name := "Ornn",
    subtitle := some "Blacksmith",
    types := [.unit],
    tags := [⟨"Ornn"⟩, ⟨"Freljord"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Ornn, Blacksmith: the effect is not written yet. -/
def SFD_058 : CardDef := SFD_058.meta

-- BEGIN GENERATED SFD-059
/--
**Svellsongur** — Gear · Calm · Energy 3 + Power 1 · Might 0
Printings: SFD-059/221

> [Equip] :rb_energy_1::rb_rune_calm: (:rb_energy_1::rb_rune_calm:: Attach this to a unit you
> control.)
> As this is attached to a unit, copy that unit's text to this Equipment's effect text for as
> long as this is attached to it.
-/
def SFD_059.meta : CardDef :=
  { id := ⟨"SFD-059"⟩,
    name := "Svellsongur",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 0,
    mightBonus := some 0,
    keywords := [{ keyword := .equip, arg := .cost ⟨1, [.domain .calm]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Svellsongur: the effect is not written yet. -/
def SFD_059 : CardDef := SFD_059.meta

-- BEGIN GENERATED SFD-060
/--
**Tianna Crownguard** — Unit · Calm · Energy 7 + Power 2 · Might 4
Printings: SFD-060/221

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> While I'm at a battlefield, opponents can't score points.
-/
def SFD_060.meta : CardDef :=
  { id := ⟨"SFD-060"⟩,
    name := "Tianna Crownguard",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Demacia"⟩],
    domains := [.calm],
    cost := some ⟨7, [.domain .calm, .domain .calm]⟩,
    might := some 4,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Tianna Crownguard: the effect is not written yet. -/
def SFD_060 : CardDef := SFD_060.meta

-- BEGIN GENERATED SFD-061
/--
**Aspiring Engineer** — Unit · Mind · Energy 3 + Power 1 · Might 3
Printings: SFD-061/221

> When you play me, return a gear from your trash to your hand.
-/
def SFD_061.meta : CardDef :=
  { id := ⟨"SFD-061"⟩,
    name := "Aspiring Engineer",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Aspiring Engineer. -/
def SFD_061 : CardDef :=
  { SFD_061.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.returnToHand (.one .friendly .inTrash [.ofType .gear])))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-062
/--
**Bubble Bot** — Unit · Mind · Energy 3 · Might 3
Printings: SFD-062/221

> When you play me, ready another friendly Mech.
-/
def SFD_062.meta : CardDef :=
  { id := ⟨"SFD-062"⟩,
    name := "Bubble Bot",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Bubble Bot. -/
def SFD_062 : CardDef :=
  { SFD_062.meta with

    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .tag ⟨"Mech"⟩, .notSelf]]
        (.prim (.ready (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-063
/--
**Chemtech Cask** — Gear · Mind · Energy 1
Printings: SFD-063/221

> When you play a spell on an opponent's turn, you may exhaust me to play a Gold gear token
> exhausted.
-/
def SFD_063.meta : CardDef :=
  { id := ⟨"SFD-063"⟩,
    name := "Chemtech Cask",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨1, []⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Chemtech Cask. -/
def SFD_063 : CardDef :=
  { SFD_063.meta with

    abilities := [.triggered
      { event := .play, subject := Selector.all .friendly .anywhere [.ofType .spell],
        condition := .not .yourTurn }
      (.of [] (.ifThen (.matches .self .ready)
        (.may (.seqOf [.prim (.exhaust .self), .prim (.create "Gold" (.const 1) .atBase false)]))
        .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-064
/--
**Cloth Armor** — Gear · Mind · Energy 1 · Might 0
Printings: SFD-064/221

> [Quick-Draw] (This has [Reaction]. When you play it, attach it to a unit you control.)
> [Equip] :rb_rune_mind: (:rb_rune_mind:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Shield 2] (+2 :rb_might: while I'm a defender.)
-/
def SFD_064.meta : CardDef :=
  { id := ⟨"SFD-064"⟩,
    name := "Cloth Armor",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.mind],
    cost := some ⟨1, []⟩,
    might := some 0,
    mightBonus := some 0,
    keywords := [{ keyword := .quickDraw },
      { keyword := .equip, arg := .cost ⟨0, [.domain .mind]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Cloth Armor. -/
def SFD_064 : CardDef :=
  { SFD_064.meta with
    grants := [.passive .always [.keyword .self { keyword := .shield, arg := .amount 2 }]],
    status := .drafted }

-- BEGIN GENERATED SFD-065
/--
**Forecaster** — Unit · Mind · Energy 2 · Might 2
Printings: SFD-065/221

> Your Mechs have [Vision]. (When you play us, look at the top card of your Main Deck. You may
> recycle it.)
-/
def SFD_065.meta : CardDef :=
  { id := ⟨"SFD-065"⟩,
    name := "Forecaster",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Forecaster: the effect is not written yet. -/
def SFD_065 : CardDef := SFD_065.meta

-- BEGIN GENERATED SFD-066
/--
**Frigid Touch** — Spell · Mind · Energy 2
Printings: SFD-066/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Give a unit -2 :rb_might: this turn.
-/
def SFD_066.meta : CardDef :=
  { id := ⟨"SFD-066"⟩,
    name := "Frigid Touch",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction },
      { keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Frigid Touch. -/
def SFD_066 : CardDef :=
  { SFD_066.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.mightMinus .it (.const 2)) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED SFD-067
/--
**Frostcoat Cub** — Unit · Mind · Energy 3 · Might 3
Printings: SFD-067/221

> You may pay :rb_rune_mind: as an additional cost to play me.
> When you play me, if you paid the additional cost, give a unit -2 :rb_might: this turn.
-/
def SFD_067.meta : CardDef :=
  { id := ⟨"SFD-067"⟩,
    name := "Frostcoat Cub",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Freljord"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Frostcoat Cub. -/
def SFD_067 : CardDef :=
  { SFD_067.meta with
    additionalCost := some ⟨0, [.domain .mind]⟩,
    abilities := [.triggered { Trigger.onSelf .play with condition := .paid }
        (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightMinus .it (.const 2)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-068
/--
**Gearhead** — Unit · Mind · Energy 5 · Might 3
Printings: SFD-068/221

> [Accelerate] (You may pay :rb_energy_1::rb_rune_mind: as an additional cost to have me enter
> ready.)
> Each Equipment attached to me gives double its base Might bonus.
-/
def SFD_068.meta : CardDef :=
  { id := ⟨"SFD-068"⟩,
    name := "Gearhead",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    might := some 3,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Gearhead: the effect is not written yet. -/
def SFD_068 : CardDef := SFD_068.meta

-- BEGIN GENERATED SFD-069
/--
**Plundering Poro** — Unit · Mind · Energy 2 · Might 2
Printings: SFD-069/221, UNL-222/219

> When I conquer, play a Gold gear token exhausted.
-/
def SFD_069.meta : CardDef :=
  { id := ⟨"SFD-069"⟩,
    name := "Plundering Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩, ⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩, ⟨"UNL"⟩] }
-- END GENERATED

/-- Plundering Poro. -/
def SFD_069 : CardDef :=
  { SFD_069.meta with
    abilities := [.triggered (.onSelf .conquer)
        (.of []
        (.prim (.create "Gold" (.const 1) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-070
/--
**Wages of Pain** — Spell · Mind · Energy 3
Printings: SFD-070/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Deal 3 to a unit at a battlefield. Play a Gold gear token exhausted.
-/
def SFD_070.meta : CardDef :=
  { id := ⟨"SFD-070"⟩,
    name := "Wages of Pain",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Wages of Pain. -/
def SFD_070 : CardDef :=
  { SFD_070.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.seqOf [.prim (.deal (.slot 0) (.const 3)),
        .prim (.create "Gold" (.const 1) .atBase false)])),
    status := .drafted }

-- BEGIN GENERATED SFD-071
/--
**Breakneck Mech** — Unit · Mind · Energy 8 + Power 2 · Might 7
Printings: SFD-071/221

> Your Mechs have [Deflect] and [Ganking]. (Opponents must pay :rb_rune_rainbow: to choose us
> with a spell or ability. We can move from battlefield to battlefield.)
> I enter ready if you control another Mech.
-/
def SFD_071.meta : CardDef :=
  { id := ⟨"SFD-071"⟩,
    name := "Breakneck Mech",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨8, [.domain .mind, .domain .mind]⟩,
    might := some 7,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Breakneck Mech. -/
def SFD_071 : CardDef :=
  { SFD_071.meta with

    abilities := [.passive .always
        [.keyword (Selector.all .friendly .anywhere [.tag ⟨"Mech"⟩]) { keyword := .deflect },
         .keyword (Selector.all .friendly .anywhere [.tag ⟨"Mech"⟩]) { keyword := .ganking }],
      .passive (.exists (Selector.all .friendly .anywhere [.tag ⟨"Mech"⟩, .notSelf]))
        [.entersReady .self]],
    status := .drafted }

-- BEGIN GENERATED SFD-072
/--
**Dropboarder** — Unit · Mind · Energy 4 · Might 4
Printings: SFD-072/221

> When you play me, if you control two or more gear, ready me.
-/
def SFD_072.meta : CardDef :=
  { id := ⟨"SFD-072"⟩,
    name := "Dropboarder",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Dropboarder. -/
def SFD_072 : CardDef :=
  { SFD_072.meta with

    abilities := [.triggered (.onSelf .play)
      (.of [] (.ifThen (.cmp .ge (.count (Selector.all .friendly .anywhere [.ofType .gear]))
        (.const 2)) (.prim (.ready .self)) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-073
/--
**Experimental Hexplate** — Gear · Mind · Energy 1 · Might 1
Printings: SFD-073/221

> [Equip] :rb_rune_mind: (:rb_rune_mind:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> I am a Mech.
-/
def SFD_073.meta : CardDef :=
  { id := ⟨"SFD-073"⟩,
    name := "Experimental Hexplate",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.mind],
    cost := some ⟨1, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .mind]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Experimental Hexplate: the effect is not written yet. -/
def SFD_073 : CardDef := SFD_073.meta

-- BEGIN GENERATED SFD-074
/--
**Pickpocket** — Unit · Mind · Energy 3 · Might 3
Printings: SFD-074/221

> When you play me, you may kill a gear with Energy cost no more than :rb_energy_1:. If you do,
> play a Gold gear token exhausted.
-/
def SFD_074.meta : CardDef :=
  { id := ⟨"SFD-074"⟩,
    name := "Pickpocket",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Pickpocket. -/
def SFD_074 : CardDef :=
  { SFD_074.meta with

    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .anywhere [.ofType .gear, .cost .le (.const 1)]]
        (.may (.seqOf [.prim (.kill (.slot 0)),
          .prim (.create "Gold" (.const 1) .atBase false)]))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-075
/--
**Prize of Progress** — Unit · Mind · Energy 4 + Power 1 · Might 3
Printings: SFD-075/221

> When you use an activated ability of a gear, give me +1 :rb_might: this turn.
-/
def SFD_075.meta : CardDef :=
  { id := ⟨"SFD-075"⟩,
    name := "Prize of Progress",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Prize of Progress: the effect is not written yet. -/
def SFD_075 : CardDef := SFD_075.meta

-- BEGIN GENERATED SFD-076
/--
**Production Surge** — Spell · Mind · Energy 4 + Power 1
Printings: SFD-076/221

> This costs :rb_energy_2: less if you control a Mech.
> Play a 3 :rb_might: Mech unit token to your base.
> Draw 1.
-/
def SFD_076.meta : CardDef :=
  { id := ⟨"SFD-076"⟩,
    name := "Production Surge",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Production Surge. -/
def SFD_076 : CardDef :=
  { SFD_076.meta with

    abilities := [.passive (.exists (Selector.all .friendly .anywhere [.tag ⟨"Mech"⟩]))
      [.costMinus .self (.const 2)]],
    spellEffect := some (.of [] (.seqOf [.prim (.create "Mech" (.const 1) .atBase false),
      .prim (.draw .you (.const 1))])),
    status := .drafted }

-- BEGIN GENERATED SFD-077
/--
**Rocket Barrage** — Spell · Mind · Energy 4 + Power 1
Printings: SFD-077/221

> [Repeat] :rb_energy_4::rb_rune_mind: (You may pay the additional cost to repeat this spell's
> effect, and may make different choices.)
> Choose one —Deal 4 to a unit in a base.Kill a gear.
-/
def SFD_077.meta : CardDef :=
  { id := ⟨"SFD-077"⟩,
    name := "Rocket Barrage",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    keywords := [{ keyword := .repeat_, arg := .cost ⟨4, [.domain .mind]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Rocket Barrage: the effect is not written yet. -/
def SFD_077 : CardDef := SFD_077.meta

-- BEGIN GENERATED SFD-078
/--
**Temporal Portal** — Gear · Mind · Energy 3
Printings: SFD-078/221

> :rb_rune_rainbow:, :rb_exhaust:: Give the next spell you play this turn [Repeat] equal to its
> cost. (You may pay the additional cost to repeat the spell's effect.)
-/
def SFD_078.meta : CardDef :=
  { id := ⟨"SFD-078"⟩,
    name := "Temporal Portal",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Temporal Portal: the effect is not written yet. -/
def SFD_078 : CardDef := SFD_078.meta

-- BEGIN GENERATED SFD-079
/--
**Bard, Mercurial** — Unit · Mind · Energy 4 + Power 1 · Might 4
Printings: SFD-079/221, SFD-228*/221, SFD-228/221

> You may exhaust your legend as an additional cost to play me.
> When you play me, if you paid the additional cost, move any number of your units to an open
> battlefield.
-/
def SFD_079.meta : CardDef :=
  { id := ⟨"SFD-079"⟩,
    name := "Bard",
    subtitle := some "Mercurial",
    types := [.unit],
    tags := [⟨"Bard"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Bard, Mercurial: the effect is not written yet. -/
def SFD_079 : CardDef := SFD_079.meta

-- BEGIN GENERATED SFD-080
/--
**Bellows Breath** — Spell · Mind · Energy 1 + Power 1
Printings: SFD-080/221

> [Action] (Play on your turn or in showdowns.)
> [Repeat] :rb_energy_1::rb_rune_mind: (You may pay the additional cost to repeat this spell's
> effect.)
> Deal 1 to up to three units at the same location.
-/
def SFD_080.meta : CardDef :=
  { id := ⟨"SFD-080"⟩,
    name := "Bellows Breath",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨1, [.domain .mind]⟩,
    keywords := [{ keyword := .action },
      { keyword := .repeat_, arg := .cost ⟨1, [.domain .mind]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Bellows Breath: the effect is not written yet. -/
def SFD_080 : CardDef := SFD_080.meta

-- BEGIN GENERATED SFD-081
/--
**Card Sharp** — Unit · Mind · Energy 3 · Might 3
Printings: SFD-081/221

> When you play me, you and each opponent may play a Gold gear token exhausted. For each
> opponent who did, you play a Gold gear token exhausted.
-/
def SFD_081.meta : CardDef :=
  { id := ⟨"SFD-081"⟩,
    name := "Card Sharp",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Card Sharp: the effect is not written yet. -/
def SFD_081 : CardDef := SFD_081.meta

-- BEGIN GENERATED SFD-082
/--
**Ezreal, Dashing** — Unit · Mind · Energy 4 + Power 1 · Might 3
Printings: SFD-082/221, SFD-082a/221, RAD-180/167

> When I attack or defend, deal damage equal to my Might to an enemy unit here.
> I don't deal combat damage.
> :rb_rune_mind:: [Action] — Move me to your base.
-/
def SFD_082.meta : CardDef :=
  { id := ⟨"SFD-082"⟩,
    name := "Ezreal",
    subtitle := some "Dashing",
    types := [.unit],
    tags := [⟨"Ezreal"⟩, ⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 3,
    sets := [⟨"SFD"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Ezreal, Dashing: the effect is not written yet. -/
def SFD_082 : CardDef := SFD_082.meta

-- BEGIN GENERATED SFD-083
/--
**Hextech Anomaly** — Gear · Mind · Energy 3 + Power 1
Printings: SFD-083/221

> :rb_exhaust:: [Reaction] — Pay any amount of :rb_rune_rainbow: to [Add] that much Energy.
> (Abilities that add resources can't be reacted to.)
-/
def SFD_083.meta : CardDef :=
  { id := ⟨"SFD-083"⟩,
    name := "Hextech Anomaly",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Hextech Anomaly: the effect is not written yet. -/
def SFD_083 : CardDef := SFD_083.meta

-- BEGIN GENERATED SFD-084
/--
**Jayce, Man of Progress** — Unit · Mind · Energy 4 · Might 4
Printings: SFD-084/221, VEN-175/166

> When you play me, you may kill a friendly gear. If you do, you may play a gear with Energy
> cost no more than :rb_energy_7: from hand this turn, ignoring its Energy cost. (You must still
> pay its Power cost.)
-/
def SFD_084.meta : CardDef :=
  { id := ⟨"SFD-084"⟩,
    name := "Jayce",
    subtitle := some "Man of Progress",
    types := [.unit],
    tags := [⟨"Jayce"⟩, ⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"SFD"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Jayce, Man of Progress: the effect is not written yet. -/
def SFD_084 : CardDef := SFD_084.meta

-- BEGIN GENERATED SFD-085
/--
**Ornn, Forge God** — Unit · Mind · Energy 6 · Might 4
Printings: SFD-085/221, SFD-085a/221

> [Deflect 2] (Opponents must pay :rb_rune_rainbow::rb_rune_rainbow: to choose me with a spell
> or ability.)
> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
> I have +1 :rb_might: for each friendly gear.
-/
def SFD_085.meta : CardDef :=
  { id := ⟨"SFD-085"⟩,
    name := "Ornn",
    subtitle := some "Forge God",
    types := [.unit],
    tags := [⟨"Ornn"⟩, ⟨"Freljord"⟩],
    domains := [.mind],
    cost := some ⟨6, []⟩,
    might := some 4,
    keywords := [{ keyword := .deflect, arg := .amount 2 },
      { keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Ornn, Forge God: the effect is not written yet. -/
def SFD_085 : CardDef := SFD_085.meta

-- BEGIN GENERATED SFD-086
/--
**World Atlas** — Gear · Mind · Energy 3 · Might 2
Printings: SFD-086/221

> [Equip] :rb_rune_mind: (:rb_rune_mind:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I hold, play two Gold gear tokens exhausted.
-/
def SFD_086.meta : CardDef :=
  { id := ⟨"SFD-086"⟩,
    name := "World Atlas",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .mind]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- World Atlas. -/
def SFD_086 : CardDef :=
  { SFD_086.meta with
    grants := [.triggered (.onSelf .hold)
        (.of []
        (.prim (.create "Gold" (.const 2) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-087
/--
**Premonition** — Spell · Mind · Energy 2 + Power 3
Printings: SFD-087/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Draw 3.
-/
def SFD_087.meta : CardDef :=
  { id := ⟨"SFD-087"⟩,
    name := "Premonition",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, [.domain .mind, .domain .mind, .domain .mind]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Premonition. -/
def SFD_087 : CardDef :=
  { SFD_087.meta with
    spellEffect := some (.of []
      (.prim (.draw .you (.const 3)))),
    status := .drafted }

-- BEGIN GENERATED SFD-088
/--
**Renata Glasc, Mastermind** — Unit · Mind · Energy 5 · Might 4
Printings: SFD-088/221, SFD-088a/221

> :rb_energy_1::rb_rune_mind:: Draw 1.
> :rb_energy_4::rb_rune_mind::rb_rune_mind::rb_rune_mind::rb_rune_mind:, :rb_exhaust:: Score 1
> point.
> Use my abilities only while I'm at a battlefield.
-/
def SFD_088.meta : CardDef :=
  { id := ⟨"SFD-088"⟩,
    name := "Renata Glasc",
    subtitle := some "Mastermind",
    types := [.unit],
    tags := [⟨"Renata Glasc"⟩, ⟨"Zaun"⟩],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Renata Glasc, Mastermind: the effect is not written yet. -/
def SFD_088 : CardDef := SFD_088.meta

-- BEGIN GENERATED SFD-089
/--
**Rumble, Scrapper** — Unit · Mind · Energy 5 + Power 1 · Might 4
Printings: SFD-089/221, SFD-089a/221

> Your Mechs have +1 :rb_might: (including me).
> When I hold, play a 3 :rb_might: Mech unit token to your base.
-/
def SFD_089.meta : CardDef :=
  { id := ⟨"SFD-089"⟩,
    name := "Rumble",
    subtitle := some "Scrapper",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Yordle"⟩, ⟨"Rumble"⟩, ⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨5, [.domain .mind]⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Rumble, Scrapper. -/
def SFD_089 : CardDef :=
  { SFD_089.meta with

    abilities := [.passive .always
        [.mightPlus (Selector.all .friendly .anywhere [.tag ⟨"Mech"⟩]) (.const 1)],
      .triggered (.onSelf .hold)
        (.of [] (.prim (.create "Mech" (.const 1) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-090
/--
**The Zero Drive** — Gear · Mind · Energy 3 · Might 2
Printings: SFD-090/221

> [Equip] :rb_energy_1::rb_rune_mind: (:rb_energy_1::rb_rune_mind:: Attach this to a unit you
> control.)
> :rb_energy_3::rb_rune_mind:, Banish this: Play all units banished with this, ignoring their
> costs. (Use only if unattached.)

Effect (given to the unit it is attached to):

> [Deathknell] — Banish me. (When I die, get the effect.)
-/
def SFD_090.meta : CardDef :=
  { id := ⟨"SFD-090"⟩,
    name := "The Zero Drive",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip, arg := .cost ⟨1, [.domain .mind]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- The Zero Drive: the effect is not written yet. -/
def SFD_090 : CardDef := SFD_090.meta

-- BEGIN GENERATED SFD-091
/--
**Buhru Captain** — Unit · Body · Energy 3 + Power 1 · Might 3
Printings: SFD-091/221

> When you play me, you may draw 1 or buff me. (To buff a unit, give it a +1 :rb_might: buff if
> it doesn't already have one.)
-/
def SFD_091.meta : CardDef :=
  { id := ⟨"SFD-091"⟩,
    name := "Buhru Captain",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨3, [.domain .body]⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Buhru Captain. -/
def SFD_091 : CardDef :=
  { SFD_091.meta with

    abilities := [.triggered (.onSelf .play)
      (.of [] (.may (.eitherOf (EffectList.ofList
        [.prim (.draw .you (.const 1)), .prim (.buff .self)])))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-092
/--
**Combat Chef** — Unit · Body · Energy 5 · Might 5
Printings: SFD-092/221

> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
-/
def SFD_092.meta : CardDef :=
  { id := ⟨"SFD-092"⟩,
    name := "Combat Chef",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.body],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Combat Chef. -/
def SFD_092 : CardDef :=
  { SFD_092.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-093
/--
**Dauntless Vanguard** — Unit · Body · Energy 4 + Power 1 · Might 4
Printings: SFD-093/221

> You may play me to an occupied enemy battlefield.
-/
def SFD_093.meta : CardDef :=
  { id := ⟨"SFD-093"⟩,
    name := "Dauntless Vanguard",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Demacia"⟩],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Dauntless Vanguard: the effect is not written yet. -/
def SFD_093 : CardDef := SFD_093.meta

-- BEGIN GENERATED SFD-094
/--
**Direwing** — Unit · Body · Energy 7 · Might 7
Printings: SFD-094/221

> I enter ready if you control another Dragon.
-/
def SFD_094.meta : CardDef :=
  { id := ⟨"SFD-094"⟩,
    name := "Direwing",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Demacia"⟩],
    domains := [.body],
    cost := some ⟨7, []⟩,
    might := some 7,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Direwing. -/
def SFD_094 : CardDef :=
  { SFD_094.meta with

    abilities := [.passive (.exists (Selector.all .friendly .anywhere [.tag ⟨"Dragon"⟩, .notSelf]))
      [.entersReady .self]],
    status := .drafted }

-- BEGIN GENERATED SFD-095
/--
**Doran's Blade** — Gear · Body · Energy 2 · Might 2
Printings: SFD-095/221

> [Equip] :rb_rune_body: (:rb_rune_body:: Attach this to a unit you control.)
-/
def SFD_095.meta : CardDef :=
  { id := ⟨"SFD-095"⟩,
    name := "Doran's Blade",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .body]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Doran's Blade. -/
def SFD_095 : CardDef :=
  { SFD_095.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-096
/--
**Laurent Bladekeeper** — Unit · Body · Energy 3 · Might 3
Printings: SFD-096/221

> Ganking (I can move from battlefield to battlefield.)
-/
def SFD_096.meta : CardDef :=
  { id := ⟨"SFD-096"⟩,
    name := "Laurent Bladekeeper",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Laurent Bladekeeper. -/
def SFD_096 : CardDef :=
  { SFD_096.meta with
    keywords := [{ keyword := .ganking }],
    status := .drafted }

-- BEGIN GENERATED SFD-097
/--
**Punch First** — Spell · Body · Energy 1 + Power 2
Printings: SFD-097/221

> [Action] (Play on your turn or in showdowns.)
> Give a unit +5 :rb_might: this turn.
-/
def SFD_097.meta : CardDef :=
  { id := ⟨"SFD-097"⟩,
    name := "Punch First",
    types := [.spell],
    domains := [.body],
    cost := some ⟨1, [.domain .body, .domain .body]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Punch First. -/
def SFD_097 : CardDef :=
  { SFD_097.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it (.const 5)) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED SFD-098
/--
**Sea Monkey** — Unit · Body · Energy 2 · Might 2
Printings: SFD-098/221

> You may pay :rb_energy_1: as an additional cost to play me.
> When you play me, if you paid the additional cost, buff me. (Give me a +1 :rb_might: buff if I
> don't already have one.)
-/
def SFD_098.meta : CardDef :=
  { id := ⟨"SFD-098"⟩,
    name := "Sea Monkey",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Sea Monkey. -/
def SFD_098 : CardDef :=
  { SFD_098.meta with
    additionalCost := some ⟨1, []⟩,
    abilities := [.triggered { Trigger.onSelf .play with condition := .paid }
        (.of []
        (.prim (.buff .self))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-099
/--
**Veteran Poro** — Unit · Body · Energy 2 · Might 2
Printings: SFD-099/221, UNL-223/219

> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
-/
def SFD_099.meta : CardDef :=
  { id := ⟨"SFD-099"⟩,
    name := "Veteran Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩, ⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩, ⟨"UNL"⟩] }
-- END GENERATED

/-- Veteran Poro. -/
def SFD_099 : CardDef :=
  { SFD_099.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-100
/--
**Yordle Explorer** — Unit · Body · Energy 4 · Might 4
Printings: SFD-100/221

> When you play a card with Power cost :rb_rune_rainbow::rb_rune_rainbow: or more, draw 1.
-/
def SFD_100.meta : CardDef :=
  { id := ⟨"SFD-100"⟩,
    name := "Yordle Explorer",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Yordle Explorer. -/
def SFD_100 : CardDef :=
  { SFD_100.meta with

    abilities := [.triggered
      { event := .play, subject := Selector.all .friendly .anywhere [.powerCost .ge (.const 2)] }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-101
/--
**Fae Dragon** — Unit · Body · Energy 7 + Power 1 · Might 7
Printings: SFD-101/221

> When you play me, buff up to four friendly units. (Give each a +1 :rb_might: buff if it
> doesn't have one.)
> When you spend a buff, play a Gold gear token exhausted.
-/
def SFD_101.meta : CardDef :=
  { id := ⟨"SFD-101"⟩,
    name := "Fae Dragon",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Dragon"⟩, ⟨"Bandle City"⟩],
    domains := [.body],
    cost := some ⟨7, [.domain .body]⟩,
    might := some 7,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Fae Dragon: the effect is not written yet. -/
def SFD_101 : CardDef := SFD_101.meta

-- BEGIN GENERATED SFD-102
/--
**Hexdrinker** — Gear · Body · Energy 2 · Might 1
Printings: SFD-102/221

> [Equip] :rb_rune_body: (:rb_rune_body:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
-/
def SFD_102.meta : CardDef :=
  { id := ⟨"SFD-102"⟩,
    name := "Hexdrinker",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .body]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Hexdrinker. -/
def SFD_102 : CardDef :=
  { SFD_102.meta with
    grants := [.passive .always [.keyword .self { keyword := .deflect }]],
    status := .drafted }

-- BEGIN GENERATED SFD-103
/--
**Jaull-Fish** — Unit · Body · Energy 7 + Power 2 · Might 6
Printings: SFD-103/221

> [Accelerate] (You may pay :rb_energy_1::rb_rune_body: as an additional cost to have me enter
> ready.)
> I cost :rb_energy_2: less for each of your [Mighty] units. (A unit is Mighty while it has 5+
> :rb_might:.)
-/
def SFD_103.meta : CardDef :=
  { id := ⟨"SFD-103"⟩,
    name := "Jaull-Fish",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨7, [.domain .body, .domain .body]⟩,
    might := some 6,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Jaull-Fish: the effect is not written yet. -/
def SFD_103 : CardDef := SFD_103.meta

-- BEGIN GENERATED SFD-104
/--
**Petricite Monument** — Gear · Body · Energy 2
Printings: SFD-104/221

> [Temporary] (Kill this at the start of its controller's Beginning Phase, before scoring.)
> Friendly units have [Deflect]. (Opponents must pay :rb_rune_rainbow: to choose them with a
> spell or ability.)
-/
def SFD_104.meta : CardDef :=
  { id := ⟨"SFD-104"⟩,
    name := "Petricite Monument",
    types := [.gear],
    domains := [.body],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .temporary }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Petricite Monument. -/
def SFD_104 : CardDef :=
  { SFD_104.meta with

    abilities := [.passive .always
      [.keyword (Selector.all .friendly .anywhere [.ofType .unit]) { keyword := .deflect }]],
    status := .drafted }

-- BEGIN GENERATED SFD-105
/--
**Ruin Runner** — Unit · Body · Energy 6 · Might 5
Printings: SFD-105/221

> I can't be chosen by enemy spells and abilities.
-/
def SFD_105.meta : CardDef :=
  { id := ⟨"SFD-105"⟩,
    name := "Ruin Runner",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.body],
    cost := some ⟨6, []⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Ruin Runner: the effect is not written yet. -/
def SFD_105 : CardDef := SFD_105.meta

-- BEGIN GENERATED SFD-106
/--
**Show of Strength** — Spell · Body · Energy 2 + Power 1
Printings: SFD-106/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Draw 1 for each of your [Mighty] units. (A unit is Mighty while it has 5+ :rb_might:.)
-/
def SFD_106.meta : CardDef :=
  { id := ⟨"SFD-106"⟩,
    name := "Show of Strength",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, [.domain .body]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Show of Strength. -/
def SFD_106 : CardDef :=
  { SFD_106.meta with

    spellEffect := some (.of [] (.prim (.draw .you
      (.count (Selector.all .friendly .anywhere [.ofType .unit, .mighty]))))),
    status := .drafted }

-- BEGIN GENERATED SFD-107
/--
**Strike Down** — Spell · Body · Energy 3 + Power 1
Printings: SFD-107/221

> Choose an equipped friendly unit. It deals damage equal to its Might to an enemy unit. Then
> detach an Equipment from it.
-/
def SFD_107.meta : CardDef :=
  { id := ⟨"SFD-107"⟩,
    name := "Strike Down",
    types := [.spell],
    domains := [.body],
    cost := some ⟨3, [.domain .body]⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Strike Down: the effect is not written yet. -/
def SFD_107 : CardDef := SFD_107.meta

-- BEGIN GENERATED SFD-108
/--
**Warmog's Armor** — Gear · Body · Energy 1 · Might 1
Printings: SFD-108/221

> [Equip] :rb_rune_body: (:rb_rune_body:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I conquer, buff me. (If I don't have a buff, I get a +1 :rb_might: buff.)
-/
def SFD_108.meta : CardDef :=
  { id := ⟨"SFD-108"⟩,
    name := "Warmog's Armor",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.body],
    cost := some ⟨1, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .body]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Warmog's Armor. -/
def SFD_108 : CardDef :=
  { SFD_108.meta with
    grants := [.triggered (.onSelf .conquer)
        (.of []
        (.prim (.buff .self))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-109
/--
**Akshan, Mischievous** — Unit · Body · Energy 4 · Might 4
Printings: SFD-109/221

> [Weaponmaster]
> You may pay :rb_rune_body::rb_rune_body: as an additional cost to play me.
> When you play me, if you paid the additional cost, move an enemy gear to your base. You
> control it until I leave the board. If it's an Equipment, attach it to me.
-/
def SFD_109.meta : CardDef :=
  { id := ⟨"SFD-109"⟩,
    name := "Akshan",
    subtitle := some "Mischievous",
    types := [.unit],
    tags := [⟨"Akshan"⟩, ⟨"Shurima"⟩, ⟨"Sentinel"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Akshan, Mischievous: the effect is not written yet. -/
def SFD_109 : CardDef := SFD_109.meta

-- BEGIN GENERATED SFD-110
/--
**Fiora, Peerless** — Unit · Body · Energy 3 + Power 1 · Might 3
Printings: SFD-110/221, SFD-110a/221

> When I attack or defend one on one, double my Might this combat.
-/
def SFD_110.meta : CardDef :=
  { id := ⟨"SFD-110"⟩,
    name := "Fiora",
    subtitle := some "Peerless",
    types := [.unit],
    tags := [⟨"Fiora"⟩, ⟨"Demacia"⟩],
    domains := [.body],
    cost := some ⟨3, [.domain .body]⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Fiora, Peerless: the effect is not written yet. -/
def SFD_110 : CardDef := SFD_110.meta

-- BEGIN GENERATED SFD-111
/--
**Here to Help** — Spell · Body · Energy 2 + Power 1
Printings: SFD-111/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> You may play a unit from hand to a battlefield you control, reducing its cost by
> :rb_energy_3:.
-/
def SFD_111.meta : CardDef :=
  { id := ⟨"SFD-111"⟩,
    name := "Here to Help",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, [.domain .body]⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Here to Help: the effect is not written yet. -/
def SFD_111 : CardDef := SFD_111.meta

-- BEGIN GENERATED SFD-112
/--
**Kato the Arm** — Unit · Body · Energy 4 + Power 1 · Might 3
Printings: SFD-112/221

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> When I move to a battlefield, give a friendly unit my keywords and +:rb_might: equal to my
> Might this turn.
-/
def SFD_112.meta : CardDef :=
  { id := ⟨"SFD-112"⟩,
    name := "Kato the Arm",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    might := some 3,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Kato the Arm: the effect is not written yet. -/
def SFD_112 : CardDef := SFD_112.meta

-- BEGIN GENERATED SFD-113
/--
**Lucian, Merciless** — Unit · Body · Energy 3 · Might 3
Printings: SFD-113/221, SFD-113a/221

> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
> The first time I conquer each turn, ready me.
-/
def SFD_113.meta : CardDef :=
  { id := ⟨"SFD-113"⟩,
    name := "Lucian",
    subtitle := some "Merciless",
    types := [.unit],
    tags := [⟨"Lucian"⟩, ⟨"Demacia"⟩, ⟨"Sentinel"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Lucian, Merciless: the effect is not written yet. -/
def SFD_113 : CardDef := SFD_113.meta

-- BEGIN GENERATED SFD-114
/--
**Marching Orders** — Spell · Body · Energy 3
Printings: SFD-114/221

> [Action] (Play on your turn or in showdowns.)
> [Repeat] :rb_energy_3: (You may pay the additional cost to repeat this spell's effect.)
> Choose a friendly unit anywhere and an enemy unit at a battlefield. They deal damage equal to
> their Mights to each other.
-/
def SFD_114.meta : CardDef :=
  { id := ⟨"SFD-114"⟩,
    name := "Marching Orders",
    types := [.spell],
    domains := [.body],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .action },
      { keyword := .repeat_, arg := .cost ⟨3, []⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Marching Orders. -/
def SFD_114 : CardDef :=
  { SFD_114.meta with

    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .enemy .atBattlefield [.ofType .unit]]
      (.seqOf [.prim (.deal (.slot 1) (.mightOf (.slot 0))),
        .prim (.deal (.slot 0) (.mightOf (.slot 1)))])),
    status := .drafted }

-- BEGIN GENERATED SFD-115
/--
**Trinity Force** — Gear · Body · Energy 4 · Might 2
Printings: SFD-115/221

> [Equip] :rb_rune_body: (:rb_rune_body:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I hold, score 1 point.
-/
def SFD_115.meta : CardDef :=
  { id := ⟨"SFD-115"⟩,
    name := "Trinity Force",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .body]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Trinity Force. -/
def SFD_115 : CardDef :=
  { SFD_115.meta with

    grants := [.triggered (.onSelf .hold) (.of [] (.prim (.score .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-116
/--
**Yone, Blademaster** — Unit · Body · Energy 5 + Power 1 · Might 5
Printings: SFD-116/221, SFD-233*/221, SFD-233/221, RAD-181/167

> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
> When I conquer an open battlefield, deal damage equal to my Might to an enemy unit in a base.
-/
def SFD_116.meta : CardDef :=
  { id := ⟨"SFD-116"⟩,
    name := "Yone",
    subtitle := some "Blademaster",
    types := [.unit],
    tags := [⟨"Yone"⟩, ⟨"Ionia"⟩, ⟨"Demon"⟩],
    domains := [.body],
    cost := some ⟨5, [.domain .body]⟩,
    might := some 5,
    keywords := [{ keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Yone, Blademaster: the effect is not written yet. -/
def SFD_116 : CardDef := SFD_116.meta

-- BEGIN GENERATED SFD-117
/--
**Ancient Henge** — Gear · Body · Energy 2 + Power 1
Printings: SFD-117/221

> :rb_exhaust:: [Reaction] — Pay any amount of Energy to [Add] that much :rb_rune_rainbow:.
> (Abilities that add resources can't be reacted to.)
-/
def SFD_117.meta : CardDef :=
  { id := ⟨"SFD-117"⟩,
    name := "Ancient Henge",
    types := [.gear],
    domains := [.body],
    cost := some ⟨2, [.domain .body]⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Ancient Henge: the effect is not written yet. -/
def SFD_117 : CardDef := SFD_117.meta

-- BEGIN GENERATED SFD-118
/--
**Boneshiver** — Gear · Body · Energy 3 · Might 2
Printings: SFD-118/221

> [Equip] :rb_energy_1::rb_rune_body: (:rb_energy_1::rb_rune_body:: Attach this to a unit you
> control.)

Effect (given to the unit it is attached to):

> When I conquer, channel 1 rune exhausted.
-/
def SFD_118.meta : CardDef :=
  { id := ⟨"SFD-118"⟩,
    name := "Boneshiver",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip, arg := .cost ⟨1, [.domain .body]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Boneshiver. -/
def SFD_118 : CardDef :=
  { SFD_118.meta with
    grants := [.triggered (.onSelf .conquer)
        (.of []
        (.prim (.channel .you (.const 0) (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-119
/--
**Jax, Unrelenting** — Unit · Body · Energy 4 + Power 1 · Might 3
Printings: SFD-119/221, SFD-119a/221

> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
> When you attach an Equipment to me, you may pay :rb_energy_1: to draw 1.
-/
def SFD_119.meta : CardDef :=
  { id := ⟨"SFD-119"⟩,
    name := "Jax",
    subtitle := some "Unrelenting",
    types := [.unit],
    tags := [⟨"Jax"⟩, ⟨"Icathia"⟩],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    might := some 3,
    keywords := [{ keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Jax, Unrelenting: the effect is not written yet. -/
def SFD_119 : CardDef := SFD_119.meta

-- BEGIN GENERATED SFD-120
/--
**Sivir, Ambitious** — Unit · Body · Energy 6 + Power 3 · Might 7
Printings: SFD-120/221, SFD-120a/221

> [Deflect 2] (Opponents must pay :rb_rune_rainbow::rb_rune_rainbow: to choose me with a spell
> or Ability.)
> When I conquer after an attack, if you assigned 5 or more excess damage to enemy units, you
> may deal that much to an enemy unit.
-/
def SFD_120.meta : CardDef :=
  { id := ⟨"SFD-120"⟩,
    name := "Sivir",
    subtitle := some "Ambitious",
    types := [.unit],
    tags := [⟨"Sivir"⟩, ⟨"Shurima"⟩],
    domains := [.body],
    cost := some ⟨6, [.domain .body, .domain .body, .domain .body]⟩,
    might := some 7,
    keywords := [{ keyword := .deflect, arg := .amount 2 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Sivir, Ambitious: the effect is not written yet. -/
def SFD_120 : CardDef := SFD_120.meta

-- BEGIN GENERATED SFD-121
/--
**Black Market Broker** — Unit · Chaos · Energy 3 · Might 3
Printings: SFD-121/221

> When you play a card from face down, play a Gold gear token exhausted.
-/
def SFD_121.meta : CardDef :=
  { id := ⟨"SFD-121"⟩,
    name := "Black Market Broker",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Black Market Broker: the effect is not written yet. -/
def SFD_121 : CardDef := SFD_121.meta

-- BEGIN GENERATED SFD-122
/--
**Called Shot** — Spell · Chaos · Energy 0 + Power 1
Printings: SFD-122/221

> [Action] (Play on your turn or in showdowns.)
> [Repeat] :rb_rune_chaos: (You may pay the additional cost to repeat this spell's effect.)
> Look at the top 2 cards of your Main Deck. Draw one and recycle the other.
-/
def SFD_122.meta : CardDef :=
  { id := ⟨"SFD-122"⟩,
    name := "Called Shot",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨0, [.domain .chaos]⟩,
    keywords := [{ keyword := .action },
      { keyword := .repeat_, arg := .cost ⟨0, [.domain .chaos]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Called Shot: the effect is not written yet. -/
def SFD_122 : CardDef := SFD_122.meta

-- BEGIN GENERATED SFD-123
/--
**Corrupt Enforcer** — Unit · Chaos · Energy 3 + Power 1 · Might 4
Printings: SFD-123/221

> When I move to a battlefield, discard 1.
> When I win a combat, draw 1.
-/
def SFD_123.meta : CardDef :=
  { id := ⟨"SFD-123"⟩,
    name := "Corrupt Enforcer",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Corrupt Enforcer. -/
def SFD_123 : CardDef :=
  { SFD_123.meta with

    abilities := [.triggered { event := .move, condition := .matches .self .onBattlefield }
        (.of [] (.prim (.discard .you (.const 1)))) .unlimited,
      .triggered (.onSelf .winCombat) (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-124
/--
**Doran's Ring** — Gear · Chaos · Energy 1 · Might 1
Printings: SFD-124/221

> [Equip] :rb_rune_chaos: (:rb_rune_chaos:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I conquer, discard 1, then draw 1.
-/
def SFD_124.meta : CardDef :=
  { id := ⟨"SFD-124"⟩,
    name := "Doran's Ring",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .chaos]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Doran's Ring. -/
def SFD_124 : CardDef :=
  { SFD_124.meta with
    grants := [.triggered (.onSelf .conquer)
        (.of []
        (.seqOf [.prim (.discard .you (.const 1)),
          .prim (.draw .you (.const 1))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-125
/--
**Fae Porter** — Unit · Chaos · Energy 4 · Might 4
Printings: SFD-125/221

> When I move to a battlefield, you may pay :rb_rune_chaos: to move a unit you control to the
> same battlefield.
-/
def SFD_125.meta : CardDef :=
  { id := ⟨"SFD-125"⟩,
    name := "Fae Porter",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Fae Porter: the effect is not written yet. -/
def SFD_125 : CardDef := SFD_125.meta

-- BEGIN GENERATED SFD-126
/--
**Loyal Pup** — Unit · Chaos · Energy 3 · Might 3
Printings: SFD-126/221

> When you defend at a battlefield, you may move me there.
-/
def SFD_126.meta : CardDef :=
  { id := ⟨"SFD-126"⟩,
    name := "Loyal Pup",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Bandle City"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Loyal Pup: the effect is not written yet. -/
def SFD_126 : CardDef := SFD_126.meta

-- BEGIN GENERATED SFD-127
/--
**Master Bingwen** — Unit · Chaos · Energy 6 · Might 6
Printings: SFD-127/221

> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
-/
def SFD_127.meta : CardDef :=
  { id := ⟨"SFD-127"⟩,
    name := "Master Bingwen",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨6, []⟩,
    might := some 6,
    keywords := [{ keyword := .weaponmaster }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Master Bingwen. -/
def SFD_127 : CardDef :=
  { SFD_127.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-128
/--
**Overzealous Fan** — Unit · Chaos · Energy 2 · Might 2
Printings: SFD-128/221

> When I defend, you may kill me to move an attacking unit to its base.
-/
def SFD_128.meta : CardDef :=
  { id := ⟨"SFD-128"⟩,
    name := "Overzealous Fan",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Overzealous Fan: the effect is not written yet. -/
def SFD_128 : CardDef := SFD_128.meta

-- BEGIN GENERATED SFD-129
/--
**Temptation** — Spell · Chaos · Energy 2
Printings: SFD-129/221

> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Move an enemy unit to a location where there's a unit with the same controller.
-/
def SFD_129.meta : CardDef :=
  { id := ⟨"SFD-129"⟩,
    name := "Temptation",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Temptation: the effect is not written yet. -/
def SFD_129 : CardDef := SFD_129.meta

-- BEGIN GENERATED SFD-130
/--
**Treasure Hunter** — Unit · Chaos · Energy 2 · Might 1
Printings: SFD-130/221

> When I move, play a Gold gear token exhausted.
-/
def SFD_130.meta : CardDef :=
  { id := ⟨"SFD-130"⟩,
    name := "Treasure Hunter",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 1,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Treasure Hunter. -/
def SFD_130 : CardDef :=
  { SFD_130.meta with
    abilities := [.triggered (.onSelf .move)
        (.of []
        (.prim (.create "Gold" (.const 1) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-131
/--
**Ancient Warmonger** — Unit · Chaos · Energy 5 · Might 4
Printings: SFD-131/221

> [Accelerate] (You may pay :rb_energy_1::rb_rune_chaos: as an additional cost to have me enter
> ready.)
> I have [Assault] equal to the number of enemy units here. (+1 :rb_might: while I'm an attacker
> for each instance of Assault.)
-/
def SFD_131.meta : CardDef :=
  { id := ⟨"SFD-131"⟩,
    name := "Ancient Warmonger",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Noxus"⟩],
    domains := [.chaos],
    cost := some ⟨5, []⟩,
    might := some 4,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Ancient Warmonger: the effect is not written yet. -/
def SFD_131 : CardDef := SFD_131.meta

-- BEGIN GENERATED SFD-132
/--
**Beast Below** — Unit · Chaos · Energy 7 + Power 2 · Might 8
Printings: SFD-132/221

> When you play me, return another friendly unit and an enemy unit to their owners' hands.
-/
def SFD_132.meta : CardDef :=
  { id := ⟨"SFD-132"⟩,
    name := "Beast Below",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨7, [.domain .chaos, .domain .chaos]⟩,
    might := some 8,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Beast Below. -/
def SFD_132 : CardDef :=
  { SFD_132.meta with

    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .notSelf],
          .targetOf .one .enemy .anywhere [.ofType .unit]]
        (.seqOf [.prim (.returnToHand (.slot 0)), .prim (.returnToHand (.slot 1))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-133
/--
**Boots of Swiftness** — Gear · Chaos · Energy 3 · Might 2
Printings: SFD-133/221

> [Equip] :rb_rune_chaos: (:rb_rune_chaos:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Ganking] (I can move from battlefield to battlefield.)
-/
def SFD_133.meta : CardDef :=
  { id := ⟨"SFD-133"⟩,
    name := "Boots of Swiftness",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .chaos]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Boots of Swiftness. -/
def SFD_133 : CardDef :=
  { SFD_133.meta with
    grants := [.passive .always [.keyword .self { keyword := .ganking }]],
    status := .drafted }

-- BEGIN GENERATED SFD-134
/--
**Cull** — Gear · Chaos · Energy 1 · Might 1
Printings: SFD-134/221

> [Equip] :rb_rune_chaos: (:rb_rune_chaos:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I conquer, play a Gold gear token exhausted.
-/
def SFD_134.meta : CardDef :=
  { id := ⟨"SFD-134"⟩,
    name := "Cull",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .chaos]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Cull. -/
def SFD_134 : CardDef :=
  { SFD_134.meta with
    grants := [.triggered (.onSelf .conquer)
        (.of []
        (.prim (.create "Gold" (.const 1) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-135
/--
**Factory Recall** — Spell · Chaos · Energy 1
Printings: SFD-135/221

> [Action] (Play on your turn or in showdowns.)
> Return a gear to its owner's hand.
-/
def SFD_135.meta : CardDef :=
  { id := ⟨"SFD-135"⟩,
    name := "Factory Recall",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Factory Recall. -/
def SFD_135 : CardDef :=
  { SFD_135.meta with

    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .gear]]
      (.prim (.returnToHand (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED SFD-136
/--
**Hard Bargain** — Spell · Chaos · Energy 2
Printings: SFD-136/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Counter a spell unless its controller pays :rb_energy_2:.
-/
def SFD_136.meta : CardDef :=
  { id := ⟨"SFD-136"⟩,
    name := "Hard Bargain",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction },
      { keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Hard Bargain: the effect is not written yet. -/
def SFD_136 : CardDef := SFD_136.meta

-- BEGIN GENERATED SFD-137
/--
**Harpoon Squad** — Unit · Chaos · Energy 4 · Might 4
Printings: SFD-137/221

> When I move from a battlefield, give me +2 :rb_might: this turn.
-/
def SFD_137.meta : CardDef :=
  { id := ⟨"SFD-137"⟩,
    name := "Harpoon Squad",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Harpoon Squad: the effect is not written yet. -/
def SFD_137 : CardDef := SFD_137.meta

-- BEGIN GENERATED SFD-138
/--
**Windsinger** — Unit · Chaos · Energy 2 · Might 1
Printings: SFD-138/221

> Hidden (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me, you may return another unit at a battlefield with 3 :rb_might: or less to
> its owner's hand.
-/
def SFD_138.meta : CardDef :=
  { id := ⟨"SFD-138"⟩,
    name := "Windsinger",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 1,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Windsinger. -/
def SFD_138 : CardDef :=
  { SFD_138.meta with

    keywords := [{ keyword := .hidden }],
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .atBattlefield [.ofType .unit, .notSelf, .might .le (.const 3)]]
        (.may (.prim (.returnToHand (.slot 0))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-139
/--
**Edge of Night** — Gear · Chaos · Energy 3 · Might 2
Printings: SFD-139/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play this from face down, attach it to a unit you control here.
> [Equip] :rb_rune_chaos: (:rb_rune_chaos:: Attach this to a unit you control.)
-/
def SFD_139.meta : CardDef :=
  { id := ⟨"SFD-139"⟩,
    name := "Edge of Night",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .hidden },
      { keyword := .equip, arg := .cost ⟨0, [.domain .chaos]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Edge of Night: the effect is not written yet. -/
def SFD_139 : CardDef := SFD_139.meta

-- BEGIN GENERATED SFD-140
/--
**Fizz, Trickster** — Unit · Chaos · Energy 3 + Power 1 · Might 3
Printings: SFD-140/221

> When you play me, you may play a spell from your trash with Energy cost no more than
> :rb_energy_3:, ignoring its Energy cost. Recycle that spell after you play it. (You must still
> pay its Power cost.)
-/
def SFD_140.meta : CardDef :=
  { id := ⟨"SFD-140"⟩,
    name := "Fizz",
    subtitle := some "Trickster",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Fizz"⟩, ⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Fizz, Trickster: the effect is not written yet. -/
def SFD_140 : CardDef := SFD_140.meta

-- BEGIN GENERATED SFD-141
/--
**Irelia, Graceful** — Unit · Chaos · Energy 4 + Power 1 · Might 4
Printings: SFD-141/221, SFD-141a/221

> Your spells that choose me cost :rb_energy_1: or :rb_rune_rainbow: less.
-/
def SFD_141.meta : CardDef :=
  { id := ⟨"SFD-141"⟩,
    name := "Irelia",
    subtitle := some "Graceful",
    types := [.unit],
    tags := [⟨"Irelia"⟩, ⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Irelia, Graceful: the effect is not written yet. -/
def SFD_141 : CardDef := SFD_141.meta

-- BEGIN GENERATED SFD-142
/--
**Jae Medarda** — Unit · Chaos · Energy 5 + Power 2 · Might 5
Printings: SFD-142/221

> When you choose me with a spell, draw 1.
-/
def SFD_142.meta : CardDef :=
  { id := ⟨"SFD-142"⟩,
    name := "Jae Medarda",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.chaos],
    cost := some ⟨5, [.domain .chaos, .domain .chaos]⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Jae Medarda: the effect is not written yet. -/
def SFD_142 : CardDef := SFD_142.meta

-- BEGIN GENERATED SFD-143
/--
**Sivir, Mercenary** — Unit · Chaos · Energy 4 + Power 1 · Might 4
Printings: SFD-143/221, SFD-143a/221

> [Accelerate] (You may pay :rb_energy_1::rb_rune_chaos: as an additional cost to have me enter
> ready.)
> If you've spent at least :rb_rune_rainbow::rb_rune_rainbow: this turn, I have +2 :rb_might:
> and [Ganking]. (I can move from battlefield to battlefield.)
-/
def SFD_143.meta : CardDef :=
  { id := ⟨"SFD-143"⟩,
    name := "Sivir",
    subtitle := some "Mercenary",
    types := [.unit],
    tags := [⟨"Sivir"⟩, ⟨"Shurima"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    might := some 4,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Sivir, Mercenary: the effect is not written yet. -/
def SFD_143 : CardDef := SFD_143.meta

-- BEGIN GENERATED SFD-144
/--
**Spirit Wheel** — Gear · Chaos · Energy 2
Printings: SFD-144/221

> When you choose a friendly unit, you may pay :rb_energy_1: and exhaust this to draw 1.
-/
def SFD_144.meta : CardDef :=
  { id := ⟨"SFD-144"⟩,
    name := "Spirit Wheel",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Spirit Wheel: the effect is not written yet. -/
def SFD_144 : CardDef := SFD_144.meta

-- BEGIN GENERATED SFD-145
/--
**Switcheroo** — Spell · Chaos · Energy 2 + Power 2
Printings: SFD-145/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Swap the Mights of two units at the same battlefield this turn.
-/
def SFD_145.meta : CardDef :=
  { id := ⟨"SFD-145"⟩,
    name := "Switcheroo",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, [.domain .chaos, .domain .chaos]⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Switcheroo: the effect is not written yet. -/
def SFD_145 : CardDef := SFD_145.meta

-- BEGIN GENERATED SFD-146
/--
**Vex, Cheerless** — Unit · Chaos · Energy 5 + Power 1 · Might 5
Printings: SFD-146/221

> While I'm in combat, friendly spells cost :rb_energy_1::rb_rune_rainbow: less to a minimum of
> :rb_energy_1:, and enemy spells cost :rb_energy_1::rb_rune_rainbow: more.
-/
def SFD_146.meta : CardDef :=
  { id := ⟨"SFD-146"⟩,
    name := "Vex",
    subtitle := some "Cheerless",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Vex"⟩, ⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨5, [.domain .chaos]⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Vex, Cheerless: the effect is not written yet. -/
def SFD_146 : CardDef := SFD_146.meta

-- BEGIN GENERATED SFD-147
/--
**Downwell** — Spell · Chaos · Energy 8 + Power 2
Printings: SFD-147/221

> Return all units and gear to their owners' hands.
-/
def SFD_147.meta : CardDef :=
  { id := ⟨"SFD-147"⟩,
    name := "Downwell",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨8, [.domain .chaos, .domain .chaos]⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Downwell. -/
def SFD_147 : CardDef :=
  { SFD_147.meta with

    spellEffect := some (.of [] (.seqOf [
      .prim (.returnToHand (Selector.all .any .anywhere [.ofType .unit])),
      .prim (.returnToHand (Selector.all .any .anywhere [.ofType .gear]))])),
    status := .drafted }

-- BEGIN GENERATED SFD-148
/--
**Draven, Audacious** — Unit · Chaos · Energy 6 + Power 1 · Might 6
Printings: SFD-148/221, SFD-148a/221

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> The first time I win a combat each turn, you score 1 point.
> When I die in combat, choose an opponent. They score 1 point.
-/
def SFD_148.meta : CardDef :=
  { id := ⟨"SFD-148"⟩,
    name := "Draven",
    subtitle := some "Audacious",
    types := [.unit],
    tags := [⟨"Draven"⟩, ⟨"Noxus"⟩],
    domains := [.chaos],
    cost := some ⟨6, [.domain .chaos]⟩,
    might := some 6,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Draven, Audacious: the effect is not written yet. -/
def SFD_148 : CardDef := SFD_148.meta

-- BEGIN GENERATED SFD-149
/--
**Ezreal, Prodigy** — Unit · Chaos · Energy 3 + Power 1 · Might 3
Printings: SFD-149/221, SFD-149a/221, VEN-SP5/006

> When you play me, discard 1, then draw 2.
> Optional additional costs you pay cost :rb_energy_1: or :rb_rune_rainbow: less.
-/
def SFD_149.meta : CardDef :=
  { id := ⟨"SFD-149"⟩,
    name := "Ezreal",
    subtitle := some "Prodigy",
    types := [.unit],
    tags := [⟨"Ezreal"⟩, ⟨"Piltover"⟩],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    might := some 3,
    sets := [⟨"SFD"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Ezreal, Prodigy: the effect is not written yet. -/
def SFD_149 : CardDef := SFD_149.meta

-- BEGIN GENERATED SFD-150
/--
**Last Rites** — Gear · Chaos · Energy 3 · Might 2
Printings: SFD-150/221

> [Equip] — :rb_rune_chaos:, Recycle 2 cards from your trash (Pay the cost: Attach this to a
> unit you control.)

Effect (given to the unit it is attached to):

> When I conquer or hold, you may play a unit from your trash. (You still pay its costs.)
-/
def SFD_150.meta : CardDef :=
  { id := ⟨"SFD-150"⟩,
    name := "Last Rites",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .equip }],
    sets := [⟨"SFD"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Last Rites: the effect is not written yet. -/
def SFD_150 : CardDef := SFD_150.meta

-- BEGIN GENERATED SFD-151
/--
**Bonds of Strength** — Spell · Order · Energy 2
Printings: SFD-151/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> [Repeat] :rb_energy_2: (You may pay the additional cost to repeat this spell's effect.)
> Give two friendly units each +1 :rb_might: this turn.
-/
def SFD_151.meta : CardDef :=
  { id := ⟨"SFD-151"⟩,
    name := "Bonds of Strength",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction },
      { keyword := .repeat_, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Bonds of Strength. -/
def SFD_151 : CardDef :=
  { SFD_151.meta with

    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .friendly .anywhere [.ofType .unit]]
      (.ifThen (.matches (.slot 1) (.not (.sameAs (.slot 0))))
        (.seqOf [.grant (.slot 0) (.mightPlus .it (.const 1)) .thisTurn,
          .grant (.slot 1) (.mightPlus .it (.const 1)) .thisTurn]) .nop)),
    status := .drafted }

-- BEGIN GENERATED SFD-152
/--
**Eminent Benefactor** — Unit · Order · Energy 6 · Might 5
Printings: SFD-152/221

> When I hold, play two Gold gear tokens exhausted.
-/
def SFD_152.meta : CardDef :=
  { id := ⟨"SFD-152"⟩,
    name := "Eminent Benefactor",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.order],
    cost := some ⟨6, []⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Eminent Benefactor. -/
def SFD_152 : CardDef :=
  { SFD_152.meta with
    abilities := [.triggered (.onSelf .hold)
        (.of []
        (.prim (.create "Gold" (.const 2) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-153
/--
**Eye of the Herald** — Gear · Order · Energy 1 · Might 0
Printings: SFD-153/221

> [Equip] :rb_rune_order: (:rb_rune_order:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I move, play a 1 :rb_might: Recruit unit token here.
-/
def SFD_153.meta : CardDef :=
  { id := ⟨"SFD-153"⟩,
    name := "Eye of the Herald",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.order],
    cost := some ⟨1, []⟩,
    might := some 0,
    mightBonus := some 0,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .order]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Eye of the Herald. -/
def SFD_153 : CardDef :=
  { SFD_153.meta with
    grants := [.triggered (.onSelf .move)
        (.of []
        (.prim (.create "Recruit" (.const 1) .here false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-154
/--
**Guards!** — Spell · Order · Energy 3
Printings: SFD-154/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> Play a 2 :rb_might: Sand Soldier unit token. You may pay :rb_rune_order: to ready it.
-/
def SFD_154.meta : CardDef :=
  { id := ⟨"SFD-154"⟩,
    name := "Guards!",
    types := [.spell],
    domains := [.order],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Guards!. -/
def SFD_154 : CardDef :=
  { SFD_154.meta with

    spellEffect := some (.of []
      (.ifThen (.canPay ⟨0, [.domain .order]⟩)
        (.eitherOf (EffectList.ofList
          [.seqOf [.prim (.pay ⟨0, [.domain .order]⟩),
            .prim (.create "Sand Soldier" (.const 1) .atBase true)],
           .prim (.create "Sand Soldier" (.const 1) .atBase false)]))
        (.prim (.create "Sand Soldier" (.const 1) .atBase false)))),
    status := .drafted }

-- BEGIN GENERATED SFD-155
/--
**Honest Broker** — Unit · Order · Energy 2 · Might 2
Printings: SFD-155/221

> [Deathknell] — Play a Gold gear token exhausted. (When I die, get the effect.)
-/
def SFD_155.meta : CardDef :=
  { id := ⟨"SFD-155"⟩,
    name := "Honest Broker",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Honest Broker. -/
def SFD_155 : CardDef :=
  { SFD_155.meta with
    abilities := [.triggered (.onSelf .die)
        (.of []
        (.prim (.create "Gold" (.const 1) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-156
/--
**Laurent Duelist** — Unit · Order · Energy 4 · Might 3
Printings: SFD-156/221

> [Assault 2] (+2 :rb_might: while I'm an attacker.)
-/
def SFD_156.meta : CardDef :=
  { id := ⟨"SFD-156"⟩,
    name := "Laurent Duelist",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 3,
    keywords := [{ keyword := .assault, arg := .amount 2 }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Laurent Duelist. -/
def SFD_156 : CardDef :=
  { SFD_156.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-157
/--
**Royal Guard** — Unit · Order · Energy 4 · Might 2
Printings: SFD-157/221

> When you play me, play a 2 :rb_might: Sand Soldier unit token here.
-/
def SFD_157.meta : CardDef :=
  { id := ⟨"SFD-157"⟩,
    name := "Royal Guard",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Royal Guard. -/
def SFD_157 : CardDef :=
  { SFD_157.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.create "Sand Soldier" (.const 1) .here false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-158
/--
**Sandshifter** — Unit · Order · Energy 5 + Power 2 · Might 6
Printings: SFD-158/221

> When you play me, kill an enemy unit with 3 :rb_might: or less.
-/
def SFD_158.meta : CardDef :=
  { id := ⟨"SFD-158"⟩,
    name := "Sandshifter",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order, .domain .order]⟩,
    might := some 6,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Sandshifter. -/
def SFD_158 : CardDef :=
  { SFD_158.meta with

    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .enemy .anywhere [.ofType .unit, .might .le (.const 3)]]
        (.prim (.kill (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-159
/--
**Trusty Ramhound** — Unit · Order · Energy 2 · Might 2
Printings: SFD-159/221

> While you have another unit here, I have +1 :rb_might:.
-/
def SFD_159.meta : CardDef :=
  { id := ⟨"SFD-159"⟩,
    name := "Trusty Ramhound",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Elite"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Trusty Ramhound. -/
def SFD_159 : CardDef :=
  { SFD_159.meta with

    abilities := [.passive
      (.exists (Selector.all .friendly .anywhere [.ofType .unit, .notSelf, .at_ .self]))
      [.mightPlus .self (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED SFD-160
/--
**Zaun Punk** — Unit · Order · Energy 3 · Might 3
Printings: SFD-160/221

> You may kill a friendly gear as an additional cost to play me.
> When you play me, if you paid the additional cost, kill a gear.
-/
def SFD_160.meta : CardDef :=
  { id := ⟨"SFD-160"⟩,
    name := "Zaun Punk",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Zaun Punk: the effect is not written yet. -/
def SFD_160 : CardDef := SFD_160.meta

-- BEGIN GENERATED SFD-161
/--
**B.F. Sword** — Gear · Order · Energy 4 · Might 3
Printings: SFD-161/221

> [Equip] :rb_rune_order: (:rb_rune_order:: Attach this to a unit you control.)
-/
def SFD_161.meta : CardDef :=
  { id := ⟨"SFD-161"⟩,
    name := "B.F. Sword",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 3,
    mightBonus := some 3,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .order]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- B.F. Sword. -/
def SFD_161 : CardDef :=
  { SFD_161.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-162
/--
**Blood Money** — Spell · Order · Energy 2
Printings: SFD-162/221

> [Action] (Play on your turn or in showdowns.)
> Kill a unit at a battlefield with 2 :rb_might: or less. If it was an enemy unit, play a Gold
> gear token exhausted. If it was a friendly unit, play two Gold gear tokens exhausted.
-/
def SFD_162.meta : CardDef :=
  { id := ⟨"SFD-162"⟩,
    name := "Blood Money",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Blood Money. -/
def SFD_162 : CardDef :=
  { SFD_162.meta with

    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit, .might .le (.const 2)]]
      (.ifThen (.exists (Selector.all .friendly .anywhere [.sameAs (.slot 0)]))
        (.seqOf [.prim (.kill (.slot 0)), .prim (.create "Gold" (.const 2) .atBase false)])
        (.ifThen (.exists (Selector.all .enemy .anywhere [.sameAs (.slot 0)]))
          (.seqOf [.prim (.kill (.slot 0)), .prim (.create "Gold" (.const 1) .atBase false)])
          .nop))),
    status := .drafted }

-- BEGIN GENERATED SFD-163
/--
**Deathgrip** — Spell · Order · Energy 2
Printings: SFD-163/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Kill a friendly unit to give +:rb_might: equal to its Might to another friendly unit this
> turn. Draw 1.
-/
def SFD_163.meta : CardDef :=
  { id := ⟨"SFD-163"⟩,
    name := "Deathgrip",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Deathgrip. -/
def SFD_163 : CardDef :=
  { SFD_163.meta with

    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .friendly .anywhere [.ofType .unit]]
      (.ifThen (.matches (.slot 1) (.not (.sameAs (.slot 0))))
        (.seqOf [.grant (.slot 1) (.mightPlus .it (.mightOf (.slot 0))) .thisTurn,
          .prim (.kill (.slot 0)), .prim (.draw .you (.const 1))]) .nop)),
    status := .drafted }

-- BEGIN GENERATED SFD-164
/--
**Drag Under** — Spell · Order · Energy 5 + Power 1
Printings: SFD-164/221

> [Action] (Play on your turn or in showdowns.)
> I cost :rb_energy_2: less to play from anywhere other than your hand.
> Kill a unit at a battlefield.
-/
def SFD_164.meta : CardDef :=
  { id := ⟨"SFD-164"⟩,
    name := "Drag Under",
    types := [.spell],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Drag Under: the effect is not written yet. -/
def SFD_164 : CardDef := SFD_164.meta

-- BEGIN GENERATED SFD-165
/--
**Glasc Mixologist** — Unit · Order · Energy 5 + Power 1 · Might 5
Printings: SFD-165/221

> [Deathknell] — You may play a unit with cost no more than :rb_energy_3: and no more than
> :rb_rune_rainbow: from your trash, ignoring its cost. (When I die, get the effect.)
-/
def SFD_165.meta : CardDef :=
  { id := ⟨"SFD-165"⟩,
    name := "Glasc Mixologist",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 5,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Glasc Mixologist: the effect is not written yet. -/
def SFD_165 : CardDef := SFD_165.meta

-- BEGIN GENERATED SFD-166
/--
**Rally the Troops** — Spell · Order · Energy 2
Printings: SFD-166/221

> [Action] (Play on your turn or in showdowns.)
> When a friendly unit is played this turn, buff it. (If it doesn't have a buff, it gets a +1
> :rb_might: buff.)
> Draw 1.
-/
def SFD_166.meta : CardDef :=
  { id := ⟨"SFD-166"⟩,
    name := "Rally the Troops",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Rally the Troops: the effect is not written yet. -/
def SFD_166 : CardDef := SFD_166.meta

-- BEGIN GENERATED SFD-167
/--
**Unsung Hero** — Unit · Order · Energy 2 · Might 2
Printings: SFD-167/221

> [Deathknell] — If I was [Mighty], draw 2. (When I die, get the effect. I'm Mighty while I have
> 5+ :rb_might:.)
-/
def SFD_167.meta : CardDef :=
  { id := ⟨"SFD-167"⟩,
    name := "Unsung Hero",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Unsung Hero: the effect is not written yet. -/
def SFD_167 : CardDef := SFD_167.meta

-- BEGIN GENERATED SFD-168
/--
**Vanguard Armory** — Gear · Order · Energy 7 + Power 1
Printings: SFD-168/221

> :rb_exhaust:: Play three 1 :rb_might: Recruit unit tokens. (You may play them to different
> locations.)
-/
def SFD_168.meta : CardDef :=
  { id := ⟨"SFD-168"⟩,
    name := "Vanguard Armory",
    types := [.gear],
    domains := [.order],
    cost := some ⟨7, [.domain .order]⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Vanguard Armory. -/
def SFD_168 : CardDef :=
  { SFD_168.meta with
    abilities := [.activated [.exhaustSelf] .normal
        (.of []
        (.prim (.create "Recruit" (.const 3) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-169
/--
**Altar of Memories** — Gear · Order · Energy 2
Printings: SFD-169/221

> When a friendly unit dies, you may exhaust me to draw 1, then put a card from your hand on the
> top or bottom of your Main Deck.
-/
def SFD_169.meta : CardDef :=
  { id := ⟨"SFD-169"⟩,
    name := "Altar of Memories",
    types := [.gear],
    domains := [.order],
    cost := some ⟨2, []⟩,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Altar of Memories: the effect is not written yet. -/
def SFD_169 : CardDef := SFD_169.meta

-- BEGIN GENERATED SFD-170
/--
**Rek'Sai, Swarm Queen** — Unit · Order · Energy 5 + Power 1 · Might 5
Printings: SFD-170/221, SFD-170a/221

> When I attack, you may reveal the top 2 cards of your Main Deck. You may play one. Then
> recycle the rest. If the played card is a unit, you may play it here.
-/
def SFD_170.meta : CardDef :=
  { id := ⟨"SFD-170"⟩,
    name := "Rek'Sai",
    subtitle := some "Swarm Queen",
    types := [.unit],
    tags := [⟨"Rek'Sai"⟩, ⟨"The Void"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Rek'Sai, Swarm Queen: the effect is not written yet. -/
def SFD_170 : CardDef := SFD_170.meta

-- BEGIN GENERATED SFD-171
/--
**Renata Glasc, Industrialist** — Unit · Order · Energy 4 + Power 1 · Might 4
Printings: SFD-171/221, SFD-171a/221

> Your tokens enter ready.
-/
def SFD_171.meta : CardDef :=
  { id := ⟨"SFD-171"⟩,
    name := "Renata Glasc",
    subtitle := some "Industrialist",
    types := [.unit],
    tags := [⟨"Renata Glasc"⟩, ⟨"Zaun"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order]⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Renata Glasc, Industrialist: the effect is not written yet. -/
def SFD_171 : CardDef := SFD_171.meta

-- BEGIN GENERATED SFD-172
/--
**Sacred Shears** — Gear · Order · Energy 2 + Power 1 · Might 1
Printings: SFD-172/221

> [Equip] :rb_rune_order: (:rb_rune_order:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Deathknell] — Draw 1. (When I die, get the effect.)
-/
def SFD_172.meta : CardDef :=
  { id := ⟨"SFD-172"⟩,
    name := "Sacred Shears",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .order]⟩ }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Sacred Shears. -/
def SFD_172 : CardDef :=
  { SFD_172.meta with
    grants := [.triggered (.onSelf .die)
        (.of []
        (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-173
/--
**Soraka, Wanderer** — Unit · Order · Energy 4 + Power 1 · Might 4
Printings: SFD-173/221, SFD-239*/221, SFD-239/221

> I must be assigned combat damage last.
> If another unit you control here would die, if it has less Might than me, instead heal it,
> exhaust it, and recall it. (Send it to base. This isn't a move.)
-/
def SFD_173.meta : CardDef :=
  { id := ⟨"SFD-173"⟩,
    name := "Soraka",
    subtitle := some "Wanderer",
    types := [.unit],
    tags := [⟨"Soraka"⟩, ⟨"Mount Targon"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order]⟩,
    might := some 4,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Soraka, Wanderer: the effect is not written yet. -/
def SFD_173 : CardDef := SFD_173.meta

-- BEGIN GENERATED SFD-174
/--
**Trove Golem** — Unit · Order · Energy 8 + Power 2 · Might 9
Printings: SFD-174/221

> When you play me, play four Gold gear tokens exhausted.
-/
def SFD_174.meta : CardDef :=
  { id := ⟨"SFD-174"⟩,
    name := "Trove Golem",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.order],
    cost := some ⟨8, [.domain .order, .domain .order]⟩,
    might := some 9,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Trove Golem. -/
def SFD_174 : CardDef :=
  { SFD_174.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.create "Gold" (.const 4) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-175
/--
**Undertitan** — Unit · Order · Energy 6 + Power 1 · Might 5
Printings: SFD-175/221

> When you play me, give your other units +2 :rb_might: this turn.
> As I'm revealed from your deck, [Add] :rb_energy_2:.
-/
def SFD_175.meta : CardDef :=
  { id := ⟨"SFD-175"⟩,
    name := "Undertitan",
    types := [.unit],
    tags := [⟨"The Void"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order]⟩,
    might := some 5,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Undertitan: the effect is not written yet. -/
def SFD_175 : CardDef := SFD_175.meta

-- BEGIN GENERATED SFD-176
/--
**Xin Zhao, Vigilant** — Unit · Order · Energy 3 + Power 1 · Might 4
Printings: SFD-176/221

> [Tank] (I must be assigned combat damage first.)
> I enter ready if you have two or more other units in your base.
-/
def SFD_176.meta : CardDef :=
  { id := ⟨"SFD-176"⟩,
    name := "Xin Zhao",
    subtitle := some "Vigilant",
    types := [.unit],
    tags := [⟨"Demacia"⟩, ⟨"Xin Zhao"⟩],
    domains := [.order],
    cost := some ⟨3, [.domain .order]⟩,
    might := some 4,
    keywords := [{ keyword := .tank }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Xin Zhao, Vigilant: the effect is not written yet. -/
def SFD_176 : CardDef := SFD_176.meta

-- BEGIN GENERATED SFD-177
/--
**Azir, Sovereign** — Unit · Order · Energy 4 · Might 4
Printings: SFD-177/221, SFD-177a/221

> [Accelerate] (You may pay :rb_energy_1::rb_rune_order: as an additional cost to have me enter
> ready.)
> When I attack, you may move any number of your token units to this battlefield.
-/
def SFD_177.meta : CardDef :=
  { id := ⟨"SFD-177"⟩,
    name := "Azir",
    subtitle := some "Sovereign",
    types := [.unit],
    tags := [⟨"Bird"⟩, ⟨"Azir"⟩, ⟨"Shurima"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Azir, Sovereign: the effect is not written yet. -/
def SFD_177 : CardDef := SFD_177.meta

-- BEGIN GENERATED SFD-178
/--
**Blade of the Ruined King** — Gear · Order · Energy 3 + Power 1 · Might 4
Printings: SFD-178/221

> [Equip] — :rb_rune_order:, Kill a friendly unit (Pay the cost: Attach this to a unit you
> control.)
-/
def SFD_178.meta : CardDef :=
  { id := ⟨"SFD-178"⟩,
    name := "Blade of the Ruined King",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.order],
    cost := some ⟨3, [.domain .order]⟩,
    might := some 4,
    mightBonus := some 4,
    keywords := [{ keyword := .equip }],
    sets := [⟨"SFD"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Blade of the Ruined King: the effect is not written yet. -/
def SFD_178 : CardDef := SFD_178.meta

-- BEGIN GENERATED SFD-179
/--
**Corina Veraza** — Unit · Order · Energy 7 + Power 1 · Might 6
Printings: SFD-179/221

> [Accelerate] (You may pay :rb_energy_1::rb_rune_order: as an additional cost to have me enter
> ready.)
> When I move to a battlefield, play three 1 :rb_might: Recruit unit tokens here.
-/
def SFD_179.meta : CardDef :=
  { id := ⟨"SFD-179"⟩,
    name := "Corina Veraza",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.order],
    cost := some ⟨7, [.domain .order]⟩,
    might := some 6,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Corina Veraza: the effect is not written yet. -/
def SFD_179 : CardDef := SFD_179.meta

-- BEGIN GENERATED SFD-180
/--
**Fiora, Worthy** — Unit · Order · Energy 3 · Might 3
Printings: SFD-180/221, SFD-180a/221

> When a unit you control becomes [Mighty], you may pay :rb_rune_order: to ready it. (A unit is
> Mighty while it has 5+ :rb_might:.)
-/
def SFD_180.meta : CardDef :=
  { id := ⟨"SFD-180"⟩,
    name := "Fiora",
    subtitle := some "Worthy",
    types := [.unit],
    tags := [⟨"Fiora"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Fiora, Worthy: the effect is not written yet. -/
def SFD_180 : CardDef := SFD_180.meta

-- BEGIN GENERATED SFD-181
/--
**Mechanized Menace** — Legend · Fury/Mind
Printings: SFD-181/221, SFD-240/221

> Your Mechs have [Shield]. (+1 :rb_might: while they're defenders.)
-/
def SFD_181.meta : CardDef :=
  { id := ⟨"SFD-181"⟩,
    name := "Mechanized Menace",
    types := [.legend],
    tags := [⟨"Rumble"⟩],
    domains := [.fury, .mind],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Mechanized Menace. -/
def SFD_181 : CardDef :=
  { SFD_181.meta with

    abilities := [.passive .always
      [.keyword (Selector.all .friendly .anywhere [.tag ⟨"Mech"⟩]) { keyword := .shield }]],
    status := .drafted }

-- BEGIN GENERATED SFD-182
/--
**Danger Zone** — Spell · Fury/Mind · Energy 1 + Power 1
Printings: SFD-182/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> [Repeat] :rb_energy_1::rb_rune_rainbow: (You may pay the additional cost to repeat this
> spell's effect.)
> Give your Mechs +1 :rb_might: this turn.
-/
def SFD_182.meta : CardDef :=
  { id := ⟨"SFD-182"⟩,
    name := "Danger Zone",
    types := [.spell],
    tags := [⟨"Rumble"⟩],
    domains := [.fury, .mind],
    cost := some ⟨1, [.any]⟩,
    keywords := [{ keyword := .reaction },
      { keyword := .repeat_, arg := .cost ⟨1, [.any]⟩ }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Danger Zone. -/
def SFD_182 : CardDef :=
  { SFD_182.meta with

    spellEffect := some (.of []
      (.grant (Selector.all .friendly .anywhere [.tag ⟨"Mech"⟩]) (.mightPlus .it (.const 1))
        .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED SFD-183
/--
**Purifier** — Legend · Fury/Body
Printings: SFD-183/221, SFD-241/221

> Your Equipment each give [Assault]. (+1 :rb_might: while equipped unit is an attacker.)
-/
def SFD_183.meta : CardDef :=
  { id := ⟨"SFD-183"⟩,
    name := "Purifier",
    types := [.legend],
    tags := [⟨"Lucian"⟩],
    domains := [.fury, .body],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Purifier: the effect is not written yet. -/
def SFD_183 : CardDef := SFD_183.meta

-- BEGIN GENERATED SFD-184
/--
**Relentless Pursuit** — Spell · Fury/Body · Energy 2 + Power 1
Printings: SFD-184/221

> [Action] (Play on your turn or in showdowns.)
> Move a friendly unit. You may attach an Equipment with the same controller to it. This turn,
> that unit has "When I conquer, you may move me to my base."
-/
def SFD_184.meta : CardDef :=
  { id := ⟨"SFD-184"⟩,
    name := "Relentless Pursuit",
    types := [.spell],
    tags := [⟨"Lucian"⟩],
    domains := [.fury, .body],
    cost := some ⟨2, [.any]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Relentless Pursuit: the effect is not written yet. -/
def SFD_184 : CardDef := SFD_184.meta

-- BEGIN GENERATED SFD-185
/--
**Glorious Executioner** — Legend · Fury/Chaos
Printings: SFD-185/221, SFD-242/221

> When you win a combat, draw 1. (You win if only your units remain after combat.)
-/
def SFD_185.meta : CardDef :=
  { id := ⟨"SFD-185"⟩,
    name := "Glorious Executioner",
    types := [.legend],
    tags := [⟨"Draven"⟩],
    domains := [.fury, .chaos],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Glorious Executioner. -/
def SFD_185 : CardDef :=
  { SFD_185.meta with

    abilities := [.triggered (.onSelf .winCombat) (.of [] (.prim (.draw .you (.const 1))))
      .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-186
/--
**Spinning Axe** — Gear · Fury/Chaos · Energy 2 + Power 1 · Might 3
Printings: SFD-186/221

> [Quick-Draw] (This has [Reaction]. When you play it, attach it to a unit you control.)
> [Equip] :rb_rune_rainbow: (:rb_rune_rainbow:: Attach this to a unit you control.)
> [Temporary] (If this is unattached, kill it at the start of its controller's Beginning Phase,
> before scoring.)
-/
def SFD_186.meta : CardDef :=
  { id := ⟨"SFD-186"⟩,
    name := "Spinning Axe",
    types := [.gear],
    tags := [⟨"Draven"⟩, ⟨"Equipment"⟩],
    domains := [.fury, .chaos],
    cost := some ⟨2, [.any]⟩,
    might := some 3,
    mightBonus := some 3,
    keywords := [{ keyword := .quickDraw },
      { keyword := .equip, arg := .cost ⟨0, [.any]⟩ },
      { keyword := .temporary }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Spinning Axe. -/
def SFD_186 : CardDef :=
  { SFD_186.meta with
    status := .drafted }

-- BEGIN GENERATED SFD-187
/--
**Void Burrower** — Legend · Fury/Order
Printings: SFD-187/221, SFD-243/221

> When you conquer, you may exhaust me to reveal the top 2 cards of your Main Deck. You may play
> one. Then recycle the rest.
-/
def SFD_187.meta : CardDef :=
  { id := ⟨"SFD-187"⟩,
    name := "Void Burrower",
    types := [.legend],
    tags := [⟨"Rek'Sai"⟩],
    domains := [.fury, .order],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Void Burrower: the effect is not written yet. -/
def SFD_187 : CardDef := SFD_187.meta

-- BEGIN GENERATED SFD-188
/--
**Void Rush** — Spell · Fury/Order · Energy 2 + Power 1
Printings: SFD-188/221

> Reveal the top 2 cards of your Main Deck. You may play one of them, reducing its cost by
> :rb_energy_2:. Draw any you did not play this way.
-/
def SFD_188.meta : CardDef :=
  { id := ⟨"SFD-188"⟩,
    name := "Void Rush",
    types := [.spell],
    tags := [⟨"Rek'Sai"⟩],
    domains := [.fury, .order],
    cost := some ⟨2, [.any]⟩,
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Void Rush: the effect is not written yet. -/
def SFD_188 : CardDef := SFD_188.meta

-- BEGIN GENERATED SFD-189
/--
**Fire Below the Mountain** — Legend · Calm/Mind
Printings: SFD-189/221, SFD-244/221

> :rb_exhaust:: [Reaction] — [Add] :rb_rune_rainbow:. Use only to play gear or use gear
> abilities. (Abilities that add resources can't be reacted to.)
-/
def SFD_189.meta : CardDef :=
  { id := ⟨"SFD-189"⟩,
    name := "Fire Below the Mountain",
    types := [.legend],
    tags := [⟨"Ornn"⟩],
    domains := [.calm, .mind],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Fire Below the Mountain: the effect is not written yet. -/
def SFD_189 : CardDef := SFD_189.meta

-- BEGIN GENERATED SFD-190
/--
**Forgefire Cape** — Gear · Calm/Mind · Energy 4 + Power 2 · Might 3
Printings: SFD-190/221

> [Unique] (Your deck can have only 1 card with this name.)
> [Equip] :rb_rune_rainbow: (:rb_rune_rainbow:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I attack or defend, deal 2 to all enemy units here.
-/
def SFD_190.meta : CardDef :=
  { id := ⟨"SFD-190"⟩,
    name := "Forgefire Cape",
    types := [.gear],
    tags := [⟨"Ornn"⟩, ⟨"Equipment"⟩],
    domains := [.calm, .mind],
    cost := some ⟨4, [.any, .any]⟩,
    might := some 3,
    mightBonus := some 3,
    keywords := [{ keyword := .unique },
      { keyword := .equip, arg := .cost ⟨0, [.any]⟩ }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Forgefire Cape. -/
def SFD_190 : CardDef :=
  { SFD_190.meta with

    grants := [.triggered (.onSelf .attack)
        (.of [] (.prim (.deal (Selector.all .enemy .here [.ofType .unit]) (.const 2)))) .unlimited,
      .triggered (.onSelf .defend)
        (.of [] (.prim (.deal (Selector.all .enemy .here [.ofType .unit]) (.const 2)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-191
/--
**Rabadon's Deathcrown** — Gear · Calm/Mind · Energy 4 + Power 2 · Might 3
Printings: SFD-191/221

> [Unique] (Your deck can have only 1 card with this name.)
> [Equip] :rb_rune_rainbow: (:rb_rune_rainbow:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> Your spells and abilities deal 3 Bonus Damage (while this is attached).
-/
def SFD_191.meta : CardDef :=
  { id := ⟨"SFD-191"⟩,
    name := "Rabadon's Deathcrown",
    types := [.gear],
    tags := [⟨"Ornn"⟩, ⟨"Equipment"⟩],
    domains := [.calm, .mind],
    cost := some ⟨4, [.any, .any]⟩,
    might := some 3,
    mightBonus := some 3,
    keywords := [{ keyword := .unique },
      { keyword := .equip, arg := .cost ⟨0, [.any]⟩ }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Rabadon's Deathcrown: the effect is not written yet. -/
def SFD_191 : CardDef := SFD_191.meta

-- BEGIN GENERATED SFD-192
/--
**Shurelya's Requiem** — Gear · Calm/Mind · Energy 4 + Power 2 · Might 2
Printings: SFD-192/221

> [Unique] (Your deck can have only 1 card with this name.)
> [Equip] :rb_rune_rainbow: (:rb_rune_rainbow:: Attach this to a unit you control.)
> When you play this, ready your units.

Effect (given to the unit it is attached to):

> Your units here have [Ganking]. (We can move from battlefield to battlefield.)
-/
def SFD_192.meta : CardDef :=
  { id := ⟨"SFD-192"⟩,
    name := "Shurelya's Requiem",
    types := [.gear],
    tags := [⟨"Ornn"⟩, ⟨"Equipment"⟩],
    domains := [.calm, .mind],
    cost := some ⟨4, [.any, .any]⟩,
    might := some 2,
    mightBonus := some 2,
    keywords := [{ keyword := .unique },
      { keyword := .equip, arg := .cost ⟨0, [.any]⟩ }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Shurelya's Requiem: the effect is not written yet. -/
def SFD_192 : CardDef := SFD_192.meta

-- BEGIN GENERATED SFD-193
/--
**Grandmaster at Arms** — Legend · Calm/Body
Printings: SFD-193/221, SFD-245/221

> :rb_energy_1:, :rb_exhaust:: Attach a detached Equipment you control to a unit you control.
> :rb_exhaust:: Attach an attached Equipment you control to a unit you control.
-/
def SFD_193.meta : CardDef :=
  { id := ⟨"SFD-193"⟩,
    name := "Grandmaster at Arms",
    types := [.legend],
    tags := [⟨"Jax"⟩],
    domains := [.calm, .body],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Grandmaster at Arms: the effect is not written yet. -/
def SFD_193 : CardDef := SFD_193.meta

-- BEGIN GENERATED SFD-194
/--
**Counter Strike** — Spell · Calm/Body · Energy 2 + Power 1
Printings: SFD-194/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a unit. The next time that unit would be dealt damage this turn, prevent it. Draw 1.
-/
def SFD_194.meta : CardDef :=
  { id := ⟨"SFD-194"⟩,
    name := "Counter Strike",
    types := [.spell],
    tags := [⟨"Jax"⟩],
    domains := [.calm, .body],
    cost := some ⟨2, [.any]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Counter Strike: the effect is not written yet. -/
def SFD_194 : CardDef := SFD_194.meta

-- BEGIN GENERATED SFD-195
/--
**Blade Dancer** — Legend · Calm/Chaos
Printings: SFD-195/221, SFD-246/221

> When you choose a friendly unit, you may exhaust me and pay :rb_rune_rainbow: to ready it.
> When you conquer, you may pay :rb_energy_1: to ready me.
-/
def SFD_195.meta : CardDef :=
  { id := ⟨"SFD-195"⟩,
    name := "Blade Dancer",
    types := [.legend],
    tags := [⟨"Irelia"⟩],
    domains := [.calm, .chaos],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Blade Dancer: the effect is not written yet. -/
def SFD_195 : CardDef := SFD_195.meta

-- BEGIN GENERATED SFD-196
/--
**Defiant Dance** — Spell · Calm/Chaos · Energy 1 + Power 1
Printings: SFD-196/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a unit +2 :rb_might: this turn and another unit -2 :rb_might: this turn.
-/
def SFD_196.meta : CardDef :=
  { id := ⟨"SFD-196"⟩,
    name := "Defiant Dance",
    types := [.spell],
    tags := [⟨"Irelia"⟩],
    domains := [.calm, .chaos],
    cost := some ⟨1, [.any]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Defiant Dance: the effect is not written yet. -/
def SFD_196 : CardDef := SFD_196.meta

-- BEGIN GENERATED SFD-197
/--
**Emperor of the Sands** — Legend · Calm/Order
Printings: SFD-197/221, SFD-247/221

> Your Sand Soldiers have [Weaponmaster].
> :rb_energy_1:, :rb_exhaust:: Play a 2 :rb_might: Sand Soldier unit token to your base. Use
> only if you've played an Equipment this turn.
-/
def SFD_197.meta : CardDef :=
  { id := ⟨"SFD-197"⟩,
    name := "Emperor of the Sands",
    types := [.legend],
    tags := [⟨"Azir"⟩],
    domains := [.calm, .order],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Emperor of the Sands: the effect is not written yet. -/
def SFD_197 : CardDef := SFD_197.meta

-- BEGIN GENERATED SFD-198
/--
**Arise!** — Spell · Calm/Order · Energy 6 + Power 1
Printings: SFD-198/221

> Play a 2 :rb_might: Sand Soldier unit token for each Equipment you control. Then ready two of
> them.
-/
def SFD_198.meta : CardDef :=
  { id := ⟨"SFD-198"⟩,
    name := "Arise!",
    types := [.spell],
    tags := [⟨"Azir"⟩],
    domains := [.calm, .order],
    cost := some ⟨6, [.any]⟩,
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Arise!: the effect is not written yet. -/
def SFD_198 : CardDef := SFD_198.meta

-- BEGIN GENERATED SFD-199
/--
**Prodigal Explorer** — Legend · Mind/Chaos
Printings: SFD-199/221, SFD-248/221

> :rb_exhaust:: [Reaction] — Draw 1. Use only if you've chosen enemy units and/or gear twice
> this turn with spells or unit abilities.
-/
def SFD_199.meta : CardDef :=
  { id := ⟨"SFD-199"⟩,
    name := "Prodigal Explorer",
    types := [.legend],
    tags := [⟨"Ezreal"⟩],
    domains := [.mind, .chaos],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Prodigal Explorer: the effect is not written yet. -/
def SFD_199 : CardDef := SFD_199.meta

-- BEGIN GENERATED SFD-200
/--
**Arcane Shift** — Spell · Mind/Chaos · Energy 3 + Power 1
Printings: SFD-200/221

> [Action] (Play on your turn or in showdowns.)
> Banish a friendly unit, then its owner plays it, ignoring its cost. Deal 3 to an enemy unit at
> a battlefield. Banish this.
-/
def SFD_200.meta : CardDef :=
  { id := ⟨"SFD-200"⟩,
    name := "Arcane Shift",
    types := [.spell],
    tags := [⟨"Ezreal"⟩],
    domains := [.mind, .chaos],
    cost := some ⟨3, [.any]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Arcane Shift: the effect is not written yet. -/
def SFD_200 : CardDef := SFD_200.meta

-- BEGIN GENERATED SFD-201
/--
**Chem-Baroness** — Legend · Mind/Order
Printings: SFD-201/221, SFD-249/221

> When you or an ally hold, you may exhaust me to play a Gold gear token exhausted.
> While your score is within 3 points of the Victory Score, your Gold [Add] an additional
> :rb_energy_1:.
-/
def SFD_201.meta : CardDef :=
  { id := ⟨"SFD-201"⟩,
    name := "Chem-Baroness",
    types := [.legend],
    tags := [⟨"Renata Glasc"⟩],
    domains := [.mind, .order],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Chem-Baroness: the effect is not written yet. -/
def SFD_201 : CardDef := SFD_201.meta

-- BEGIN GENERATED SFD-202
/--
**Hostile Takeover** — Spell · Mind/Order · Energy 5 + Power 2
Printings: SFD-202/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> Take control of an enemy unit at a battlefield. Ready it. (Start a combat if other enemies are
> there. Otherwise, conquer.)
> Lose control of that unit and recall it at end of turn. (Send it to base. This isn't a move.)
-/
def SFD_202.meta : CardDef :=
  { id := ⟨"SFD-202"⟩,
    name := "Hostile Takeover",
    types := [.spell],
    tags := [⟨"Renata Glasc"⟩],
    domains := [.mind, .order],
    cost := some ⟨5, [.any, .any]⟩,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Hostile Takeover: the effect is not written yet. -/
def SFD_202 : CardDef := SFD_202.meta

-- BEGIN GENERATED SFD-203
/--
**Battle Mistress** — Legend · Body/Chaos
Printings: SFD-203/221, SFD-250/221

> When you recycle a rune, you may exhaust me to play a Gold gear token exhausted.
> When one or more enemy units die, ready me.
-/
def SFD_203.meta : CardDef :=
  { id := ⟨"SFD-203"⟩,
    name := "Battle Mistress",
    types := [.legend],
    tags := [⟨"Sivir"⟩],
    domains := [.body, .chaos],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Battle Mistress: the effect is not written yet. -/
def SFD_203 : CardDef := SFD_203.meta

-- BEGIN GENERATED SFD-204
/--
**On the Hunt** — Spell · Body/Chaos · Energy 1 + Power 2
Printings: SFD-204/221

> Ready your units.
-/
def SFD_204.meta : CardDef :=
  { id := ⟨"SFD-204"⟩,
    name := "On the Hunt",
    types := [.spell],
    tags := [⟨"Sivir"⟩],
    domains := [.body, .chaos],
    cost := some ⟨1, [.any, .any]⟩,
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- On the Hunt: the effect is not written yet. -/
def SFD_204 : CardDef := SFD_204.meta

-- BEGIN GENERATED SFD-205
/--
**Grand Duelist** — Legend · Body/Order
Printings: SFD-205/221, SFD-251/221

> When one of your units becomes [Mighty], you may exhaust me to channel 1 rune exhausted. (A
> unit is Mighty while it has 5+ :rb_might:.)
-/
def SFD_205.meta : CardDef :=
  { id := ⟨"SFD-205"⟩,
    name := "Grand Duelist",
    types := [.legend],
    tags := [⟨"Fiora"⟩],
    domains := [.body, .order],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Grand Duelist: the effect is not written yet. -/
def SFD_205 : CardDef := SFD_205.meta

-- BEGIN GENERATED SFD-206
/--
**Riposte** — Spell · Body/Order · Energy 2 + Power 2
Printings: SFD-206/221

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a friendly unit and a spell. Counter that spell and give that unit +:rb_might: equal to
> that spell's Energy cost this turn.
-/
def SFD_206.meta : CardDef :=
  { id := ⟨"SFD-206"⟩,
    name := "Riposte",
    types := [.spell],
    tags := [⟨"Fiora"⟩],
    domains := [.body, .order],
    cost := some ⟨2, [.any, .any]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"SFD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Riposte: the effect is not written yet. -/
def SFD_206 : CardDef := SFD_206.meta

-- BEGIN GENERATED SFD-207
/--
**Emperor's Dais** — Battlefield · Colorless
Printings: SFD-207/221

> When you conquer here, you may pay :rb_energy_1: and return a unit you control here to its
> owner's hand. If you do, play a 2 :rb_might: Sand Soldier unit token here.
-/
def SFD_207.meta : CardDef :=
  { id := ⟨"SFD-207"⟩,
    name := "Emperor's Dais",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Emperor's Dais. -/
def SFD_207 : CardDef :=
  { SFD_207.meta with

    abilities := [.triggered (.onSelf .youConquer)
      (.of [] (.ifThen (.and (.canPay ⟨1, []⟩)
          (.exists (Selector.all .friendly .here [.ofType .unit])))
        (.may (.seqOf [.prim (.pay ⟨1, []⟩),
          .prim (.returnToHand (Selector.one .friendly .here [.ofType .unit])),
          .prim (.create "Sand Soldier" (.const 1) .here false)])) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-208
/--
**Forge of the Fluft** — Battlefield · Colorless
Printings: SFD-208/221

> While you control this battlefield, friendly legends have ":rb_exhaust:: Attach an Equipment
> you control to a unit you control."
-/
def SFD_208.meta : CardDef :=
  { id := ⟨"SFD-208"⟩,
    name := "Forge of the Fluft",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Forge of the Fluft: the effect is not written yet. -/
def SFD_208 : CardDef := SFD_208.meta

-- BEGIN GENERATED SFD-209
/--
**Forgotten Monument** — Battlefield · Colorless
Printings: SFD-209/221

> Players can't score here until their third turn.
-/
def SFD_209.meta : CardDef :=
  { id := ⟨"SFD-209"⟩,
    name := "Forgotten Monument",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Forgotten Monument. -/
def SFD_209 : CardDef :=
  { SFD_209.meta with
    abilities := [.passive .always [.cantPlayer .eachPlayer .score .here 3]],
    status := .drafted }

-- BEGIN GENERATED SFD-210
/--
**Hall of Legends** — Battlefield · Colorless
Printings: SFD-210/221

> When you conquer here, you may pay :rb_energy_1: to ready your legend.
-/
def SFD_210.meta : CardDef :=
  { id := ⟨"SFD-210"⟩,
    name := "Hall of Legends",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Hall of Legends: the effect is not written yet. -/
def SFD_210 : CardDef := SFD_210.meta

-- BEGIN GENERATED SFD-211
/--
**Marai Spire** — Battlefield · Colorless
Printings: SFD-211/221

> While you control this battlefield, friendly [Repeat] costs cost :rb_energy_1: less.
-/
def SFD_211.meta : CardDef :=
  { id := ⟨"SFD-211"⟩,
    name := "Marai Spire",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Marai Spire: the effect is not written yet. -/
def SFD_211 : CardDef := SFD_211.meta

-- BEGIN GENERATED SFD-212
/--
**Minefield** — Battlefield · Colorless
Printings: SFD-212/221

> When you conquer here, put the top 2 cards of your Main Deck into your trash.
-/
def SFD_212.meta : CardDef :=
  { id := ⟨"SFD-212"⟩,
    name := "Minefield",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Minefield. -/
def SFD_212 : CardDef :=
  { SFD_212.meta with

    abilities := [.triggered (.onSelf .youConquer)
      (.of [] (.repeatN (.const 2)
        (.prim (.bin (Selector.one .friendly .inMainDeck [.top 1]))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-213
/--
**Ornn's Forge** — Battlefield · Colorless
Printings: SFD-213/221

> While you control this battlefield, the first friendly non-token gear played each turn costs
> :rb_energy_1: less.
-/
def SFD_213.meta : CardDef :=
  { id := ⟨"SFD-213"⟩,
    name := "Ornn's Forge",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Ornn's Forge: the effect is not written yet. -/
def SFD_213 : CardDef := SFD_213.meta

-- BEGIN GENERATED SFD-214
/--
**Power Nexus** — Battlefield · Colorless
Printings: SFD-214/221

> When you hold here, you may pay
> :rb_rune_rainbow::rb_rune_rainbow::rb_rune_rainbow::rb_rune_rainbow: to score 1 point.
-/
def SFD_214.meta : CardDef :=
  { id := ⟨"SFD-214"⟩,
    name := "Power Nexus",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Power Nexus. -/
def SFD_214 : CardDef :=
  { SFD_214.meta with

    abilities := [.triggered (.onSelf .youHold)
      (.of [] (.ifThen (.canPay ⟨0, [.any, .any, .any, .any]⟩)
        (.may (.seqOf [.prim (.pay ⟨0, [.any, .any, .any, .any]⟩),
          .prim (.score .you (.const 1))])) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-215
/--
**Ravenbloom Conservatory** — Battlefield · Colorless
Printings: SFD-215/221

> When you defend here, reveal the top card of your Main Deck. If it's a spell, put it in your
> hand. Otherwise, recycle it.
-/
def SFD_215.meta : CardDef :=
  { id := ⟨"SFD-215"⟩,
    name := "Ravenbloom Conservatory",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Ravenbloom Conservatory: the effect is not written yet. -/
def SFD_215 : CardDef := SFD_215.meta

-- BEGIN GENERATED SFD-216
/--
**Rockfall Path** — Battlefield · Colorless
Printings: SFD-216/221

> Units can't be played here.
-/
def SFD_216.meta : CardDef :=
  { id := ⟨"SFD-216"⟩,
    name := "Rockfall Path",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Rockfall Path: the effect is not written yet. -/
def SFD_216 : CardDef := SFD_216.meta

-- BEGIN GENERATED SFD-217
/--
**Seat of Power** — Battlefield · Colorless
Printings: SFD-217/221

> When you conquer here, draw 1 for each other battlefield you or allies control.
-/
def SFD_217.meta : CardDef :=
  { id := ⟨"SFD-217"⟩,
    name := "Seat of Power",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Seat of Power. -/
def SFD_217 : CardDef :=
  { SFD_217.meta with

    abilities := [.triggered (.onSelf .youConquer)
      (.of [] (.prim (.draw .you (.count
        (Selector.all .any .anywhere [.ofType .battlefield, .controlled, .notSelf]))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-218
/--
**Sunken Temple** — Battlefield · Colorless
Printings: SFD-218/221

> When you conquer here with one or more [Mighty] units, you may pay :rb_energy_1: to draw 1. (A
> unit is Mighty while it has 5+ :rb_might:.)
-/
def SFD_218.meta : CardDef :=
  { id := ⟨"SFD-218"⟩,
    name := "Sunken Temple",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Sunken Temple. -/
def SFD_218 : CardDef :=
  { SFD_218.meta with

    abilities := [.triggered (.onSelf .youConquer)
      (.of [] (.ifThen (.and (.canPay ⟨1, []⟩)
          (.exists (Selector.all .friendly .here [.ofType .unit, .mighty])))
        (.may (.seqOf [.prim (.pay ⟨1, []⟩), .prim (.draw .you (.const 1))])) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-219
/--
**The Papertree** — Battlefield · Colorless
Printings: SFD-219/221

> When you hold here, each player channels 1 rune exhausted.
-/
def SFD_219.meta : CardDef :=
  { id := ⟨"SFD-219"⟩,
    name := "The Papertree",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- The Papertree. -/
def SFD_219 : CardDef :=
  { SFD_219.meta with

    abilities := [.triggered (.onSelf .youHold)
      (.of [] (.prim (.channel .eachPlayer (.const 0) (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-220
/--
**Treasure Hoard** — Battlefield · Colorless
Printings: SFD-220/221

> When you conquer here, you may pay :rb_energy_1: to play a Gold gear token exhausted.
-/
def SFD_220.meta : CardDef :=
  { id := ⟨"SFD-220"⟩,
    name := "Treasure Hoard",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Treasure Hoard. -/
def SFD_220 : CardDef :=
  { SFD_220.meta with

    abilities := [.triggered (.onSelf .youConquer)
      (.of [] (.ifThen (.canPay ⟨1, []⟩)
        (.may (.seqOf [.prim (.pay ⟨1, []⟩), .prim (.create "Gold" (.const 1) .atBase false)]))
        .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED SFD-221
/--
**Veiled Temple** — Battlefield · Colorless
Printings: SFD-221/221

> When you conquer here, you may ready a friendly gear. If it's an Equipment, you may detach it.
-/
def SFD_221.meta : CardDef :=
  { id := ⟨"SFD-221"⟩,
    name := "Veiled Temple",
    types := [.battlefield],
    sets := [⟨"SFD"⟩] }
-- END GENERATED

/-- Veiled Temple: the effect is not written yet. -/
def SFD_221 : CardDef := SFD_221.meta

-- BEGIN GENERATED SFD-T03
/--
**Gold** — Gear · Colorless
Printings: SFD-T03, UNL-T05

> Kill this, :rb_exhaust:: [Reaction] — [Add] :rb_rune_rainbow:. (Abilities that add resources
> can't be reacted to.)
-/
def SFD_T03.meta : CardDef :=
  { id := ⟨"SFD-T03"⟩,
    name := "Gold",
    types := [.gear],
    sets := [⟨"SFD"⟩, ⟨"UNL"⟩] }
-- END GENERATED

/-- Gold: "Kill this, [Exhaust]: [Reaction] — [Add] one Power of any domain." -/
def SFD_T03 : CardDef :=
  { SFD_T03.meta with
    abilities := [.activated [.killSelf, .exhaustSelf] .reaction
      (.of [] (.prim (.addPower .you (.const 1) none none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED LIST
/-- The cards first printed in Spiritforged. -/
def cards : List CardDef :=
  [SFD_001,
    SFD_002,
    SFD_003,
    SFD_004,
    SFD_005,
    SFD_006,
    SFD_007,
    SFD_008,
    SFD_009,
    SFD_010,
    SFD_011,
    SFD_012,
    SFD_013,
    SFD_014,
    SFD_015,
    SFD_016,
    SFD_017,
    SFD_018,
    SFD_019,
    SFD_020,
    SFD_021,
    SFD_022,
    SFD_023,
    SFD_024,
    SFD_025,
    SFD_026,
    SFD_027,
    SFD_028,
    SFD_029,
    SFD_030,
    SFD_031,
    SFD_032,
    SFD_033,
    SFD_034,
    SFD_035,
    SFD_036,
    SFD_037,
    SFD_038,
    SFD_039,
    SFD_040,
    SFD_041,
    SFD_042,
    SFD_043,
    SFD_044,
    SFD_045,
    SFD_046,
    SFD_047,
    SFD_048,
    SFD_049,
    SFD_050,
    SFD_051,
    SFD_052,
    SFD_053,
    SFD_054,
    SFD_055,
    SFD_056,
    SFD_057,
    SFD_058,
    SFD_059,
    SFD_060,
    SFD_061,
    SFD_062,
    SFD_063,
    SFD_064,
    SFD_065,
    SFD_066,
    SFD_067,
    SFD_068,
    SFD_069,
    SFD_070,
    SFD_071,
    SFD_072,
    SFD_073,
    SFD_074,
    SFD_075,
    SFD_076,
    SFD_077,
    SFD_078,
    SFD_079,
    SFD_080,
    SFD_081,
    SFD_082,
    SFD_083,
    SFD_084,
    SFD_085,
    SFD_086,
    SFD_087,
    SFD_088,
    SFD_089,
    SFD_090,
    SFD_091,
    SFD_092,
    SFD_093,
    SFD_094,
    SFD_095,
    SFD_096,
    SFD_097,
    SFD_098,
    SFD_099,
    SFD_100,
    SFD_101,
    SFD_102,
    SFD_103,
    SFD_104,
    SFD_105,
    SFD_106,
    SFD_107,
    SFD_108,
    SFD_109,
    SFD_110,
    SFD_111,
    SFD_112,
    SFD_113,
    SFD_114,
    SFD_115,
    SFD_116,
    SFD_117,
    SFD_118,
    SFD_119,
    SFD_120,
    SFD_121,
    SFD_122,
    SFD_123,
    SFD_124,
    SFD_125,
    SFD_126,
    SFD_127,
    SFD_128,
    SFD_129,
    SFD_130,
    SFD_131,
    SFD_132,
    SFD_133,
    SFD_134,
    SFD_135,
    SFD_136,
    SFD_137,
    SFD_138,
    SFD_139,
    SFD_140,
    SFD_141,
    SFD_142,
    SFD_143,
    SFD_144,
    SFD_145,
    SFD_146,
    SFD_147,
    SFD_148,
    SFD_149,
    SFD_150,
    SFD_151,
    SFD_152,
    SFD_153,
    SFD_154,
    SFD_155,
    SFD_156,
    SFD_157,
    SFD_158,
    SFD_159,
    SFD_160,
    SFD_161,
    SFD_162,
    SFD_163,
    SFD_164,
    SFD_165,
    SFD_166,
    SFD_167,
    SFD_168,
    SFD_169,
    SFD_170,
    SFD_171,
    SFD_172,
    SFD_173,
    SFD_174,
    SFD_175,
    SFD_176,
    SFD_177,
    SFD_178,
    SFD_179,
    SFD_180,
    SFD_181,
    SFD_182,
    SFD_183,
    SFD_184,
    SFD_185,
    SFD_186,
    SFD_187,
    SFD_188,
    SFD_189,
    SFD_190,
    SFD_191,
    SFD_192,
    SFD_193,
    SFD_194,
    SFD_195,
    SFD_196,
    SFD_197,
    SFD_198,
    SFD_199,
    SFD_200,
    SFD_201,
    SFD_202,
    SFD_203,
    SFD_204,
    SFD_205,
    SFD_206,
    SFD_207,
    SFD_208,
    SFD_209,
    SFD_210,
    SFD_211,
    SFD_212,
    SFD_213,
    SFD_214,
    SFD_215,
    SFD_216,
    SFD_217,
    SFD_218,
    SFD_219,
    SFD_220,
    SFD_221,
    SFD_T03]
-- END GENERATED LIST

end RiftboundCards.Spiritforged

end
