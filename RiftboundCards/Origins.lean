module

public import Riftbound.Card.CardDef

/-!
# Origins (OGN)

The cards first printed in Origins. Each card has a generated block (the official text and
the metadata) and, right after it, the part written by hand (the effect and the
implementation status). `scripts/gen_lean.py` rewrites the generated blocks only
(docs/card-data.md §4.1).
-/

@[expose] public section

namespace RiftboundCards.Origins

open Riftbound

-- BEGIN GENERATED OGN-001
/--
**Blazing Scorcher** — Unit · Fury · Energy 5 · Might 5
Printings: OGN-001/298

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
-/
def OGN_001.meta : CardDef :=
  { id := ⟨"OGN-001"⟩,
    name := "Blazing Scorcher",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Blazing Scorcher. -/
def OGN_001 : CardDef :=
  { OGN_001.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-002
/--
**Brazen Buccaneer** — Unit · Fury · Energy 6 · Might 5
Printings: OGN-002/298

> As you play me, you may discard a card as an additional cost. If you do, reduce my cost by
> :rb_energy_2:.
-/
def OGN_002.meta : CardDef :=
  { id := ⟨"OGN-002"⟩,
    name := "Brazen Buccaneer",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.fury],
    cost := some ⟨6, []⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Brazen Buccaneer: the effect is not written yet. -/
def OGN_002 : CardDef := OGN_002.meta

-- BEGIN GENERATED OGN-003
/--
**Chemtech Enforcer** — Unit · Fury · Energy 2 · Might 2
Printings: OGN-003/298

> [Assault 2] (+2 :rb_might: while I'm an attacker.)
> When you play me, discard 1.
-/
def OGN_003.meta : CardDef :=
  { id := ⟨"OGN-003"⟩,
    name := "Chemtech Enforcer",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .assault, arg := .amount 2 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Chemtech Enforcer. -/
def OGN_003 : CardDef :=
  { OGN_003.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.discard .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-004
/--
**Cleave** — Spell · Fury · Energy 1
Printings: OGN-004/298

> [Action] (Play on your turn or in showdowns.)
> Give a unit [Assault 3] this turn. (+3 :rb_might: while it's an attacker.)
-/
def OGN_004.meta : CardDef :=
  { id := ⟨"OGN-004"⟩,
    name := "Cleave",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Cleave. -/
def OGN_004 : CardDef :=
  { OGN_004.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.keyword .it ⟨.assault, .amount 3⟩) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED OGN-005
/--
**Disintegrate** — Spell · Fury · Energy 4
Printings: OGN-005/298

> [Action] (Play on your turn or in showdowns.)
> Deal 3 to a unit at a battlefield. If this kills it, draw 1.
-/
def OGN_005.meta : CardDef :=
  { id := ⟨"OGN-005"⟩,
    name := "Disintegrate",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Disintegrate: the effect is not written yet. -/
def OGN_005 : CardDef := OGN_005.meta

-- BEGIN GENERATED OGN-006
/--
**Flame Chompers** — Unit · Fury · Energy 3 · Might 3
Printings: OGN-006/298

> When you discard me, you may pay :rb_rune_fury: to play me.
-/
def OGN_006.meta : CardDef :=
  { id := ⟨"OGN-006"⟩,
    name := "Flame Chompers",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Flame Chompers: the effect is not written yet. -/
def OGN_006 : CardDef := OGN_006.meta

-- BEGIN GENERATED OGN-007
/--
**Fury Rune** — Rune · Fury
Printings: OGN-007/298, OGN-007a/298, VEN-R01, RAD-R01, RAD-R01a

> (no text)
-/
def OGN_007.meta : CardDef :=
  { id := ⟨"OGN-007"⟩,
    name := "Fury Rune",
    types := [.rune],
    domains := [.fury],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Fury Rune. -/
def OGN_007 : CardDef :=
  { OGN_007.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-008
/--
**Get Excited!** — Spell · Fury · Energy 2 + Power 1
Printings: OGN-008/298

> [Action] (Play on your turn or in showdowns.)
> Discard 1. Deal its Energy cost as damage to a unit at a battlefield. (Ignore its Power cost.)
-/
def OGN_008.meta : CardDef :=
  { id := ⟨"OGN-008"⟩,
    name := "Get Excited!",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Get Excited!: the effect is not written yet. -/
def OGN_008 : CardDef := OGN_008.meta

-- BEGIN GENERATED OGN-009
/--
**Hextech Ray** — Spell · Fury · Energy 1 + Power 1
Printings: OGN-009/298

> [Action] (Play on your turn or in showdowns.)
> Deal 3 to a unit at a battlefield.
-/
def OGN_009.meta : CardDef :=
  { id := ⟨"OGN-009"⟩,
    name := "Hextech Ray",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨1, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Hextech Ray. -/
def OGN_009 : CardDef :=
  { OGN_009.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.prim (.deal (.slot 0) (.const 3)))),
    status := .drafted }

-- BEGIN GENERATED OGN-010
/--
**Legion Rearguard** — Unit · Fury · Energy 2 · Might 2
Printings: OGN-010/298

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
-/
def OGN_010.meta : CardDef :=
  { id := ⟨"OGN-010"⟩,
    name := "Legion Rearguard",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Legion Rearguard. -/
def OGN_010 : CardDef :=
  { OGN_010.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-011
/--
**Magma Wurm** — Unit · Fury · Energy 8 + Power 1 · Might 8
Printings: OGN-011/298

> Other friendly units enter ready.
-/
def OGN_011.meta : CardDef :=
  { id := ⟨"OGN-011"⟩,
    name := "Magma Wurm",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.fury],
    cost := some ⟨8, [.domain .fury]⟩,
    might := some 8,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Magma Wurm: the effect is not written yet. -/
def OGN_011 : CardDef := OGN_011.meta

-- BEGIN GENERATED OGN-012
/--
**Noxus Hopeful** — Unit · Fury · Energy 4 · Might 4
Printings: OGN-012/298

> [Legion] — I cost :rb_energy_2: less. (Get the effect if you've played another card this
> turn.)
-/
def OGN_012.meta : CardDef :=
  { id := ⟨"OGN-012"⟩,
    name := "Noxus Hopeful",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .legion }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Noxus Hopeful: the effect is not written yet. -/
def OGN_012 : CardDef := OGN_012.meta

-- BEGIN GENERATED OGN-013
/--
**Pouty Poro** — Unit · Fury · Energy 2 · Might 2
Printings: OGN-013/298, UNL-220/219

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
-/
def OGN_013.meta : CardDef :=
  { id := ⟨"OGN-013"⟩,
    name := "Pouty Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"OGN"⟩, ⟨"UNL"⟩] }
-- END GENERATED

/-- Pouty Poro. -/
def OGN_013 : CardDef :=
  { OGN_013.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-014
/--
**Sky Splitter** — Spell · Fury · Energy 8 + Power 1
Printings: OGN-014/298

> [Action] (Play on your turn or in showdowns.)
> This spell's Energy cost is reduced by the highest Might among units you control.
> Deal 5 to a unit at a battlefield.
-/
def OGN_014.meta : CardDef :=
  { id := ⟨"OGN-014"⟩,
    name := "Sky Splitter",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨8, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Sky Splitter: the effect is not written yet. -/
def OGN_014 : CardDef := OGN_014.meta

-- BEGIN GENERATED OGN-015
/--
**Captain Farron** — Unit · Fury · Energy 4 + Power 1 · Might 5
Printings: OGN-015/298

> Other friendly units here have [Assault]. (+1 :rb_might: while they're attackers.)
-/
def OGN_015.meta : CardDef :=
  { id := ⟨"OGN-015"⟩,
    name := "Captain Farron",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Captain Farron. -/
def OGN_015 : CardDef :=
  { OGN_015.meta with
    abilities := [.passive .always
      [.keyword (Selector.all .friendly .here [.ofType .unit, .notSelf]) ⟨.assault, .amount 1⟩]],
    status := .drafted }

-- BEGIN GENERATED OGN-016
/--
**Dangerous Duo** — Unit · Fury · Energy 3 · Might 3
Printings: OGN-016/298

> [Legion] — When you play me, give a unit +2 :rb_might: this turn. (Get the effect if you've
> played another card this turn.)
-/
def OGN_016.meta : CardDef :=
  { id := ⟨"OGN-016"⟩,
    name := "Dangerous Duo",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Bandle City"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .legion }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Dangerous Duo. -/
def OGN_016 : CardDef :=
  { OGN_016.meta with
    abilities := [.triggered { Trigger.onSelf .play with condition := .legion }
        (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-017
/--
**Iron Ballista** — Gear · Fury · Energy 3
Printings: OGN-017/298

> This enters exhausted.
> :rb_exhaust:: Deal 2 to a unit at a battlefield.
-/
def OGN_017.meta : CardDef :=
  { id := ⟨"OGN-017"⟩,
    name := "Iron Ballista",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Iron Ballista. -/
def OGN_017 : CardDef :=
  { OGN_017.meta with
    abilities :=
      [.triggered (.onSelf .play) (.of [] (.prim (.exhaust .self))) .unlimited,
       .activated [.exhaustSelf] .normal
        (.of [.targetOf .one .any .atBattlefield [.ofType .unit]] (.prim (.deal (.slot 0) (.const 2))))
        .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-018
/--
**Noxus Saboteur** — Unit · Fury · Energy 3 · Might 3
Printings: OGN-018/298

> Your opponents' [Hidden] cards can't be revealed here.
-/
def OGN_018.meta : CardDef :=
  { id := ⟨"OGN-018"⟩,
    name := "Noxus Saboteur",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Noxus Saboteur: the effect is not written yet. -/
def OGN_018 : CardDef := OGN_018.meta

-- BEGIN GENERATED OGN-019
/--
**Raging Soul** — Unit · Fury · Energy 4 · Might 4
Printings: OGN-019/298

> If you've discarded a card this turn, I have [Assault] and [Ganking]. (+1 :rb_might: while I'm
> an attacker. I can move from battlefield to battlefield.)
-/
def OGN_019.meta : CardDef :=
  { id := ⟨"OGN-019"⟩,
    name := "Raging Soul",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Raging Soul: the effect is not written yet. -/
def OGN_019 : CardDef := OGN_019.meta

-- BEGIN GENERATED OGN-020
/--
**Scrapyard Champion** — Unit · Fury · Energy 5 + Power 1 · Might 5
Printings: OGN-020/298

> [Legion] — When you play me, discard 2, then draw 2. (Get the effect if you've played another
> card this turn.)
-/
def OGN_020.meta : CardDef :=
  { id := ⟨"OGN-020"⟩,
    name := "Scrapyard Champion",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Bandle City"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 5,
    keywords := [{ keyword := .legion }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Scrapyard Champion. -/
def OGN_020 : CardDef :=
  { OGN_020.meta with
    abilities := [.triggered { Trigger.onSelf .play with condition := .legion }
        (.of []
        (.seqOf [.prim (.discard .you (.const 2)),
          .prim (.draw .you (.const 2))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-021
/--
**Sun Disc** — Gear · Fury · Energy 2 + Power 1
Printings: OGN-021/298

> :rb_exhaust:: [Legion] — The next unit you play this turn enters ready. (Get the effect if
> you've played another card this turn.)
-/
def OGN_021.meta : CardDef :=
  { id := ⟨"OGN-021"⟩,
    name := "Sun Disc",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Sun Disc: the effect is not written yet. -/
def OGN_021 : CardDef := OGN_021.meta

-- BEGIN GENERATED OGN-022
/--
**Thermo Beam** — Spell · Fury · Energy 5 + Power 2
Printings: OGN-022/298

> [Action] (Play on your turn or in showdowns.)
> Kill all gear.
-/
def OGN_022.meta : CardDef :=
  { id := ⟨"OGN-022"⟩,
    name := "Thermo Beam",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury, .domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Thermo Beam. -/
def OGN_022 : CardDef :=
  { OGN_022.meta with
    spellEffect := some (.of []
      (.prim (.kill (Selector.all .any .anywhere [.ofType .gear])))),
    status := .drafted }

-- BEGIN GENERATED OGN-023
/--
**Unlicensed Armory** — Gear · Fury · Energy 2
Printings: OGN-023/298

> Discard 1, :rb_exhaust:: Choose a friendly unit. The next time it dies this turn, you may pay
> :rb_rune_fury: to recall it exhausted instead. (Send it to base. This isn't a move.)
-/
def OGN_023.meta : CardDef :=
  { id := ⟨"OGN-023"⟩,
    name := "Unlicensed Armory",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Unlicensed Armory: the effect is not written yet. -/
def OGN_023 : CardDef := OGN_023.meta

-- BEGIN GENERATED OGN-024
/--
**Void Seeker** — Spell · Fury · Energy 3 + Power 1
Printings: OGN-024/298

> [Action] (Play on your turn or in showdowns.)
> Deal 4 to a unit at a battlefield. Draw 1.
-/
def OGN_024.meta : CardDef :=
  { id := ⟨"OGN-024"⟩,
    name := "Void Seeker",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Void Seeker. -/
def OGN_024 : CardDef :=
  { OGN_024.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.seqOf [.prim (.deal (.slot 0) (.const 4)),
        .prim (.draw .you (.const 1))])),
    status := .drafted }

-- BEGIN GENERATED OGN-025
/--
**Blind Fury** — Spell · Fury · Energy 4 + Power 2
Printings: OGN-025/298

> [Action] (Play on your turn or in showdowns.)
> Each opponent reveals the top card of their Main Deck. Choose one and banish it, then play it,
> ignoring its cost. Then recycle the rest.
-/
def OGN_025.meta : CardDef :=
  { id := ⟨"OGN-025"⟩,
    name := "Blind Fury",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury, .domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Blind Fury: the effect is not written yet. -/
def OGN_025 : CardDef := OGN_025.meta

-- BEGIN GENERATED OGN-026
/--
**Brynhir Thundersong** — Unit · Fury · Energy 6 · Might 5
Printings: OGN-026/298

> When you play me, opponents can't play cards this turn.
-/
def OGN_026.meta : CardDef :=
  { id := ⟨"OGN-026"⟩,
    name := "Brynhir Thundersong",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.fury],
    cost := some ⟨6, []⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Brynhir Thundersong: the effect is not written yet. -/
def OGN_026 : CardDef := OGN_026.meta

-- BEGIN GENERATED OGN-027
/--
**Darius, Trifarian** — Unit · Fury · Energy 5 + Power 1 · Might 5
Printings: OGN-027/298, OGN-027a/298

> When you play your second card in a turn, give me +2 :rb_might: this turn and ready me.
-/
def OGN_027.meta : CardDef :=
  { id := ⟨"OGN-027"⟩,
    name := "Darius",
    subtitle := some "Trifarian",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Darius"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Darius, Trifarian: the effect is not written yet. -/
def OGN_027 : CardDef := OGN_027.meta

-- BEGIN GENERATED OGN-028
/--
**Draven, Showboat** — Unit · Fury · Energy 5 + Power 1 · Might 3
Printings: OGN-028/298, VEN-172/166

> My Might is increased by your points.
-/
def OGN_028.meta : CardDef :=
  { id := ⟨"OGN-028"⟩,
    name := "Draven",
    subtitle := some "Showboat",
    types := [.unit],
    tags := [⟨"Draven"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 3,
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Draven, Showboat: the effect is not written yet. -/
def OGN_028 : CardDef := OGN_028.meta

-- BEGIN GENERATED OGN-029
/--
**Falling Star** — Spell · Fury · Energy 2 + Power 2
Printings: OGN-029/298

> Deal 3 to a unit.
> Deal 3 to a unit.
-/
def OGN_029.meta : CardDef :=
  { id := ⟨"OGN-029"⟩,
    name := "Falling Star",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury, .domain .fury]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Falling Star. -/
def OGN_029 : CardDef :=
  { OGN_029.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit],
        .targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.prim (.deal (.slot 0) (.const 3)),
        .prim (.deal (.slot 1) (.const 3))])),
    status := .drafted }

-- BEGIN GENERATED OGN-030
/--
**Jinx, Demolitionist** — Unit · Fury · Energy 3 + Power 1 · Might 4
Printings: OGN-030/298, OGN-030a/298, VEN-168/166

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> [Assault 2] (+2 :rb_might: while I'm an attacker.)
> When you play me, discard 2.
-/
def OGN_030.meta : CardDef :=
  { id := ⟨"OGN-030"⟩,
    name := "Jinx",
    subtitle := some "Demolitionist",
    types := [.unit],
    tags := [⟨"Jinx"⟩, ⟨"Zaun"⟩],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    might := some 4,
    keywords := [{ keyword := .accelerate },
      { keyword := .assault, arg := .amount 2 }],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Jinx, Demolitionist. -/
def OGN_030 : CardDef :=
  { OGN_030.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.discard .you (.const 2)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-031
/--
**Raging Firebrand** — Unit · Fury · Energy 6 + Power 1 · Might 4
Printings: OGN-031/298

> When you play me, the next spell you play this turn costs :rb_energy_5: less.
-/
def OGN_031.meta : CardDef :=
  { id := ⟨"OGN-031"⟩,
    name := "Raging Firebrand",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Mount Targon"⟩],
    domains := [.fury],
    cost := some ⟨6, [.domain .fury]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Raging Firebrand: the effect is not written yet. -/
def OGN_031 : CardDef := OGN_031.meta

-- BEGIN GENERATED OGN-032
/--
**Ravenborn Tome** — Gear · Fury · Energy 3
Printings: OGN-032/298

> :rb_exhaust:: The next spell you play this turn deals 1 Bonus Damage. (Each instance of damage
> the spell deals is increased by 1.)
-/
def OGN_032.meta : CardDef :=
  { id := ⟨"OGN-032"⟩,
    name := "Ravenborn Tome",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Ravenborn Tome: the effect is not written yet. -/
def OGN_032 : CardDef := OGN_032.meta

-- BEGIN GENERATED OGN-033
/--
**Shakedown** — Spell · Fury · Energy 2 + Power 1
Printings: OGN-033/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose an enemy unit. Deal 6 to it unless its controller has you draw 2.
-/
def OGN_033.meta : CardDef :=
  { id := ⟨"OGN-033"⟩,
    name := "Shakedown",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Shakedown: the effect is not written yet. -/
def OGN_033 : CardDef := OGN_033.meta

-- BEGIN GENERATED OGN-034
/--
**Tryndamere, Barbarian** — Unit · Fury · Energy 7 + Power 2 · Might 8
Printings: OGN-034/298

> When I conquer after an attack, if you assigned 5 or more excess damage to enemy units, you
> score 1 point.
-/
def OGN_034.meta : CardDef :=
  { id := ⟨"OGN-034"⟩,
    name := "Tryndamere",
    subtitle := some "Barbarian",
    types := [.unit],
    tags := [⟨"Tryndamere"⟩, ⟨"Freljord"⟩],
    domains := [.fury],
    cost := some ⟨7, [.domain .fury, .domain .fury]⟩,
    might := some 8,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Tryndamere, Barbarian: the effect is not written yet. -/
def OGN_034 : CardDef := OGN_034.meta

-- BEGIN GENERATED OGN-035
/--
**Vayne, Hunter** — Unit · Fury · Energy 4 + Power 1 · Might 2
Printings: OGN-035/298, SFD-223*/221, SFD-223/221

> [Assault 3] (+3 :rb_might: while I'm an attacker.)
> If an opponent controls a battlefield, I enter ready.
> When I conquer, you may pay :rb_energy_1: to return me to my owner's hand.
-/
def OGN_035.meta : CardDef :=
  { id := ⟨"OGN-035"⟩,
    name := "Vayne",
    subtitle := some "Hunter",
    types := [.unit],
    tags := [⟨"Vayne"⟩, ⟨"Demacia"⟩],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    might := some 2,
    keywords := [{ keyword := .assault, arg := .amount 3 }],
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Vayne, Hunter: the effect is not written yet. -/
def OGN_035 : CardDef := OGN_035.meta

-- BEGIN GENERATED OGN-036
/--
**Vi, Destructive** — Unit · Fury · Energy 2 + Power 1 · Might 3
Printings: OGN-036/298, VEN-167/166

> [Ganking] (I can move from battlefield to battlefield.)
> Recycle 1 from your trash: Give me +1 :rb_might: this turn.
-/
def OGN_036.meta : CardDef :=
  { id := ⟨"OGN-036"⟩,
    name := "Vi",
    subtitle := some "Destructive",
    types := [.unit],
    tags := [⟨"Vi"⟩, ⟨"Piltover"⟩],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    might := some 3,
    keywords := [{ keyword := .ganking }],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Vi, Destructive: the effect is not written yet. -/
def OGN_036 : CardDef := OGN_036.meta

-- BEGIN GENERATED OGN-037
/--
**Immortal Phoenix** — Unit · Fury · Energy 3 + Power 1 · Might 3
Printings: OGN-037/298

> [Assault 2] (+2 :rb_might: while I'm an attacker.)
> When you kill a unit with a spell, you may pay :rb_energy_1::rb_rune_fury: to play me from
> your trash.
-/
def OGN_037.meta : CardDef :=
  { id := ⟨"OGN-037"⟩,
    name := "Immortal Phoenix",
    types := [.unit],
    tags := [⟨"Spirit"⟩],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    might := some 3,
    keywords := [{ keyword := .assault, arg := .amount 2 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Immortal Phoenix: the effect is not written yet. -/
def OGN_037 : CardDef := OGN_037.meta

-- BEGIN GENERATED OGN-038
/--
**Kadregrin the Infernal** — Unit · Fury · Energy 9 + Power 2 · Might 9
Printings: OGN-038/298

> When you play me, draw 1 for each of your [Mighty] units. (A unit is Mighty while it has 5+
> :rb_might:.)
-/
def OGN_038.meta : CardDef :=
  { id := ⟨"OGN-038"⟩,
    name := "Kadregrin the Infernal",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Demacia"⟩],
    domains := [.fury],
    cost := some ⟨9, [.domain .fury, .domain .fury]⟩,
    might := some 9,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Kadregrin the Infernal: the effect is not written yet. -/
def OGN_038 : CardDef := OGN_038.meta

-- BEGIN GENERATED OGN-039
/--
**Kai'Sa, Survivor** — Unit · Fury · Energy 4 · Might 4
Printings: OGN-039/298, OGN-039a/298, VEN-SP1/006

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> When I conquer, draw 1.
-/
def OGN_039.meta : CardDef :=
  { id := ⟨"OGN-039"⟩,
    name := "Kai'Sa",
    subtitle := some "Survivor",
    types := [.unit],
    tags := [⟨"Kai'Sa"⟩, ⟨"The Void"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Kai'Sa, Survivor. -/
def OGN_039 : CardDef :=
  { OGN_039.meta with
    abilities := [.triggered (.onSelf .conquer)
        (.of []
        (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-040
/--
**Seal of Rage** — Gear · Fury · Energy 0 + Power 1
Printings: OGN-040/298, SFD-222/221

> :rb_exhaust:: [Reaction] — [Add] :rb_rune_fury:. (Abilities that add resources can't be
> reacted to.)
-/
def OGN_040.meta : CardDef :=
  { id := ⟨"OGN-040"⟩,
    name := "Seal of Rage",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨0, [.domain .fury]⟩,
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Seal of Rage. -/
def OGN_040 : CardDef :=
  { OGN_040.meta with
    abilities := [.activated [.exhaustSelf] .reaction
        (.of []
        (.prim (.addPower .you (.const 1) (some .fury) none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-041
/--
**Volibear, Furious** — Unit · Fury · Energy 10 + Power 2 · Might 9
Printings: OGN-041/298, OGN-041a/298

> [Deflect 2] (Opponents must pay :rb_rune_rainbow::rb_rune_rainbow: to choose me with a spell
> or ability.)
> When I attack, deal 5 damage split among any number of enemy units here.
-/
def OGN_041.meta : CardDef :=
  { id := ⟨"OGN-041"⟩,
    name := "Volibear",
    subtitle := some "Furious",
    types := [.unit],
    tags := [⟨"Volibear"⟩, ⟨"Freljord"⟩],
    domains := [.fury],
    cost := some ⟨10, [.domain .fury, .domain .fury]⟩,
    might := some 9,
    keywords := [{ keyword := .deflect, arg := .amount 2 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Volibear, Furious: the effect is not written yet. -/
def OGN_041 : CardDef := OGN_041.meta

-- BEGIN GENERATED OGN-042
/--
**Calm Rune** — Rune · Calm
Printings: OGN-042/298, OGN-042a/298, VEN-R02, RAD-R02, RAD-R02a

> (no text)
-/
def OGN_042.meta : CardDef :=
  { id := ⟨"OGN-042"⟩,
    name := "Calm Rune",
    types := [.rune],
    domains := [.calm],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Calm Rune. -/
def OGN_042 : CardDef :=
  { OGN_042.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-043
/--
**Charm** — Spell · Calm · Energy 1 + Power 1
Printings: OGN-043/298

> Move an enemy unit.
-/
def OGN_043.meta : CardDef :=
  { id := ⟨"OGN-043"⟩,
    name := "Charm",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, [.domain .calm]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Charm: the effect is not written yet. -/
def OGN_043 : CardDef := OGN_043.meta

-- BEGIN GENERATED OGN-044
/--
**Clockwork Keeper** — Unit · Calm · Energy 2 · Might 2
Printings: OGN-044/298

> As you play me, you may pay :rb_rune_calm: as an additional cost. If you do, draw 1.
-/
def OGN_044.meta : CardDef :=
  { id := ⟨"OGN-044"⟩,
    name := "Clockwork Keeper",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Clockwork Keeper. -/
def OGN_044 : CardDef :=
  { OGN_044.meta with
    additionalCost := some ⟨0, [.domain .calm]⟩,
    abilities := [.triggered { Trigger.onSelf .play with condition := .paid }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-045
/--
**Defy** — Spell · Calm · Energy 1 + Power 1
Printings: OGN-045/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Counter a spell that costs no more than :rb_energy_4: and no more than :rb_rune_rainbow:.
-/
def OGN_045.meta : CardDef :=
  { id := ⟨"OGN-045"⟩,
    name := "Defy",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, [.domain .calm]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Defy: the effect is not written yet. -/
def OGN_045 : CardDef := OGN_045.meta

-- BEGIN GENERATED OGN-046
/--
**En Garde** — Spell · Calm · Energy 1
Printings: OGN-046/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a friendly unit +1 :rb_might: this turn, then an additional +1 :rb_might: this turn if it
> is the only unit you control there.
-/
def OGN_046.meta : CardDef :=
  { id := ⟨"OGN-046"⟩,
    name := "En Garde",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- En Garde: the effect is not written yet. -/
def OGN_046 : CardDef := OGN_046.meta

-- BEGIN GENERATED OGN-047
/--
**Find Your Center** — Spell · Calm · Energy 3
Printings: OGN-047/298

> [Action] (Play on your turn or in showdowns.)
> If an opponent's score is within 3 points of the Victory Score, this costs :rb_energy_2: less.
> Draw 1 and channel 1 rune exhausted.
-/
def OGN_047.meta : CardDef :=
  { id := ⟨"OGN-047"⟩,
    name := "Find Your Center",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Find Your Center: the effect is not written yet. -/
def OGN_047 : CardDef := OGN_047.meta

-- BEGIN GENERATED OGN-048
/--
**Meditation** — Spell · Calm · Energy 2
Printings: OGN-048/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> As an additional cost to play this, you may exhaust a friendly unit. If you do, draw 2.
> Otherwise, draw 1.
-/
def OGN_048.meta : CardDef :=
  { id := ⟨"OGN-048"⟩,
    name := "Meditation",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Meditation: the effect is not written yet. -/
def OGN_048 : CardDef := OGN_048.meta

-- BEGIN GENERATED OGN-049
/--
**Playful Phantom** — Unit · Calm · Energy 5 · Might 5
Printings: OGN-049/298

> (no text)
-/
def OGN_049.meta : CardDef :=
  { id := ⟨"OGN-049"⟩,
    name := "Playful Phantom",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.calm],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Playful Phantom. -/
def OGN_049 : CardDef :=
  { OGN_049.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-050
/--
**Rune Prison** — Spell · Calm · Energy 2 + Power 1
Printings: OGN-050/298

> [Action] (Play on your turn or in showdowns.)
> Stun a unit. (It doesn't deal combat damage this turn.)
-/
def OGN_050.meta : CardDef :=
  { id := ⟨"OGN-050"⟩,
    name := "Rune Prison",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, [.domain .calm]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Rune Prison. -/
def OGN_050 : CardDef :=
  { OGN_050.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.prim (.stun (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED OGN-051
/--
**Solari Shieldbearer** — Unit · Calm · Energy 3 · Might 2
Printings: OGN-051/298

> When you play me, stun a unit. (It doesn't deal combat damage this turn.)
-/
def OGN_051.meta : CardDef :=
  { id := ⟨"OGN-051"⟩,
    name := "Solari Shieldbearer",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 2,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Solari Shieldbearer. -/
def OGN_051 : CardDef :=
  { OGN_051.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .anywhere [.ofType .unit]] (.prim (.stun (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-052
/--
**Stalwart Poro** — Unit · Calm · Energy 2 · Might 2
Printings: OGN-052/298

> [Shield] (+1 :rb_might: while I'm a defender.)
-/
def OGN_052.meta : CardDef :=
  { id := ⟨"OGN-052"⟩,
    name := "Stalwart Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .shield, arg := .amount 1 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Stalwart Poro. -/
def OGN_052 : CardDef :=
  { OGN_052.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-053
/--
**Stand United** — Spell · Calm · Energy 3
Printings: OGN-053/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Buff a friendly unit. Buffs give an additional +1 :rb_might: to friendly units this turn. (To
> buff a unit, give it a +1 :rb_might: buff if it doesn't already have one.)
-/
def OGN_053.meta : CardDef :=
  { id := ⟨"OGN-053"⟩,
    name := "Stand United",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Stand United: the effect is not written yet. -/
def OGN_053 : CardDef := OGN_053.meta

-- BEGIN GENERATED OGN-054
/--
**Sunlit Guardian** — Unit · Calm · Energy 3 · Might 3
Printings: OGN-054/298

> [Shield] (+1 :rb_might: while I'm a defender.)
> [Tank] (I must be assigned combat damage first.)
-/
def OGN_054.meta : CardDef :=
  { id := ⟨"OGN-054"⟩,
    name := "Sunlit Guardian",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .shield, arg := .amount 1 },
      { keyword := .tank }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Sunlit Guardian. -/
def OGN_054 : CardDef :=
  { OGN_054.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-055
/--
**Wielder of Water** — Unit · Calm · Energy 3 · Might 2
Printings: OGN-055/298

> While I'm attacking or defending alone, I have +2 :rb_might:.
-/
def OGN_055.meta : CardDef :=
  { id := ⟨"OGN-055"⟩,
    name := "Wielder of Water",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 2,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Wielder of Water: the effect is not written yet. -/
def OGN_055 : CardDef := OGN_055.meta

-- BEGIN GENERATED OGN-056
/--
**Adaptatron** — Unit · Calm · Energy 4 · Might 3
Printings: OGN-056/298

> When I conquer, you may kill a gear. If you do, buff me. (If I don't have a buff, I get a +1
> :rb_might: buff.)
-/
def OGN_056.meta : CardDef :=
  { id := ⟨"OGN-056"⟩,
    name := "Adaptatron",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Piltover"⟩],
    domains := [.calm],
    cost := some ⟨4, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Adaptatron: the effect is not written yet. -/
def OGN_056 : CardDef := OGN_056.meta

-- BEGIN GENERATED OGN-057
/--
**Block** — Spell · Calm · Energy 2
Printings: OGN-057/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Give a unit [Shield 3] and [Tank] this turn. (+3 :rb_might: while it's a defender. It must be
> assigned combat damage first.)
-/
def OGN_057.meta : CardDef :=
  { id := ⟨"OGN-057"⟩,
    name := "Block",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Block. -/
def OGN_057 : CardDef :=
  { OGN_057.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.grant (.slot 0) (.keyword .it ⟨.shield, .amount 3⟩) .thisTurn,
        .grant (.slot 0) (.keyword .it ⟨.tank, .none⟩) .thisTurn])),
    status := .drafted }

-- BEGIN GENERATED OGN-058
/--
**Discipline** — Spell · Calm · Energy 2
Printings: OGN-058/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a unit +2 :rb_might: this turn. Draw 1.
-/
def OGN_058.meta : CardDef :=
  { id := ⟨"OGN-058"⟩,
    name := "Discipline",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Discipline. -/
def OGN_058 : CardDef :=
  { OGN_058.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn,
        .prim (.draw .you (.const 1))])),
    status := .drafted }

-- BEGIN GENERATED OGN-059
/--
**Eclipse Herald** — Unit · Calm · Energy 7 + Power 1 · Might 7
Printings: OGN-059/298

> When you stun an enemy unit, ready me and give me +1 :rb_might: this turn.
-/
def OGN_059.meta : CardDef :=
  { id := ⟨"OGN-059"⟩,
    name := "Eclipse Herald",
    types := [.unit],
    tags := [⟨"Bird"⟩, ⟨"Mount Targon"⟩],
    domains := [.calm],
    cost := some ⟨7, [.domain .calm]⟩,
    might := some 7,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Eclipse Herald: the effect is not written yet. -/
def OGN_059 : CardDef := OGN_059.meta

-- BEGIN GENERATED OGN-060
/--
**Mask of Foresight** — Gear · Calm · Energy 2
Printings: OGN-060/298

> When a friendly unit attacks or defends alone, give it +1 :rb_might: this turn.
-/
def OGN_060.meta : CardDef :=
  { id := ⟨"OGN-060"⟩,
    name := "Mask of Foresight",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Mask of Foresight: the effect is not written yet. -/
def OGN_060 : CardDef := OGN_060.meta

-- BEGIN GENERATED OGN-061
/--
**Poro Herder** — Unit · Calm · Energy 3 + Power 1 · Might 3
Printings: OGN-061/298

> When you play me, if you control a Poro, buff me and draw 1. (If I don't have a buff, I get a
> +1 :rb_might: buff.)
-/
def OGN_061.meta : CardDef :=
  { id := ⟨"OGN-061"⟩,
    name := "Poro Herder",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Poro Herder: the effect is not written yet. -/
def OGN_061 : CardDef := OGN_061.meta

-- BEGIN GENERATED OGN-062
/--
**Reinforce** — Spell · Calm · Energy 5
Printings: OGN-062/298

> Look at the top 5 cards of your Main Deck. You may banish a unit from among them, then play
> it, reducing its cost by :rb_energy_5:. Recycle the remaining cards.
-/
def OGN_062.meta : CardDef :=
  { id := ⟨"OGN-062"⟩,
    name := "Reinforce",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨5, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Reinforce: the effect is not written yet. -/
def OGN_062 : CardDef := OGN_062.meta

-- BEGIN GENERATED OGN-063
/--
**Spirit's Refuge** — Gear · Calm · Energy 2 + Power 1
Printings: OGN-063/298

> When you play this, buff a friendly unit. (If it doesn't have a buff, it gets a +1 :rb_might:
> buff.)
> Friendly buffed units have [Deflect] if they didn't already. (Opponents must pay
> :rb_rune_rainbow: to choose those units with a spell or ability.)
-/
def OGN_063.meta : CardDef :=
  { id := ⟨"OGN-063"⟩,
    name := "Spirit's Refuge",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨2, [.domain .calm]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Spirit's Refuge: the effect is not written yet. -/
def OGN_063 : CardDef := OGN_063.meta

-- BEGIN GENERATED OGN-064
/--
**Wind Wall** — Spell · Calm · Energy 3 + Power 2
Printings: OGN-064/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Counter a spell.
-/
def OGN_064.meta : CardDef :=
  { id := ⟨"OGN-064"⟩,
    name := "Wind Wall",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm, .domain .calm]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Wind Wall: the effect is not written yet. -/
def OGN_064 : CardDef := OGN_064.meta

-- BEGIN GENERATED OGN-065
/--
**Wizened Elder** — Unit · Calm · Energy 4 · Might 4
Printings: OGN-065/298

> While I'm buffed, I have an additional +1 :rb_might:.
-/
def OGN_065.meta : CardDef :=
  { id := ⟨"OGN-065"⟩,
    name := "Wizened Elder",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Wizened Elder. -/
def OGN_065 : CardDef :=
  { OGN_065.meta with
    abilities := [.passive (.matches .self .buffed) [.mightPlus .self (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED OGN-066
/--
**Ahri, Alluring** — Unit · Calm · Energy 5 + Power 1 · Might 4
Printings: OGN-066/298, OGN-066a/298

> When I hold, you score 1 point.
-/
def OGN_066.meta : CardDef :=
  { id := ⟨"OGN-066"⟩,
    name := "Ahri",
    subtitle := some "Alluring",
    types := [.unit],
    tags := [⟨"Ahri"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Ahri, Alluring: the effect is not written yet. -/
def OGN_066 : CardDef := OGN_066.meta

-- BEGIN GENERATED OGN-067
/--
**Blitzcrank, Impassive** — Unit · Calm · Energy 5 + Power 1 · Might 5
Printings: OGN-067/298

> [Tank] (I must be assigned combat damage first.)
> When you play me to a battlefield, you may move an enemy unit to here.
> When I hold, return me to my owner's hand.
-/
def OGN_067.meta : CardDef :=
  { id := ⟨"OGN-067"⟩,
    name := "Blitzcrank",
    subtitle := some "Impassive",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Blitzcrank"⟩, ⟨"Zaun"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 5,
    keywords := [{ keyword := .tank }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Blitzcrank, Impassive: the effect is not written yet. -/
def OGN_067 : CardDef := OGN_067.meta

-- BEGIN GENERATED OGN-068
/--
**Caitlyn, Patrolling** — Unit · Calm · Energy 3 + Power 1 · Might 3
Printings: OGN-068/298

> I must be assigned combat damage last.
> :rb_exhaust:: Deal damage equal to my Might to a unit at a battlefield. Use this ability only
> while I'm at a battlefield.
-/
def OGN_068.meta : CardDef :=
  { id := ⟨"OGN-068"⟩,
    name := "Caitlyn",
    subtitle := some "Patrolling",
    types := [.unit],
    tags := [⟨"Caitlyn"⟩, ⟨"Piltover"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Caitlyn, Patrolling: the effect is not written yet. -/
def OGN_068 : CardDef := OGN_068.meta

-- BEGIN GENERATED OGN-069
/--
**Last Stand** — Spell · Calm · Energy 3 + Power 1
Printings: OGN-069/298

> [Action] (Play on your turn or in showdowns.)
> Double a friendly unit's Might this turn. Give it [Temporary]. (Kill it at the start of its
> controller's Beginning Phase, before scoring.)
-/
def OGN_069.meta : CardDef :=
  { id := ⟨"OGN-069"⟩,
    name := "Last Stand",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Last Stand: the effect is not written yet. -/
def OGN_069 : CardDef := OGN_069.meta

-- BEGIN GENERATED OGN-070
/--
**Mageseeker Warden** — Unit · Calm · Energy 6 + Power 1 · Might 5
Printings: OGN-070/298

> While I'm at a battlefield, opponents can only play units to their base.
> While I'm at a battlefield, spells and abilities can't ready enemy units and gear.
-/
def OGN_070.meta : CardDef :=
  { id := ⟨"OGN-070"⟩,
    name := "Mageseeker Warden",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.calm],
    cost := some ⟨6, [.domain .calm]⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Mageseeker Warden: the effect is not written yet. -/
def OGN_070 : CardDef := OGN_070.meta

-- BEGIN GENERATED OGN-071
/--
**Party Favors** — Spell · Calm · Energy 3
Printings: OGN-071/298

> Each other player chooses Cards or Runes. For each player that chooses Cards, you and that
> player each draw 1. For each player that chooses Runes, you and that player each channel 1
> rune exhausted.
-/
def OGN_071.meta : CardDef :=
  { id := ⟨"OGN-071"⟩,
    name := "Party Favors",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Party Favors: the effect is not written yet. -/
def OGN_071 : CardDef := OGN_071.meta

-- BEGIN GENERATED OGN-072
/--
**Solari Shrine** — Gear · Calm · Energy 3
Printings: OGN-072/298

> When you kill a stunned enemy unit, you may exhaust this to draw 1.
-/
def OGN_072.meta : CardDef :=
  { id := ⟨"OGN-072"⟩,
    name := "Solari Shrine",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Solari Shrine: the effect is not written yet. -/
def OGN_072 : CardDef := OGN_072.meta

-- BEGIN GENERATED OGN-073
/--
**Sona, Harmonious** — Unit · Calm · Energy 4 + Power 1 · Might 4
Printings: OGN-073/298, VEN-SP2/006

> While I'm at a battlefield, ready 4 friendly runes at the end of your turn.
-/
def OGN_073.meta : CardDef :=
  { id := ⟨"OGN-073"⟩,
    name := "Sona",
    subtitle := some "Harmonious",
    types := [.unit],
    tags := [⟨"Sona"⟩, ⟨"Demacia"⟩],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Sona, Harmonious: the effect is not written yet. -/
def OGN_073 : CardDef := OGN_073.meta

-- BEGIN GENERATED OGN-074
/--
**Taric, Protector** — Unit · Calm · Energy 4 + Power 1 · Might 4
Printings: OGN-074/298

> [Shield] (+1 :rb_might: while I'm a defender.)
> [Tank] (I must be assigned combat damage first.)
> Other friendly units here have [Shield].
-/
def OGN_074.meta : CardDef :=
  { id := ⟨"OGN-074"⟩,
    name := "Taric",
    subtitle := some "Protector",
    types := [.unit],
    tags := [⟨"Taric"⟩, ⟨"Mount Targon"⟩],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    might := some 4,
    keywords := [{ keyword := .shield, arg := .amount 1 },
      { keyword := .tank }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Taric, Protector. -/
def OGN_074 : CardDef :=
  { OGN_074.meta with
    abilities := [.passive .always
      [.keyword (Selector.all .friendly .here [.ofType .unit, .notSelf]) ⟨.shield, .amount 1⟩]],
    status := .drafted }

-- BEGIN GENERATED OGN-075
/--
**Tasty Faefolk** — Unit · Calm · Energy 7 · Might 6
Printings: OGN-075/298

> [Accelerate] (You may pay :rb_energy_1::rb_rune_calm: as an additional cost to have me enter
> ready.)
> [Deathknell] — Channel 2 runes exhausted and draw 1. (When I die, get the effect.)
-/
def OGN_075.meta : CardDef :=
  { id := ⟨"OGN-075"⟩,
    name := "Tasty Faefolk",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Bandle City"⟩],
    domains := [.calm],
    cost := some ⟨7, []⟩,
    might := some 6,
    keywords := [{ keyword := .accelerate },
      { keyword := .deathknell }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Tasty Faefolk. -/
def OGN_075 : CardDef :=
  { OGN_075.meta with
    abilities := [.triggered (.onSelf .die)
        (.of []
        (.seqOf [.prim (.channel .you (.const 0) (.const 2)),
          .prim (.draw .you (.const 1))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-076
/--
**Yasuo, Remorseful** — Unit · Calm · Energy 6 + Power 2 · Might 6
Printings: OGN-076/298, OGN-076a/298

> When I attack, deal damage equal to my Might to an enemy unit here.
-/
def OGN_076.meta : CardDef :=
  { id := ⟨"OGN-076"⟩,
    name := "Yasuo",
    subtitle := some "Remorseful",
    types := [.unit],
    tags := [⟨"Yasuo"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨6, [.domain .calm, .domain .calm]⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Yasuo, Remorseful. -/
def OGN_076 : CardDef :=
  { OGN_076.meta with
    abilities := [.triggered (.onSelf .attack)
      (.of [.targetOf .one .enemy .here [.ofType .unit]]
        (.prim (.deal (.slot 0) (.mightOf .self)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-077
/--
**Zhonya's Hourglass** — Gear · Calm · Energy 2
Printings: OGN-077/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> The next time a friendly unit would die, kill this instead. Recall that unit exhausted. (Send
> it to base. This isn't a move.)
-/
def OGN_077.meta : CardDef :=
  { id := ⟨"OGN-077"⟩,
    name := "Zhonya's Hourglass",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Zhonya's Hourglass: the effect is not written yet. -/
def OGN_077 : CardDef := OGN_077.meta

-- BEGIN GENERATED OGN-078
/--
**Lee Sin, Ascetic** — Unit · Calm · Energy 5 + Power 1 · Might 5
Printings: OGN-078/298, OGN-078a/298

> [Shield] (+1 :rb_might: while I'm a defender.)
> :rb_exhaust:: Buff me. (I get a +1 :rb_might: buff.)
> I can have any number of buffs.
-/
def OGN_078.meta : CardDef :=
  { id := ⟨"OGN-078"⟩,
    name := "Lee Sin",
    subtitle := some "Ascetic",
    types := [.unit],
    tags := [⟨"Lee Sin"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 5,
    keywords := [{ keyword := .shield, arg := .amount 1 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Lee Sin, Ascetic: the effect is not written yet. -/
def OGN_078 : CardDef := OGN_078.meta

-- BEGIN GENERATED OGN-079
/--
**Leona, Zealot** — Unit · Calm · Energy 6 + Power 1 · Might 6
Printings: OGN-079/298, OGN-079a/298

> If an opponent's score is within 3 points of the Victory Score, I enter ready.
> Stunned enemy units here have -8 :rb_might:, to a minimum of 1 :rb_might:.
-/
def OGN_079.meta : CardDef :=
  { id := ⟨"OGN-079"⟩,
    name := "Leona",
    subtitle := some "Zealot",
    types := [.unit],
    tags := [⟨"Leona"⟩, ⟨"Mount Targon"⟩],
    domains := [.calm],
    cost := some ⟨6, [.domain .calm]⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Leona, Zealot: the effect is not written yet. -/
def OGN_079 : CardDef := OGN_079.meta

-- BEGIN GENERATED OGN-080
/--
**Mystic Reversal** — Spell · Calm · Energy 4 + Power 3
Printings: OGN-080/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Gain control of a spell. You may make new choices for it.
-/
def OGN_080.meta : CardDef :=
  { id := ⟨"OGN-080"⟩,
    name := "Mystic Reversal",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm, .domain .calm, .domain .calm]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Mystic Reversal: the effect is not written yet. -/
def OGN_080 : CardDef := OGN_080.meta

-- BEGIN GENERATED OGN-081
/--
**Seal of Focus** — Gear · Calm · Energy 0 + Power 1
Printings: OGN-081/298, SFD-226/221

> :rb_exhaust:: [Reaction] — [Add] :rb_rune_calm:. (Abilities that add resources can't be
> reacted to.)
-/
def OGN_081.meta : CardDef :=
  { id := ⟨"OGN-081"⟩,
    name := "Seal of Focus",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨0, [.domain .calm]⟩,
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Seal of Focus. -/
def OGN_081 : CardDef :=
  { OGN_081.meta with
    abilities := [.activated [.exhaustSelf] .reaction
        (.of []
        (.prim (.addPower .you (.const 1) (some .calm) none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-082
/--
**Whiteflame Protector** — Unit · Calm · Energy 8 + Power 2 · Might 8
Printings: OGN-082/298

> When you play me, give a unit +8 :rb_might: this turn.
-/
def OGN_082.meta : CardDef :=
  { id := ⟨"OGN-082"⟩,
    name := "Whiteflame Protector",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Mount Targon"⟩],
    domains := [.calm],
    cost := some ⟨8, [.domain .calm, .domain .calm]⟩,
    might := some 8,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Whiteflame Protector. -/
def OGN_082 : CardDef :=
  { OGN_082.meta with
    abilities := [.triggered (.onSelf .play)
        (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 8)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-083
/--
**Consult the Past** — Spell · Mind · Energy 4
Printings: OGN-083/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Reaction] (Play any time, even before spells and abilities resolve.)
> Draw 2.
-/
def OGN_083.meta : CardDef :=
  { id := ⟨"OGN-083"⟩,
    name := "Consult the Past",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Consult the Past. -/
def OGN_083 : CardDef :=
  { OGN_083.meta with
    spellEffect := some (.of []
      (.prim (.draw .you (.const 2)))),
    status := .drafted }

-- BEGIN GENERATED OGN-084
/--
**Eager Apprentice** — Unit · Mind · Energy 3 · Might 3
Printings: OGN-084/298

> While I'm at a battlefield, the Energy costs for spells you play is reduced by :rb_energy_1:,
> to a minimum of :rb_energy_1:.
-/
def OGN_084.meta : CardDef :=
  { id := ⟨"OGN-084"⟩,
    name := "Eager Apprentice",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Eager Apprentice: the effect is not written yet. -/
def OGN_084 : CardDef := OGN_084.meta

-- BEGIN GENERATED OGN-085
/--
**Falling Comet** — Spell · Mind · Energy 5
Printings: OGN-085/298

> [Action] (Play on your turn or in showdowns.)
> Deal 6 to a unit at a battlefield.
-/
def OGN_085.meta : CardDef :=
  { id := ⟨"OGN-085"⟩,
    name := "Falling Comet",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Falling Comet. -/
def OGN_085 : CardDef :=
  { OGN_085.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.prim (.deal (.slot 0) (.const 6)))),
    status := .drafted }

-- BEGIN GENERATED OGN-086
/--
**Jeweled Colossus** — Unit · Mind · Energy 5 · Might 5
Printings: OGN-086/298

> [Vision] (When you play me, look at the top card of your Main Deck. You may recycle it.)
> [Shield] (+1 :rb_might: while I'm a defender.)
-/
def OGN_086.meta : CardDef :=
  { id := ⟨"OGN-086"⟩,
    name := "Jeweled Colossus",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .vision },
      { keyword := .shield, arg := .amount 1 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Jeweled Colossus. -/
def OGN_086 : CardDef :=
  { OGN_086.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-087
/--
**Lecturing Yordle** — Unit · Mind · Energy 3 · Might 2
Printings: OGN-087/298

> [Tank] (I must be assigned combat damage first.)
> When you play me, draw 1.
-/
def OGN_087.meta : CardDef :=
  { id := ⟨"OGN-087"⟩,
    name := "Lecturing Yordle",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 2,
    keywords := [{ keyword := .tank }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Lecturing Yordle. -/
def OGN_087 : CardDef :=
  { OGN_087.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-088
/--
**Mega-Mech** — Unit · Mind · Energy 7 · Might 8
Printings: OGN-088/298

> (no text)
-/
def OGN_088.meta : CardDef :=
  { id := ⟨"OGN-088"⟩,
    name := "Mega-Mech",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨7, []⟩,
    might := some 8,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Mega-Mech. -/
def OGN_088 : CardDef :=
  { OGN_088.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-089
/--
**Mind Rune** — Rune · Mind
Printings: OGN-089/298, OGN-089a/298, VEN-R03, RAD-R03, RAD-R03a

> (no text)
-/
def OGN_089.meta : CardDef :=
  { id := ⟨"OGN-089"⟩,
    name := "Mind Rune",
    types := [.rune],
    domains := [.mind],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Mind Rune. -/
def OGN_089 : CardDef :=
  { OGN_089.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-090
/--
**Orb of Regret** — Gear · Mind · Energy 1
Printings: OGN-090/298

> :rb_exhaust:: Give a unit -1 :rb_might: this turn, to a minimum of 1 :rb_might:.
-/
def OGN_090.meta : CardDef :=
  { id := ⟨"OGN-090"⟩,
    name := "Orb of Regret",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨1, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Orb of Regret. -/
def OGN_090 : CardDef :=
  { OGN_090.meta with
    abilities := [.activated [.exhaustSelf] .normal
      (.of [.targetOf .one .any .anywhere [.ofType .unit]] (.grant (.slot 0) (.mightMinusMin .it (.const 1) 1) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-091
/--
**Pit Crew** — Unit · Mind · Energy 3 · Might 3
Printings: OGN-091/298

> When you play a gear, ready me.
-/
def OGN_091.meta : CardDef :=
  { id := ⟨"OGN-091"⟩,
    name := "Pit Crew",
    types := [.unit],
    tags := [⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Pit Crew. -/
def OGN_091 : CardDef :=
  { OGN_091.meta with
    abilities := [.triggered
      { event := .play, subject := Selector.all .friendly .anywhere [.ofType .gear] }
      (.of [] (.prim (.ready .self))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-092
/--
**Riptide Rex** — Unit · Mind · Energy 6 + Power 2 · Might 6
Printings: OGN-092/298

> When you play me, deal 6 to an enemy unit at a battlefield.
-/
def OGN_092.meta : CardDef :=
  { id := ⟨"OGN-092"⟩,
    name := "Riptide Rex",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind, .domain .mind]⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Riptide Rex. -/
def OGN_092 : CardDef :=
  { OGN_092.meta with
    abilities := [.triggered (.onSelf .play)
        (.of [.targetOf .one .enemy .atBattlefield [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 6)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-093
/--
**Smoke Screen** — Spell · Mind · Energy 2 + Power 1
Printings: OGN-093/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a unit -4 :rb_might: this turn, to a minimum of 1 :rb_might:.
-/
def OGN_093.meta : CardDef :=
  { id := ⟨"OGN-093"⟩,
    name := "Smoke Screen",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, [.domain .mind]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Smoke Screen. -/
def OGN_093 : CardDef :=
  { OGN_093.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.mightMinusMin .it (.const 4) 1) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED OGN-094
/--
**Sprite Call** — Spell · Mind · Energy 3
Printings: OGN-094/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Play a ready 3 :rb_might: Sprite unit token with [Temporary]. (Kill it at the start of its
> controller's Beginning Phase, before scoring.)
-/
def OGN_094.meta : CardDef :=
  { id := ⟨"OGN-094"⟩,
    name := "Sprite Call",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Sprite Call. -/
def OGN_094 : CardDef :=
  { OGN_094.meta with
    spellEffect := some (.of []
      (.prim (.create "Sprite" (.const 1) .atBase true))),
    status := .drafted }

-- BEGIN GENERATED OGN-095
/--
**Stupefy** — Spell · Mind · Energy 1
Printings: OGN-095/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a unit -1 :rb_might: this turn, to a minimum of 1 :rb_might:. Draw 1.
-/
def OGN_095.meta : CardDef :=
  { id := ⟨"OGN-095"⟩,
    name := "Stupefy",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Stupefy. -/
def OGN_095 : CardDef :=
  { OGN_095.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.grant (.slot 0) (.mightMinusMin .it (.const 1) 1) .thisTurn,
        .prim (.draw .you (.const 1))])),
    status := .drafted }

-- BEGIN GENERATED OGN-096
/--
**Watchful Sentry** — Unit · Mind · Energy 2 · Might 1
Printings: OGN-096/298

> [Deathknell] — Draw 1. (When I die, get the effect.)
-/
def OGN_096.meta : CardDef :=
  { id := ⟨"OGN-096"⟩,
    name := "Watchful Sentry",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Watchful Sentry. -/
def OGN_096 : CardDef :=
  { OGN_096.meta with
    abilities := [.triggered (.onSelf .die)
        (.of []
        (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-097
/--
**Blastcone Fae** — Unit · Mind · Energy 2 + Power 1 · Might 2
Printings: OGN-097/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me, give a unit -2 :rb_might: this turn, to a minimum of 1 :rb_might:.
-/
def OGN_097.meta : CardDef :=
  { id := ⟨"OGN-097"⟩,
    name := "Blastcone Fae",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨2, [.domain .mind]⟩,
    might := some 2,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Blastcone Fae. -/
def OGN_097 : CardDef :=
  { OGN_097.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightMinusMin .it (.const 2) 1) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-098
/--
**Energy Conduit** — Gear · Mind · Energy 3
Printings: OGN-098/298

> :rb_exhaust:: [Reaction] — [Add] :rb_energy_1:. (Abilities that add resources can't be reacted
> to.)
-/
def OGN_098.meta : CardDef :=
  { id := ⟨"OGN-098"⟩,
    name := "Energy Conduit",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Energy Conduit. -/
def OGN_098 : CardDef :=
  { OGN_098.meta with
    abilities := [.activated [.exhaustSelf] .reaction
        (.of []
        (.prim (.addEnergy .you (.const 1) none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-099
/--
**Garbage Grabber** — Gear · Mind · Energy 2
Printings: OGN-099/298

> Recycle 3 from your trash, :rb_energy_1:, :rb_exhaust:: Draw 1.
-/
def OGN_099.meta : CardDef :=
  { id := ⟨"OGN-099"⟩,
    name := "Garbage Grabber",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Garbage Grabber: the effect is not written yet. -/
def OGN_099 : CardDef := OGN_099.meta

-- BEGIN GENERATED OGN-100
/--
**Gemcraft Seer** — Unit · Mind · Energy 3 + Power 1 · Might 3
Printings: OGN-100/298

> [Vision] (When you play me, look at the top card of your Main Deck. You may recycle it.)
> Other friendly units have [Vision].
-/
def OGN_100.meta : CardDef :=
  { id := ⟨"OGN-100"⟩,
    name := "Gemcraft Seer",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    might := some 3,
    keywords := [{ keyword := .vision }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Gemcraft Seer: the effect is not written yet. -/
def OGN_100 : CardDef := OGN_100.meta

-- BEGIN GENERATED OGN-101
/--
**Mushroom Pouch** — Gear · Mind · Energy 2
Printings: OGN-101/298

> At the start of your Beginning Phase, if you control a facedown card at a battlefield, draw 1.
-/
def OGN_101.meta : CardDef :=
  { id := ⟨"OGN-101"⟩,
    name := "Mushroom Pouch",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Mushroom Pouch: the effect is not written yet. -/
def OGN_101 : CardDef := OGN_101.meta

-- BEGIN GENERATED OGN-102
/--
**Portal Rescue** — Spell · Mind · Energy 3 + Power 1
Printings: OGN-102/298

> [Action] (Play on your turn or in showdowns.)
> Banish a friendly unit, then play it to base, ignoring its cost.
-/
def OGN_102.meta : CardDef :=
  { id := ⟨"OGN-102"⟩,
    name := "Portal Rescue",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Portal Rescue: the effect is not written yet. -/
def OGN_102 : CardDef := OGN_102.meta

-- BEGIN GENERATED OGN-103
/--
**Ravenbloom Student** — Unit · Mind · Energy 2 · Might 2
Printings: OGN-103/298

> When you play a spell, give me +1 :rb_might: this turn.
-/
def OGN_103.meta : CardDef :=
  { id := ⟨"OGN-103"⟩,
    name := "Ravenbloom Student",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Ravenbloom Student. -/
def OGN_103 : CardDef :=
  { OGN_103.meta with
    abilities := [.triggered
      { event := .play, subject := Selector.all .friendly .anywhere [.ofType .spell] }
      (.of [] (.grant .self (.mightPlus .it (.const 1)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-104
/--
**Retreat** — Spell · Mind · Energy 1
Printings: OGN-104/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Return a friendly unit to its owner's hand. Its owner channels 1 rune exhausted.
-/
def OGN_104.meta : CardDef :=
  { id := ⟨"OGN-104"⟩,
    name := "Retreat",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Retreat. -/
def OGN_104 : CardDef :=
  { OGN_104.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
      (.seqOf [.prim (.returnToHand (.slot 0)), .prim (.channel .you (.const 0) (.const 1))])),
    status := .drafted }

-- BEGIN GENERATED OGN-105
/--
**Singularity** — Spell · Mind · Energy 6 + Power 2
Printings: OGN-105/298

> Deal 6 to each of up to two units.
-/
def OGN_105.meta : CardDef :=
  { id := ⟨"OGN-105"⟩,
    name := "Singularity",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind, .domain .mind]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Singularity: the effect is not written yet. -/
def OGN_105 : CardDef := OGN_105.meta

-- BEGIN GENERATED OGN-106
/--
**Sprite Mother** — Unit · Mind · Energy 4 + Power 1 · Might 3
Printings: OGN-106/298

> When you play me, play a ready 3 :rb_might: Sprite unit token with [Temporary] here. (Kill it
> at the start of its controller's Beginning Phase, before scoring.)
-/
def OGN_106.meta : CardDef :=
  { id := ⟨"OGN-106"⟩,
    name := "Sprite Mother",
    types := [.unit],
    tags := [⟨"Fae"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Sprite Mother. -/
def OGN_106 : CardDef :=
  { OGN_106.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.create "Sprite" (.const 1) .here true))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-107
/--
**Ava Achiever** — Unit · Mind · Energy 5 · Might 4
Printings: OGN-107/298

> When I attack, you may pay :rb_rune_mind: to play a card with [Hidden] from your hand here,
> ignoring its cost.
-/
def OGN_107.meta : CardDef :=
  { id := ⟨"OGN-107"⟩,
    name := "Ava Achiever",
    types := [.unit],
    tags := [⟨"Yordle"⟩],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Ava Achiever: the effect is not written yet. -/
def OGN_107 : CardDef := OGN_107.meta

-- BEGIN GENERATED OGN-108
/--
**Convergent Mutation** — Spell · Mind · Energy 2 + Power 1
Printings: OGN-108/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a friendly unit. This turn, increase its Might to the Might of another friendly unit.
-/
def OGN_108.meta : CardDef :=
  { id := ⟨"OGN-108"⟩,
    name := "Convergent Mutation",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, [.domain .mind]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Convergent Mutation: the effect is not written yet. -/
def OGN_108 : CardDef := OGN_108.meta

-- BEGIN GENERATED OGN-109
/--
**Dr. Mundo, Expert** — Unit · Mind · Energy 8 + Power 2 · Might 6
Printings: OGN-109/298

> My Might is increased by the number of cards in your trash.
> At the start of your Beginning Phase, recycle 3 from your trash.
-/
def OGN_109.meta : CardDef :=
  { id := ⟨"OGN-109"⟩,
    name := "Dr. Mundo",
    subtitle := some "Expert",
    types := [.unit],
    tags := [⟨"Dr. Mundo"⟩, ⟨"Zaun"⟩],
    domains := [.mind],
    cost := some ⟨8, [.domain .mind, .domain .mind]⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Dr. Mundo, Expert: the effect is not written yet. -/
def OGN_109 : CardDef := OGN_109.meta

-- BEGIN GENERATED OGN-110
/--
**Ekko, Recurrent** — Unit · Mind · Energy 5 + Power 1 · Might 5
Printings: OGN-110/298

> [Accelerate] (You may pay :rb_energy_1::rb_rune_mind: as an additional cost to have me enter
> ready.)
> [Deathknell] — Recycle me to ready your runes. (When I die, get the effect.)
-/
def OGN_110.meta : CardDef :=
  { id := ⟨"OGN-110"⟩,
    name := "Ekko",
    subtitle := some "Recurrent",
    types := [.unit],
    tags := [⟨"Ekko"⟩, ⟨"Zaun"⟩],
    domains := [.mind],
    cost := some ⟨5, [.domain .mind]⟩,
    might := some 5,
    keywords := [{ keyword := .accelerate },
      { keyword := .deathknell }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Ekko, Recurrent: the effect is not written yet. -/
def OGN_110 : CardDef := OGN_110.meta

-- BEGIN GENERATED OGN-111
/--
**Heimerdinger, Inventor** — Unit · Mind · Energy 3 + Power 1 · Might 3
Printings: OGN-111/298

> I have all :rb_exhaust: abilities of all friendly legends, units, and gear.
-/
def OGN_111.meta : CardDef :=
  { id := ⟨"OGN-111"⟩,
    name := "Heimerdinger",
    subtitle := some "Inventor",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Heimerdinger"⟩, ⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Heimerdinger, Inventor: the effect is not written yet. -/
def OGN_111 : CardDef := OGN_111.meta

-- BEGIN GENERATED OGN-112
/--
**Kai'Sa, Evolutionary** — Unit · Mind · Energy 6 + Power 1 · Might 6
Printings: OGN-112/298, OGN-112a/298

> [Ganking] (I can move from battlefield to battlefield.)
> When I conquer, you may play a spell from your trash with Energy cost less than your points
> without paying its Energy cost. Then recycle it. (You must still pay its Power cost.)
-/
def OGN_112.meta : CardDef :=
  { id := ⟨"OGN-112"⟩,
    name := "Kai'Sa",
    subtitle := some "Evolutionary",
    types := [.unit],
    tags := [⟨"Kai'Sa"⟩, ⟨"The Void"⟩],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind]⟩,
    might := some 6,
    keywords := [{ keyword := .ganking }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Kai'Sa, Evolutionary: the effect is not written yet. -/
def OGN_112 : CardDef := OGN_112.meta

-- BEGIN GENERATED OGN-113
/--
**Malzahar, Fanatic** — Unit · Mind · Energy 4 · Might 3
Printings: OGN-113/298

> Kill a friendly unit or gear, :rb_exhaust:: [Action] — [Add]
> :rb_rune_rainbow::rb_rune_rainbow:. (Use on your turn or in showdowns. Abilities that add
> resources can't be reacted to.)
-/
def OGN_113.meta : CardDef :=
  { id := ⟨"OGN-113"⟩,
    name := "Malzahar",
    subtitle := some "Fanatic",
    types := [.unit],
    tags := [⟨"Malzahar"⟩, ⟨"The Void"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Malzahar, Fanatic: the effect is not written yet. -/
def OGN_113 : CardDef := OGN_113.meta

-- BEGIN GENERATED OGN-114
/--
**Progress Day** — Spell · Mind · Energy 6 + Power 1
Printings: OGN-114/298

> Draw 4.
-/
def OGN_114.meta : CardDef :=
  { id := ⟨"OGN-114"⟩,
    name := "Progress Day",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Progress Day. -/
def OGN_114 : CardDef :=
  { OGN_114.meta with
    spellEffect := some (.of []
      (.prim (.draw .you (.const 4)))),
    status := .drafted }

-- BEGIN GENERATED OGN-115
/--
**Promising Future** — Spell · Mind · Energy 5 + Power 1
Printings: OGN-115/298

> Each player looks at the top 5 cards of their Main Deck, chooses one, then recycles the rest.
> Starting with the next player, each player plays those cards, ignoring Energy costs. (They
> must still pay Power costs.)
-/
def OGN_115.meta : CardDef :=
  { id := ⟨"OGN-115"⟩,
    name := "Promising Future",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨5, [.domain .mind]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Promising Future: the effect is not written yet. -/
def OGN_115 : CardDef := OGN_115.meta

-- BEGIN GENERATED OGN-116
/--
**Thousand-Tailed Watcher** — Unit · Mind · Energy 7 + Power 1 · Might 7
Printings: OGN-116/298

> [Accelerate] (You may pay :rb_energy_1::rb_rune_mind: as an additional cost to have me enter
> ready.)
> When you play me, give enemy units -3 :rb_might: this turn, to a minimum of 1 :rb_might:.
-/
def OGN_116.meta : CardDef :=
  { id := ⟨"OGN-116"⟩,
    name := "Thousand-Tailed Watcher",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨7, [.domain .mind]⟩,
    might := some 7,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Thousand-Tailed Watcher: the effect is not written yet. -/
def OGN_116 : CardDef := OGN_116.meta

-- BEGIN GENERATED OGN-117
/--
**Viktor, Innovator** — Unit · Mind · Energy 4 + Power 1 · Might 3
Printings: OGN-117/298, OGN-117a/298, VEN-176/166

> When you play a card on an opponent's turn, play a 1 :rb_might: Recruit unit token in your
> base.
-/
def OGN_117.meta : CardDef :=
  { id := ⟨"OGN-117"⟩,
    name := "Viktor",
    subtitle := some "Innovator",
    types := [.unit],
    tags := [⟨"Viktor"⟩, ⟨"Zaun"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 3,
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Viktor, Innovator. -/
def OGN_117 : CardDef :=
  { OGN_117.meta with
    abilities := [.triggered
      { event := .play, subject := Selector.all .friendly .anywhere [],
        condition := .not .yourTurn }
      (.of [] (.prim (.create "Recruit" (.const 1) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-118
/--
**Wraith of Echoes** — Unit · Mind · Energy 6 + Power 1 · Might 5
Printings: OGN-118/298

> The first time a friendly unit dies each turn, draw 1.
-/
def OGN_118.meta : CardDef :=
  { id := ⟨"OGN-118"⟩,
    name := "Wraith of Echoes",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind]⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Wraith of Echoes: the effect is not written yet. -/
def OGN_118 : CardDef := OGN_118.meta

-- BEGIN GENERATED OGN-119
/--
**Ahri, Inquisitive** — Unit · Mind · Energy 3 + Power 1 · Might 3
Printings: OGN-119/298, OGN-119a/298, SFD-227*/221, SFD-227/221, VEN-SP3/006

> When I attack or defend, give an enemy unit here -2 :rb_might: this turn, to a minimum of 1
> :rb_might:.
-/
def OGN_119.meta : CardDef :=
  { id := ⟨"OGN-119"⟩,
    name := "Ahri",
    subtitle := some "Inquisitive",
    types := [.unit],
    tags := [⟨"Ahri"⟩, ⟨"Ionia"⟩],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    might := some 3,
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Ahri, Inquisitive. -/
def OGN_119 : CardDef :=
  { OGN_119.meta with
    abilities :=
      [.triggered (.onSelf .attack)
        (.of [.targetOf .one .enemy .here [.ofType .unit]]
          (.grant (.slot 0) (.mightMinusMin .it (.const 2) 1) .thisTurn)) .unlimited,
       .triggered (.onSelf .defend)
        (.of [.targetOf .one .enemy .here [.ofType .unit]]
          (.grant (.slot 0) (.mightMinusMin .it (.const 2) 1) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-120
/--
**Seal of Insight** — Gear · Mind · Energy 0 + Power 1
Printings: OGN-120/298, SFD-229/221

> :rb_exhaust:: [Reaction] — [Add] :rb_rune_mind:. (Abilities that add resources can't be
> reacted to.)
-/
def OGN_120.meta : CardDef :=
  { id := ⟨"OGN-120"⟩,
    name := "Seal of Insight",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨0, [.domain .mind]⟩,
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Seal of Insight. -/
def OGN_120 : CardDef :=
  { OGN_120.meta with
    abilities := [.activated [.exhaustSelf] .reaction
        (.of []
        (.prim (.addPower .you (.const 1) (some .mind) none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-121
/--
**Teemo, Strategist** — Unit · Mind · Energy 2 + Power 1 · Might 2
Printings: OGN-121/298, OGN-121a/298, SFD-230*/221, SFD-230/221

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When I defend or I'm played from [Hidden], reveal the top 5 cards of your Main Deck. Deal 1 to
> an enemy unit here for each card with [Hidden], then recycle them.
-/
def OGN_121.meta : CardDef :=
  { id := ⟨"OGN-121"⟩,
    name := "Teemo",
    subtitle := some "Strategist",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Teemo"⟩, ⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨2, [.domain .mind]⟩,
    might := some 2,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Teemo, Strategist: the effect is not written yet. -/
def OGN_121 : CardDef := OGN_121.meta

-- BEGIN GENERATED OGN-122
/--
**Time Warp** — Spell · Mind · Energy 10 + Power 4
Printings: OGN-122/298

> Take a turn after this one. Banish this.
-/
def OGN_122.meta : CardDef :=
  { id := ⟨"OGN-122"⟩,
    name := "Time Warp",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨10, [.domain .mind, .domain .mind, .domain .mind, .domain .mind]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Time Warp. -/
def OGN_122 : CardDef :=
  { OGN_122.meta with
    spellEffect := some (.of [] (.seqOf [.prim (.extraTurn .you), .prim (.banish .self)])),
    status := .drafted }

-- BEGIN GENERATED OGN-123
/--
**Unchecked Power** — Spell · Mind · Energy 7 + Power 2
Printings: OGN-123/298

> Exhaust all friendly units, then deal 12 to all units at battlefields.
-/
def OGN_123.meta : CardDef :=
  { id := ⟨"OGN-123"⟩,
    name := "Unchecked Power",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨7, [.domain .mind, .domain .mind]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Unchecked Power. -/
def OGN_123 : CardDef :=
  { OGN_123.meta with
    spellEffect := some (.of []
      (.seqOf [.prim (.exhaust (Selector.all .friendly .anywhere [.ofType .unit])),
        .prim (.deal (Selector.all .any .atBattlefield [.ofType .unit]) (.const 12))])),
    status := .drafted }

-- BEGIN GENERATED OGN-124
/--
**Arena Bar** — Gear · Body · Energy 3
Printings: OGN-124/298

> :rb_exhaust:: Buff an exhausted friendly unit. (If it doesn't have a buff, it gets a +1
> :rb_might: buff.)
-/
def OGN_124.meta : CardDef :=
  { id := ⟨"OGN-124"⟩,
    name := "Arena Bar",
    types := [.gear],
    domains := [.body],
    cost := some ⟨3, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Arena Bar. -/
def OGN_124 : CardDef :=
  { OGN_124.meta with
    abilities := [.activated [.exhaustSelf] .normal
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .exhausted]]
        (.prim (.buff (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-125
/--
**Bilgewater Bully** — Unit · Body · Energy 6 · Might 6
Printings: OGN-125/298

> While I'm buffed, I have [Ganking]. (I can move from battlefield to battlefield.)
-/
def OGN_125.meta : CardDef :=
  { id := ⟨"OGN-125"⟩,
    name := "Bilgewater Bully",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨6, []⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Bilgewater Bully. -/
def OGN_125 : CardDef :=
  { OGN_125.meta with
    abilities := [.passive (.matches .self .buffed) [.keyword .self ⟨.ganking, .none⟩]],
    status := .drafted }

-- BEGIN GENERATED OGN-126
/--
**Body Rune** — Rune · Body
Printings: OGN-126/298, OGN-126a/298, VEN-R04, RAD-R04, RAD-R04a

> (no text)
-/
def OGN_126.meta : CardDef :=
  { id := ⟨"OGN-126"⟩,
    name := "Body Rune",
    types := [.rune],
    domains := [.body],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Body Rune. -/
def OGN_126 : CardDef :=
  { OGN_126.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-127
/--
**Cannon Barrage** — Spell · Body · Energy 2 + Power 1
Printings: OGN-127/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Deal 2 to all enemy units in combat.
-/
def OGN_127.meta : CardDef :=
  { id := ⟨"OGN-127"⟩,
    name := "Cannon Barrage",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, [.domain .body]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Cannon Barrage: the effect is not written yet. -/
def OGN_127 : CardDef := OGN_127.meta

-- BEGIN GENERATED OGN-128
/--
**Challenge** — Spell · Body · Energy 2 + Power 1
Printings: OGN-128/298

> [Action] (Play on your turn or in showdowns.)
> Choose a friendly unit and an enemy unit. They deal damage equal to their Mights to each
> other.
-/
def OGN_128.meta : CardDef :=
  { id := ⟨"OGN-128"⟩,
    name := "Challenge",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, [.domain .body]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Challenge: the effect is not written yet. -/
def OGN_128 : CardDef := OGN_128.meta

-- BEGIN GENERATED OGN-129
/--
**Confront** — Spell · Body · Energy 2
Printings: OGN-129/298

> [Action] (Play on your turn or in showdowns.)
> Units you play this turn enter ready. Draw 1.
-/
def OGN_129.meta : CardDef :=
  { id := ⟨"OGN-129"⟩,
    name := "Confront",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Confront: the effect is not written yet. -/
def OGN_129 : CardDef := OGN_129.meta

-- BEGIN GENERATED OGN-130
/--
**Crackshot Corsair** — Unit · Body · Energy 3 · Might 3
Printings: OGN-130/298

> When I attack, deal 1 to an enemy unit here.
-/
def OGN_130.meta : CardDef :=
  { id := ⟨"OGN-130"⟩,
    name := "Crackshot Corsair",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Crackshot Corsair. -/
def OGN_130 : CardDef :=
  { OGN_130.meta with
    abilities := [.triggered (.onSelf .attack)
        (.of [.targetOf .one .enemy .here [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-131
/--
**Dune Drake** — Unit · Body · Energy 5 · Might 5
Printings: OGN-131/298

> When I attack, give me +2 :rb_might: this turn if there is a ready enemy unit here.
-/
def OGN_131.meta : CardDef :=
  { id := ⟨"OGN-131"⟩,
    name := "Dune Drake",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Shurima"⟩],
    domains := [.body],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Dune Drake. -/
def OGN_131 : CardDef :=
  { OGN_131.meta with
    abilities := [.triggered (.onSelf .attack)
      (.of [] (.ifThen (.exists (Selector.all .enemy .here [.ofType .unit, .ready]))
        (.grant .self (.mightPlus .it (.const 2)) .thisTurn) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-132
/--
**First Mate** — Unit · Body · Energy 3 · Might 3
Printings: OGN-132/298

> When you play me, ready another unit.
-/
def OGN_132.meta : CardDef :=
  { id := ⟨"OGN-132"⟩,
    name := "First Mate",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- First Mate. -/
def OGN_132 : CardDef :=
  { OGN_132.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .anywhere [.ofType .unit, .notSelf]] (.prim (.ready (.slot 0))))
      .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-133
/--
**Flurry of Blades** — Spell · Body · Energy 1
Printings: OGN-133/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Deal 1 to all units at battlefields.
-/
def OGN_133.meta : CardDef :=
  { id := ⟨"OGN-133"⟩,
    name := "Flurry of Blades",
    types := [.spell],
    domains := [.body],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Flurry of Blades. -/
def OGN_133 : CardDef :=
  { OGN_133.meta with
    spellEffect := some (.of []
      (.prim (.deal (Selector.all .any .atBattlefield [.ofType .unit]) (.const 1)))),
    status := .drafted }

-- BEGIN GENERATED OGN-134
/--
**Mobilize** — Spell · Body · Energy 2
Printings: OGN-134/298

> Channel 1 rune exhausted. If you can't, draw 1.
-/
def OGN_134.meta : CardDef :=
  { id := ⟨"OGN-134"⟩,
    name := "Mobilize",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Mobilize: the effect is not written yet. -/
def OGN_134 : CardDef := OGN_134.meta

-- BEGIN GENERATED OGN-135
/--
**Pakaa Cub** — Unit · Body · Energy 3 · Might 3
Printings: OGN-135/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
-/
def OGN_135.meta : CardDef :=
  { id := ⟨"OGN-135"⟩,
    name := "Pakaa Cub",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Ixtal"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Pakaa Cub. -/
def OGN_135 : CardDef :=
  { OGN_135.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-136
/--
**Pit Rookie** — Unit · Body · Energy 2 · Might 2
Printings: OGN-136/298

> When you play me, buff another friendly unit. (If it doesn't have a buff, it gets a +1
> :rb_might: buff.)
-/
def OGN_136.meta : CardDef :=
  { id := ⟨"OGN-136"⟩,
    name := "Pit Rookie",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Pit Rookie. -/
def OGN_136 : CardDef :=
  { OGN_136.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .notSelf]] (.prim (.buff (.slot 0))))
      .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-137
/--
**Stormclaw Ursine** — Unit · Body · Energy 7 · Might 6
Printings: OGN-137/298

> [Tank] (I must be assigned combat damage first.)
> When you play me, channel 1 rune exhausted.
-/
def OGN_137.meta : CardDef :=
  { id := ⟨"OGN-137"⟩,
    name := "Stormclaw Ursine",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨7, []⟩,
    might := some 6,
    keywords := [{ keyword := .tank }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Stormclaw Ursine. -/
def OGN_137 : CardDef :=
  { OGN_137.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.channel .you (.const 0) (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-138
/--
**Catalyst of Aeons** — Spell · Body · Energy 4
Printings: OGN-138/298

> Channel 2 runes exhausted. If you couldn't channel 2 runes this way, draw 1.
-/
def OGN_138.meta : CardDef :=
  { id := ⟨"OGN-138"⟩,
    name := "Catalyst of Aeons",
    types := [.spell],
    domains := [.body],
    cost := some ⟨4, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Catalyst of Aeons: the effect is not written yet. -/
def OGN_138 : CardDef := OGN_138.meta

-- BEGIN GENERATED OGN-139
/--
**Cithria of Cloudfield** — Unit · Body · Energy 2 · Might 1
Printings: OGN-139/298

> When you play another unit, buff me. (If I don't have a buff, I get a +1 :rb_might: buff.)
-/
def OGN_139.meta : CardDef :=
  { id := ⟨"OGN-139"⟩,
    name := "Cithria of Cloudfield",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Demacia"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 1,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Cithria of Cloudfield. -/
def OGN_139 : CardDef :=
  { OGN_139.meta with
    abilities := [.triggered
      { event := .play, subject := Selector.all .friendly .anywhere [.ofType .unit, .notSelf] }
      (.of [] (.prim (.buff .self))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-140
/--
**Herald of Scales** — Unit · Body · Energy 4 · Might 3
Printings: OGN-140/298

> Your Dragons' Energy costs are reduced by :rb_energy_2:, to a minimum of :rb_energy_1:.
-/
def OGN_140.meta : CardDef :=
  { id := ⟨"OGN-140"⟩,
    name := "Herald of Scales",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Herald of Scales: the effect is not written yet. -/
def OGN_140 : CardDef := OGN_140.meta

-- BEGIN GENERATED OGN-141
/--
**Kinkou Monk** — Unit · Body · Energy 4 + Power 1 · Might 4
Printings: OGN-141/298

> When you play me, buff up to two other friendly units. (Each one that doesn't have a buff gets
> a +1 :rb_might: buff.)
-/
def OGN_141.meta : CardDef :=
  { id := ⟨"OGN-141"⟩,
    name := "Kinkou Monk",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Kinkou Monk: the effect is not written yet. -/
def OGN_141 : CardDef := OGN_141.meta

-- BEGIN GENERATED OGN-142
/--
**Mountain Drake** — Unit · Body · Energy 9 · Might 10
Printings: OGN-142/298

> (no text)
-/
def OGN_142.meta : CardDef :=
  { id := ⟨"OGN-142"⟩,
    name := "Mountain Drake",
    types := [.unit],
    tags := [⟨"Dragon"⟩],
    domains := [.body],
    cost := some ⟨9, []⟩,
    might := some 10,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Mountain Drake. -/
def OGN_142 : CardDef :=
  { OGN_142.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-143
/--
**Pirate's Haven** — Gear · Body · Energy 3
Printings: OGN-143/298

> When you ready a friendly unit, give it +1 :rb_might: this turn.
-/
def OGN_143.meta : CardDef :=
  { id := ⟨"OGN-143"⟩,
    name := "Pirate's Haven",
    types := [.gear],
    domains := [.body],
    cost := some ⟨3, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Pirate's Haven: the effect is not written yet. -/
def OGN_143 : CardDef := OGN_143.meta

-- BEGIN GENERATED OGN-144
/--
**Spoils of War** — Spell · Body · Energy 4 + Power 1
Printings: OGN-144/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> If an enemy unit has died this turn, this costs :rb_energy_2: less.
> Draw 2.
-/
def OGN_144.meta : CardDef :=
  { id := ⟨"OGN-144"⟩,
    name := "Spoils of War",
    types := [.spell],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Spoils of War: the effect is not written yet. -/
def OGN_144 : CardDef := OGN_144.meta

-- BEGIN GENERATED OGN-145
/--
**Unyielding Spirit** — Spell · Body · Energy 1 + Power 1
Printings: OGN-145/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Prevent all spell and ability damage this turn.
-/
def OGN_145.meta : CardDef :=
  { id := ⟨"OGN-145"⟩,
    name := "Unyielding Spirit",
    types := [.spell],
    domains := [.body],
    cost := some ⟨1, [.domain .body]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Unyielding Spirit: the effect is not written yet. -/
def OGN_145 : CardDef := OGN_145.meta

-- BEGIN GENERATED OGN-146
/--
**Wallop** — Spell · Body · Energy 2
Printings: OGN-146/298

> [Action] (Play on your turn or in showdowns.)
> As you play this, you may spend a buff as an additional cost. If you do, ignore this spell's
> cost.
> Ready a unit.
-/
def OGN_146.meta : CardDef :=
  { id := ⟨"OGN-146"⟩,
    name := "Wallop",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Wallop: the effect is not written yet. -/
def OGN_146 : CardDef := OGN_146.meta

-- BEGIN GENERATED OGN-147
/--
**Wildclaw Shaman** — Unit · Body · Energy 4 · Might 3
Printings: OGN-147/298

> When you play me, you may spend a buff to buff me and ready me. (If I don't have a buff, I get
> a +1 :rb_might: buff.)
-/
def OGN_147.meta : CardDef :=
  { id := ⟨"OGN-147"⟩,
    name := "Wildclaw Shaman",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Wildclaw Shaman: the effect is not written yet. -/
def OGN_147 : CardDef := OGN_147.meta

-- BEGIN GENERATED OGN-148
/--
**Anivia, Primal** — Unit · Body · Energy 7 + Power 2 · Might 8
Printings: OGN-148/298

> When I attack, deal 3 to all enemy units here.
-/
def OGN_148.meta : CardDef :=
  { id := ⟨"OGN-148"⟩,
    name := "Anivia",
    subtitle := some "Primal",
    types := [.unit],
    tags := [⟨"Bird"⟩, ⟨"Anivia"⟩, ⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨7, [.domain .body, .domain .body]⟩,
    might := some 8,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Anivia, Primal. -/
def OGN_148 : CardDef :=
  { OGN_148.meta with
    abilities := [.triggered (.onSelf .attack)
      (.of [] (.forEach (Selector.all .enemy .here [.ofType .unit]) (.prim (.deal .it (.const 3))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-149
/--
**Carnivorous Snapvine** — Unit · Body · Energy 5 + Power 2 · Might 6
Printings: OGN-149/298

> When you play me, choose an enemy unit at a battlefield. We deal damage equal to our Mights to
> each other.
-/
def OGN_149.meta : CardDef :=
  { id := ⟨"OGN-149"⟩,
    name := "Carnivorous Snapvine",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩],
    domains := [.body],
    cost := some ⟨5, [.domain .body, .domain .body]⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Carnivorous Snapvine: the effect is not written yet. -/
def OGN_149 : CardDef := OGN_149.meta

-- BEGIN GENERATED OGN-150
/--
**Kraken Hunter** — Unit · Body · Energy 3 + Power 2 · Might 5
Printings: OGN-150/298

> [Accelerate] (You may pay :rb_energy_1::rb_rune_body: as an additional cost to have me enter
> ready.)
> [Assault] (+1 :rb_might: while I'm an attacker.)
> As you play me, you may spend any number of buffs as an additional cost. Reduce my cost by
> :rb_rune_body: for each buff you spend.
-/
def OGN_150.meta : CardDef :=
  { id := ⟨"OGN-150"⟩,
    name := "Kraken Hunter",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨3, [.domain .body, .domain .body]⟩,
    might := some 5,
    keywords := [{ keyword := .accelerate },
      { keyword := .assault, arg := .amount 1 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Kraken Hunter: the effect is not written yet. -/
def OGN_150 : CardDef := OGN_150.meta

-- BEGIN GENERATED OGN-151
/--
**Lee Sin, Centered** — Unit · Body · Energy 6 · Might 6
Printings: OGN-151/298, OGN-151a/298

> [Accelerate] (You may pay :rb_energy_1::rb_rune_body: as an additional cost to have me enter
> ready.)
> Other buffed friendly units at my battlefield have +2 :rb_might:.
-/
def OGN_151.meta : CardDef :=
  { id := ⟨"OGN-151"⟩,
    name := "Lee Sin",
    subtitle := some "Centered",
    types := [.unit],
    tags := [⟨"Lee Sin"⟩, ⟨"Ionia"⟩],
    domains := [.body],
    cost := some ⟨6, []⟩,
    might := some 6,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Lee Sin, Centered. -/
def OGN_151 : CardDef :=
  { OGN_151.meta with
    abilities := [.passive .always
      [.mightPlus (Selector.all .friendly .here [.ofType .unit, .buffed, .notSelf]) (.const 2)]],
    status := .drafted }

-- BEGIN GENERATED OGN-152
/--
**Mistfall** — Gear · Body · Energy 3
Printings: OGN-152/298

> When you buff a friendly unit, you may pay :rb_rune_body: and exhaust this to ready it.
-/
def OGN_152.meta : CardDef :=
  { id := ⟨"OGN-152"⟩,
    name := "Mistfall",
    types := [.gear],
    domains := [.body],
    cost := some ⟨3, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Mistfall: the effect is not written yet. -/
def OGN_152 : CardDef := OGN_152.meta

-- BEGIN GENERATED OGN-153
/--
**Overt Operation** — Spell · Body · Energy 5 + Power 2
Printings: OGN-153/298

> [Action] (Play on your turn or in showdowns.)
> For each friendly unit, you may spend its buff to ready it. Then buff all friendly units.
> (Each one that doesn't have a buff gets a +1 :rb_might: buff.)
-/
def OGN_153.meta : CardDef :=
  { id := ⟨"OGN-153"⟩,
    name := "Overt Operation",
    types := [.spell],
    domains := [.body],
    cost := some ⟨5, [.domain .body, .domain .body]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Overt Operation: the effect is not written yet. -/
def OGN_153 : CardDef := OGN_153.meta

-- BEGIN GENERATED OGN-154
/--
**Primal Strength** — Spell · Body · Energy 4 + Power 1
Printings: OGN-154/298

> [Action] (Play on your turn or in showdowns.)
> Give a unit +7 :rb_might: this turn.
-/
def OGN_154.meta : CardDef :=
  { id := ⟨"OGN-154"⟩,
    name := "Primal Strength",
    types := [.spell],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Primal Strength. -/
def OGN_154 : CardDef :=
  { OGN_154.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it (.const 7)) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED OGN-155
/--
**Qiyana, Victorious** — Unit · Body · Energy 4 + Power 1 · Might 4
Printings: OGN-155/298

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> When I conquer, draw 1 or channel 1 rune exhausted.
-/
def OGN_155.meta : CardDef :=
  { id := ⟨"OGN-155"⟩,
    name := "Qiyana",
    subtitle := some "Victorious",
    types := [.unit],
    tags := [⟨"Qiyana"⟩, ⟨"Ixtal"⟩],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    might := some 4,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Qiyana, Victorious: the effect is not written yet. -/
def OGN_155 : CardDef := OGN_155.meta

-- BEGIN GENERATED OGN-156
/--
**Sabotage** — Spell · Body · Energy 1 + Power 1
Printings: OGN-156/298

> Choose an opponent. They reveal their hand. Choose a non-unit card from it, and recycle that
> card.
-/
def OGN_156.meta : CardDef :=
  { id := ⟨"OGN-156"⟩,
    name := "Sabotage",
    types := [.spell],
    domains := [.body],
    cost := some ⟨1, [.domain .body]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Sabotage: the effect is not written yet. -/
def OGN_156 : CardDef := OGN_156.meta

-- BEGIN GENERATED OGN-157
/--
**Udyr, Wildman** — Unit · Body · Energy 6 + Power 1 · Might 6
Printings: OGN-157/298

> Spend my buff: Choose one you've not chosen this turn —Deal 2 to a unit at a battlefield.Stun
> a unit at a battlefield.Ready me.Give me [Ganking] this turn.
-/
def OGN_157.meta : CardDef :=
  { id := ⟨"OGN-157"⟩,
    name := "Udyr",
    subtitle := some "Wildman",
    types := [.unit],
    tags := [⟨"Udyr"⟩, ⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨6, [.domain .body]⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Udyr, Wildman: the effect is not written yet. -/
def OGN_157 : CardDef := OGN_157.meta

-- BEGIN GENERATED OGN-158
/--
**Volibear, Imposing** — Unit · Body · Energy 12 + Power 2 · Might 10
Printings: OGN-158/298, OGN-158a/298

> [Shield 3] (+3 :rb_might: while I'm a defender.)
> [Tank] (I must be assigned combat damage first.)
> When an opponent moves to a battlefield other than mine, draw 1. (Bases are not battlefields.)
-/
def OGN_158.meta : CardDef :=
  { id := ⟨"OGN-158"⟩,
    name := "Volibear",
    subtitle := some "Imposing",
    types := [.unit],
    tags := [⟨"Volibear"⟩, ⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨12, [.domain .body, .domain .body]⟩,
    might := some 10,
    keywords := [{ keyword := .shield, arg := .amount 3 },
      { keyword := .tank }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Volibear, Imposing: the effect is not written yet. -/
def OGN_158 : CardDef := OGN_158.meta

-- BEGIN GENERATED OGN-159
/--
**Warwick, Hunter** — Unit · Body · Energy 6 + Power 1 · Might 5
Printings: OGN-159/298

> I enter ready.
> When I attack, kill all damaged enemy units here.
-/
def OGN_159.meta : CardDef :=
  { id := ⟨"OGN-159"⟩,
    name := "Warwick",
    subtitle := some "Hunter",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Warwick"⟩, ⟨"Zaun"⟩],
    domains := [.body],
    cost := some ⟨6, [.domain .body]⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Warwick, Hunter. -/
def OGN_159 : CardDef :=
  { OGN_159.meta with
    abilities := [.passive .always [.entersReady .self],
      .triggered (.onSelf .attack)
        (.of []
        (.prim (.kill (Selector.all .enemy .here [.ofType .unit, .damaged])))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-160
/--
**Dazzling Aurora** — Gear · Body · Energy 9 + Power 2
Printings: OGN-160/298

> At the end of your turn, reveal cards from the top of your Main Deck until you reveal a unit.
> Play it, ignoring its cost, and recycle the rest.
-/
def OGN_160.meta : CardDef :=
  { id := ⟨"OGN-160"⟩,
    name := "Dazzling Aurora",
    types := [.gear],
    domains := [.body],
    cost := some ⟨9, [.domain .body, .domain .body]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Dazzling Aurora: the effect is not written yet. -/
def OGN_160 : CardDef := OGN_160.meta

-- BEGIN GENERATED OGN-161
/--
**Deadbloom Predator** — Unit · Body · Energy 8 + Power 2 · Might 8
Printings: OGN-161/298

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> You may play me to an occupied enemy battlefield.
-/
def OGN_161.meta : CardDef :=
  { id := ⟨"OGN-161"⟩,
    name := "Deadbloom Predator",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩],
    domains := [.body],
    cost := some ⟨8, [.domain .body, .domain .body]⟩,
    might := some 8,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Deadbloom Predator: the effect is not written yet. -/
def OGN_161 : CardDef := OGN_161.meta

-- BEGIN GENERATED OGN-162
/--
**Miss Fortune, Captain** — Unit · Body · Energy 5 + Power 1 · Might 5
Printings: OGN-162/298, OGN-162a/298

> [Accelerate] (You may pay :rb_energy_1::rb_rune_body: as an additional cost to have me enter
> ready.)
> [Ganking] (I can move from battlefield to battlefield.)
> The first time I move each turn, you may ready something else that's exhausted.
-/
def OGN_162.meta : CardDef :=
  { id := ⟨"OGN-162"⟩,
    name := "Miss Fortune",
    subtitle := some "Captain",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Miss Fortune"⟩, ⟨"Bilgewater"⟩],
    domains := [.body],
    cost := some ⟨5, [.domain .body]⟩,
    might := some 5,
    keywords := [{ keyword := .accelerate },
      { keyword := .ganking }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Miss Fortune, Captain: the effect is not written yet. -/
def OGN_162 : CardDef := OGN_162.meta

-- BEGIN GENERATED OGN-163
/--
**Seal of Strength** — Gear · Body · Energy 0 + Power 1
Printings: OGN-163/298, SFD-231/221

> :rb_exhaust:: [Reaction] — [Add] :rb_rune_body:. (Abilities that add resources can't be
> reacted to.)
-/
def OGN_163.meta : CardDef :=
  { id := ⟨"OGN-163"⟩,
    name := "Seal of Strength",
    types := [.gear],
    domains := [.body],
    cost := some ⟨0, [.domain .body]⟩,
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Seal of Strength. -/
def OGN_163 : CardDef :=
  { OGN_163.meta with
    abilities := [.activated [.exhaustSelf] .reaction
        (.of []
        (.prim (.addPower .you (.const 1) (some .body) none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-164
/--
**Sett, Brawler** — Unit · Body · Energy 5 + Power 1 · Might 4
Printings: OGN-164/298, OGN-164a/298, SFD-232*/221, SFD-232/221, VEN-SP4/006

> When I'm played and when I conquer, buff me. (If I don't have a buff, I get a +1 :rb_might:
> buff.)
> Spend my buff: Give me +4 :rb_might: this turn.
-/
def OGN_164.meta : CardDef :=
  { id := ⟨"OGN-164"⟩,
    name := "Sett",
    subtitle := some "Brawler",
    types := [.unit],
    tags := [⟨"Sett"⟩, ⟨"Ionia"⟩],
    domains := [.body],
    cost := some ⟨5, [.domain .body]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Sett, Brawler: the effect is not written yet. -/
def OGN_164 : CardDef := OGN_164.meta

-- BEGIN GENERATED OGN-165
/--
**Cemetery Attendant** — Unit · Chaos · Energy 3 + Power 1 · Might 3
Printings: OGN-165/298

> When you play me, return a unit from your trash to your hand.
-/
def OGN_165.meta : CardDef :=
  { id := ⟨"OGN-165"⟩,
    name := "Cemetery Attendant",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Cemetery Attendant. -/
def OGN_165 : CardDef :=
  { OGN_165.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.returnToHand (.one .friendly .inTrash [.ofType .unit])))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-166
/--
**Chaos Rune** — Rune · Chaos
Printings: OGN-166/298, OGN-166a/298, VEN-R05, RAD-R05, RAD-R05a

> (no text)
-/
def OGN_166.meta : CardDef :=
  { id := ⟨"OGN-166"⟩,
    name := "Chaos Rune",
    types := [.rune],
    domains := [.chaos],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Chaos Rune. -/
def OGN_166 : CardDef :=
  { OGN_166.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-167
/--
**Ember Monk** — Unit · Chaos · Energy 4 · Might 4
Printings: OGN-167/298

> When you play a card from [Hidden], give me +2 :rb_might: this turn.
-/
def OGN_167.meta : CardDef :=
  { id := ⟨"OGN-167"⟩,
    name := "Ember Monk",
    types := [.unit],
    tags := [⟨"Bandle City"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Ember Monk: the effect is not written yet. -/
def OGN_167 : CardDef := OGN_167.meta

-- BEGIN GENERATED OGN-168
/--
**Fight or Flight** — Spell · Chaos · Energy 2
Printings: OGN-168/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Move a unit from a battlefield to its base.
-/
def OGN_168.meta : CardDef :=
  { id := ⟨"OGN-168"⟩,
    name := "Fight or Flight",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Fight or Flight. -/
def OGN_168 : CardDef :=
  { OGN_168.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.prim (.move (.slot 0) .base))),
    status := .drafted }

-- BEGIN GENERATED OGN-169
/--
**Gust** — Spell · Chaos · Energy 1
Printings: OGN-169/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Return a unit at a battlefield with 3 :rb_might: or less to its owner's hand.
-/
def OGN_169.meta : CardDef :=
  { id := ⟨"OGN-169"⟩,
    name := "Gust",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Gust. -/
def OGN_169 : CardDef :=
  { OGN_169.meta with
    spellEffect := some (.of
      [.targetOf .one .any .atBattlefield [.ofType .unit, .might .le (.const 3)]]
      (.prim (.returnToHand (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED OGN-170
/--
**Morbid Return** — Spell · Chaos · Energy 2
Printings: OGN-170/298

> [Action] (Play on your turn or in showdowns.)
> Return a unit from your trash to your hand.
-/
def OGN_170.meta : CardDef :=
  { id := ⟨"OGN-170"⟩,
    name := "Morbid Return",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Morbid Return. -/
def OGN_170 : CardDef :=
  { OGN_170.meta with
    spellEffect := some (.of []
      (.prim (.returnToHand (.one .friendly .inTrash [.ofType .unit])))),
    status := .drafted }

-- BEGIN GENERATED OGN-171
/--
**Mystic Poro** — Unit · Chaos · Energy 2 · Might 2
Printings: OGN-171/298, UNL-224/219

> [Vision] (When you play me, look at the top card of your Main Deck. You may recycle it.)
-/
def OGN_171.meta : CardDef :=
  { id := ⟨"OGN-171"⟩,
    name := "Mystic Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .vision }],
    sets := [⟨"OGN"⟩, ⟨"UNL"⟩] }
-- END GENERATED

/-- Mystic Poro. -/
def OGN_171 : CardDef :=
  { OGN_171.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-172
/--
**Rebuke** — Spell · Chaos · Energy 2 + Power 2
Printings: OGN-172/298

> [Action] (Play on your turn or in showdowns.)
> Return a unit at a battlefield to its owner's hand.
-/
def OGN_172.meta : CardDef :=
  { id := ⟨"OGN-172"⟩,
    name := "Rebuke",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, [.domain .chaos, .domain .chaos]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Rebuke. -/
def OGN_172 : CardDef :=
  { OGN_172.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.prim (.returnToHand (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED OGN-173
/--
**Ride the Wind** — Spell · Chaos · Energy 2 + Power 1
Printings: OGN-173/298

> [Action] (Play on your turn or in showdowns.)
> Move a friendly unit and ready it.
-/
def OGN_173.meta : CardDef :=
  { id := ⟨"OGN-173"⟩,
    name := "Ride the Wind",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, [.domain .chaos]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Ride the Wind: the effect is not written yet. -/
def OGN_173 : CardDef := OGN_173.meta

-- BEGIN GENERATED OGN-174
/--
**Sai Scout** — Unit · Chaos · Energy 6 · Might 5
Printings: OGN-174/298

> [Vision] (When you play me, look at the top card of your Main Deck. You may recycle it.)
> You may play me to an open battlefield.
-/
def OGN_174.meta : CardDef :=
  { id := ⟨"OGN-174"⟩,
    name := "Sai Scout",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.chaos],
    cost := some ⟨6, []⟩,
    might := some 5,
    keywords := [{ keyword := .vision }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Sai Scout: the effect is not written yet. -/
def OGN_174 : CardDef := OGN_174.meta

-- BEGIN GENERATED OGN-175
/--
**Shipyard Skulker** — Unit · Chaos · Energy 3 · Might 3
Printings: OGN-175/298

> (no text)
-/
def OGN_175.meta : CardDef :=
  { id := ⟨"OGN-175"⟩,
    name := "Shipyard Skulker",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Shipyard Skulker. -/
def OGN_175 : CardDef :=
  { OGN_175.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-176
/--
**Sneaky Deckhand** — Unit · Chaos · Energy 3 · Might 2
Printings: OGN-176/298

> You may play me to an open battlefield.
-/
def OGN_176.meta : CardDef :=
  { id := ⟨"OGN-176"⟩,
    name := "Sneaky Deckhand",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 2,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Sneaky Deckhand: the effect is not written yet. -/
def OGN_176 : CardDef := OGN_176.meta

-- BEGIN GENERATED OGN-177
/--
**Stealthy Pursuer** — Unit · Chaos · Energy 4 + Power 1 · Might 4
Printings: OGN-177/298

> When a friendly unit moves from my location, I may be moved with it.
-/
def OGN_177.meta : CardDef :=
  { id := ⟨"OGN-177"⟩,
    name := "Stealthy Pursuer",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Stealthy Pursuer: the effect is not written yet. -/
def OGN_177 : CardDef := OGN_177.meta

-- BEGIN GENERATED OGN-178
/--
**Undercover Agent** — Unit · Chaos · Energy 5 + Power 1 · Might 5
Printings: OGN-178/298

> [Deathknell] — Discard 2, then draw 2. (When I die, get the effect.)
-/
def OGN_178.meta : CardDef :=
  { id := ⟨"OGN-178"⟩,
    name := "Undercover Agent",
    types := [.unit],
    domains := [.chaos],
    cost := some ⟨5, [.domain .chaos]⟩,
    might := some 5,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Undercover Agent. -/
def OGN_178 : CardDef :=
  { OGN_178.meta with
    abilities := [.triggered (.onSelf .die)
        (.of []
        (.seqOf [.prim (.discard .you (.const 2)),
          .prim (.draw .you (.const 2))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-179
/--
**Acceptable Losses** — Spell · Chaos · Energy 1
Printings: OGN-179/298

> [Action] (Play on your turn or in showdowns.)
> Each player kills one of their gear.
-/
def OGN_179.meta : CardDef :=
  { id := ⟨"OGN-179"⟩,
    name := "Acceptable Losses",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Acceptable Losses: the effect is not written yet. -/
def OGN_179 : CardDef := OGN_179.meta

-- BEGIN GENERATED OGN-180
/--
**Fading Memories** — Spell · Chaos · Energy 4 + Power 1
Printings: OGN-180/298

> Give a unit at a battlefield or a gear [Temporary]. (Kill it at the start of its controller's
> Beginning Phase, before scoring.)
-/
def OGN_180.meta : CardDef :=
  { id := ⟨"OGN-180"⟩,
    name := "Fading Memories",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Fading Memories: the effect is not written yet. -/
def OGN_180 : CardDef := OGN_180.meta

-- BEGIN GENERATED OGN-181
/--
**Pack of Wonders** — Gear · Chaos · Energy 2
Printings: OGN-181/298

> :rb_exhaust:: Return another friendly gear, unit, or [Hidden] card to its owner's hand.
-/
def OGN_181.meta : CardDef :=
  { id := ⟨"OGN-181"⟩,
    name := "Pack of Wonders",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Pack of Wonders: the effect is not written yet. -/
def OGN_181 : CardDef := OGN_181.meta

-- BEGIN GENERATED OGN-182
/--
**Scrapheap** — Gear · Chaos · Energy 2
Printings: OGN-182/298

> When this is played, discarded, or killed, draw 1.
-/
def OGN_182.meta : CardDef :=
  { id := ⟨"OGN-182"⟩,
    name := "Scrapheap",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Scrapheap: the effect is not written yet. -/
def OGN_182 : CardDef := OGN_182.meta

-- BEGIN GENERATED OGN-183
/--
**Stacked Deck** — Spell · Chaos · Energy 1
Printings: OGN-183/298

> [Action] (Play on your turn or in showdowns.)
> Look at the top 3 cards of your Main Deck. Put 1 into your hand and recycle the rest.
-/
def OGN_183.meta : CardDef :=
  { id := ⟨"OGN-183"⟩,
    name := "Stacked Deck",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Stacked Deck: the effect is not written yet. -/
def OGN_183 : CardDef := OGN_183.meta

-- BEGIN GENERATED OGN-184
/--
**The Syren** — Gear · Chaos · Energy 2
Printings: OGN-184/298

> :rb_energy_1:, :rb_exhaust:: Move a friendly unit at a battlefield to your base.
-/
def OGN_184.meta : CardDef :=
  { id := ⟨"OGN-184"⟩,
    name := "The Syren",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- The Syren. -/
def OGN_184 : CardDef :=
  { OGN_184.meta with
    abilities := [.activated [.exhaustSelf, .pay ⟨1, []⟩] .normal
        (.of [.targetOf .one .friendly .atBattlefield [.ofType .unit]]
        (.prim (.move (.slot 0) .base))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-185
/--
**Traveling Merchant** — Unit · Chaos · Energy 2 · Might 2
Printings: OGN-185/298

> When I move, discard 1, then draw 1.
-/
def OGN_185.meta : CardDef :=
  { id := ⟨"OGN-185"⟩,
    name := "Traveling Merchant",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Traveling Merchant. -/
def OGN_185 : CardDef :=
  { OGN_185.meta with
    abilities := [.triggered (.onSelf .move)
        (.of []
        (.seqOf [.prim (.discard .you (.const 1)),
          .prim (.draw .you (.const 1))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-186
/--
**Treasure Trove** — Gear · Chaos · Energy 2
Printings: OGN-186/298

> When this leaves the board, draw 1 and channel 1 rune exhausted.
> :rb_rune_chaos:, :rb_exhaust:: Kill this.
-/
def OGN_186.meta : CardDef :=
  { id := ⟨"OGN-186"⟩,
    name := "Treasure Trove",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Treasure Trove: the effect is not written yet. -/
def OGN_186 : CardDef := OGN_186.meta

-- BEGIN GENERATED OGN-187
/--
**Whirlwind** — Spell · Chaos · Energy 4 + Power 1
Printings: OGN-187/298

> Starting with the next player, each player may return a unit to its owner's hand.
-/
def OGN_187.meta : CardDef :=
  { id := ⟨"OGN-187"⟩,
    name := "Whirlwind",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Whirlwind: the effect is not written yet. -/
def OGN_187 : CardDef := OGN_187.meta

-- BEGIN GENERATED OGN-188
/--
**Zaunite Bouncer** — Unit · Chaos · Energy 4 + Power 2 · Might 2
Printings: OGN-188/298

> When you play me, return another unit at a battlefield to its owner's hand.
-/
def OGN_188.meta : CardDef :=
  { id := ⟨"OGN-188"⟩,
    name := "Zaunite Bouncer",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos, .domain .chaos]⟩,
    might := some 2,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Zaunite Bouncer. -/
def OGN_188 : CardDef :=
  { OGN_188.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .atBattlefield [.ofType .unit, .notSelf]]
        (.prim (.returnToHand (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-189
/--
**Kayn, Unleashed** — Unit · Chaos · Energy 6 + Power 1 · Might 6
Printings: OGN-189/298, RAD-182/167

> [Ganking] (I can move from battlefield to battlefield.)
> If I have moved twice this turn, I don't take damage.
-/
def OGN_189.meta : CardDef :=
  { id := ⟨"OGN-189"⟩,
    name := "Kayn",
    subtitle := some "Unleashed",
    types := [.unit],
    tags := [⟨"Kayn"⟩, ⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨6, [.domain .chaos]⟩,
    might := some 6,
    keywords := [{ keyword := .ganking }],
    sets := [⟨"OGN"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Kayn, Unleashed: the effect is not written yet. -/
def OGN_189 : CardDef := OGN_189.meta

-- BEGIN GENERATED OGN-190
/--
**Kog'Maw, Caustic** — Unit · Chaos · Energy 3 + Power 1 · Might 1
Printings: OGN-190/298

> [Deathknell] — Deal 4 to all units at my battlefield. (When I die, get the effect.)
-/
def OGN_190.meta : CardDef :=
  { id := ⟨"OGN-190"⟩,
    name := "Kog'Maw",
    subtitle := some "Caustic",
    types := [.unit],
    tags := [⟨"Kog'Maw"⟩, ⟨"The Void"⟩],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    might := some 1,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Kog'Maw, Caustic: the effect is not written yet. -/
def OGN_190 : CardDef := OGN_190.meta

-- BEGIN GENERATED OGN-191
/--
**Maddened Marauder** — Unit · Chaos · Energy 5 · Might 4
Printings: OGN-191/298

> [Tank] (I must be assigned combat damage first.)
> When you play me, move a unit from a battlefield to its base.
-/
def OGN_191.meta : CardDef :=
  { id := ⟨"OGN-191"⟩,
    name := "Maddened Marauder",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨5, []⟩,
    might := some 4,
    keywords := [{ keyword := .tank }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Maddened Marauder. -/
def OGN_191 : CardDef :=
  { OGN_191.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .atBattlefield [.ofType .unit]] (.prim (.move (.slot 0) .base)))
      .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-192
/--
**Mindsplitter** — Unit · Chaos · Energy 7 + Power 2 · Might 7
Printings: OGN-192/298

> When you play me, choose an opponent. They reveal their hand. Choose a card from it, and they
> discard that card.
-/
def OGN_192.meta : CardDef :=
  { id := ⟨"OGN-192"⟩,
    name := "Mindsplitter",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Mount Targon"⟩],
    domains := [.chaos],
    cost := some ⟨7, [.domain .chaos, .domain .chaos]⟩,
    might := some 7,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Mindsplitter: the effect is not written yet. -/
def OGN_192 : CardDef := OGN_192.meta

-- BEGIN GENERATED OGN-193
/--
**Miss Fortune, Buccaneer** — Unit · Chaos · Energy 4 + Power 1 · Might 4
Printings: OGN-193/298, OGN-193a/298

> You may play me to an open battlefield.
> Friendly units may be played to open battlefields.
-/
def OGN_193.meta : CardDef :=
  { id := ⟨"OGN-193"⟩,
    name := "Miss Fortune",
    subtitle := some "Buccaneer",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Miss Fortune"⟩, ⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Miss Fortune, Buccaneer: the effect is not written yet. -/
def OGN_193 : CardDef := OGN_193.meta

-- BEGIN GENERATED OGN-194
/--
**Nocturne, Horrifying** — Unit · Chaos · Energy 4 + Power 1 · Might 4
Printings: OGN-194/298

> [Ganking] (I can move from battlefield to battlefield.)
> When you look at cards from the top of your deck (and don't draw them) and see me, you may
> play me for :rb_rune_rainbow:.
-/
def OGN_194.meta : CardDef :=
  { id := ⟨"OGN-194"⟩,
    name := "Nocturne",
    subtitle := some "Horrifying",
    types := [.unit],
    tags := [⟨"Nocturne"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    might := some 4,
    keywords := [{ keyword := .ganking }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Nocturne, Horrifying: the effect is not written yet. -/
def OGN_194 : CardDef := OGN_194.meta

-- BEGIN GENERATED OGN-195
/--
**Rhasa the Sunderer** — Unit · Chaos · Energy 10 + Power 1 · Might 6
Printings: OGN-195/298

> I cost :rb_energy_1: less for each card in your trash.
-/
def OGN_195.meta : CardDef :=
  { id := ⟨"OGN-195"⟩,
    name := "Rhasa the Sunderer",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨10, [.domain .chaos]⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Rhasa the Sunderer. -/
def OGN_195 : CardDef :=
  { OGN_195.meta with
    abilities := [.passive .always [.costMinus .self (.count (.all .friendly .inTrash []))]],
    status := .drafted }

-- BEGIN GENERATED OGN-196
/--
**Soulgorger** — Unit · Chaos · Energy 8 + Power 2 · Might 5
Printings: OGN-196/298

> When you play me, you may play a unit from your trash, ignoring its Energy cost. (You must
> still pay its Power cost.)
-/
def OGN_196.meta : CardDef :=
  { id := ⟨"OGN-196"⟩,
    name := "Soulgorger",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨8, [.domain .chaos, .domain .chaos]⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Soulgorger: the effect is not written yet. -/
def OGN_196 : CardDef := OGN_196.meta

-- BEGIN GENERATED OGN-197
/--
**Teemo, Scout** — Unit · Chaos · Energy 2 · Might 1
Printings: OGN-197/298, OGN-197a/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me, give me +3 :rb_might: this turn.
-/
def OGN_197.meta : CardDef :=
  { id := ⟨"OGN-197"⟩,
    name := "Teemo",
    subtitle := some "Scout",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Teemo"⟩, ⟨"Bandle City"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Teemo, Scout. -/
def OGN_197 : CardDef :=
  { OGN_197.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.grant .self (.mightPlus .it (.const 3)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-198
/--
**The Harrowing** — Spell · Chaos · Energy 6 + Power 2
Printings: OGN-198/298

> Play a unit from your trash, ignoring its Energy cost. (You must still pay its Power cost.)
-/
def OGN_198.meta : CardDef :=
  { id := ⟨"OGN-198"⟩,
    name := "The Harrowing",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨6, [.domain .chaos, .domain .chaos]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- The Harrowing: the effect is not written yet. -/
def OGN_198 : CardDef := OGN_198.meta

-- BEGIN GENERATED OGN-199
/--
**Tideturner** — Unit · Chaos · Energy 2 · Might 2
Printings: OGN-199/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me, you may choose a friendly unit. Move me to its location and it to my
> original location.
-/
def OGN_199.meta : CardDef :=
  { id := ⟨"OGN-199"⟩,
    name := "Tideturner",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Tideturner: the effect is not written yet. -/
def OGN_199 : CardDef := OGN_199.meta

-- BEGIN GENERATED OGN-200
/--
**Twisted Fate, Gambler** — Unit · Chaos · Energy 4 · Might 4
Printings: OGN-200/298

> When I attack, reveal the top rune of your rune deck, then recycle it. Do one of the following
> based on its domain::rb_rune_fury: — Deal 2 to an enemy unit here and 1 to all other enemy
> units here.:rb_rune_mind: — Draw 1.:rb_rune_order: — Stun an enemy unit.
-/
def OGN_200.meta : CardDef :=
  { id := ⟨"OGN-200"⟩,
    name := "Twisted Fate",
    subtitle := some "Gambler",
    types := [.unit],
    tags := [⟨"Twisted Fate"⟩, ⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Twisted Fate, Gambler: the effect is not written yet. -/
def OGN_200 : CardDef := OGN_200.meta

-- BEGIN GENERATED OGN-201
/--
**Invert Timelines** — Spell · Chaos · Energy 3 + Power 1
Printings: OGN-201/298

> Each player discards their hand, then draws 4.
-/
def OGN_201.meta : CardDef :=
  { id := ⟨"OGN-201"⟩,
    name := "Invert Timelines",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Invert Timelines: the effect is not written yet. -/
def OGN_201 : CardDef := OGN_201.meta

-- BEGIN GENERATED OGN-202
/--
**Jinx, Rebel** — Unit · Chaos · Energy 5 + Power 1 · Might 5
Printings: OGN-202/298, OGN-202a/298

> When you discard one or more cards, ready me and give me +1 :rb_might: this turn.
-/
def OGN_202.meta : CardDef :=
  { id := ⟨"OGN-202"⟩,
    name := "Jinx",
    subtitle := some "Rebel",
    types := [.unit],
    tags := [⟨"Jinx"⟩, ⟨"Zaun"⟩],
    domains := [.chaos],
    cost := some ⟨5, [.domain .chaos]⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Jinx, Rebel: the effect is not written yet. -/
def OGN_202 : CardDef := OGN_202.meta

-- BEGIN GENERATED OGN-203
/--
**Possession** — Spell · Chaos · Energy 8 + Power 3
Printings: OGN-203/298

> [Action] (Play on your turn or in showdowns.)
> Choose an enemy unit at a battlefield. Take control of it and recall it. (Send it to your
> base. This isn't a move.)
-/
def OGN_203.meta : CardDef :=
  { id := ⟨"OGN-203"⟩,
    name := "Possession",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨8, [.domain .chaos, .domain .chaos, .domain .chaos]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Possession. -/
def OGN_203 : CardDef :=
  { OGN_203.meta with
    spellEffect := some (.of [.targetOf .one .enemy .atBattlefield [.ofType .unit]]
    (.seqOf [.prim (.takeControl (.slot 0)), .prim (.recall (.slot 0) false)])),
    status := .drafted }

-- BEGIN GENERATED OGN-204
/--
**Seal of Discord** — Gear · Chaos · Energy 0 + Power 1
Printings: OGN-204/298, SFD-234/221

> :rb_exhaust:: [Reaction] — [Add] :rb_rune_chaos:. (Abilities that add resources can't be
> reacted to.)
-/
def OGN_204.meta : CardDef :=
  { id := ⟨"OGN-204"⟩,
    name := "Seal of Discord",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨0, [.domain .chaos]⟩,
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Seal of Discord. -/
def OGN_204 : CardDef :=
  { OGN_204.meta with
    abilities := [.activated [.exhaustSelf] .reaction
        (.of []
        (.prim (.addPower .you (.const 1) (some .chaos) none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-205
/--
**Yasuo, Windrider** — Unit · Chaos · Energy 5 + Power 1 · Might 4
Printings: OGN-205/298, OGN-205a/298, SFD-235*/221, SFD-235/221

> [Ganking] (I can move from battlefield to battlefield.)
> The third time I move in a turn, you score 1 point.
-/
def OGN_205.meta : CardDef :=
  { id := ⟨"OGN-205"⟩,
    name := "Yasuo",
    subtitle := some "Windrider",
    types := [.unit],
    tags := [⟨"Yasuo"⟩, ⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨5, [.domain .chaos]⟩,
    might := some 4,
    keywords := [{ keyword := .ganking }],
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Yasuo, Windrider: the effect is not written yet. -/
def OGN_205 : CardDef := OGN_205.meta

-- BEGIN GENERATED OGN-206
/--
**Back to Back** — Spell · Order · Energy 3
Printings: OGN-206/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give two friendly units each +2 :rb_might: this turn.
-/
def OGN_206.meta : CardDef :=
  { id := ⟨"OGN-206"⟩,
    name := "Back to Back",
    types := [.spell],
    domains := [.order],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Back to Back: the effect is not written yet. -/
def OGN_206 : CardDef := OGN_206.meta

-- BEGIN GENERATED OGN-207
/--
**Call to Glory** — Spell · Order · Energy 3
Printings: OGN-207/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> As you play this, you may spend a buff as an additional cost. If you do, ignore this spell's
> cost.
> Give a unit +3 :rb_might: this turn.
-/
def OGN_207.meta : CardDef :=
  { id := ⟨"OGN-207"⟩,
    name := "Call to Glory",
    types := [.spell],
    domains := [.order],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Call to Glory: the effect is not written yet. -/
def OGN_207 : CardDef := OGN_207.meta

-- BEGIN GENERATED OGN-208
/--
**Cruel Patron** — Unit · Order · Energy 4 · Might 6
Printings: OGN-208/298

> As an additional cost to play me, kill a friendly unit.
-/
def OGN_208.meta : CardDef :=
  { id := ⟨"OGN-208"⟩,
    name := "Cruel Patron",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Cruel Patron: the effect is not written yet. -/
def OGN_208 : CardDef := OGN_208.meta

-- BEGIN GENERATED OGN-209
/--
**Cull the Weak** — Spell · Order · Energy 2 + Power 1
Printings: OGN-209/298

> Each player kills one of their units.
-/
def OGN_209.meta : CardDef :=
  { id := ⟨"OGN-209"⟩,
    name := "Cull the Weak",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Cull the Weak: the effect is not written yet. -/
def OGN_209 : CardDef := OGN_209.meta

-- BEGIN GENERATED OGN-210
/--
**Daring Poro** — Unit · Order · Energy 2 · Might 2
Printings: OGN-210/298, UNL-225/219

> [Assault] (+1 :rb_might: while I'm an attacker.)
-/
def OGN_210.meta : CardDef :=
  { id := ⟨"OGN-210"⟩,
    name := "Daring Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .assault, arg := .amount 1 }],
    sets := [⟨"OGN"⟩, ⟨"UNL"⟩] }
-- END GENERATED

/-- Daring Poro. -/
def OGN_210 : CardDef :=
  { OGN_210.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-211
/--
**Faithful Manufactor** — Unit · Order · Energy 3 · Might 2
Printings: OGN-211/298

> When you play me, play a 1 :rb_might: Recruit unit token here.
-/
def OGN_211.meta : CardDef :=
  { id := ⟨"OGN-211"⟩,
    name := "Faithful Manufactor",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 2,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Faithful Manufactor. -/
def OGN_211 : CardDef :=
  { OGN_211.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.create "Recruit" (.const 1) .here false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-212
/--
**Forge of the Future** — Gear · Order · Energy 2
Printings: OGN-212/298

> When you play this, play a 1 :rb_might: Recruit unit token at your base.
> Kill this: Recycle up to 4 cards from trashes.
-/
def OGN_212.meta : CardDef :=
  { id := ⟨"OGN-212"⟩,
    name := "Forge of the Future",
    types := [.gear],
    domains := [.order],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Forge of the Future: the effect is not written yet. -/
def OGN_212 : CardDef := OGN_212.meta

-- BEGIN GENERATED OGN-213
/--
**Hidden Blade** — Spell · Order · Energy 2 + Power 1
Printings: OGN-213/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Kill a unit at a battlefield. Its controller draws 2.
-/
def OGN_213.meta : CardDef :=
  { id := ⟨"OGN-213"⟩,
    name := "Hidden Blade",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Hidden Blade: the effect is not written yet. -/
def OGN_213 : CardDef := OGN_213.meta

-- BEGIN GENERATED OGN-214
/--
**Order Rune** — Rune · Order
Printings: OGN-214/298, OGN-214a/298, VEN-R06, RAD-R06, RAD-R06a

> (no text)
-/
def OGN_214.meta : CardDef :=
  { id := ⟨"OGN-214"⟩,
    name := "Order Rune",
    types := [.rune],
    domains := [.order],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Order Rune. -/
def OGN_214 : CardDef :=
  { OGN_214.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-215
/--
**Petty Officer** — Unit · Order · Energy 5 · Might 5
Printings: OGN-215/298

> [Assault] (+1 :rb_might: while I'm an attacker.)
-/
def OGN_215.meta : CardDef :=
  { id := ⟨"OGN-215"⟩,
    name := "Petty Officer",
    types := [.unit],
    tags := [⟨"Pirate"⟩, ⟨"Bilgewater"⟩],
    domains := [.order],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .assault, arg := .amount 1 }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Petty Officer. -/
def OGN_215 : CardDef :=
  { OGN_215.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-216
/--
**Soaring Scout** — Unit · Order · Energy 2 · Might 1
Printings: OGN-216/298

> [Deathknell] — Channel 1 rune exhausted. (When I die, get the effect.)
-/
def OGN_216.meta : CardDef :=
  { id := ⟨"OGN-216"⟩,
    name := "Soaring Scout",
    types := [.unit],
    tags := [⟨"Bird"⟩, ⟨"Freljord"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Soaring Scout. -/
def OGN_216 : CardDef :=
  { OGN_216.meta with
    abilities := [.triggered (.onSelf .die)
        (.of []
        (.prim (.channel .you (.const 0) (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-217
/--
**Trifarian Gloryseeker** — Unit · Order · Energy 2 · Might 2
Printings: OGN-217/298

> [Legion] — When you play me, buff me. (If I don't have a buff, I get a +1 :rb_might: buff. Get
> the effect if you've played another card this turn.)
-/
def OGN_217.meta : CardDef :=
  { id := ⟨"OGN-217"⟩,
    name := "Trifarian Gloryseeker",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .legion }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Trifarian Gloryseeker. -/
def OGN_217 : CardDef :=
  { OGN_217.meta with
    abilities := [.triggered { Trigger.onSelf .play with condition := .legion }
        (.of []
        (.prim (.buff .self))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-218
/--
**Vanguard Captain** — Unit · Order · Energy 3 + Power 1 · Might 3
Printings: OGN-218/298

> [Legion] — When you play me, play two 1 :rb_might: Recruit unit tokens here. (Get the effect
> if you've played another card this turn.)
-/
def OGN_218.meta : CardDef :=
  { id := ⟨"OGN-218"⟩,
    name := "Vanguard Captain",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨3, [.domain .order]⟩,
    might := some 3,
    keywords := [{ keyword := .legion }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Vanguard Captain. -/
def OGN_218 : CardDef :=
  { OGN_218.meta with
    abilities := [.triggered { Trigger.onSelf .play with condition := .legion }
        (.of []
        (.prim (.create "Recruit" (.const 2) .here false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-219
/--
**Vanguard Sergeant** — Unit · Order · Energy 4 · Might 4
Printings: OGN-219/298

> (no text)
-/
def OGN_219.meta : CardDef :=
  { id := ⟨"OGN-219"⟩,
    name := "Vanguard Sergeant",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Vanguard Sergeant. -/
def OGN_219 : CardDef :=
  { OGN_219.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-220
/--
**Facebreaker** — Spell · Order · Energy 2
Printings: OGN-220/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Stun a friendly unit and an enemy unit at the same battlefield. (They don't deal combat damage
> this turn.)
-/
def OGN_220.meta : CardDef :=
  { id := ⟨"OGN-220"⟩,
    name := "Facebreaker",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Facebreaker: the effect is not written yet. -/
def OGN_220 : CardDef := OGN_220.meta

-- BEGIN GENERATED OGN-221
/--
**Imperial Decree** — Spell · Order · Energy 5 + Power 2
Printings: OGN-221/298

> [Action] (Play on your turn or in showdowns.)
> When any unit takes damage this turn, kill it.
-/
def OGN_221.meta : CardDef :=
  { id := ⟨"OGN-221"⟩,
    name := "Imperial Decree",
    types := [.spell],
    domains := [.order],
    cost := some ⟨5, [.domain .order, .domain .order]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Imperial Decree: the effect is not written yet. -/
def OGN_221 : CardDef := OGN_221.meta

-- BEGIN GENERATED OGN-222
/--
**Noxian Drummer** — Unit · Order · Energy 3 · Might 3
Printings: OGN-222/298

> When I move to a battlefield, play a 1 :rb_might: Recruit unit token here. (It is also at the
> battlefield.)
-/
def OGN_222.meta : CardDef :=
  { id := ⟨"OGN-222"⟩,
    name := "Noxian Drummer",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Noxian Drummer. -/
def OGN_222 : CardDef :=
  { OGN_222.meta with
    abilities := [.triggered
      { Trigger.onSelf .move with
        condition := .cmp .ge (.count (Selector.all .friendly .here [.ofType .unit])) (.const 1) }
      (.of [] (.prim (.create "Recruit" (.const 1) .here false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-223
/--
**Peak Guardian** — Unit · Order · Energy 6 + Power 1 · Might 5
Printings: OGN-223/298

> When you play me, buff me. Then, if I am at a battlefield, buff all other friendly units
> there. (To buff a unit, give it a +1 :rb_might: buff if it doesn't already have one.)
-/
def OGN_223.meta : CardDef :=
  { id := ⟨"OGN-223"⟩,
    name := "Peak Guardian",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order]⟩,
    might := some 5,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Peak Guardian. -/
def OGN_223 : CardDef :=
  { OGN_223.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.seqOf [.prim (.buff .self),
        .prim (.buff (Selector.all .friendly .here [.ofType .unit, .notSelf]))]))
      .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-224
/--
**Salvage** — Spell · Order · Energy 2 + Power 1
Printings: OGN-224/298

> [Action] (Play on your turn or in showdowns.)
> You may kill a gear. Draw 1.
-/
def OGN_224.meta : CardDef :=
  { id := ⟨"OGN-224"⟩,
    name := "Salvage",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Salvage. -/
def OGN_224 : CardDef :=
  { OGN_224.meta with
    spellEffect := some (.of []
      (.seqOf [.may (.prim (.kill (Selector.one .any .anywhere [.ofType .gear]))),
        .prim (.draw .you (.const 1))])),
    status := .drafted }

-- BEGIN GENERATED OGN-225
/--
**Solari Chief** — Unit · Order · Energy 5 + Power 1 · Might 4
Printings: OGN-225/298

> When you play me, choose an enemy unit. If it is stunned, kill it. Otherwise, stun it. (It
> doesn't deal combat damage this turn.)
-/
def OGN_225.meta : CardDef :=
  { id := ⟨"OGN-225"⟩,
    name := "Solari Chief",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Solari Chief: the effect is not written yet. -/
def OGN_225 : CardDef := OGN_225.meta

-- BEGIN GENERATED OGN-226
/--
**Spectral Matron** — Unit · Order · Energy 4 + Power 2 · Might 4
Printings: OGN-226/298

> When you play me, you may play a unit costing no more than :rb_energy_3: and no more than
> :rb_rune_rainbow: from your trash, ignoring its cost.
-/
def OGN_226.meta : CardDef :=
  { id := ⟨"OGN-226"⟩,
    name := "Spectral Matron",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order, .domain .order]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Spectral Matron: the effect is not written yet. -/
def OGN_226 : CardDef := OGN_226.meta

-- BEGIN GENERATED OGN-227
/--
**Symbol of the Solari** — Gear · Order · Energy 1
Printings: OGN-227/298

> If a combat where you are the attacker ends in a tie, recall ALL units instead. (Send them to
> base. This isn't a move. Ties are calculated after combat damage is dealt.)
-/
def OGN_227.meta : CardDef :=
  { id := ⟨"OGN-227"⟩,
    name := "Symbol of the Solari",
    types := [.gear],
    domains := [.order],
    cost := some ⟨1, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Symbol of the Solari: the effect is not written yet. -/
def OGN_227 : CardDef := OGN_227.meta

-- BEGIN GENERATED OGN-228
/--
**Vanguard Helm** — Gear · Order · Energy 2
Printings: OGN-228/298

> When a buffed friendly unit dies, buff another friendly unit. (If it doesn't have a buff, it
> gets a +1 :rb_might: buff.)
-/
def OGN_228.meta : CardDef :=
  { id := ⟨"OGN-228"⟩,
    name := "Vanguard Helm",
    types := [.gear],
    domains := [.order],
    cost := some ⟨2, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Vanguard Helm: the effect is not written yet. -/
def OGN_228 : CardDef := OGN_228.meta

-- BEGIN GENERATED OGN-229
/--
**Vengeance** — Spell · Order · Energy 4 + Power 2
Printings: OGN-229/298

> Kill a unit.
-/
def OGN_229.meta : CardDef :=
  { id := ⟨"OGN-229"⟩,
    name := "Vengeance",
    types := [.spell],
    domains := [.order],
    cost := some ⟨4, [.domain .order, .domain .order]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Vengeance. -/
def OGN_229 : CardDef :=
  { OGN_229.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.prim (.kill (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED OGN-230
/--
**Albus Ferros** — Unit · Order · Energy 4 · Might 3
Printings: OGN-230/298

> When you play me, spend any number of buffs. For each buff spent, channel 1 rune exhausted.
-/
def OGN_230.meta : CardDef :=
  { id := ⟨"OGN-230"⟩,
    name := "Albus Ferros",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Albus Ferros: the effect is not written yet. -/
def OGN_230 : CardDef := OGN_230.meta

-- BEGIN GENERATED OGN-231
/--
**Commander Ledros** — Unit · Order · Energy 6 + Power 4 · Might 8
Printings: OGN-231/298

> As you play me, you may kill any number of friendly units as an additional cost. Reduce my
> cost by :rb_rune_order: for each killed this way.
> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> [Ganking] (I can move from battlefield to battlefield.)
-/
def OGN_231.meta : CardDef :=
  { id := ⟨"OGN-231"⟩,
    name := "Commander Ledros",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order, .domain .order, .domain .order, .domain .order]⟩,
    might := some 8,
    keywords := [{ keyword := .deflect, arg := .amount 1 },
      { keyword := .ganking }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Commander Ledros: the effect is not written yet. -/
def OGN_231 : CardDef := OGN_231.meta

-- BEGIN GENERATED OGN-232
/--
**Fiora, Victorious** — Unit · Order · Energy 4 · Might 4
Printings: OGN-232/298

> While I'm [Mighty], I have [Deflect], [Ganking], and [Shield]. (I'm Mighty while I have 5+
> :rb_might:.)
-/
def OGN_232.meta : CardDef :=
  { id := ⟨"OGN-232"⟩,
    name := "Fiora",
    subtitle := some "Victorious",
    types := [.unit],
    tags := [⟨"Fiora"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Fiora, Victorious: the effect is not written yet. -/
def OGN_232 : CardDef := OGN_232.meta

-- BEGIN GENERATED OGN-233
/--
**Grand Strategem** — Spell · Order · Energy 6 + Power 3
Printings: OGN-233/298

> [Action] (Play on your turn or in showdowns.)
> Give friendly units +5 :rb_might: this turn.
-/
def OGN_233.meta : CardDef :=
  { id := ⟨"OGN-233"⟩,
    name := "Grand Strategem",
    types := [.spell],
    domains := [.order],
    cost := some ⟨6, [.domain .order, .domain .order, .domain .order]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Grand Strategem. -/
def OGN_233 : CardDef :=
  { OGN_233.meta with
    spellEffect := some (.of []
      (.grant (Selector.all .friendly .anywhere [.ofType .unit]) (.mightPlus .it (.const 5))
        .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED OGN-234
/--
**Harnessed Dragon** — Unit · Order · Energy 8 + Power 2 · Might 6
Printings: OGN-234/298

> When you play me, kill an enemy unit.
-/
def OGN_234.meta : CardDef :=
  { id := ⟨"OGN-234"⟩,
    name := "Harnessed Dragon",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨8, [.domain .order, .domain .order]⟩,
    might := some 6,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Harnessed Dragon. -/
def OGN_234 : CardDef :=
  { OGN_234.meta with
    abilities := [.triggered (.onSelf .play)
        (.of [.targetOf .one .enemy .anywhere [.ofType .unit]]
        (.prim (.kill (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-235
/--
**Karma, Channeler** — Unit · Order · Energy 6 + Power 1 · Might 6
Printings: OGN-235/298, SFD-237*/221, SFD-237/221

> [Vision] (When you play me, look at the top card of your Main Deck. You may recycle it.)
> When you recycle one or more cards, buff a friendly unit. (If it doesn't have a buff, it gets
> a +1 :rb_might: buff. Runes aren't cards.)
-/
def OGN_235.meta : CardDef :=
  { id := ⟨"OGN-235"⟩,
    name := "Karma",
    subtitle := some "Channeler",
    types := [.unit],
    tags := [⟨"Vi"⟩, ⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order]⟩,
    might := some 6,
    keywords := [{ keyword := .vision }],
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Karma, Channeler: the effect is not written yet. -/
def OGN_235 : CardDef := OGN_235.meta

-- BEGIN GENERATED OGN-236
/--
**Karthus, Eternal** — Unit · Order · Energy 3 + Power 1 · Might 3
Printings: OGN-236/298

> Your [Deathknell] effects trigger an additional time.
-/
def OGN_236.meta : CardDef :=
  { id := ⟨"OGN-236"⟩,
    name := "Karthus",
    subtitle := some "Eternal",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Karthus"⟩, ⟨"Shadow Isles"⟩],
    domains := [.order],
    cost := some ⟨3, [.domain .order]⟩,
    might := some 3,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/--
Karthus, Eternal.
Approximation: Deathknell is the keyword for a trigger on dying; every trigger on dying is
taken to be one.
-/
def OGN_236 : CardDef :=
  { OGN_236.meta with
    abilities := [.passive .always [.triggersExtra .die .anywhere]],
    status := .drafted }

-- BEGIN GENERATED OGN-237
/--
**King's Edict** — Spell · Order · Energy 6 + Power 2
Printings: OGN-237/298

> Starting with the next player, each other player chooses a unit you don't control that hasn't
> been chosen for this spell. Kill those units.
-/
def OGN_237.meta : CardDef :=
  { id := ⟨"OGN-237"⟩,
    name := "King's Edict",
    types := [.spell],
    domains := [.order],
    cost := some ⟨6, [.domain .order, .domain .order]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- King's Edict: the effect is not written yet. -/
def OGN_237 : CardDef := OGN_237.meta

-- BEGIN GENERATED OGN-238
/--
**Leona, Determined** — Unit · Order · Energy 4 + Power 1 · Might 4
Printings: OGN-238/298, OGN-238a/298, VEN-184/166

> [Shield] (+1 :rb_might: while I'm a defender.)
> When I attack, stun an enemy unit here. (It doesn't deal combat damage this turn.)
-/
def OGN_238.meta : CardDef :=
  { id := ⟨"OGN-238"⟩,
    name := "Leona",
    subtitle := some "Determined",
    types := [.unit],
    tags := [⟨"Leona"⟩, ⟨"Mount Targon"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order]⟩,
    might := some 4,
    keywords := [{ keyword := .shield, arg := .amount 1 }],
    sets := [⟨"OGN"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Leona, Determined. -/
def OGN_238 : CardDef :=
  { OGN_238.meta with
    abilities := [.triggered (.onSelf .attack)
      (.of [.targetOf .one .enemy .here [.ofType .unit]] (.prim (.stun (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-239
/--
**Machine Evangel** — Unit · Order · Energy 5 + Power 1 · Might 4
Printings: OGN-239/298

> [Deathknell] — Play three 1 :rb_might: Recruit unit tokens into your base. (When I die, get
> the effect.)
-/
def OGN_239.meta : CardDef :=
  { id := ⟨"OGN-239"⟩,
    name := "Machine Evangel",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 4,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Machine Evangel. -/
def OGN_239 : CardDef :=
  { OGN_239.meta with
    abilities := [.triggered (.onSelf .die)
        (.of []
        (.prim (.create "Recruit" (.const 3) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-240
/--
**Sett, Kingpin** — Unit · Order · Energy 4 + Power 1 · Might 5
Printings: OGN-240/298, OGN-240a/298, RAD-183/167

> [Tank] (I must be assigned combat damage first.)
> I get +1 :rb_might: for each buffed friendly unit at my battlefield.
-/
def OGN_240.meta : CardDef :=
  { id := ⟨"OGN-240"⟩,
    name := "Sett",
    subtitle := some "Kingpin",
    types := [.unit],
    tags := [⟨"Sett"⟩, ⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order]⟩,
    might := some 5,
    keywords := [{ keyword := .tank }],
    sets := [⟨"OGN"⟩, ⟨"RAD"⟩] }
-- END GENERATED

/-- Sett, Kingpin. -/
def OGN_240 : CardDef :=
  { OGN_240.meta with
    abilities := [.passive .always
      [.mightPlus .self (.count (Selector.all .friendly .here [.ofType .unit, .buffed]))]],
    status := .drafted }

-- BEGIN GENERATED OGN-241
/--
**Shen, Kinkou** — Unit · Order · Energy 3 + Power 1 · Might 3
Printings: OGN-241/298

> [Reaction] (Play any time, even before spells and abilities resolve, including to a
> battlefield you control.)
> [Shield 2] (+2 :rb_might: while I'm a defender.)
> [Tank] (I must be assigned combat damage first.)
-/
def OGN_241.meta : CardDef :=
  { id := ⟨"OGN-241"⟩,
    name := "Shen",
    subtitle := some "Kinkou",
    types := [.unit],
    tags := [⟨"Shen"⟩, ⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨3, [.domain .order]⟩,
    might := some 3,
    keywords := [{ keyword := .reaction },
      { keyword := .shield, arg := .amount 2 },
      { keyword := .tank }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Shen, Kinkou. -/
def OGN_241 : CardDef :=
  { OGN_241.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-242
/--
**Baited Hook** — Gear · Order · Energy 3
Printings: OGN-242/298

> :rb_energy_1::rb_rune_order:, :rb_exhaust:: Kill a friendly unit. Look at the top 5 cards of
> your Main Deck. You may banish a unit from among them that has Might up to 1 more than the
> killed unit and play it, ignoring its cost. Then recycle the rest.
-/
def OGN_242.meta : CardDef :=
  { id := ⟨"OGN-242"⟩,
    name := "Baited Hook",
    types := [.gear],
    domains := [.order],
    cost := some ⟨3, []⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Baited Hook: the effect is not written yet. -/
def OGN_242 : CardDef := OGN_242.meta

-- BEGIN GENERATED OGN-243
/--
**Darius, Executioner** — Unit · Order · Energy 6 + Power 1 · Might 6
Printings: OGN-243/298, OGN-243a/298, SFD-236*/221, SFD-236/221

> [Legion] — When you play me, ready me. (Get the effect if you've played another card this
> turn)
> Other friendly units have +1 :rb_might: here.
-/
def OGN_243.meta : CardDef :=
  { id := ⟨"OGN-243"⟩,
    name := "Darius",
    subtitle := some "Executioner",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Darius"⟩, ⟨"Noxus"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order]⟩,
    might := some 6,
    keywords := [{ keyword := .legion }],
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Darius, Executioner. -/
def OGN_243 : CardDef :=
  { OGN_243.meta with
    abilities :=
      [.triggered { Trigger.onSelf .play with condition := .legion }
        (.of [] (.prim (.ready .self))) .unlimited,
       .passive .always
        [.mightPlus (Selector.all .friendly .here [.ofType .unit, .notSelf]) (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED OGN-244
/--
**Divine Judgment** — Spell · Order · Energy 7 + Power 2
Printings: OGN-244/298

> Each player chooses 2 units, 2 gear, 2 runes, and 2 cards in their hands. Recycle the rest.
-/
def OGN_244.meta : CardDef :=
  { id := ⟨"OGN-244"⟩,
    name := "Divine Judgment",
    types := [.spell],
    domains := [.order],
    cost := some ⟨7, [.domain .order, .domain .order]⟩,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Divine Judgment: the effect is not written yet. -/
def OGN_244 : CardDef := OGN_244.meta

-- BEGIN GENERATED OGN-245
/--
**Seal of Unity** — Gear · Order · Energy 0 + Power 1
Printings: OGN-245/298, SFD-238/221

> :rb_exhaust:: [Reaction] — [Add] :rb_rune_order:. (Abilities that add resources can't be
> reacted to.)
-/
def OGN_245.meta : CardDef :=
  { id := ⟨"OGN-245"⟩,
    name := "Seal of Unity",
    types := [.gear],
    domains := [.order],
    cost := some ⟨0, [.domain .order]⟩,
    sets := [⟨"OGN"⟩, ⟨"SFD"⟩] }
-- END GENERATED

/-- Seal of Unity. -/
def OGN_245 : CardDef :=
  { OGN_245.meta with
    abilities := [.activated [.exhaustSelf] .reaction
        (.of []
        (.prim (.addPower .you (.const 1) (some .order) none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-246
/--
**Viktor, Leader** — Unit · Order · Energy 4 + Power 1 · Might 4
Printings: OGN-246/298, OGN-246a/298

> When another non-Recruit unit you control dies, play a 1 :rb_might: Recruit unit token into
> your base.
-/
def OGN_246.meta : CardDef :=
  { id := ⟨"OGN-246"⟩,
    name := "Viktor",
    subtitle := some "Leader",
    types := [.unit],
    tags := [⟨"Viktor"⟩, ⟨"Zaun"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order]⟩,
    might := some 4,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Viktor, Leader: the effect is not written yet. -/
def OGN_246 : CardDef := OGN_246.meta

-- BEGIN GENERATED OGN-247
/--
**Daughter of the Void** — Legend · Fury/Mind
Printings: OGN-247/298, OGN-299*/298, OGN-299/298

> :rb_exhaust:: [Reaction] — [Add] :rb_rune_rainbow:. Use only to play spells. (Abilities that
> add resources can't be reacted to.)
-/
def OGN_247.meta : CardDef :=
  { id := ⟨"OGN-247"⟩,
    name := "Daughter of the Void",
    types := [.legend],
    tags := [⟨"Kai'Sa"⟩],
    domains := [.fury, .mind],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Daughter of the Void: the effect is not written yet. -/
def OGN_247 : CardDef := OGN_247.meta

-- BEGIN GENERATED OGN-248
/--
**Icathian Rain, Kai'Sa** — Spell · Fury/Mind · Energy 7 + Power 3
Printings: OGN-248/298

> Deal 2 to a unit.
> Deal 2 to a unit.
> Deal 2 to a unit.
> Deal 2 to a unit.
> Deal 2 to a unit.
> Deal 2 to a unit.
-/
def OGN_248.meta : CardDef :=
  { id := ⟨"OGN-248"⟩,
    name := "Icathian Rain",
    subtitle := some "Kai'Sa",
    types := [.spell],
    tags := [⟨"Kai'Sa"⟩],
    domains := [.fury, .mind],
    cost := some ⟨7, [.any, .any, .any]⟩,
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Icathian Rain, Kai'Sa. -/
def OGN_248 : CardDef :=
  { OGN_248.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit],
        .targetOf .one .any .anywhere [.ofType .unit],
        .targetOf .one .any .anywhere [.ofType .unit],
        .targetOf .one .any .anywhere [.ofType .unit],
        .targetOf .one .any .anywhere [.ofType .unit],
        .targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.prim (.deal (.slot 0) (.const 2)),
        .prim (.deal (.slot 1) (.const 2)),
        .prim (.deal (.slot 2) (.const 2)),
        .prim (.deal (.slot 3) (.const 2)),
        .prim (.deal (.slot 4) (.const 2)),
        .prim (.deal (.slot 5) (.const 2))])),
    status := .drafted }

-- BEGIN GENERATED OGN-249
/--
**Relentless Storm** — Legend · Fury/Body
Printings: OGN-249/298, OGN-300*/298, OGN-300/298

> When you play a [Mighty] unit, you may exhaust me to channel 1 rune exhausted. (A unit is
> Mighty while it has 5+ :rb_might:.)
-/
def OGN_249.meta : CardDef :=
  { id := ⟨"OGN-249"⟩,
    name := "Relentless Storm",
    types := [.legend],
    tags := [⟨"Volibear"⟩],
    domains := [.fury, .body],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Relentless Storm: the effect is not written yet. -/
def OGN_249 : CardDef := OGN_249.meta

-- BEGIN GENERATED OGN-250
/--
**Stormbringer, Volibear** — Spell · Fury/Body · Energy 6 + Power 2
Printings: OGN-250/298

> Choose a friendly unit in your base. Deal damage equal to its Might to all enemy units at a
> battlefield, then move your unit there.
-/
def OGN_250.meta : CardDef :=
  { id := ⟨"OGN-250"⟩,
    name := "Stormbringer",
    subtitle := some "Volibear",
    types := [.spell],
    tags := [⟨"Volibear"⟩],
    domains := [.fury, .body],
    cost := some ⟨6, [.any, .any]⟩,
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Stormbringer, Volibear: the effect is not written yet. -/
def OGN_250 : CardDef := OGN_250.meta

-- BEGIN GENERATED OGN-251
/--
**Loose Cannon** — Legend · Fury/Chaos
Printings: OGN-251/298, OGN-301*/298, OGN-301/298

> At start of your Beginning Phase, draw 1 if you have one or fewer cards in your hand.
-/
def OGN_251.meta : CardDef :=
  { id := ⟨"OGN-251"⟩,
    name := "Loose Cannon",
    types := [.legend],
    tags := [⟨"Jinx"⟩],
    domains := [.fury, .chaos],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Loose Cannon: the effect is not written yet. -/
def OGN_251 : CardDef := OGN_251.meta

-- BEGIN GENERATED OGN-252
/--
**Super Mega Death Rocket!, Jinx** — Spell · Fury/Chaos · Energy 4 + Power 1
Printings: OGN-252/298

> Deal 5 to a unit.
> When you conquer, you may discard 1 to return this from your trash to your hand.
-/
def OGN_252.meta : CardDef :=
  { id := ⟨"OGN-252"⟩,
    name := "Super Mega Death Rocket!",
    subtitle := some "Jinx",
    types := [.spell],
    tags := [⟨"Jinx"⟩],
    domains := [.fury, .chaos],
    cost := some ⟨4, [.any]⟩,
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Super Mega Death Rocket!, Jinx: the effect is not written yet. -/
def OGN_252 : CardDef := OGN_252.meta

-- BEGIN GENERATED OGN-253
/--
**Hand of Noxus** — Legend · Fury/Order
Printings: OGN-253/298, OGN-302*/298, OGN-302/298

> :rb_exhaust:: [Reaction], [Legion] — [Add] :rb_energy_1:. (Abilities that add resources can't
> be reacted to. Get the effect if you've played a card this turn.)
-/
def OGN_253.meta : CardDef :=
  { id := ⟨"OGN-253"⟩,
    name := "Hand of Noxus",
    types := [.legend],
    tags := [⟨"Darius"⟩],
    domains := [.fury, .order],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Hand of Noxus: the effect is not written yet. -/
def OGN_253 : CardDef := OGN_253.meta

-- BEGIN GENERATED OGN-254
/--
**Noxian Guillotine, Darius** — Spell · Fury/Order · Energy 4 + Power 1
Printings: OGN-254/298

> [Action] (Play on your turn or in showdowns.)
> Choose a unit. Kill it the next time it takes damage this turn.
> [Legion] — Kill it now instead. (Get the effect if you've played another card this turn.)
-/
def OGN_254.meta : CardDef :=
  { id := ⟨"OGN-254"⟩,
    name := "Noxian Guillotine",
    subtitle := some "Darius",
    types := [.spell],
    tags := [⟨"Darius"⟩],
    domains := [.fury, .order],
    cost := some ⟨4, [.any]⟩,
    keywords := [{ keyword := .action },
      { keyword := .legion }],
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Noxian Guillotine, Darius: the effect is not written yet. -/
def OGN_254 : CardDef := OGN_254.meta

-- BEGIN GENERATED OGN-255
/--
**Nine-Tailed Fox** — Legend · Calm/Mind
Printings: OGN-255/298, OGN-303*/298, OGN-303/298

> When an enemy unit attacks a battlefield you control, give it -1 :rb_might: this turn, to a
> minimum of 1 :rb_might:.
-/
def OGN_255.meta : CardDef :=
  { id := ⟨"OGN-255"⟩,
    name := "Nine-Tailed Fox",
    types := [.legend],
    tags := [⟨"Ahri"⟩],
    domains := [.calm, .mind],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Nine-Tailed Fox: the effect is not written yet. -/
def OGN_255 : CardDef := OGN_255.meta

-- BEGIN GENERATED OGN-256
/--
**Fox-Fire, Ahri** — Spell · Calm/Mind · Energy 3
Printings: OGN-256/298

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Action] (Play on your turn or in showdowns.)
> Kill any number of units at a battlefield with total Might 4 or less.
-/
def OGN_256.meta : CardDef :=
  { id := ⟨"OGN-256"⟩,
    name := "Fox-Fire",
    subtitle := some "Ahri",
    types := [.spell],
    tags := [⟨"Ahri"⟩],
    domains := [.calm, .mind],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Fox-Fire, Ahri: the effect is not written yet. -/
def OGN_256 : CardDef := OGN_256.meta

-- BEGIN GENERATED OGN-257
/--
**Blind Monk** — Legend · Calm/Body
Printings: OGN-257/298, OGN-304*/298, OGN-304/298

> :rb_energy_1:, :rb_exhaust:: Buff a friendly unit. (If it doesn't have a buff, it gets a +1
> :rb_might: buff.)
-/
def OGN_257.meta : CardDef :=
  { id := ⟨"OGN-257"⟩,
    name := "Blind Monk",
    types := [.legend],
    tags := [⟨"Lee Sin"⟩],
    domains := [.calm, .body],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Blind Monk. -/
def OGN_257 : CardDef :=
  { OGN_257.meta with
    abilities := [.activated [.exhaustSelf, .pay ⟨1, []⟩] .normal
        (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.prim (.buff (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-258
/--
**Dragon's Rage, Lee Sin** — Spell · Calm/Body · Energy 4 + Power 1
Printings: OGN-258/298

> Move an enemy unit. Then choose another enemy unit at its destination. They deal damage equal
> to their Mights to each other.
-/
def OGN_258.meta : CardDef :=
  { id := ⟨"OGN-258"⟩,
    name := "Dragon's Rage",
    subtitle := some "Lee Sin",
    types := [.spell],
    tags := [⟨"Lee Sin"⟩],
    domains := [.calm, .body],
    cost := some ⟨4, [.any]⟩,
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Dragon's Rage, Lee Sin: the effect is not written yet. -/
def OGN_258 : CardDef := OGN_258.meta

-- BEGIN GENERATED OGN-259
/--
**Unforgiven** — Legend · Calm/Chaos
Printings: OGN-259/298, OGN-305*/298, OGN-305/298

> :rb_energy_2:, :rb_exhaust:: Move a friendly unit to or from your base.
-/
def OGN_259.meta : CardDef :=
  { id := ⟨"OGN-259"⟩,
    name := "Unforgiven",
    types := [.legend],
    tags := [⟨"Yasuo"⟩],
    domains := [.calm, .chaos],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Unforgiven: the effect is not written yet. -/
def OGN_259 : CardDef := OGN_259.meta

-- BEGIN GENERATED OGN-260
/--
**Last Breath, Yasuo** — Spell · Calm/Chaos · Energy 3 + Power 2
Printings: OGN-260/298

> [Action] (Play on your turn or in showdowns.)
> Ready a friendly unit. It deals damage equal to its Might to an enemy unit at a battlefield.
-/
def OGN_260.meta : CardDef :=
  { id := ⟨"OGN-260"⟩,
    name := "Last Breath",
    subtitle := some "Yasuo",
    types := [.spell],
    tags := [⟨"Yasuo"⟩],
    domains := [.calm, .chaos],
    cost := some ⟨3, [.any, .any]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Last Breath, Yasuo: the effect is not written yet. -/
def OGN_260 : CardDef := OGN_260.meta

-- BEGIN GENERATED OGN-261
/--
**Radiant Dawn** — Legend · Calm/Order
Printings: OGN-261/298, OGN-306*/298, OGN-306/298

> When you stun one or more enemy units, buff a friendly unit. (If it doesn't have a buff, it
> gets a +1 :rb_might: buff.)
-/
def OGN_261.meta : CardDef :=
  { id := ⟨"OGN-261"⟩,
    name := "Radiant Dawn",
    types := [.legend],
    tags := [⟨"Leona"⟩],
    domains := [.calm, .order],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Radiant Dawn: the effect is not written yet. -/
def OGN_261 : CardDef := OGN_261.meta

-- BEGIN GENERATED OGN-262
/--
**Zenith Blade, Leona** — Spell · Calm/Order · Energy 3 + Power 2
Printings: OGN-262/298

> [Action] (Play on your turn or in showdowns.)
> Stun an enemy unit at a battlefield. You may move a friendly unit to that enemy unit's
> battlefield. (A stunned unit doesn't deal combat damage this turn.)
-/
def OGN_262.meta : CardDef :=
  { id := ⟨"OGN-262"⟩,
    name := "Zenith Blade",
    subtitle := some "Leona",
    types := [.spell],
    tags := [⟨"Leona"⟩],
    domains := [.calm, .order],
    cost := some ⟨3, [.any, .any]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Zenith Blade, Leona: the effect is not written yet. -/
def OGN_262 : CardDef := OGN_262.meta

-- BEGIN GENERATED OGN-263
/--
**Swift Scout** — Legend · Mind/Chaos
Printings: OGN-263/298, OGN-307*/298, OGN-307/298

> You may pay :rb_energy_1: to hide a card with [Hidden] instead of :rb_rune_rainbow:.
> :rb_energy_1:, :rb_exhaust:: Put a Teemo unit you own into your hand from your Champion Zone
> or the board.
-/
def OGN_263.meta : CardDef :=
  { id := ⟨"OGN-263"⟩,
    name := "Swift Scout",
    types := [.legend],
    tags := [⟨"Teemo"⟩],
    domains := [.mind, .chaos],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Swift Scout: the effect is not written yet. -/
def OGN_263 : CardDef := OGN_263.meta

-- BEGIN GENERATED OGN-264
/--
**Guerilla Warfare, Teemo** — Spell · Mind/Chaos · Energy 2 + Power 1
Printings: OGN-264/298

> Return up to two cards with [Hidden] from your trash to your hand. You can hide ignoring costs
> this turn.
-/
def OGN_264.meta : CardDef :=
  { id := ⟨"OGN-264"⟩,
    name := "Guerilla Warfare",
    subtitle := some "Teemo",
    types := [.spell],
    tags := [⟨"Teemo"⟩],
    domains := [.mind, .chaos],
    cost := some ⟨2, [.any]⟩,
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Guerilla Warfare, Teemo: the effect is not written yet. -/
def OGN_264 : CardDef := OGN_264.meta

-- BEGIN GENERATED OGN-265
/--
**Herald of the Arcane** — Legend · Mind/Order
Printings: OGN-265/298, OGN-308*/298, OGN-308/298

> :rb_energy_1:, :rb_exhaust:: Play a 1 :rb_might: Recruit unit token.
-/
def OGN_265.meta : CardDef :=
  { id := ⟨"OGN-265"⟩,
    name := "Herald of the Arcane",
    types := [.legend],
    tags := [⟨"Viktor"⟩],
    domains := [.mind, .order],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Herald of the Arcane. -/
def OGN_265 : CardDef :=
  { OGN_265.meta with
    abilities := [.activated [.exhaustSelf, .pay ⟨1, []⟩] .normal
        (.of []
        (.prim (.create "Recruit" (.const 1) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-266
/--
**Siphon Power, Viktor** — Spell · Mind/Order · Energy 2 + Power 1
Printings: OGN-266/298

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a battlefield. Give friendly units there +1 :rb_might: this turn and enemy units there
> -1 :rb_might: this turn, to a minimum of 1 :rb_might:.
-/
def OGN_266.meta : CardDef :=
  { id := ⟨"OGN-266"⟩,
    name := "Siphon Power",
    subtitle := some "Viktor",
    types := [.spell],
    tags := [⟨"Viktor"⟩],
    domains := [.mind, .order],
    cost := some ⟨2, [.any]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Siphon Power, Viktor: the effect is not written yet. -/
def OGN_266 : CardDef := OGN_266.meta

-- BEGIN GENERATED OGN-267
/--
**Bounty Hunter** — Legend · Body/Chaos
Printings: OGN-267/298, OGN-309*/298, OGN-309/298

> :rb_exhaust:: Give a unit [Ganking] this turn. (It can move from battlefield to battlefield.)
-/
def OGN_267.meta : CardDef :=
  { id := ⟨"OGN-267"⟩,
    name := "Bounty Hunter",
    types := [.legend],
    tags := [⟨"Miss Fortune"⟩],
    domains := [.body, .chaos],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Bounty Hunter. -/
def OGN_267 : CardDef :=
  { OGN_267.meta with
    abilities := [.activated [.exhaustSelf] .normal
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.keyword .it ⟨.ganking, .none⟩) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-268
/--
**Bullet Time, Miss Fortune** — Spell · Body/Chaos · Energy 1
Printings: OGN-268/298

> [Action] (Play on your turn or in showdowns.)
> Pay any amount of :rb_rune_rainbow: to deal that much damage to all enemy units at a
> battlefield.
-/
def OGN_268.meta : CardDef :=
  { id := ⟨"OGN-268"⟩,
    name := "Bullet Time",
    subtitle := some "Miss Fortune",
    types := [.spell],
    tags := [⟨"Miss Fortune"⟩],
    domains := [.body, .chaos],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Bullet Time, Miss Fortune: the effect is not written yet. -/
def OGN_268 : CardDef := OGN_268.meta

-- BEGIN GENERATED OGN-269
/--
**The Boss** — Legend · Body/Order
Printings: OGN-269/298, OGN-310*/298, OGN-310/298

> When a buffed unit you control would die, you may pay :rb_rune_rainbow: and exhaust me to
> spend its buff and recall it exhausted instead. (Send it to base. This isn't a move.)
> When you conquer, ready me.
-/
def OGN_269.meta : CardDef :=
  { id := ⟨"OGN-269"⟩,
    name := "The Boss",
    types := [.legend],
    tags := [⟨"Sett"⟩],
    domains := [.body, .order],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- The Boss: the effect is not written yet. -/
def OGN_269 : CardDef := OGN_269.meta

-- BEGIN GENERATED OGN-270
/--
**Showstopper, Sett** — Spell · Body/Order · Energy 1 + Power 1
Printings: OGN-270/298

> Buff a friendly unit in your base, then move it to a battlefield. (If it doesn't have a buff,
> it gets a +1 :rb_might: buff.)
-/
def OGN_270.meta : CardDef :=
  { id := ⟨"OGN-270"⟩,
    name := "Showstopper",
    subtitle := some "Sett",
    types := [.spell],
    tags := [⟨"Sett"⟩],
    domains := [.body, .order],
    cost := some ⟨1, [.any]⟩,
    sets := [⟨"OGN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Showstopper, Sett: the effect is not written yet. -/
def OGN_270 : CardDef := OGN_270.meta

-- BEGIN GENERATED OGN-271
/--
**Recruit (DE)** — Unit · Colorless · Might 1
Printings: OGN-271/298

> (no text)
-/
def OGN_271.meta : CardDef :=
  { id := ⟨"OGN-271"⟩,
    name := "Recruit (DE)",
    types := [.unit],
    tags := [⟨"Recruit"⟩],
    might := some 1,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Recruit (DE). -/
def OGN_271 : CardDef :=
  { OGN_271.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-272
/--
**Recruit (NX)** — Unit · Colorless · Might 1
Printings: OGN-272/298

> (no text)
-/
def OGN_272.meta : CardDef :=
  { id := ⟨"OGN-272"⟩,
    name := "Recruit (NX)",
    types := [.unit],
    tags := [⟨"Recruit"⟩],
    might := some 1,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Recruit (NX). -/
def OGN_272 : CardDef :=
  { OGN_272.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-273
/--
**Recruit (ZN)** — Unit · Colorless · Might 1
Printings: OGN-273/298

> (no text)
-/
def OGN_273.meta : CardDef :=
  { id := ⟨"OGN-273"⟩,
    name := "Recruit (ZN)",
    types := [.unit],
    tags := [⟨"Recruit"⟩],
    might := some 1,
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Recruit (ZN). -/
def OGN_273 : CardDef :=
  { OGN_273.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-274
/--
**Sprite** — Unit · Colorless · Might 3
Printings: OGN-274/298, UNL-T07

> [Temporary] (Kill me at the start of your Beginning Phase, before scoring.)
-/
def OGN_274.meta : CardDef :=
  { id := ⟨"OGN-274"⟩,
    name := "Sprite",
    types := [.unit],
    tags := [⟨"Fae"⟩],
    might := some 3,
    keywords := [{ keyword := .temporary }],
    sets := [⟨"OGN"⟩, ⟨"UNL"⟩] }
-- END GENERATED

/-- Sprite. -/
def OGN_274 : CardDef :=
  { OGN_274.meta with
    status := .drafted }

-- BEGIN GENERATED OGN-275
/--
**Altar to Unity** — Battlefield · Colorless
Printings: OGN-275/298

> When you hold here, play a 1 :rb_might: Recruit unit token in your base.
-/
def OGN_275.meta : CardDef :=
  { id := ⟨"OGN-275"⟩,
    name := "Altar to Unity",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Altar to Unity. -/
def OGN_275 : CardDef :=
  { OGN_275.meta with
    abilities := [.triggered (.onSelf .youHold)
      (.of [] (.prim (.create "Recruit" (.const 1) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-276
/--
**Aspirant's Climb** — Battlefield · Colorless
Printings: OGN-276/298

> Increase the points needed to win the game by 1.
-/
def OGN_276.meta : CardDef :=
  { id := ⟨"OGN-276"⟩,
    name := "Aspirant's Climb",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Aspirant's Climb. -/
def OGN_276 : CardDef :=
  { OGN_276.meta with
    abilities := [.passive .always [.victoryScorePlus (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED OGN-277
/--
**Back-Alley Bar** — Battlefield · Colorless
Printings: OGN-277/298

> When a unit moves from here, give it +1 :rb_might: this turn.
-/
def OGN_277.meta : CardDef :=
  { id := ⟨"OGN-277"⟩,
    name := "Back-Alley Bar",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Back-Alley Bar: the effect is not written yet. -/
def OGN_277 : CardDef := OGN_277.meta

-- BEGIN GENERATED OGN-278
/--
**Bandle Tree** — Battlefield · Colorless
Printings: OGN-278/298

> You may hide an additional card here.
-/
def OGN_278.meta : CardDef :=
  { id := ⟨"OGN-278"⟩,
    name := "Bandle Tree",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Bandle Tree: the effect is not written yet. -/
def OGN_278 : CardDef := OGN_278.meta

-- BEGIN GENERATED OGN-279
/--
**Fortified Position** — Battlefield · Colorless
Printings: OGN-279/298

> When you defend here, choose a unit. It gains [Shield 2] this combat. (+2 :rb_might: while
> it's a defender.)
-/
def OGN_279.meta : CardDef :=
  { id := ⟨"OGN-279"⟩,
    name := "Fortified Position",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Fortified Position: the effect is not written yet. -/
def OGN_279 : CardDef := OGN_279.meta

-- BEGIN GENERATED OGN-280
/--
**Grove of the God-Willow** — Battlefield · Colorless
Printings: OGN-280/298

> When you hold here, draw 1.
-/
def OGN_280.meta : CardDef :=
  { id := ⟨"OGN-280"⟩,
    name := "Grove of the God-Willow",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Grove of the God-Willow. -/
def OGN_280 : CardDef :=
  { OGN_280.meta with
    abilities := [.triggered (.onSelf .youHold)
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-281
/--
**Hallowed Tomb** — Battlefield · Colorless
Printings: OGN-281/298

> When you hold here, you may return your Chosen Champion from your trash to your Champion Zone
> if it is empty.
-/
def OGN_281.meta : CardDef :=
  { id := ⟨"OGN-281"⟩,
    name := "Hallowed Tomb",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Hallowed Tomb: the effect is not written yet. -/
def OGN_281 : CardDef := OGN_281.meta

-- BEGIN GENERATED OGN-282
/--
**Monastery of Hirana** — Battlefield · Colorless
Printings: OGN-282/298

> When you conquer here, you may spend a buff to draw 1.
-/
def OGN_282.meta : CardDef :=
  { id := ⟨"OGN-282"⟩,
    name := "Monastery of Hirana",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Monastery of Hirana: the effect is not written yet. -/
def OGN_282 : CardDef := OGN_282.meta

-- BEGIN GENERATED OGN-283
/--
**Navori Fighting Pit** — Battlefield · Colorless
Printings: OGN-283/298

> When you hold here, buff a unit here. (If it doesn't have a buff, it gets a +1 :rb_might:
> buff.)
-/
def OGN_283.meta : CardDef :=
  { id := ⟨"OGN-283"⟩,
    name := "Navori Fighting Pit",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Navori Fighting Pit. -/
def OGN_283 : CardDef :=
  { OGN_283.meta with
    abilities := [.triggered (.onSelf .youHold)
      (.of [.targetOf .one .any .here [.ofType .unit]] (.prim (.buff (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-284
/--
**Obelisk of Power** — Battlefield · Colorless
Printings: OGN-284/298

> At the start of each player's first Beginning Phase, that player channels 1 rune.
-/
def OGN_284.meta : CardDef :=
  { id := ⟨"OGN-284"⟩,
    name := "Obelisk of Power",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Obelisk of Power: the effect is not written yet. -/
def OGN_284 : CardDef := OGN_284.meta

-- BEGIN GENERATED OGN-285
/--
**Reaver's Row** — Battlefield · Colorless
Printings: OGN-285/298

> When you defend here, you may move a friendly unit here to base.
-/
def OGN_285.meta : CardDef :=
  { id := ⟨"OGN-285"⟩,
    name := "Reaver's Row",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Reaver's Row: the effect is not written yet. -/
def OGN_285 : CardDef := OGN_285.meta

-- BEGIN GENERATED OGN-286
/--
**Reckoner's Arena** — Battlefield · Colorless
Printings: OGN-286/298

> When you hold here, activate the conquer effects of units here.
-/
def OGN_286.meta : CardDef :=
  { id := ⟨"OGN-286"⟩,
    name := "Reckoner's Arena",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Reckoner's Arena: the effect is not written yet. -/
def OGN_286 : CardDef := OGN_286.meta

-- BEGIN GENERATED OGN-287
/--
**Sigil of the Storm** — Battlefield · Colorless
Printings: OGN-287/298

> When you conquer here, recycle one of your runes.
-/
def OGN_287.meta : CardDef :=
  { id := ⟨"OGN-287"⟩,
    name := "Sigil of the Storm",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Sigil of the Storm: the effect is not written yet. -/
def OGN_287 : CardDef := OGN_287.meta

-- BEGIN GENERATED OGN-288
/--
**Startipped Peak** — Battlefield · Colorless
Printings: OGN-288/298

> When you hold here, you may channel 1 rune exhausted.
-/
def OGN_288.meta : CardDef :=
  { id := ⟨"OGN-288"⟩,
    name := "Startipped Peak",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Startipped Peak. -/
def OGN_288 : CardDef :=
  { OGN_288.meta with
    abilities := [.triggered (.onSelf .youHold)
      (.of [] (.may (.prim (.channel .you (.const 0) (.const 1))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-289
/--
**Targon's Peak** — Battlefield · Colorless
Printings: OGN-289/298

> When you conquer here, ready 2 runes at the end of this turn.
-/
def OGN_289.meta : CardDef :=
  { id := ⟨"OGN-289"⟩,
    name := "Targon's Peak",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Targon's Peak: the effect is not written yet. -/
def OGN_289 : CardDef := OGN_289.meta

-- BEGIN GENERATED OGN-290
/--
**The Arena's Greatest** — Battlefield · Colorless
Printings: OGN-290/298

> At the start of each player's first Beginning Phase, that player gains 1 point.
-/
def OGN_290.meta : CardDef :=
  { id := ⟨"OGN-290"⟩,
    name := "The Arena's Greatest",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- The Arena's Greatest: the effect is not written yet. -/
def OGN_290 : CardDef := OGN_290.meta

-- BEGIN GENERATED OGN-291
/--
**The Candlelit Sanctum** — Battlefield · Colorless
Printings: OGN-291/298

> When you conquer here, look at the top two cards of your Main Deck. You may recycle one or
> both of them. Put those you don't back in any order.
-/
def OGN_291.meta : CardDef :=
  { id := ⟨"OGN-291"⟩,
    name := "The Candlelit Sanctum",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- The Candlelit Sanctum: the effect is not written yet. -/
def OGN_291 : CardDef := OGN_291.meta

-- BEGIN GENERATED OGN-292
/--
**The Dreaming Tree** — Battlefield · Colorless
Printings: OGN-292/298

> When a player chooses a friendly unit here with a spell for the first time each turn, they
> draw 1.
-/
def OGN_292.meta : CardDef :=
  { id := ⟨"OGN-292"⟩,
    name := "The Dreaming Tree",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- The Dreaming Tree: the effect is not written yet. -/
def OGN_292 : CardDef := OGN_292.meta

-- BEGIN GENERATED OGN-293
/--
**The Grand Plaza** — Battlefield · Colorless
Printings: OGN-293/298

> When you hold here, if you have 7+ units here, you win the game.
-/
def OGN_293.meta : CardDef :=
  { id := ⟨"OGN-293"⟩,
    name := "The Grand Plaza",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- The Grand Plaza. -/
def OGN_293 : CardDef :=
  { OGN_293.meta with
    abilities := [.triggered
      { event := .youHold,
        condition := .cmp .ge (.count (.all .friendly .here [.ofType .unit])) (.const 7) }
      (.of [] (.prim (.win .you))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGN-294
/--
**Trifarian War Camp** — Battlefield · Colorless
Printings: OGN-294/298

> Units here have +1 :rb_might:. (This includes attackers.)
-/
def OGN_294.meta : CardDef :=
  { id := ⟨"OGN-294"⟩,
    name := "Trifarian War Camp",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Trifarian War Camp. -/
def OGN_294 : CardDef :=
  { OGN_294.meta with
    abilities := [.passive .always
      [.mightPlus (Selector.all .any .here [.ofType .unit]) (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED OGN-295
/--
**Vilemaw's Lair** — Battlefield · Colorless
Printings: OGN-295/298

> Units can't move from here to base.
-/
def OGN_295.meta : CardDef :=
  { id := ⟨"OGN-295"⟩,
    name := "Vilemaw's Lair",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Vilemaw's Lair: the effect is not written yet. -/
def OGN_295 : CardDef := OGN_295.meta

-- BEGIN GENERATED OGN-296
/--
**Void Gate** — Battlefield · Colorless
Printings: OGN-296/298

> Spells and abilities affecting units here each deal 1 Bonus Damage. (Each instance of damage
> the spell deals is increased by 1.)
-/
def OGN_296.meta : CardDef :=
  { id := ⟨"OGN-296"⟩,
    name := "Void Gate",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Void Gate: the effect is not written yet. -/
def OGN_296 : CardDef := OGN_296.meta

-- BEGIN GENERATED OGN-297
/--
**Windswept Hillock** — Battlefield · Colorless
Printings: OGN-297/298

> Units here have [Ganking]. (They can move from battlefield to battlefield.)
-/
def OGN_297.meta : CardDef :=
  { id := ⟨"OGN-297"⟩,
    name := "Windswept Hillock",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Windswept Hillock. -/
def OGN_297 : CardDef :=
  { OGN_297.meta with
    abilities := [.passive .always
      [.keyword (Selector.all .any .here [.ofType .unit]) ⟨.ganking, .none⟩]],
    status := .drafted }

-- BEGIN GENERATED OGN-298
/--
**Zaun Warrens** — Battlefield · Colorless
Printings: OGN-298/298

> When you conquer here, discard 1, then draw 1.
-/
def OGN_298.meta : CardDef :=
  { id := ⟨"OGN-298"⟩,
    name := "Zaun Warrens",
    types := [.battlefield],
    sets := [⟨"OGN"⟩] }
-- END GENERATED

/-- Zaun Warrens. -/
def OGN_298 : CardDef :=
  { OGN_298.meta with
    abilities := [.triggered (.onSelf .youConquer)
      (.of [] (.seqOf [.prim (.discard .you (.const 1)), .prim (.draw .you (.const 1))])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED LIST
/-- The cards first printed in Origins. -/
def cards : List CardDef :=
  [OGN_001,
    OGN_002,
    OGN_003,
    OGN_004,
    OGN_005,
    OGN_006,
    OGN_007,
    OGN_008,
    OGN_009,
    OGN_010,
    OGN_011,
    OGN_012,
    OGN_013,
    OGN_014,
    OGN_015,
    OGN_016,
    OGN_017,
    OGN_018,
    OGN_019,
    OGN_020,
    OGN_021,
    OGN_022,
    OGN_023,
    OGN_024,
    OGN_025,
    OGN_026,
    OGN_027,
    OGN_028,
    OGN_029,
    OGN_030,
    OGN_031,
    OGN_032,
    OGN_033,
    OGN_034,
    OGN_035,
    OGN_036,
    OGN_037,
    OGN_038,
    OGN_039,
    OGN_040,
    OGN_041,
    OGN_042,
    OGN_043,
    OGN_044,
    OGN_045,
    OGN_046,
    OGN_047,
    OGN_048,
    OGN_049,
    OGN_050,
    OGN_051,
    OGN_052,
    OGN_053,
    OGN_054,
    OGN_055,
    OGN_056,
    OGN_057,
    OGN_058,
    OGN_059,
    OGN_060,
    OGN_061,
    OGN_062,
    OGN_063,
    OGN_064,
    OGN_065,
    OGN_066,
    OGN_067,
    OGN_068,
    OGN_069,
    OGN_070,
    OGN_071,
    OGN_072,
    OGN_073,
    OGN_074,
    OGN_075,
    OGN_076,
    OGN_077,
    OGN_078,
    OGN_079,
    OGN_080,
    OGN_081,
    OGN_082,
    OGN_083,
    OGN_084,
    OGN_085,
    OGN_086,
    OGN_087,
    OGN_088,
    OGN_089,
    OGN_090,
    OGN_091,
    OGN_092,
    OGN_093,
    OGN_094,
    OGN_095,
    OGN_096,
    OGN_097,
    OGN_098,
    OGN_099,
    OGN_100,
    OGN_101,
    OGN_102,
    OGN_103,
    OGN_104,
    OGN_105,
    OGN_106,
    OGN_107,
    OGN_108,
    OGN_109,
    OGN_110,
    OGN_111,
    OGN_112,
    OGN_113,
    OGN_114,
    OGN_115,
    OGN_116,
    OGN_117,
    OGN_118,
    OGN_119,
    OGN_120,
    OGN_121,
    OGN_122,
    OGN_123,
    OGN_124,
    OGN_125,
    OGN_126,
    OGN_127,
    OGN_128,
    OGN_129,
    OGN_130,
    OGN_131,
    OGN_132,
    OGN_133,
    OGN_134,
    OGN_135,
    OGN_136,
    OGN_137,
    OGN_138,
    OGN_139,
    OGN_140,
    OGN_141,
    OGN_142,
    OGN_143,
    OGN_144,
    OGN_145,
    OGN_146,
    OGN_147,
    OGN_148,
    OGN_149,
    OGN_150,
    OGN_151,
    OGN_152,
    OGN_153,
    OGN_154,
    OGN_155,
    OGN_156,
    OGN_157,
    OGN_158,
    OGN_159,
    OGN_160,
    OGN_161,
    OGN_162,
    OGN_163,
    OGN_164,
    OGN_165,
    OGN_166,
    OGN_167,
    OGN_168,
    OGN_169,
    OGN_170,
    OGN_171,
    OGN_172,
    OGN_173,
    OGN_174,
    OGN_175,
    OGN_176,
    OGN_177,
    OGN_178,
    OGN_179,
    OGN_180,
    OGN_181,
    OGN_182,
    OGN_183,
    OGN_184,
    OGN_185,
    OGN_186,
    OGN_187,
    OGN_188,
    OGN_189,
    OGN_190,
    OGN_191,
    OGN_192,
    OGN_193,
    OGN_194,
    OGN_195,
    OGN_196,
    OGN_197,
    OGN_198,
    OGN_199,
    OGN_200,
    OGN_201,
    OGN_202,
    OGN_203,
    OGN_204,
    OGN_205,
    OGN_206,
    OGN_207,
    OGN_208,
    OGN_209,
    OGN_210,
    OGN_211,
    OGN_212,
    OGN_213,
    OGN_214,
    OGN_215,
    OGN_216,
    OGN_217,
    OGN_218,
    OGN_219,
    OGN_220,
    OGN_221,
    OGN_222,
    OGN_223,
    OGN_224,
    OGN_225,
    OGN_226,
    OGN_227,
    OGN_228,
    OGN_229,
    OGN_230,
    OGN_231,
    OGN_232,
    OGN_233,
    OGN_234,
    OGN_235,
    OGN_236,
    OGN_237,
    OGN_238,
    OGN_239,
    OGN_240,
    OGN_241,
    OGN_242,
    OGN_243,
    OGN_244,
    OGN_245,
    OGN_246,
    OGN_247,
    OGN_248,
    OGN_249,
    OGN_250,
    OGN_251,
    OGN_252,
    OGN_253,
    OGN_254,
    OGN_255,
    OGN_256,
    OGN_257,
    OGN_258,
    OGN_259,
    OGN_260,
    OGN_261,
    OGN_262,
    OGN_263,
    OGN_264,
    OGN_265,
    OGN_266,
    OGN_267,
    OGN_268,
    OGN_269,
    OGN_270,
    OGN_271,
    OGN_272,
    OGN_273,
    OGN_274,
    OGN_275,
    OGN_276,
    OGN_277,
    OGN_278,
    OGN_279,
    OGN_280,
    OGN_281,
    OGN_282,
    OGN_283,
    OGN_284,
    OGN_285,
    OGN_286,
    OGN_287,
    OGN_288,
    OGN_289,
    OGN_290,
    OGN_291,
    OGN_292,
    OGN_293,
    OGN_294,
    OGN_295,
    OGN_296,
    OGN_297,
    OGN_298]
-- END GENERATED LIST

end RiftboundCards.Origins

end
