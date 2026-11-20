module

public import Riftbound.Card.CardDef

/-!
# Proving Grounds (OGS)

The cards first printed in Proving Grounds. Each card has a generated block (the official text and
the metadata) and, right after it, the part written by hand (the effect and the
implementation status). `scripts/gen_lean.py` rewrites the generated blocks only
(docs/card-data.md §4.1).
-/

@[expose] public section

namespace RiftboundCards.ProvingGrounds

open Riftbound

-- BEGIN GENERATED OGS-001
/--
**Annie, Fiery** — Unit · Fury · Energy 5 + Power 1 · Might 4
Printings: OGS-001/024

> Your spells and abilities deal 1 Bonus Damage. (Each instance of damage they deal is increased
> by 1.)
-/
def OGS_001.meta : CardDef :=
  { id := ⟨"OGS-001"⟩,
    name := "Annie",
    subtitle := some "Fiery",
    types := [.unit],
    tags := [⟨"Annie"⟩, ⟨"Noxus"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 4,
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Annie, Fiery. -/
def OGS_001 : CardDef :=
  { OGS_001.meta with
    abilities := [.passive .always [.bonusDamage (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED OGS-002
/--
**Firestorm** — Spell · Fury · Energy 6 + Power 1
Printings: OGS-002/024

> Deal 3 to all enemy units at a battlefield.
-/
def OGS_002.meta : CardDef :=
  { id := ⟨"OGS-002"⟩,
    name := "Firestorm",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨6, [.domain .fury]⟩,
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/--
Firestorm.
Reading: a Battlefield is chosen when the card is played, and every enemy unit there is
dealt 3.
-/
def OGS_002 : CardDef :=
  { OGS_002.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .battlefield]]
    (.prim (.deal (.all .enemy .atBattlefield [.ofType .unit, .at_ (.slot 0)]) (.const 3)))),
    status := .drafted }

-- BEGIN GENERATED OGS-003
/--
**Incinerate** — Spell · Fury · Energy 2
Printings: OGS-003/024

> [Action] (Play on your turn or in showdowns.)
> Deal 2 to a unit at a battlefield.
-/
def OGS_003.meta : CardDef :=
  { id := ⟨"OGS-003"⟩,
    name := "Incinerate",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Incinerate. -/
def OGS_003 : CardDef :=
  { OGS_003.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
    (.prim (.deal (.slot 0) (.const 2)))),
    status := .drafted }

-- BEGIN GENERATED OGS-004
/--
**Master Yi, Meditative** — Unit · Calm · Energy 5 + Power 1 · Might 4
Printings: OGS-004/024

> While you have 8+ runes, I have +4 :rb_might:.
-/
def OGS_004.meta : CardDef :=
  { id := ⟨"OGS-004"⟩,
    name := "Master Yi",
    subtitle := some "Meditative",
    types := [.unit],
    tags := [⟨"Master Yi"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 4,
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Master Yi, Meditative. -/
def OGS_004 : CardDef :=
  { OGS_004.meta with
    abilities := [.passive
      (.cmp .ge (.count (.all .friendly .anywhere [.ofType .rune])) (.const 8))
      [.mightPlus .self (.const 4)]],
    status := .drafted }

-- BEGIN GENERATED OGS-005
/--
**Zephyr Sage** — Unit · Calm · Energy 6 + Power 1 · Might 6
Printings: OGS-005/024

> [Shield] (+1 :rb_might: while I'm a defender.)
-/
def OGS_005.meta : CardDef :=
  { id := ⟨"OGS-005"⟩,
    name := "Zephyr Sage",
    types := [.unit],
    tags := [⟨"Ionia"⟩, ⟨"Bird"⟩],
    domains := [.calm],
    cost := some ⟨6, [.domain .calm]⟩,
    might := some 6,
    keywords := [{ keyword := .shield, arg := .amount 1 }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Zephyr Sage. -/
def OGS_005 : CardDef :=
  { OGS_005.meta with
    status := .drafted }

-- BEGIN GENERATED OGS-006
/--
**Lux, Illuminated** — Unit · Mind · Energy 6 + Power 1 · Might 5
Printings: OGS-006/024

> When you play a spell that costs :rb_energy_5: or more, give me +3 :rb_might: this turn.
-/
def OGS_006.meta : CardDef :=
  { id := ⟨"OGS-006"⟩,
    name := "Lux",
    subtitle := some "Illuminated",
    types := [.unit],
    tags := [⟨"Lux"⟩, ⟨"Demacia"⟩],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind]⟩,
    might := some 5,
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Lux, Illuminated. -/
def OGS_006 : CardDef :=
  { OGS_006.meta with
    abilities := [.triggered
      { event := .play, subject := .all .friendly .anywhere [.ofType .spell, .cost .ge (.const 5)] }
      (.of [] (.grant .self (.mightPlus .it (.const 3)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGS-007
/--
**Garen, Rugged** — Unit · Body · Energy 6 + Power 1 · Might 5
Printings: OGS-007/024

> [Assault 2], [Shield 2] (+2 :rb_might: while I'm an attacker or defender.)
-/
def OGS_007.meta : CardDef :=
  { id := ⟨"OGS-007"⟩,
    name := "Garen",
    subtitle := some "Rugged",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Garen"⟩, ⟨"Demacia"⟩],
    domains := [.body],
    cost := some ⟨6, [.domain .body]⟩,
    might := some 5,
    keywords := [{ keyword := .assault, arg := .amount 2 },
      { keyword := .shield, arg := .amount 2 }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Garen, Rugged. -/
def OGS_007 : CardDef :=
  { OGS_007.meta with
    status := .drafted }

-- BEGIN GENERATED OGS-008
/--
**Gentlemen's Duel** — Spell · Body · Energy 6 + Power 1
Printings: OGS-008/024

> [Action] (Play on your turn or in showdowns.)
> Give a friendly unit +3 :rb_might: this turn. Then choose an enemy unit. They deal damage
> equal to their Mights to each other.
-/
def OGS_008.meta : CardDef :=
  { id := ⟨"OGS-008"⟩,
    name := "Gentlemen's Duel",
    types := [.spell],
    domains := [.body],
    cost := some ⟨6, [.domain .body]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/--
Gentlemen's Duel.
The two amounts are bound before either unit is dealt damage, so the exchange is
simultaneous.
-/
def OGS_008 : CardDef :=
  { OGS_008.meta with
    spellEffect := some (.of
    [.targetOf .one .friendly .anywhere [.ofType .unit],
     .targetOf .one .enemy .anywhere [.ofType .unit]]
    (.seqOf [
      .grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn,
      .bind ⟨"mine"⟩ (.mightOf (.slot 0))
        (.bind ⟨"theirs"⟩ (.mightOf (.slot 1))
          (.seqOf [.prim (.deal (.slot 1) (.var ⟨"mine"⟩)),
                   .prim (.deal (.slot 0) (.var ⟨"theirs"⟩))]))])),
    status := .drafted }

-- BEGIN GENERATED OGS-009
/--
**Master Yi, Honed** — Unit · Body · Energy 7 + Power 1 · Might 6
Printings: OGS-009/024

> [Ganking] (I can move from battlefield to battlefield.)
> I enter ready.
-/
def OGS_009.meta : CardDef :=
  { id := ⟨"OGS-009"⟩,
    name := "Master Yi",
    subtitle := some "Honed",
    types := [.unit],
    tags := [⟨"Master Yi"⟩, ⟨"Ionia"⟩],
    domains := [.body],
    cost := some ⟨7, [.domain .body]⟩,
    might := some 6,
    keywords := [{ keyword := .ganking }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Master Yi, Honed. -/
def OGS_009 : CardDef :=
  { OGS_009.meta with
    abilities := [.passive .always [.entersReady .self]],
    status := .drafted }

-- BEGIN GENERATED OGS-010
/--
**Annie, Stubborn** — Unit · Chaos · Energy 4 + Power 1 · Might 3
Printings: OGS-010/024

> When you play me, return a spell from your trash to your hand.
-/
def OGS_010.meta : CardDef :=
  { id := ⟨"OGS-010"⟩,
    name := "Annie",
    subtitle := some "Stubborn",
    types := [.unit],
    tags := [⟨"Annie"⟩, ⟨"Noxus"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    might := some 3,
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Annie, Stubborn. -/
def OGS_010 : CardDef :=
  { OGS_010.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.prim (.returnToHand (.one .friendly .inTrash [.ofType .spell])))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGS-011
/--
**Flash** — Spell · Chaos · Energy 2
Printings: OGS-011/024

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Move up to 2 friendly units to base.
-/
def OGS_011.meta : CardDef :=
  { id := ⟨"OGS-011"⟩,
    name := "Flash",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Flash. -/
def OGS_011 : CardDef :=
  { OGS_011.meta with
    spellEffect := some (.of [.targetOf (.upTo 2) .friendly .anywhere [.ofType .unit]]
    (.prim (.move (.slot 0) .base))),
    status := .drafted }

-- BEGIN GENERATED OGS-012
/--
**Blast of Power** — Spell · Order · Energy 6 + Power 1
Printings: OGS-012/024

> [Action] (Play on your turn or in showdowns.)
> Kill a unit at a battlefield.
-/
def OGS_012.meta : CardDef :=
  { id := ⟨"OGS-012"⟩,
    name := "Blast of Power",
    types := [.spell],
    domains := [.order],
    cost := some ⟨6, [.domain .order]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Blast of Power. -/
def OGS_012 : CardDef :=
  { OGS_012.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
    (.prim (.kill (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED OGS-013
/--
**Garen, Commander** — Unit · Order · Energy 6 + Power 1 · Might 5
Printings: OGS-013/024

> Other friendly units have +1 :rb_might: here.
-/
def OGS_013.meta : CardDef :=
  { id := ⟨"OGS-013"⟩,
    name := "Garen",
    subtitle := some "Commander",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Garen"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order]⟩,
    might := some 5,
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Garen, Commander. -/
def OGS_013 : CardDef :=
  { OGS_013.meta with
    abilities := [.passive .always
      [.mightPlus (.all .friendly .here [.ofType .unit, .notSelf]) (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED OGS-014
/--
**Lux, Crownguard** — Unit · Order · Energy 4 · Might 2
Printings: OGS-014/024, VEN-SP6/006

> :rb_exhaust:: [Reaction] — [Add] :rb_energy_2:. Use only to play spells. (Abilities that add
> resources can't be reacted to.)
-/
def OGS_014.meta : CardDef :=
  { id := ⟨"OGS-014"⟩,
    name := "Lux",
    subtitle := some "Crownguard",
    types := [.unit],
    tags := [⟨"Lux"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 2,
    sets := [⟨"OGS"⟩, ⟨"VEN"⟩] }
-- END GENERATED

/-- Lux, Crownguard. -/
def OGS_014 : CardDef :=
  { OGS_014.meta with
    abilities := [.activated [.exhaustSelf] .reaction
      (.of [] (.prim (.addEnergy .you (.const 2) (some .play)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGS-015
/--
**Recruit the Vanguard** — Spell · Order · Energy 6
Printings: OGS-015/024

> [Action] (Play on your turn or in showdowns.)
> Play four 1 :rb_might: Recruit unit tokens. (They can be played to your base or to
> battlefields you control.)
-/
def OGS_015.meta : CardDef :=
  { id := ⟨"OGS-015"⟩,
    name := "Recruit the Vanguard",
    types := [.spell],
    domains := [.order],
    cost := some ⟨6, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/--
Recruit the Vanguard.
Not written: the Recruit token needs a definition (name, type, Might), and the tokens are
played to a place chosen then (docs/ir-gaps.md).
-/
def OGS_015 : CardDef :=
  { OGS_015.meta with
    status := .todo }

-- BEGIN GENERATED OGS-016
/--
**Vanguard Attendant** — Unit · Order · Energy 6 + Power 1 · Might 5
Printings: OGS-016/024

> I enter ready.
-/
def OGS_016.meta : CardDef :=
  { id := ⟨"OGS-016"⟩,
    name := "Vanguard Attendant",
    types := [.unit],
    tags := [⟨"Elite"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order]⟩,
    might := some 5,
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Vanguard Attendant. -/
def OGS_016 : CardDef :=
  { OGS_016.meta with
    abilities := [.passive .always [.entersReady .self]],
    status := .drafted }

-- BEGIN GENERATED OGS-017
/--
**Dark Child, Starter** — Legend · Fury/Chaos
Printings: OGS-017/024

> At the end of your turn, ready 2 runes.
-/
def OGS_017.meta : CardDef :=
  { id := ⟨"OGS-017"⟩,
    name := "Dark Child",
    subtitle := some "Starter",
    types := [.legend],
    tags := [⟨"Annie"⟩],
    domains := [.fury, .chaos],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Dark Child, Starter. -/
def OGS_017 : CardDef :=
  { OGS_017.meta with
    abilities := [.triggered { event := .at_ .endOfTurn, condition := .yourTurn }
      (.of [] (.prim (.ready (.pick (.exactly 2) .friendly .anywhere
        (FilterList.ofList [.ofType .rune]))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGS-018
/--
**Tibbers, Annie** — Unit · Fury/Chaos · Energy 8 + Power 2 · Might 7
Printings: OGS-018/024

> When you play me, deal 3 to all units at battlefields.
-/
def OGS_018.meta : CardDef :=
  { id := ⟨"OGS-018"⟩,
    name := "Tibbers",
    subtitle := some "Annie",
    types := [.unit],
    tags := [⟨"Annie"⟩],
    domains := [.fury, .chaos],
    cost := some ⟨8, [.any, .any]⟩,
    might := some 7,
    sets := [⟨"OGS"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Tibbers, Annie. -/
def OGS_018 : CardDef :=
  { OGS_018.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.prim (.deal (.all .any .atBattlefield [.ofType .unit]) (.const 3)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGS-019
/--
**Wuju Bladesman, Starter** — Legend · Calm/Body
Printings: OGS-019/024

> While a friendly unit defends alone, it gets +2 :rb_might:.
-/
def OGS_019.meta : CardDef :=
  { id := ⟨"OGS-019"⟩,
    name := "Wuju Bladesman",
    subtitle := some "Starter",
    types := [.legend],
    tags := [⟨"Master Yi"⟩],
    domains := [.calm, .body],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Wuju Bladesman, Starter. -/
def OGS_019 : CardDef :=
  { OGS_019.meta with
    abilities := [.passive .always
      [.mightPlus (.all .friendly .anywhere [.ofType .unit, .defender, .alone]) (.const 2)]],
    status := .drafted }

-- BEGIN GENERATED OGS-020
/--
**Highlander, Yi** — Spell · Calm/Body · Energy 4
Printings: OGS-020/024

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a friendly unit. The next time it dies this turn, recall it exhausted instead. (Send it
> to base. This isn't a move.)
-/
def OGS_020.meta : CardDef :=
  { id := ⟨"OGS-020"⟩,
    name := "Highlander",
    subtitle := some "Yi",
    types := [.spell],
    tags := [⟨"Master Yi"⟩],
    domains := [.calm, .body],
    cost := some ⟨4, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Highlander, Yi. -/
def OGS_020 : CardDef :=
  { OGS_020.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
    (.replaceNext .die (.slot 0) (.prim (.recall (.slot 0) true)) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED OGS-021
/--
**Lady of Luminosity, Starter** — Legend · Mind/Order
Printings: OGS-021/024

> When you play a spell that costs :rb_energy_5: or more, draw 1.
-/
def OGS_021.meta : CardDef :=
  { id := ⟨"OGS-021"⟩,
    name := "Lady of Luminosity",
    subtitle := some "Starter",
    types := [.legend],
    tags := [⟨"Lux"⟩],
    domains := [.mind, .order],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Lady of Luminosity, Starter. -/
def OGS_021 : CardDef :=
  { OGS_021.meta with
    abilities := [.triggered
      { event := .play, subject := .all .friendly .anywhere [.ofType .spell, .cost .ge (.const 5)] }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGS-022
/--
**Final Spark, Lux** — Spell · Mind/Order · Energy 8
Printings: OGS-022/024

> [Action] (Play on your turn or in showdowns.)
> Deal 8 to a unit.
-/
def OGS_022.meta : CardDef :=
  { id := ⟨"OGS-022"⟩,
    name := "Final Spark",
    subtitle := some "Lux",
    types := [.spell],
    tags := [⟨"Lux"⟩],
    domains := [.mind, .order],
    cost := some ⟨8, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Final Spark, Lux. -/
def OGS_022 : CardDef :=
  { OGS_022.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
    (.prim (.deal (.slot 0) (.const 8)))),
    status := .drafted }

-- BEGIN GENERATED OGS-023
/--
**Might of Demacia, Starter** — Legend · Body/Order
Printings: OGS-023/024

> When you conquer, if you have 4+ units at that battlefield, draw 2.
-/
def OGS_023.meta : CardDef :=
  { id := ⟨"OGS-023"⟩,
    name := "Might of Demacia",
    subtitle := some "Starter",
    types := [.legend],
    tags := [⟨"Garen"⟩],
    domains := [.body, .order],
    sets := [⟨"OGS"⟩] }
-- END GENERATED

/-- Might of Demacia, Starter. -/
def OGS_023 : CardDef :=
  { OGS_023.meta with
    abilities := [.triggered
      { event := .youConquer,
        condition := .cmp .ge (.count (.all .friendly .here [.ofType .unit])) (.const 4) }
      (.of [] (.prim (.draw .you (.const 2)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED OGS-024
/--
**Decisive Strike, Garen** — Spell · Body/Order · Energy 5 + Power 1
Printings: OGS-024/024

> [Action] (Play on your turn or in showdowns.)
> Give friendly units +2 :rb_might: this turn.
-/
def OGS_024.meta : CardDef :=
  { id := ⟨"OGS-024"⟩,
    name := "Decisive Strike",
    subtitle := some "Garen",
    types := [.spell],
    tags := [⟨"Garen"⟩],
    domains := [.body, .order],
    cost := some ⟨5, [.any]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"OGS"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Decisive Strike, Garen. -/
def OGS_024 : CardDef :=
  { OGS_024.meta with
    spellEffect := some (.of []
    (.grant (.all .friendly .anywhere [.ofType .unit]) (.mightPlus .it (.const 2)) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED LIST
/-- The cards first printed in Proving Grounds. -/
def cards : List CardDef :=
  [OGS_001,
    OGS_002,
    OGS_003,
    OGS_004,
    OGS_005,
    OGS_006,
    OGS_007,
    OGS_008,
    OGS_009,
    OGS_010,
    OGS_011,
    OGS_012,
    OGS_013,
    OGS_014,
    OGS_015,
    OGS_016,
    OGS_017,
    OGS_018,
    OGS_019,
    OGS_020,
    OGS_021,
    OGS_022,
    OGS_023,
    OGS_024]
-- END GENERATED LIST

end RiftboundCards.ProvingGrounds

end
