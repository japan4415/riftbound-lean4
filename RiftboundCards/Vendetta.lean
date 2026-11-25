module

public import Riftbound.Card.CardDef

/-!
# Vendetta (VEN)

The cards first printed in Vendetta. Each card has a generated block (the official text and
the metadata) and, right after it, the part written by hand (the effect and the
implementation status). `scripts/gen_lean.py` rewrites the generated blocks only
(docs/card-data.md §4.1).
-/

@[expose] public section

namespace RiftboundCards.Vendetta

open Riftbound

-- BEGIN GENERATED VEN-001
/--
**Baccai Sandspinner** — Unit · Fury · Energy 6 · Might 6
Printings: VEN-001/166

> [Empower] :rb_energy_5:. This ability costs :rb_energy_3: less if you control 4 or fewer
> runes. (Pay the cost: Empower me. Use only if not Empowered.)
> [Empowered][>] I have [Deflect] and [Assault 2]. (Opponents must pay :rb_rune_rainbow: to
> choose me with a spell or ability. +2 :rb_might: while I'm an attacker.)
-/
def VEN_001.meta : CardDef :=
  { id := ⟨"VEN-001"⟩,
    name := "Baccai Sandspinner",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.fury],
    cost := some ⟨6, []⟩,
    might := some 6,
    keywords := [{ keyword := .empower, arg := .cost ⟨5, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Baccai Sandspinner. -/
def VEN_001 : CardDef :=
  { VEN_001.meta with
    abilities := [.empower [.pay ⟨5, []⟩,
        .energyDiscount (.cmp .le (.count (.all .friendly .anywhere [.ofType .rune])) (.const 4))
          (.const 3)],
      .passive (.empowered .self)
        [.keyword .self ⟨.deflect, .none⟩, .keyword .self ⟨.assault, .amount 2⟩]],
    status := .drafted }

-- BEGIN GENERATED VEN-002
/--
**Blade Twirler** — Unit · Fury · Energy 4 · Might 4
Printings: VEN-002/166

> The first time I move each turn, choose a player. They [Burn 1]. (They put the top card of
> their Main Deck into their trash.)
-/
def VEN_002.meta : CardDef :=
  { id := ⟨"VEN-002"⟩,
    name := "Blade Twirler",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Ionia"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Blade Twirler: the effect is not written yet. -/
def VEN_002 : CardDef := VEN_002.meta

-- BEGIN GENERATED VEN-003
/--
**Brittle Steel** — Spell · Fury · Energy 2 + Power 1
Printings: VEN-003/166

> Kill a gear.
> [Flow] :rb_energy_4::rb_rune_fury: (You may play this from your trash for its Flow cost. Then
> banish it.)
-/
def VEN_003.meta : CardDef :=
  { id := ⟨"VEN-003"⟩,
    name := "Brittle Steel",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, [.domain .fury]⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨4, [.domain .fury]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Brittle Steel. -/
def VEN_003 : CardDef :=
  { VEN_003.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .gear]] (.prim (.kill (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED VEN-004
/--
**Dune Surfer** — Unit · Fury · Energy 3 · Might 3
Printings: VEN-004/166

> You ignore [Tank] while assigning combat damage here.
-/
def VEN_004.meta : CardDef :=
  { id := ⟨"VEN-004"⟩,
    name := "Dune Surfer",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Dune Surfer. -/
def VEN_004 : CardDef :=
  { VEN_004.meta with
    abilities := [.passive .always [.ignoreKeyword .tank .here]],
    status := .drafted }

-- BEGIN GENERATED VEN-005
/--
**Forsaken Baccai** — Unit · Fury · Energy 2 · Might 2
Printings: VEN-005/166

> If you control fewer runes than an opponent at the start of your Beginning Phase, give me +1
> :rb_might: this turn.
-/
def VEN_005.meta : CardDef :=
  { id := ⟨"VEN-005"⟩,
    name := "Forsaken Baccai",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Forsaken Baccai. -/
def VEN_005 : CardDef :=
  { VEN_005.meta with
    abilities := [.triggered
      { event := .at_ .beginning,
        condition := .cmp .lt (.count (.all .friendly .anywhere [.ofType .rune]))
          (.count (.all .enemy .anywhere [.ofType .rune])) }
      (.of [] (.grant .self (.mightPlus .it (.const 1)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-006
/--
**Oasis Raider** — Unit · Fury · Energy 4 · Might 4
Printings: VEN-006/166

> If you control fewer runes than an opponent at the start of your Beginning Phase, give me +2
> :rb_might: and [Ganking] this turn. (I can move from battlefield to battlefield.)
-/
def VEN_006.meta : CardDef :=
  { id := ⟨"VEN-006"⟩,
    name := "Oasis Raider",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Oasis Raider. -/
def VEN_006 : CardDef :=
  { VEN_006.meta with
    abilities := [.triggered
      { event := .at_ .beginning,
        condition := .cmp .lt (.count (.all .friendly .anywhere [.ofType .rune]))
          (.count (.all .enemy .anywhere [.ofType .rune])) }
      (.of [] (.seqOf [.grant .self (.mightPlus .it (.const 2)) .thisTurn,
        .grant .self (.keyword .it ⟨.ganking, .none⟩) .thisTurn])) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-007
/--
**Punching Poro** — Unit · Fury · Energy 2 · Might 2
Printings: VEN-007/166

> [Empower] — Discard 1 (Pay the cost: Empower me. Use only if not Empowered.)
> [Empowered][>] I have +1 :rb_might:.
-/
def VEN_007.meta : CardDef :=
  { id := ⟨"VEN-007"⟩,
    name := "Punching Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩, ⟨"Ionia"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .empower }],
    sets := [⟨"VEN"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Punching Poro: the effect is not written yet. -/
def VEN_007 : CardDef := VEN_007.meta

-- BEGIN GENERATED VEN-008
/--
**Ruthless Strike** — Spell · Fury · Energy 3
Printings: VEN-008/166

> [Action] (Play on your turn or in showdowns.)
> As an additional cost to play this, you may discard 1.
> Deal 3 to a unit at a battlefield. If you paid the additional cost, deal 5 to it instead.
-/
def VEN_008.meta : CardDef :=
  { id := ⟨"VEN-008"⟩,
    name := "Ruthless Strike",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Ruthless Strike: the effect is not written yet. -/
def VEN_008 : CardDef := VEN_008.meta

-- BEGIN GENERATED VEN-009
/--
**Baccai Reaper** — Unit · Fury · Energy 3 + Power 1 · Might 4
Printings: VEN-009/166

> When I attack, you may pay :rb_rune_fury: to give me [Assault 2] this turn. (+2 :rb_might:
> while I'm an attacker.)
-/
def VEN_009.meta : CardDef :=
  { id := ⟨"VEN-009"⟩,
    name := "Baccai Reaper",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Baccai Reaper. -/
def VEN_009 : CardDef :=
  { VEN_009.meta with
    abilities := [.triggered (.onSelf .attack)
      (.of [] (.ifThen (.canPay ⟨0, [.domain .fury]⟩)
        (.may (.seqOf [.prim (.pay ⟨0, [.domain .fury]⟩),
          .grant .self (.keyword .it ⟨.assault, .amount 2⟩) .thisTurn])) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-010
/--
**Consuming Curse** — Spell · Fury · Energy 2
Printings: VEN-010/166

> [Action] (Play on your turn or in showdowns.)
> Deal 2 to a unit at a battlefield. This deals 1 Bonus Damage for each card with this name in
> your trash.
-/
def VEN_010.meta : CardDef :=
  { id := ⟨"VEN-010"⟩,
    name := "Consuming Curse",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Consuming Curse. -/
def VEN_010 : CardDef :=
  { VEN_010.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.prim (.deal (.slot 0) (.add (.const 2)
        (.count (.all .friendly .inTrash [.named "Consuming Curse"])))))),
    status := .drafted }

-- BEGIN GENERATED VEN-011
/--
**Pendulum Blade** — Gear · Fury · Energy 3 · Might 1
Printings: VEN-011/166

> [Equip] :rb_rune_fury: (:rb_rune_fury:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> When I move to a battlefield, give me +2 :rb_might: this turn.
-/
def VEN_011.meta : CardDef :=
  { id := ⟨"VEN-011"⟩,
    name := "Pendulum Blade",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .fury]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Pendulum Blade. -/
def VEN_011 : CardDef :=
  { VEN_011.meta with
    grants := [.triggered { event := .move, condition := .matches .self .onBattlefield }
      (.of [] (.grant .self (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-012
/--
**Perfect Execution** — Spell · Fury · Energy 3 + Power 1
Printings: VEN-012/166

> Ready a unit and give it [Assault 3] this turn. (+3 :rb_might: while it's an attacker.)
> [Flow] :rb_energy_3::rb_rune_fury: (You may play this from your trash for its Flow cost. Then
> banish it.)
-/
def VEN_012.meta : CardDef :=
  { id := ⟨"VEN-012"⟩,
    name := "Perfect Execution",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨3, [.domain .fury]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Perfect Execution. -/
def VEN_012 : CardDef :=
  { VEN_012.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.prim (.ready (.slot 0)),
        .grant (.slot 0) (.keyword .it ⟨.assault, .amount 3⟩) .thisTurn])),
    status := .drafted }

-- BEGIN GENERATED VEN-013
/--
**Shadow Assassin** — Unit · Fury · Energy 5 · Might 5
Printings: VEN-013/166

> I enter ready if you have a card with my name in your trash.
-/
def VEN_013.meta : CardDef :=
  { id := ⟨"VEN-013"⟩,
    name := "Shadow Assassin",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.fury],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shadow Assassin. -/
def VEN_013 : CardDef :=
  { VEN_013.meta with
    abilities := [.passive (.cmp .ge
        (.count (.all .friendly .inTrash [.named "Shadow Assassin"])) (.const 1))
      [.entersReady .self]],
    status := .drafted }

-- BEGIN GENERATED VEN-014
/--
**Shadow Fiend** — Unit · Fury · Energy 2 · Might 2
Printings: VEN-014/166

> [Empower] :rb_energy_2::rb_rune_fury: (:rb_energy_2::rb_rune_fury:: Empower me. Use only if
> not Empowered.)
> [Empowered][>] I have [Assault 3]. (+3 :rb_might: while I'm an attacker.)
-/
def VEN_014.meta : CardDef :=
  { id := ⟨"VEN-014"⟩,
    name := "Shadow Fiend",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .empower, arg := .cost ⟨2, [.domain .fury]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shadow Fiend. -/
def VEN_014 : CardDef :=
  { VEN_014.meta with
    abilities := [.passive (.empowered .self) [.keyword .self ⟨.assault, .amount 3⟩]],
    status := .drafted }

-- BEGIN GENERATED VEN-015
/--
**Decree of Rage** — Spell · Fury · Energy 1 + Power 1
Printings: VEN-015/166

> [Action] (Play on your turn or in showdowns.)
> This can't be countered.
> Deal 4 to an enemy Calm (:rb_rune_calm:) unit.
-/
def VEN_015.meta : CardDef :=
  { id := ⟨"VEN-015"⟩,
    name := "Decree of Rage",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨1, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Decree of Rage: the effect is not written yet. -/
def VEN_015 : CardDef := VEN_015.meta

-- BEGIN GENERATED VEN-016
/--
**Eclipse Dragon** — Unit · Fury · Energy 8 · Might 8
Printings: VEN-016/166

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> When I move, if you control 4 or fewer runes, draw 1.
-/
def VEN_016.meta : CardDef :=
  { id := ⟨"VEN-016"⟩,
    name := "Eclipse Dragon",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Mount Targon"⟩],
    domains := [.fury],
    cost := some ⟨8, []⟩,
    might := some 8,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Eclipse Dragon. -/
def VEN_016 : CardDef :=
  { VEN_016.meta with
    abilities := [.triggered
      { event := .move,
        condition := .cmp .le (.count (.all .friendly .anywhere [.ofType .rune])) (.const 4) }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-017
/--
**Morgana, Vindictive** — Unit · Fury · Energy 5 + Power 1 · Might 5
Printings: VEN-017/166, VEN-186/166

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> When you play me, deal damage to a unit equal to the damage marked on it.
-/
def VEN_017.meta : CardDef :=
  { id := ⟨"VEN-017"⟩,
    name := "Morgana",
    subtitle := some "Vindictive",
    types := [.unit],
    tags := [⟨"Demacia"⟩, ⟨"Morgana"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 5,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Morgana, Vindictive: the effect is not written yet. -/
def VEN_017 : CardDef := VEN_017.meta

-- BEGIN GENERATED VEN-018
/--
**Rage Amplifier** — Gear · Fury · Energy 4 + Power 1
Printings: VEN-018/166

> [Empower] :rb_energy_6::rb_rune_fury: (:rb_energy_6::rb_rune_fury:: Empower this. Use only if
> not Empowered.)
> Your units have +1 :rb_might:. If I'm [Empowered], they have +2 :rb_might: instead.
-/
def VEN_018.meta : CardDef :=
  { id := ⟨"VEN-018"⟩,
    name := "Rage Amplifier",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    keywords := [{ keyword := .empower, arg := .cost ⟨6, [.domain .fury]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Rage Amplifier. -/
def VEN_018 : CardDef :=
  { VEN_018.meta with
    abilities := [.passive .always
      [.mightPlus (.all .friendly .anywhere [.ofType .unit]) (.const 1)],
      .passive (.empowered .self)
        [.mightPlus (.all .friendly .anywhere [.ofType .unit]) (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED VEN-019
/--
**Renekton, Rage Fueled** — Unit · Fury · Energy 6 · Might 6
Printings: VEN-019/166, VEN-019a/166

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> When I attack, if you control 4 or fewer runes, deal 2 to all enemy units here.
-/
def VEN_019.meta : CardDef :=
  { id := ⟨"VEN-019"⟩,
    name := "Renekton",
    subtitle := some "Rage Fueled",
    types := [.unit],
    tags := [⟨"Shurima"⟩, ⟨"Renekton"⟩],
    domains := [.fury],
    cost := some ⟨6, []⟩,
    might := some 6,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Renekton, Rage Fueled. -/
def VEN_019 : CardDef :=
  { VEN_019.meta with
    abilities := [.triggered
      { event := .attack,
        condition := .cmp .le (.count (.all .friendly .anywhere [.ofType .rune])) (.const 4) }
      (.of [] (.prim (.deal (.all .enemy .here [.ofType .unit]) (.const 2)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-020
/--
**Twilight Reveler** — Unit · Fury · Energy 3 · Might 3
Printings: VEN-020/166

> When I attack, ready another friendly unit.
-/
def VEN_020.meta : CardDef :=
  { id := ⟨"VEN-020"⟩,
    name := "Twilight Reveler",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Twilight Reveler. -/
def VEN_020 : CardDef :=
  { VEN_020.meta with
    abilities := [.triggered (.onSelf .attack)
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .notSelf]] (.prim (.ready (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-021
/--
**Akali, Deadly Weapon** — Unit · Fury · Energy 3 · Might 3
Printings: VEN-021/166, VEN-021a/166

> [Empower] :rb_energy_2::rb_rune_fury: (:rb_energy_2::rb_rune_fury:: Empower me. Use only if
> not Empowered.)
> When I move, you may deal 1 to a unit at a battlefield I moved to or from. If I'm [Empowered],
> deal 2 instead.
> [Empowered][>] I have +1 :rb_might:.
-/
def VEN_021.meta : CardDef :=
  { id := ⟨"VEN-021"⟩,
    name := "Akali",
    subtitle := some "Deadly Weapon",
    types := [.unit],
    tags := [⟨"Ionia"⟩, ⟨"Akali"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .empower, arg := .cost ⟨2, [.domain .fury]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Akali, Deadly Weapon: the effect is not written yet. -/
def VEN_021 : CardDef := VEN_021.meta

-- BEGIN GENERATED VEN-022
/--
**Endless Riches** — Gear · Fury · Energy 5 + Power 1
Printings: VEN-022/166

> When you play this, banish your hand and trash, then [Burn 7].
> Skip your Draw Phase.
> You may play cards from your trash.
> If a card would go to your trash from anywhere other than your Main Deck, banish it instead.
-/
def VEN_022.meta : CardDef :=
  { id := ⟨"VEN-022"⟩,
    name := "Endless Riches",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Endless Riches: the effect is not written yet. -/
def VEN_022 : CardDef := VEN_022.meta

-- BEGIN GENERATED VEN-023
/--
**Zed, From the Shadows** — Unit · Fury · Energy 4 + Power 1 · Might 4
Printings: VEN-023/166, VEN-023a/166, VEN-169/166

> You may discard 1 as an additional cost to play me.
> When you play me, if you paid the additional cost, play a 0 :rb_might: Shadow Clone unit
> token. (It has "When I attack, you may banish a unit from your trash. If you do, give me
> [Assault 4] this turn.")
-/
def VEN_023.meta : CardDef :=
  { id := ⟨"VEN-023"⟩,
    name := "Zed",
    subtitle := some "From the Shadows",
    types := [.unit],
    tags := [⟨"Ionia"⟩, ⟨"Zed"⟩],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Zed, From the Shadows: the effect is not written yet. -/
def VEN_023 : CardDef := VEN_023.meta

-- BEGIN GENERATED VEN-024
/--
**Affectionate Poro** — Unit · Calm · Energy 3 · Might 3
Printings: VEN-024/166

> When a combat that I was in ends, if I haven't been dealt damage this turn, draw 1.
-/
def VEN_024.meta : CardDef :=
  { id := ⟨"VEN-024"⟩,
    name := "Affectionate Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩, ⟨"Noxus"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Affectionate Poro: the effect is not written yet. -/
def VEN_024 : CardDef := VEN_024.meta

-- BEGIN GENERATED VEN-025
/--
**Esteemed Hierophant** — Unit · Calm · Energy 5 · Might 5
Printings: VEN-025/166

> While you control 7 or more runes, prevent all damage that enemy spells and abilities would
> deal to me.
-/
def VEN_025.meta : CardDef :=
  { id := ⟨"VEN-025"⟩,
    name := "Esteemed Hierophant",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Esteemed Hierophant: the effect is not written yet. -/
def VEN_025 : CardDef := VEN_025.meta

-- BEGIN GENERATED VEN-026
/--
**Field Musicians** — Unit · Calm · Energy 4 · Might 3
Printings: VEN-026/166

> When you play me, give a unit +3 :rb_might: this turn.
-/
def VEN_026.meta : CardDef :=
  { id := ⟨"VEN-026"⟩,
    name := "Field Musicians",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨4, []⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Field Musicians. -/
def VEN_026 : CardDef :=
  { VEN_026.meta with
    abilities := [.triggered (.onSelf .play)
        (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-027
/--
**Hand Hammer** — Gear · Calm · Energy 2 · Might 1
Printings: VEN-027/166

> [Equip] :rb_rune_calm: (:rb_rune_calm:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> I have +2 :rb_might: while I'm at a battlefield with exactly one other unit you control.
-/
def VEN_027.meta : CardDef :=
  { id := ⟨"VEN-027"⟩,
    name := "Hand Hammer",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .equip, arg := .cost ⟨0, [.domain .calm]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Hand Hammer. -/
def VEN_027 : CardDef :=
  { VEN_027.meta with
    grants := [.passive
      (.and (.matches .self .onBattlefield)
        (.cmp .eq (.count (.all .friendly .here [.ofType .unit, .notSelf])) (.const 1)))
      [.mightPlus .self (.const 2)]],
    status := .drafted }

-- BEGIN GENERATED VEN-028
/--
**Mournful Witness** — Unit · Calm · Energy 2 · Might 2
Printings: VEN-028/166

> When a combat that I was in ends, empower me. (I become Empowered if I'm not already.)
> [Empowered][>] I have +2 :rb_might:.
-/
def VEN_028.meta : CardDef :=
  { id := ⟨"VEN-028"⟩,
    name := "Mournful Witness",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Mournful Witness: the effect is not written yet. -/
def VEN_028 : CardDef := VEN_028.meta

-- BEGIN GENERATED VEN-029
/--
**Ol' Poro** — Unit · Calm · Energy 2 · Might 4
Printings: VEN-029/166

> I can't be played on your first, second, or third turns.
-/
def VEN_029.meta : CardDef :=
  { id := ⟨"VEN-029"⟩,
    name := "Ol' Poro",
    types := [.unit],
    tags := [⟨"Poro"⟩, ⟨"Bandle City"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Ol' Poro: the effect is not written yet. -/
def VEN_029 : CardDef := VEN_029.meta

-- BEGIN GENERATED VEN-030
/--
**Serene Ascetic** — Unit · Calm · Energy 3 · Might 3
Printings: VEN-030/166

> [Empower] :rb_energy_3: (:rb_energy_3:: Empower me. Use only if not Empowered.)
> [Empowered][>] I have [Deflect] and [Shield 3]. (Opponents must pay :rb_rune_rainbow: to
> choose me with a spell or ability.+3 :rb_might: while I'm a defender.)
-/
def VEN_030.meta : CardDef :=
  { id := ⟨"VEN-030"⟩,
    name := "Serene Ascetic",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .empower, arg := .cost ⟨3, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Serene Ascetic. -/
def VEN_030 : CardDef :=
  { VEN_030.meta with
    abilities := [.passive (.empowered .self)
      [.keyword .self ⟨.deflect, .none⟩, .keyword .self ⟨.shield, .amount 3⟩]],
    status := .drafted }

-- BEGIN GENERATED VEN-031
/--
**Twilight Shroud** — Spell · Calm · Energy 1
Printings: VEN-031/166

> Give a friendly unit +1 :rb_might: this turn. It can't be chosen by enemy spells and abilities
> this turn.
> [Flow] :rb_energy_2: (You may play this from your trash for its Flow cost. Then banish it.)
-/
def VEN_031.meta : CardDef :=
  { id := ⟨"VEN-031"⟩,
    name := "Twilight Shroud",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Twilight Shroud: the effect is not written yet. -/
def VEN_031 : CardDef := VEN_031.meta

-- BEGIN GENERATED VEN-032
/--
**Frostcoat Mother** — Unit · Calm · Energy 3 · Might 3
Printings: VEN-032/166

> [Empower] :rb_energy_12:. This ability costs :rb_energy_1: less for each rune you control.
> (Pay the cost: Empower me. Use only if not Empowered.)
> [Empowered][>] I have +3 :rb_might:.
-/
def VEN_032.meta : CardDef :=
  { id := ⟨"VEN-032"⟩,
    name := "Frostcoat Mother",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Freljord"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .empower, arg := .cost ⟨12, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Frostcoat Mother. -/
def VEN_032 : CardDef :=
  { VEN_032.meta with
    abilities := [.empower [.pay ⟨12, []⟩, .energyDiscount .always
        (.count (.all .friendly .anywhere [.ofType .rune]))],
      .passive (.empowered .self) [.mightPlus .self (.const 3)]],
    status := .drafted }

-- BEGIN GENERATED VEN-033
/--
**Pakaa Protector** — Unit · Calm · Energy 5 · Might 4
Printings: VEN-033/166

> When I move, reveal the top card of your Main Deck. If it's a unit, draw it. Otherwise, put it
> in your trash and give me +2 :rb_might: this turn.
-/
def VEN_033.meta : CardDef :=
  { id := ⟨"VEN-033"⟩,
    name := "Pakaa Protector",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨5, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Pakaa Protector: the effect is not written yet. -/
def VEN_033 : CardDef := VEN_033.meta

-- BEGIN GENERATED VEN-034
/--
**Resonating Strike** — Spell · Calm · Energy 2 + Power 1
Printings: VEN-034/166

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Reaction] (Play on your turn or in showdowns.)
> Choose a battlefield you control and a unit you control at a different location. Move that
> unit to that battlefield and give it +2 :rb_might: this turn.
-/
def VEN_034.meta : CardDef :=
  { id := ⟨"VEN-034"⟩,
    name := "Resonating Strike",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, [.domain .calm]⟩,
    keywords := [{ keyword := .hidden },
      { keyword := .reaction }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Resonating Strike. -/
def VEN_034 : CardDef :=
  { VEN_034.meta with
    spellEffect := some (.of
      [.targetOf .one .any .atBattlefield [.ofType .battlefield, .controlled],
        .targetOf .one .friendly .anywhere [.ofType .unit, .not (.at_ (.slot 0))]]
      (.seqOf [.prim (.move (.slot 1) (.at_ (.slot 0))),
        .grant (.slot 1) (.mightPlus .it (.const 2)) .thisTurn])),
    status := .drafted }

-- BEGIN GENERATED VEN-035
/--
**Sanction** — Spell · Calm · Energy 3 + Power 1
Printings: VEN-035/166

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose one —Empower a unit. Disempower it at end of turn.Disempower a unit that's [Empowered].
> Empower it at end of turn.
-/
def VEN_035.meta : CardDef :=
  { id := ⟨"VEN-035"⟩,
    name := "Sanction",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Sanction: the effect is not written yet. -/
def VEN_035 : CardDef := VEN_035.meta

-- BEGIN GENERATED VEN-036
/--
**Sandstone Chimera** — Unit · Calm · Energy 7 + Power 2 · Might 8
Printings: VEN-036/166

> While I'm at a battlefield, players only channel 1 rune at the start of their Channel Phase.
-/
def VEN_036.meta : CardDef :=
  { id := ⟨"VEN-036"⟩,
    name := "Sandstone Chimera",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨7, [.domain .calm, .domain .calm]⟩,
    might := some 8,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Sandstone Chimera: the effect is not written yet. -/
def VEN_036 : CardDef := VEN_036.meta

-- BEGIN GENERATED VEN-037
/--
**Tomb-Raider Barbara** — Unit · Calm · Energy 4 · Might 4
Printings: VEN-037/166

> When you play me, if you control 7 or more runes, choose an enemy gear. If it's [Empowered],
> disempower it. Otherwise, kill it.
-/
def VEN_037.meta : CardDef :=
  { id := ⟨"VEN-037"⟩,
    name := "Tomb-Raider Barbara",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Tomb-Raider Barbara. -/
def VEN_037 : CardDef :=
  { VEN_037.meta with
    abilities := [.triggered
      { event := .play,
        condition := .cmp .ge (.count (.all .friendly .anywhere [.ofType .rune])) (.const 7) }
      (.of [.targetOf .one .enemy .anywhere [.ofType .gear]]
        (.ifThen (.empowered (.slot 0))
          (.prim (.disempower (.slot 0))) (.prim (.kill (.slot 0))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-038
/--
**Akali, Silent** — Unit · Calm · Energy 4 + Power 1 · Might 4
Printings: VEN-038/166, VEN-038a/166

> I can't be chosen by enemy spells and abilities unless I'm in combat.
> When I move to a battlefield, give me +2 :rb_might: this turn.
-/
def VEN_038.meta : CardDef :=
  { id := ⟨"VEN-038"⟩,
    name := "Akali",
    subtitle := some "Silent",
    types := [.unit],
    tags := [⟨"Ionia"⟩, ⟨"Akali"⟩],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Akali, Silent: the effect is not written yet. -/
def VEN_038 : CardDef := VEN_038.meta

-- BEGIN GENERATED VEN-039
/--
**Crumbling Sands** — Spell · Calm · Energy 1 + Power 1
Printings: VEN-039/166

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Counter a spell if an opponent has played another spell this turn.
-/
def VEN_039.meta : CardDef :=
  { id := ⟨"VEN-039"⟩,
    name := "Crumbling Sands",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, [.domain .calm]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Crumbling Sands: the effect is not written yet. -/
def VEN_039 : CardDef := VEN_039.meta

-- BEGIN GENERATED VEN-040
/--
**Decree of Focus** — Spell · Calm · Energy 1
Printings: VEN-040/166

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a friendly unit that's in combat with an enemy Fury (:rb_rune_fury:) unit or that's
> being chosen by an enemy Fury spell. Give it +4 :rb_might: this turn.
-/
def VEN_040.meta : CardDef :=
  { id := ⟨"VEN-040"⟩,
    name := "Decree of Focus",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Decree of Focus: the effect is not written yet. -/
def VEN_040 : CardDef := VEN_040.meta

-- BEGIN GENERATED VEN-041
/--
**Riven, Shattered** — Unit · Calm · Energy 3 + Power 1 · Might 3
Printings: VEN-041/166, VEN-171/166

> [Weaponmaster] (When you play me, you may [Equip] one of your Equipment to me for
> :rb_rune_rainbow: less, even if it's already attached.)
> When I attack, choose an enemy unit here. Deal 2 to it for each Equipment attached to me.
-/
def VEN_041.meta : CardDef :=
  { id := ⟨"VEN-041"⟩,
    name := "Riven",
    subtitle := some "Shattered",
    types := [.unit],
    tags := [⟨"Noxus"⟩, ⟨"Riven"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 3,
    keywords := [{ keyword := .weaponmaster }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Riven, Shattered. -/
def VEN_041 : CardDef :=
  { VEN_041.meta with
    abilities := [.triggered (.onSelf .attack)
      (.of [.targetOf .one .enemy .here [.ofType .unit]]
        (.prim (.deal (.slot 0) (.mul (.const 2)
          (.count (.all .any .anywhere [.attachedTo .self, .tag ⟨"Equipment"⟩])))))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-042
/--
**Shen, Scourge of Shadows** — Unit · Calm · Energy 5 + Power 1 · Might 6
Printings: VEN-042/166, VEN-042a/166, VEN-170/166

> When I hold, if there is exactly one other unit you control here, draw 1.
-/
def VEN_042.meta : CardDef :=
  { id := ⟨"VEN-042"⟩,
    name := "Shen",
    subtitle := some "Scourge of Shadows",
    types := [.unit],
    tags := [⟨"Shen"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨5, [.domain .calm]⟩,
    might := some 6,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shen, Scourge of Shadows. -/
def VEN_042 : CardDef :=
  { VEN_042.meta with
    abilities := [.triggered
      { event := .hold,
        condition := .cmp .eq (.count (.all .friendly .here [.ofType .unit, .notSelf])) (.const 1) }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-043
/--
**Steel Paws** — Unit · Calm · Energy 1 · Might 0
Printings: VEN-043/166

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> [Empower] :rb_energy_7: (:rb_energy_7:: Empower me. Use only if not Empowered.)
> [Empowered][>] I have +7 :rb_might:.
-/
def VEN_043.meta : CardDef :=
  { id := ⟨"VEN-043"⟩,
    name := "Steel Paws",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Piltover"⟩],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    might := some 0,
    keywords := [{ keyword := .deflect, arg := .amount 1 },
      { keyword := .empower, arg := .cost ⟨7, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Steel Paws. -/
def VEN_043 : CardDef :=
  { VEN_043.meta with
    abilities := [.passive (.empowered .self) [.mightPlus .self (.const 7)]],
    status := .drafted }

-- BEGIN GENERATED VEN-044
/--
**Astral Heron** — Unit · Calm · Energy 7 · Might 7
Printings: VEN-044/166

> When you play your first card each turn, if I'm at a battlefield, your next card costs
> :rb_energy_2::rb_rune_rainbow::rb_rune_rainbow: less.
-/
def VEN_044.meta : CardDef :=
  { id := ⟨"VEN-044"⟩,
    name := "Astral Heron",
    types := [.unit],
    tags := [⟨"Bird"⟩, ⟨"Mount Targon"⟩],
    domains := [.calm],
    cost := some ⟨7, []⟩,
    might := some 7,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Astral Heron: the effect is not written yet. -/
def VEN_044 : CardDef := VEN_044.meta

-- BEGIN GENERATED VEN-045
/--
**Helm of Suppression** — Gear · Calm · Energy 4 + Power 1
Printings: VEN-045/166

> [Empower] :rb_energy_4::rb_rune_calm: (:rb_energy_4::rb_rune_calm:: Empower this. Use only if
> not Empowered.)
> Opponents' spells cost :rb_energy_1: more. If this is [Empowered], they cost
> :rb_energy_1::rb_rune_rainbow: more instead.
-/
def VEN_045.meta : CardDef :=
  { id := ⟨"VEN-045"⟩,
    name := "Helm of Suppression",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    keywords := [{ keyword := .empower, arg := .cost ⟨4, [.domain .calm]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Helm of Suppression. -/
def VEN_045 : CardDef :=
  { VEN_045.meta with
    abilities := [.passive .always
      [.costPlus (.all .enemy .anywhere [.ofType .spell]) (.const 1)],
      .passive (.empowered .self)
        [.costPower (.all .enemy .anywhere [.ofType .spell]) (.const 1) none true]],
    status := .drafted }

-- BEGIN GENERATED VEN-046
/--
**Nasus, Ascended** — Unit · Calm · Energy 8 + Power 1 · Might 8
Printings: VEN-046/166, VEN-046a/166

> [Deflect 2] (Opponents must pay :rb_rune_rainbow::rb_rune_rainbow: to choose me with a spell
> or ability.)
> [Empower] :rb_energy_8: (:rb_energy_8:: Empower me. Use only if not Empowered.)
> [Empowered][>] When I conquer, you score 1 point.
-/
def VEN_046.meta : CardDef :=
  { id := ⟨"VEN-046"⟩,
    name := "Nasus",
    subtitle := some "Ascended",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Shurima"⟩, ⟨"Nasus"⟩],
    domains := [.calm],
    cost := some ⟨8, [.domain .calm]⟩,
    might := some 8,
    keywords := [{ keyword := .deflect, arg := .amount 2 },
      { keyword := .empower, arg := .cost ⟨8, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Nasus, Ascended. -/
def VEN_046 : CardDef :=
  { VEN_046.meta with
    abilities := [.triggered { event := .conquer, condition := .empowered .self }
      (.of [] (.prim (.score .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-047
/--
**Apprentice Mage** — Unit · Mind · Energy 3 · Might 3
Printings: VEN-047/166

> [Empower] :rb_energy_2: (:rb_energy_2:: Empower me. Use only if not Empowered.)
> When I become [Empowered], [Predict 2]. (Look at the top 2 cards of your Main Deck. Recycle
> any of them and put the rest back in any order.)
> [Empowered][>] I have +1 :rb_might:.
-/
def VEN_047.meta : CardDef :=
  { id := ⟨"VEN-047"⟩,
    name := "Apprentice Mage",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .empower, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Apprentice Mage: the effect is not written yet. -/
def VEN_047 : CardDef := VEN_047.meta

-- BEGIN GENERATED VEN-048
/--
**Cloud Drake** — Unit · Mind · Energy 6 · Might 5
Printings: VEN-048/166

> When you play me, draw 1.
-/
def VEN_048.meta : CardDef :=
  { id := ⟨"VEN-048"⟩,
    name := "Cloud Drake",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Demacia"⟩],
    domains := [.mind],
    cost := some ⟨6, []⟩,
    might := some 5,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Cloud Drake. -/
def VEN_048 : CardDef :=
  { VEN_048.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-049
/--
**Dredge Up** — Spell · Mind · Energy 2
Printings: VEN-049/166

> Draw 1.
> [Flow] :rb_energy_2: (You may play this from your trash for its Flow cost. Then banish it.)
-/
def VEN_049.meta : CardDef :=
  { id := ⟨"VEN-049"⟩,
    name := "Dredge Up",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Dredge Up. -/
def VEN_049 : CardDef :=
  { VEN_049.meta with
    spellEffect := some (.of []
      (.prim (.draw .you (.const 1)))),
    status := .drafted }

-- BEGIN GENERATED VEN-050
/--
**Grumpy Rockbear** — Unit · Mind · Energy 4 · Might 4
Printings: VEN-050/166

> [Empower] :rb_energy_12:. This ability costs :rb_energy_1: less for each rune you control.
> (Pay the cost: Empower me. Use only if not Empowered.)
> [Empowered][>] I have [Deflect] and [Shield 3]. (Opponents must pay :rb_rune_rainbow: to
> choose me with a spell or ability.+3 :rb_might: while I'm a defender.)
-/
def VEN_050.meta : CardDef :=
  { id := ⟨"VEN-050"⟩,
    name := "Grumpy Rockbear",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .empower, arg := .cost ⟨12, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Grumpy Rockbear. -/
def VEN_050 : CardDef :=
  { VEN_050.meta with
    abilities := [.empower [.pay ⟨12, []⟩, .energyDiscount .always
        (.count (.all .friendly .anywhere [.ofType .rune]))],
      .passive (.empowered .self)
        [.keyword .self ⟨.deflect, .none⟩, .keyword .self ⟨.shield, .amount 3⟩]],
    status := .drafted }

-- BEGIN GENERATED VEN-051
/--
**Iterative Design** — Spell · Mind · Energy 4
Printings: VEN-051/166

> Play a 3 :rb_might: Mech unit token.
> [Flow] :rb_energy_2::rb_rune_mind: (You may play this from your trash for its Flow cost. Then
> banish it.)
-/
def VEN_051.meta : CardDef :=
  { id := ⟨"VEN-051"⟩,
    name := "Iterative Design",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨2, [.domain .mind]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Iterative Design. -/
def VEN_051 : CardDef :=
  { VEN_051.meta with
    spellEffect := some (.of []
      (.prim (.create "Mech" (.const 1) .atBase false))),
    status := .drafted }

-- BEGIN GENERATED VEN-052
/--
**Mesmerize** — Spell · Mind · Energy 1 + Power 1
Printings: VEN-052/166

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose one —Return a friendly unit to its owner's hand.Give an enemy unit -2 :rb_might: this
> turn.
-/
def VEN_052.meta : CardDef :=
  { id := ⟨"VEN-052"⟩,
    name := "Mesmerize",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨1, [.domain .mind]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Mesmerize: the effect is not written yet. -/
def VEN_052 : CardDef := VEN_052.meta

-- BEGIN GENERATED VEN-053
/--
**Otterpus** — Unit · Mind · Energy 2 · Might 2
Printings: VEN-053/166

> If a player would score 1 point from conquering or holding during their first or second turn,
> they draw 1 instead.
-/
def VEN_053.meta : CardDef :=
  { id := ⟨"VEN-053"⟩,
    name := "Otterpus",
    types := [.unit],
    tags := [⟨"Bandle City"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Otterpus. -/
def VEN_053 : CardDef :=
  { VEN_053.meta with
    abilities := [.replacement .score
      (.and (.or (.scoreFrom .conquer) (.scoreFrom .hold))
        (.and (.cmp .le (.turnsTaken .eventPlayer) (.const 2))
          (.cmp .eq .eventAmount (.const 1))))
      (.of [] (.prim (.draw .eventPlayer (.const 1))))],
    status := .drafted }

-- BEGIN GENERATED VEN-054
/--
**Questionable Tome** — Gear · Mind · Energy 3
Printings: VEN-054/166

> [Empower] —  :rb_exhaust: (Pay the cost: Empower me. Use only if not Empowered.)
> Disempower this, :rb_energy_1:, :rb_exhaust:: Draw 1.
-/
def VEN_054.meta : CardDef :=
  { id := ⟨"VEN-054"⟩,
    name := "Questionable Tome",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .empower }],
    sets := [⟨"VEN"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Questionable Tome. -/
def VEN_054 : CardDef :=
  { VEN_054.meta with
    abilities := [.empower [.exhaustSelf],
      .activated [.disempowerSelf, .pay ⟨1, []⟩, .exhaustSelf] .normal
        (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-055
/--
**Applied Researchers** — Unit · Mind · Energy 4 · Might 4
Printings: VEN-055/166

> [Empower] :rb_energy_3: (:rb_energy_3:: Empower me. Use only if not Empowered.)
> [Empowered][>] Your spells cost :rb_energy_1::rb_rune_rainbow: less, to a minimum of
> :rb_energy_1:.
-/
def VEN_055.meta : CardDef :=
  { id := ⟨"VEN-055"⟩,
    name := "Applied Researchers",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .empower, arg := .cost ⟨3, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Applied Researchers. -/
def VEN_055 : CardDef :=
  { VEN_055.meta with
    abilities := [.passive (.empowered .self)
      [.costMinusMin (.all .friendly .anywhere [.ofType .spell]) (.const 1) 1,
        .costPower (.all .friendly .anywhere [.ofType .spell]) (.const 1) none false]],
    status := .drafted }

-- BEGIN GENERATED VEN-056
/--
**Clairvoyance** — Spell · Mind · Energy 7
Printings: VEN-056/166

> [Reaction] (Play any time, even before spells and abilities resolve.)
> [Predict 5]. (Look at the top 5 cards of your Main Deck. Recycle any of them and put the rest
> back in any order.)
> Draw 2.
-/
def VEN_056.meta : CardDef :=
  { id := ⟨"VEN-056"⟩,
    name := "Clairvoyance",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨7, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Clairvoyance: the effect is not written yet. -/
def VEN_056 : CardDef := VEN_056.meta

-- BEGIN GENERATED VEN-057
/--
**Covert Informant** — Unit · Mind · Energy 3 + Power 1 · Might 4
Printings: VEN-057/166

> [Empower] :rb_energy_3: (:rb_energy_3:: Empower me. Use only if not Empowered.)
> [Empowered][>] When I move, draw 1.
-/
def VEN_057.meta : CardDef :=
  { id := ⟨"VEN-057"⟩,
    name := "Covert Informant",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    might := some 4,
    keywords := [{ keyword := .empower, arg := .cost ⟨3, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Covert Informant. -/
def VEN_057 : CardDef :=
  { VEN_057.meta with
    abilities := [.triggered { event := .move, condition := .empowered .self }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-058
/--
**Patched Porobot** — Unit Gear · Mind · Energy 2 · Might 2
Printings: VEN-058/166

> (I enter exhausted.)
> When you play me, if you control 3 or more other gear, draw 1.
-/
def VEN_058.meta : CardDef :=
  { id := ⟨"VEN-058"⟩,
    name := "Patched Porobot",
    types := [.unit, .gear],
    tags := [⟨"Mech"⟩, ⟨"Poro"⟩, ⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Patched Porobot. -/
def VEN_058 : CardDef :=
  { VEN_058.meta with
    abilities := [.passive .always [.entersExhausted],
      .triggered
        { event := .play, condition := .cmp .ge
            (.count (.all .friendly .anywhere [.ofType .gear, .notSelf])) (.const 3) }
        (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-059
/--
**Shock Blast** — Spell · Mind · Energy 3 + Power 1
Printings: VEN-059/166

> [Action] (Play on your turn or in showdowns.)
> This costs :rb_energy_2: less if you control something that's [Empowered].
> Deal 4 to a unit at a battlefield.
-/
def VEN_059.meta : CardDef :=
  { id := ⟨"VEN-059"⟩,
    name := "Shock Blast",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shock Blast. -/
def VEN_059 : CardDef :=
  { VEN_059.meta with
    abilities := [.passive
      (.or (.exists (.all .friendly .anywhere [.empowered]))
        (.cmp .gt (.count (.all .friendly .inLegendZone [.empowered])) (.const 0)))
      [.costMinus .self (.const 2)]],
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.prim (.deal (.slot 0) (.const 4)))),
    status := .drafted }

-- BEGIN GENERATED VEN-060
/--
**Sky Cruiser** — Unit · Mind · Energy 4 + Power 1 · Might 3
Printings: VEN-060/166

> Discard a gear, :rb_energy_1:, :rb_exhaust:: Deal 4 to a unit at a battlefield.
-/
def VEN_060.meta : CardDef :=
  { id := ⟨"VEN-060"⟩,
    name := "Sky Cruiser",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Sky Cruiser: the effect is not written yet. -/
def VEN_060 : CardDef := VEN_060.meta

-- BEGIN GENERATED VEN-061
/--
**Decree of Insight** — Spell · Mind · Energy 1
Printings: VEN-061/166

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Ignore [Deflect] while paying this spell's cost.
> Give an enemy Body (:rb_rune_body:) unit -5 :rb_might: this turn.
-/
def VEN_061.meta : CardDef :=
  { id := ⟨"VEN-061"⟩,
    name := "Decree of Insight",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Decree of Insight: the effect is not written yet. -/
def VEN_061 : CardDef := VEN_061.meta

-- BEGIN GENERATED VEN-062
/--
**Hextech Formula** — Gear · Mind · Energy 2
Printings: VEN-062/166

> This enters exhausted.
> :rb_exhaust:: Empower another gear. (It becomes Empowered if it's not already.)
-/
def VEN_062.meta : CardDef :=
  { id := ⟨"VEN-062"⟩,
    name := "Hextech Formula",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Hextech Formula. -/
def VEN_062 : CardDef :=
  { VEN_062.meta with
    abilities := [.passive .always [.entersExhausted],
      .activated [.exhaustSelf] .normal
        (.of [.targetOf .one .any .anywhere [.ofType .gear, .notSelf]]
          (.prim (.empower (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-063
/--
**Nasus, Guardian of Knowledge** — Unit · Mind · Energy 5 + Power 1 · Might 6
Printings: VEN-063/166, VEN-063a/166, VEN-178/166

> Once each turn, when an enemy unit here dies, channel 1 rune exhausted.
-/
def VEN_063.meta : CardDef :=
  { id := ⟨"VEN-063"⟩,
    name := "Nasus",
    subtitle := some "Guardian of Knowledge",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Shurima"⟩, ⟨"Nasus"⟩],
    domains := [.mind],
    cost := some ⟨5, [.domain .mind]⟩,
    might := some 6,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Nasus, Guardian of Knowledge. -/
def VEN_063 : CardDef :=
  { VEN_063.meta with
    abilities := [.triggered
      { event := .die, subject := .all .enemy .anywhere [.ofType .unit, .at_ .self] }
      (.of [] (.prim (.channel .you (.const 0) (.const 1)))) (.perTurn 1)],
    status := .drafted }

-- BEGIN GENERATED VEN-064
/--
**Plaza Guardian** — Unit · Mind · Energy 10 · Might 8
Printings: VEN-064/166

> I cost :rb_energy_1: less for each gear you control.
> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
-/
def VEN_064.meta : CardDef :=
  { id := ⟨"VEN-064"⟩,
    name := "Plaza Guardian",
    types := [.unit],
    tags := [⟨"Mech"⟩, ⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨10, []⟩,
    might := some 8,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Plaza Guardian. -/
def VEN_064 : CardDef :=
  { VEN_064.meta with
    abilities := [.passive .always
      [.costMinus .self (.count (.all .friendly .anywhere [.ofType .gear]))]],
    status := .drafted }

-- BEGIN GENERATED VEN-065
/--
**Swain, Visionary** — Unit · Mind · Energy 6 + Power 1 · Might 6
Printings: VEN-065/166, VEN-173/166

> [Vision] (When you play me, look at the top card of your Main Deck. You may recycle it.)
> When I conquer, if you've played a non-token unit, a non-token gear, and a spell this turn,
> you score 1 point.
-/
def VEN_065.meta : CardDef :=
  { id := ⟨"VEN-065"⟩,
    name := "Swain",
    subtitle := some "Visionary",
    types := [.unit],
    tags := [⟨"Noxus"⟩, ⟨"Swain"⟩, ⟨"Demon"⟩],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind]⟩,
    might := some 6,
    keywords := [{ keyword := .vision }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Swain, Visionary: the effect is not written yet. -/
def VEN_065 : CardDef := VEN_065.meta

-- BEGIN GENERATED VEN-066
/--
**Temporal Breach** — Spell · Mind · Energy 2 + Power 1
Printings: VEN-066/166

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> Banish a unit, then its owner plays it to the same location, ignoring its cost.
-/
def VEN_066.meta : CardDef :=
  { id := ⟨"VEN-066"⟩,
    name := "Temporal Breach",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, [.domain .mind]⟩,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Temporal Breach: the effect is not written yet. -/
def VEN_066 : CardDef := VEN_066.meta

-- BEGIN GENERATED VEN-067
/--
**Bottled Constellation** — Gear · Mind · Energy 10 + Power 2
Printings: VEN-067/166

> At the start of your Main Phase, you may kill 3 other friendly units and/or gear to score 1
> point.
-/
def VEN_067.meta : CardDef :=
  { id := ⟨"VEN-067"⟩,
    name := "Bottled Constellation",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨10, [.domain .mind, .domain .mind]⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Bottled Constellation: the effect is not written yet. -/
def VEN_067 : CardDef := VEN_067.meta

-- BEGIN GENERATED VEN-068
/--
**Jayce, Brilliant Inventor** — Unit · Mind · Energy 6 + Power 1 · Might 6
Printings: VEN-068/166, VEN-068a/166

> When you play me or the first time you play a non-token gear each turn, you may ready
> something besides me that's exhausted.
-/
def VEN_068.meta : CardDef :=
  { id := ⟨"VEN-068"⟩,
    name := "Jayce",
    subtitle := some "Brilliant Inventor",
    types := [.unit],
    tags := [⟨"Jayce"⟩, ⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind]⟩,
    might := some 6,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Jayce, Brilliant Inventor: the effect is not written yet. -/
def VEN_068 : CardDef := VEN_068.meta

-- BEGIN GENERATED VEN-069
/--
**Mel, Newly Awakened** — Unit · Mind · Energy 4 + Power 1 · Might 4
Printings: VEN-069/166, VEN-069a/166

> When you play me, draw 1.
> [Empower] :rb_energy_3: (:rb_energy_3:: Empower me. Use only if not Empowered.)
> [Empowered][>] Your spells and abilities can't be countered. If a spell or ability you control
> would give -:rb_might: to a unit it chooses, it gives an additional -1 :rb_might:.
-/
def VEN_069.meta : CardDef :=
  { id := ⟨"VEN-069"⟩,
    name := "Mel",
    subtitle := some "Newly Awakened",
    types := [.unit],
    tags := [⟨"Noxus"⟩, ⟨"Mel"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 4,
    keywords := [{ keyword := .empower, arg := .cost ⟨3, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Mel, Newly Awakened: the effect is not written yet. -/
def VEN_069 : CardDef := VEN_069.meta

-- BEGIN GENERATED VEN-070
/--
**Brutal Hunter** — Unit · Body · Energy 3 + Power 1 · Might 4
Printings: VEN-070/166

> [Empower] :rb_energy_3: (:rb_energy_3:: Empower me. Use only if not Empowered.)
> [Empowered][>] I have +2 :rb_might: and [Ganking]. (I can move from battlefield to
> battlefield.)
-/
def VEN_070.meta : CardDef :=
  { id := ⟨"VEN-070"⟩,
    name := "Brutal Hunter",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.body],
    cost := some ⟨3, [.domain .body]⟩,
    might := some 4,
    keywords := [{ keyword := .empower, arg := .cost ⟨3, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Brutal Hunter. -/
def VEN_070 : CardDef :=
  { VEN_070.meta with
    abilities := [.passive (.empowered .self)
      [.mightPlus .self (.const 2), .keyword .self ⟨.ganking, .none⟩]],
    status := .drafted }

-- BEGIN GENERATED VEN-071
/--
**Fretful Feline** — Unit · Body · Energy 6 · Might 5
Printings: VEN-071/166

> When I become ready, give me +2 :rb_might: this turn.
-/
def VEN_071.meta : CardDef :=
  { id := ⟨"VEN-071"⟩,
    name := "Fretful Feline",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Piltover"⟩],
    domains := [.body],
    cost := some ⟨6, []⟩,
    might := some 5,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Fretful Feline. -/
def VEN_071 : CardDef :=
  { VEN_071.meta with
    abilities := [.triggered (.onSelf .ready)
      (.of [] (.grant .self (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-072
/--
**Guttural Roar** — Spell · Body · Energy 2
Printings: VEN-072/166

> [Action] (Play on your turn or in showdowns.)
> Give a unit +2 :rb_might: this turn. If it's [Empowered], give it +4 :rb_might: this turn
> instead.
-/
def VEN_072.meta : CardDef :=
  { id := ⟨"VEN-072"⟩,
    name := "Guttural Roar",
    types := [.spell],
    domains := [.body],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Guttural Roar. -/
def VEN_072 : CardDef :=
  { VEN_072.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.ifThen (.empowered (.slot 0))
        (.grant (.slot 0) (.mightPlus .it (.const 4)) .thisTurn)
        (.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn))),
    status := .drafted }

-- BEGIN GENERATED VEN-073
/--
**Jagged Cutlass** — Gear · Body · Energy 3 · Might 2
Printings: VEN-073/166

> Equip :rb_rune_body: (:rb_rune_body:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> I can't be moved by enemy spells and abilities.
-/
def VEN_073.meta : CardDef :=
  { id := ⟨"VEN-073"⟩,
    name := "Jagged Cutlass",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 2,
    mightBonus := some 2,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Jagged Cutlass: the effect is not written yet. -/
def VEN_073 : CardDef := VEN_073.meta

-- BEGIN GENERATED VEN-074
/--
**Legion Marauder** — Unit · Body · Energy 2 · Might 2
Printings: VEN-074/166

> [Empower] — :rb_energy_1: or :rb_rune_body: (Pay either cost: Empower me. Use only if not
> Empowered.)
> [Empowered][>] I have +1 :rb_might:.
-/
def VEN_074.meta : CardDef :=
  { id := ⟨"VEN-074"⟩,
    name := "Legion Marauder",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .empower }],
    sets := [⟨"VEN"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Legion Marauder. -/
def VEN_074 : CardDef :=
  { VEN_074.meta with
    abilities := [.empower [.pay ⟨1, []⟩], .empower [.pay ⟨0, [.domain .body]⟩],
      .passive (.empowered .self) [.mightPlus .self (.const 1)]],
    status := .drafted }

-- BEGIN GENERATED VEN-075
/--
**Platewyrm Egg** — Gear · Body · Energy 3
Printings: VEN-075/166

> This enters exhausted.
> [Empower] — :rb_energy_1:, :rb_exhaust: (Pay the cost: Empower this. Use only if not
> Empowered.)
> [Reaction][>] :rb_exhaust:: [Add] :rb_energy_1:. If this is [Empowered], [Add] :rb_energy_2:
> instead.
-/
def VEN_075.meta : CardDef :=
  { id := ⟨"VEN-075"⟩,
    name := "Platewyrm Egg",
    types := [.gear],
    domains := [.body],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .empower },
      { keyword := .reaction }],
    sets := [⟨"VEN"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Platewyrm Egg. -/
def VEN_075 : CardDef :=
  { VEN_075.meta with
    abilities := [.passive .always [.entersExhausted],
      .empower [.pay ⟨1, []⟩, .exhaustSelf],
      .activated [.exhaustSelf] .reaction
        (.of [] (.ifThen (.not (.empowered .self))
          (.prim (.addEnergy .you (.const 1) none)) .nop)) .unlimited,
      .activated [.exhaustSelf] .reaction
        (.of [] (.ifThen (.empowered .self)
          (.prim (.addEnergy .you (.const 2) none)) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-076
/--
**Repair Specialist** — Unit · Body · Energy 3 · Might 3
Printings: VEN-076/166

> I have [Assault] equal to the number of gear you control. (+1 :rb_might: while I'm an attacker
> for each instance of Assault.)
-/
def VEN_076.meta : CardDef :=
  { id := ⟨"VEN-076"⟩,
    name := "Repair Specialist",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Repair Specialist. -/
def VEN_076 : CardDef :=
  { VEN_076.meta with
    abilities := [.passive .always [.assaultCount (.all .friendly .anywhere [.ofType .gear])]],
    status := .drafted }

-- BEGIN GENERATED VEN-077
/--
**Tools of Empire** — Gear · Body · Energy 4
Printings: VEN-077/166

> [Empower] :rb_energy_2: (:rb_energy_2:: Empower this. Use only if not Empowered.)
> :rb_exhaust:: Give a unit +2 :rb_might: this turn. If this is [Empowered], give that unit +4
> :rb_might: this turn instead.
-/
def VEN_077.meta : CardDef :=
  { id := ⟨"VEN-077"⟩,
    name := "Tools of Empire",
    types := [.gear],
    domains := [.body],
    cost := some ⟨4, []⟩,
    keywords := [{ keyword := .empower, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Tools of Empire. -/
def VEN_077 : CardDef :=
  { VEN_077.meta with
    abilities := [.activated [.exhaustSelf] .normal
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.ifThen (.empowered .self)
          (.grant (.slot 0) (.mightPlus .it (.const 4)) .thisTurn)
          (.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-078
/--
**Baccai Witherclaw** — Unit · Body · Energy 4 · Might 4
Printings: VEN-078/166

> [Empower] :rb_energy_1::rb_rune_rainbow::rb_rune_rainbow:
> (:rb_energy_1::rb_rune_rainbow::rb_rune_rainbow:: Empower me. Use only if not Empowered.)
> [Empowered][>] I have +2 :rb_might:.
> [Empowered][>][>>][Deathknell][>] Channel 2 runes exhausted. (When I die while Empowered, get
> the effect.)
-/
def VEN_078.meta : CardDef :=
  { id := ⟨"VEN-078"⟩,
    name := "Baccai Witherclaw",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .empower, arg := .cost ⟨1, [.any, .any]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Baccai Witherclaw. -/
def VEN_078 : CardDef :=
  { VEN_078.meta with
    abilities := [.passive (.empowered .self) [.mightPlus .self (.const 2)],
      .triggered { event := .die, condition := .leftEmpowered }
        (.of [] (.prim (.channel .you (.const 0) (.const 2)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-079
/--
**Dame the Despoiler** — Unit · Body · Energy 5 · Might 5
Printings: VEN-079/166

> [Empower] :rb_energy_5::rb_rune_body: (:rb_energy_5::rb_rune_body:: Empower me. Use only if
> not Empowered.)
> [Empowered][>] When I attack or defend, choose a unit here. Increase my Might to its Might
> this turn, then give me +1 :rb_might: this turn.
-/
def VEN_079.meta : CardDef :=
  { id := ⟨"VEN-079"⟩,
    name := "Dame the Despoiler",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.body],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .empower, arg := .cost ⟨5, [.domain .body]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Dame the Despoiler. -/
def VEN_079 : CardDef :=
  { VEN_079.meta with
    abilities :=
      let effect := EffectDef.of [.targetOf .one .any .here [.ofType .unit]]
        (.grant .self (.mightPlus .it (.add
          (.sub (.mightOf (.slot 0)) (.mightOf .self)) (.const 1))) .thisTurn)
      [.triggered { event := .attack, condition := .empowered .self } effect .unlimited,
        .triggered { event := .defend, condition := .empowered .self } effect .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-080
/--
**Noxian Demolitionist** — Unit · Body · Energy 2 · Might 1
Printings: VEN-080/166

> When I conquer, you may kill a gear with Energy cost no more than my Might.
-/
def VEN_080.meta : CardDef :=
  { id := ⟨"VEN-080"⟩,
    name := "Noxian Demolitionist",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 1,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Noxian Demolitionist. -/
def VEN_080 : CardDef :=
  { VEN_080.meta with
    abilities := [.triggered (.onSelf .conquer)
      (.of [.targetOf (.upTo 1) .any .anywhere
        [.ofType .gear, .cost .le (.mightOf .self)]] (.prim (.kill (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-081
/--
**Onslaught** — Spell · Body · Energy 4
Printings: VEN-081/166

> Give a unit +6 :rb_might: this turn.
> [Flow] :rb_energy_4: (You may play this from your trash for its Flow cost. Then banish it.)
-/
def VEN_081.meta : CardDef :=
  { id := ⟨"VEN-081"⟩,
    name := "Onslaught",
    types := [.spell],
    domains := [.body],
    cost := some ⟨4, []⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨4, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Onslaught. -/
def VEN_081 : CardDef :=
  { VEN_081.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it (.const 6)) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED VEN-082
/--
**Profiteer** — Unit · Body · Energy 4 · Might 4
Printings: VEN-082/166

> When you play me, you may disempower something you control to empower a legend, unit, or gear.
-/
def VEN_082.meta : CardDef :=
  { id := ⟨"VEN-082"⟩,
    name := "Profiteer",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Profiteer: the effect is not written yet. -/
def VEN_082 : CardDef := VEN_082.meta

-- BEGIN GENERATED VEN-083
/--
**Rampage** — Spell · Body · Energy 3
Printings: VEN-083/166

> As you play this, you may pay :rb_rune_body: as an additional cost.
> Choose a friendly unit and an enemy unit. If you paid the additional cost, give the friendly
> unit +2 :rb_might: this turn. They deal damage equal to their Mights to each other.
-/
def VEN_083.meta : CardDef :=
  { id := ⟨"VEN-083"⟩,
    name := "Rampage",
    types := [.spell],
    domains := [.body],
    cost := some ⟨3, []⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Rampage: the effect is not written yet. -/
def VEN_083 : CardDef := VEN_083.meta

-- BEGIN GENERATED VEN-084
/--
**Ambessa, The Wolf** — Unit · Body · Energy 4 · Might 4
Printings: VEN-084/166, VEN-084a/166

> [Empower] :rb_energy_3::rb_rune_body: (:rb_energy_3::rb_rune_body:: Empower me. Use only if
> not Empowered.)
> [Empowered][>] I have +3 :rb_might: and can't be dealt damage unless I'm in combat.
-/
def VEN_084.meta : CardDef :=
  { id := ⟨"VEN-084"⟩,
    name := "Ambessa",
    subtitle := some "The Wolf",
    types := [.unit],
    tags := [⟨"Noxus"⟩, ⟨"Ambessa"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .empower, arg := .cost ⟨3, [.domain .body]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Ambessa, The Wolf. -/
def VEN_084 : CardDef :=
  { VEN_084.meta with
    abilities := [.passive (.empowered .self) [.mightPlus .self (.const 3)],
      .passive (.and (.empowered .self) (.not .inCombatHere)) [.noDamage]],
    status := .drafted }

-- BEGIN GENERATED VEN-085
/--
**Decree of Strength** — Spell · Body · Energy 1
Printings: VEN-085/166

> Choose an opponent. They reveal their hand and you choose a Mind (:rb_rune_mind:) card from
> it. They recycle that card.
-/
def VEN_085.meta : CardDef :=
  { id := ⟨"VEN-085"⟩,
    name := "Decree of Strength",
    types := [.spell],
    domains := [.body],
    cost := some ⟨1, []⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Decree of Strength: the effect is not written yet. -/
def VEN_085 : CardDef := VEN_085.meta

-- BEGIN GENERATED VEN-086
/--
**Gangplank, Naval** — Unit · Body · Energy 6 · Might 6
Printings: VEN-086/166, VEN-181/166

> [Empower] :rb_rune_body::rb_rune_body: (:rb_rune_body::rb_rune_body:: Empower me. Use only if
> not Empowered.)
> [Empowered][>] If a spell or ability that chooses me would stun me, give me -:rb_might:, or
> return me to hand, give me +3 :rb_might: instead.
-/
def VEN_086.meta : CardDef :=
  { id := ⟨"VEN-086"⟩,
    name := "Gangplank",
    subtitle := some "Naval",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩, ⟨"Gangplank"⟩],
    domains := [.body],
    cost := some ⟨6, []⟩,
    might := some 6,
    keywords := [{ keyword := .empower, arg := .cost ⟨0, [.domain .body, .domain .body]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Gangplank, Naval: the effect is not written yet. -/
def VEN_086 : CardDef := VEN_086.meta

-- BEGIN GENERATED VEN-087
/--
**Hextech Disc** — Gear · Body · Energy 4 + Power 1
Printings: VEN-087/166

> [Empower] — :rb_exhaust: (Pay the cost: Empower this. Use only if not Empowered.)
> Disempower this, :rb_energy_1:, :rb_exhaust:: Play a 3 :rb_might: Mech unit token to your
> base.
-/
def VEN_087.meta : CardDef :=
  { id := ⟨"VEN-087"⟩,
    name := "Hextech Disc",
    types := [.gear],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    keywords := [{ keyword := .empower }],
    sets := [⟨"VEN"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Hextech Disc. -/
def VEN_087 : CardDef :=
  { VEN_087.meta with
    abilities := [.empower [.exhaustSelf],
      .activated [.disempowerSelf, .pay ⟨1, []⟩, .exhaustSelf] .normal
        (.of [] (.prim (.create "Mech" (.const 1) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-088
/--
**Jayce, Hammer in Hand** — Unit · Body · Energy 4 + Power 1 · Might 5
Printings: VEN-088/166, VEN-088a/166

> When I become ready, choose one to give me this turn —[Assault 2] (+2 :rb_might: while I'm an
> attacker.)[Deflect 2] (Opponents must pay :rb_rune_rainbow::rb_rune_rainbow: to choose me with
> a spell or ability.)[Ganking] (I can move from battlefield to battlefield.)
-/
def VEN_088.meta : CardDef :=
  { id := ⟨"VEN-088"⟩,
    name := "Jayce",
    subtitle := some "Hammer in Hand",
    types := [.unit],
    tags := [⟨"Jayce"⟩, ⟨"Piltover"⟩],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    might := some 5,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Jayce, Hammer in Hand: the effect is not written yet. -/
def VEN_088 : CardDef := VEN_088.meta

-- BEGIN GENERATED VEN-089
/--
**Wild Claw** — Spell · Body · Energy 7 + Power 1
Printings: VEN-089/166

> Look at the top 5 cards of your Main Deck. You may banish a unit or gear from among them and
> play it, reducing its Energy cost by :rb_energy_5:. Recycle the rest. Then you may do this:
> Empower it. (It becomes Empowered if it's not already.)
-/
def VEN_089.meta : CardDef :=
  { id := ⟨"VEN-089"⟩,
    name := "Wild Claw",
    types := [.spell],
    domains := [.body],
    cost := some ⟨7, [.domain .body]⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Wild Claw: the effect is not written yet. -/
def VEN_089 : CardDef := VEN_089.meta

-- BEGIN GENERATED VEN-090
/--
**Cataclysmic Duel** — Spell · Body · Energy 8 + Power 3
Printings: VEN-090/166

> Each player chooses a unit they control. Kill the rest.
-/
def VEN_090.meta : CardDef :=
  { id := ⟨"VEN-090"⟩,
    name := "Cataclysmic Duel",
    types := [.spell],
    domains := [.body],
    cost := some ⟨8, [.domain .body, .domain .body, .domain .body]⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Cataclysmic Duel: the effect is not written yet. -/
def VEN_090 : CardDef := VEN_090.meta

-- BEGIN GENERATED VEN-091
/--
**Corrupted Dragon** — Unit · Body · Energy 10 + Power 2 · Might 10
Printings: VEN-091/166

> If your score is not within 3 points of the Victory Score, I enter ready.
> When I attack, you may move any number of enemy units here each with 5 :rb_might: or less to
> their base.
-/
def VEN_091.meta : CardDef :=
  { id := ⟨"VEN-091"⟩,
    name := "Corrupted Dragon",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Shadow Isles"⟩],
    domains := [.body],
    cost := some ⟨10, [.domain .body, .domain .body]⟩,
    might := some 10,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Corrupted Dragon: the effect is not written yet. -/
def VEN_091 : CardDef := VEN_091.meta

-- BEGIN GENERATED VEN-092
/--
**Renekton, Brute** — Unit · Body · Energy 5 · Might 4
Printings: VEN-092/166, VEN-092a/166, VEN-177/166

> :rb_energy_1:: Give me +1 :rb_might: this turn.
> When my Might becomes 10 or more, empower me. (I become Empowered if I'm not already.)
> [Empowered][>] I have [Deflect] and [Ganking]. (Opponents must pay :rb_rune_rainbow: to choose
> me with a spell or ability. I can move from battlefield to battlefield.)
-/
def VEN_092.meta : CardDef :=
  { id := ⟨"VEN-092"⟩,
    name := "Renekton",
    subtitle := some "Brute",
    types := [.unit],
    tags := [⟨"Shurima"⟩, ⟨"Renekton"⟩],
    domains := [.body],
    cost := some ⟨5, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Renekton, Brute. -/
def VEN_092 : CardDef :=
  { VEN_092.meta with
    abilities := [
      .activated [.pay ⟨1, []⟩] .normal
        (.of [] (.grant .self (.mightPlus .it (.const 1)) .thisTurn)) .unlimited,
      .triggered { event := .mightAtLeast 10 } (.of [] (.prim (.empower .self))) .unlimited,
      .passive (.empowered .self)
        [.keyword .self { keyword := .deflect, arg := .amount 1 },
         .keyword .self { keyword := .ganking }]],
    status := .drafted }

-- BEGIN GENERATED VEN-093
/--
**Kinkou Lifeblade** — Unit · Chaos · Energy 4 · Might 4
Printings: VEN-093/166

> [Empower] :rb_energy_2: (:rb_energy_2:: Empower me. Use only if not Empowered.)
> [Empowered][>] I have +1 :rb_might: and [Ganking]. (I can move from battlefield to
> battlefield.)
-/
def VEN_093.meta : CardDef :=
  { id := ⟨"VEN-093"⟩,
    name := "Kinkou Lifeblade",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .empower, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Kinkou Lifeblade. -/
def VEN_093 : CardDef :=
  { VEN_093.meta with
    abilities := [.passive (.empowered .self)
      [.mightPlus .self (.const 1), .keyword .self ⟨.ganking, .none⟩]],
    status := .drafted }

-- BEGIN GENERATED VEN-094
/--
**Mask Mother** — Unit · Chaos · Energy 3 · Might 3
Printings: VEN-094/166

> When you discard me, you may pay :rb_energy_1: to give a friendly unit +2 :rb_might: this
> turn.
-/
def VEN_094.meta : CardDef :=
  { id := ⟨"VEN-094"⟩,
    name := "Mask Mother",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Mask Mother: the effect is not written yet. -/
def VEN_094 : CardDef := VEN_094.meta

-- BEGIN GENERATED VEN-095
/--
**Shadow Order Disciple** — Unit · Chaos · Energy 2 · Might 2
Printings: VEN-095/166

> When I move, you may [Burn 1] to give me +1 :rb_might: this turn. (To Burn 1, put the top card
> of your Main Deck into your trash.)
-/
def VEN_095.meta : CardDef :=
  { id := ⟨"VEN-095"⟩,
    name := "Shadow Order Disciple",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shadow Order Disciple: the effect is not written yet. -/
def VEN_095 : CardDef := VEN_095.meta

-- BEGIN GENERATED VEN-096
/--
**Shadowblade Lurker** — Unit · Chaos · Energy 5 · Might 5
Printings: VEN-096/166

> I cost :rb_energy_2: less for each card with my name in your trash.
-/
def VEN_096.meta : CardDef :=
  { id := ⟨"VEN-096"⟩,
    name := "Shadowblade Lurker",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shadowblade Lurker. -/
def VEN_096 : CardDef :=
  { VEN_096.meta with
    abilities := [.passive .always [.costMinus .self (.mul (.const 2)
      (.count (.all .friendly .inTrash [.named "Shadowblade Lurker"])))]],
    status := .drafted }

-- BEGIN GENERATED VEN-097
/--
**Spiderling** — Unit · Chaos · Energy 3 · Might 1
Printings: VEN-097/166

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> I have +1 :rb_might: for each other unit you control here with my name.
> Your deck can have any number of cards named Spiderling.
-/
def VEN_097.meta : CardDef :=
  { id := ⟨"VEN-097"⟩,
    name := "Spiderling",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Spider"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 1,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Spiderling: the effect is not written yet. -/
def VEN_097 : CardDef := VEN_097.meta

-- BEGIN GENERATED VEN-098
/--
**Stargazer** — Unit · Chaos · Energy 5 · Might 4
Printings: VEN-098/166

> Spells with [Flow] you play from your trash cost :rb_energy_2: less, to a minimum of
> :rb_energy_1:.
-/
def VEN_098.meta : CardDef :=
  { id := ⟨"VEN-098"⟩,
    name := "Stargazer",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.chaos],
    cost := some ⟨5, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Stargazer. -/
def VEN_098 : CardDef :=
  { VEN_098.meta with
    abilities := [.passive .always
      [.costMinusMin (.all .friendly .anywhere [.ofType .spell, .hasKeyword .flow, .inTrashZone])
        (.const 2) 1]],
    status := .drafted }

-- BEGIN GENERATED VEN-099
/--
**Tornado Warrior** — Unit · Chaos · Energy 3 · Might 3
Printings: VEN-099/166

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me from face down, you may empower something here. Disempower it at end of turn.
-/
def VEN_099.meta : CardDef :=
  { id := ⟨"VEN-099"⟩,
    name := "Tornado Warrior",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Tornado Warrior: the effect is not written yet. -/
def VEN_099 : CardDef := VEN_099.meta

-- BEGIN GENERATED VEN-100
/--
**Up from the Deep** — Spell · Chaos · Energy 3
Printings: VEN-100/166

> Play two 1 :rb_might: Tentacle unit tokens from Bilgewater.
> [Flow] :rb_energy_3: (You may play this from your trash for its Flow cost. Then banish it.)
-/
def VEN_100.meta : CardDef :=
  { id := ⟨"VEN-100"⟩,
    name := "Up from the Deep",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨3, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Up from the Deep: the effect is not written yet. -/
def VEN_100 : CardDef := VEN_100.meta

-- BEGIN GENERATED VEN-101
/--
**Gust Monk** — Unit · Chaos · Energy 2 · Might 2
Printings: VEN-101/166

> You may pay :rb_energy_1: as an additional cost to play me.
> When you play me, if you paid the additional cost, banish a card from any trash to give a unit
> [Assault 2] this turn. (+2 :rb_might: while it's an attacker.)
-/
def VEN_101.meta : CardDef :=
  { id := ⟨"VEN-101"⟩,
    name := "Gust Monk",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Gust Monk: the effect is not written yet. -/
def VEN_101 : CardDef := VEN_101.meta

-- BEGIN GENERATED VEN-102
/--
**Ravenbloom Prefect** — Unit · Chaos · Energy 3 · Might 3
Printings: VEN-102/166

> When an opponent plays a gear, you may banish me to banish it.
-/
def VEN_102.meta : CardDef :=
  { id := ⟨"VEN-102"⟩,
    name := "Ravenbloom Prefect",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Ravenbloom Prefect: the effect is not written yet. -/
def VEN_102 : CardDef := VEN_102.meta

-- BEGIN GENERATED VEN-103
/--
**Shadows of the Past** — Spell · Chaos · Energy 3 + Power 1
Printings: VEN-103/166

> Return up to 2 units from trashes to their owners' hands.

Effect (given to the unit it is attached to):

> 1
-/
def VEN_103.meta : CardDef :=
  { id := ⟨"VEN-103"⟩,
    name := "Shadows of the Past",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shadows of the Past: the effect is not written yet. -/
def VEN_103 : CardDef := VEN_103.meta

-- BEGIN GENERATED VEN-104
/--
**Tail-Cloaked Matriarch** — Unit · Chaos · Energy 4 · Might 4
Printings: VEN-104/166

> [Empower] :rb_energy_2::rb_rune_chaos: (:rb_energy_2::rb_rune_chaos:: Empower me. Use only if
> not Empowered.)
> When I become [Empowered], you may choose a unit in your trash with Energy cost no more than
> :rb_energy_3: and Power cost no more than :rb_rune_rainbow:. Play it to your base, ignoring
> its cost.
-/
def VEN_104.meta : CardDef :=
  { id := ⟨"VEN-104"⟩,
    name := "Tail-Cloaked Matriarch",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .empower, arg := .cost ⟨2, [.domain .chaos]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Tail-Cloaked Matriarch: the effect is not written yet. -/
def VEN_104 : CardDef := VEN_104.meta

-- BEGIN GENERATED VEN-105
/--
**Twilight Step** — Spell · Chaos · Energy 2 + Power 1
Printings: VEN-105/166

> Move a unit with 3 :rb_might: or less.
> [Flow] :rb_energy_4::rb_rune_chaos: (You may play this from your trash for its Flow cost. Then
> banish it.)
-/
def VEN_105.meta : CardDef :=
  { id := ⟨"VEN-105"⟩,
    name := "Twilight Step",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, [.domain .chaos]⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨4, [.domain .chaos]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Twilight Step: the effect is not written yet. -/
def VEN_105 : CardDef := VEN_105.meta

-- BEGIN GENERATED VEN-106
/--
**Wind and Ghosts** — Spell · Chaos · Energy 3 + Power 1
Printings: VEN-106/166

> [Action] (Play on your turn or in showdowns.)
> Choose a unit at a battlefield. If it has 3 :rb_might: or less, banish it. Otherwise, return
> it to its owner's hand.
-/
def VEN_106.meta : CardDef :=
  { id := ⟨"VEN-106"⟩,
    name := "Wind and Ghosts",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Wind and Ghosts. -/
def VEN_106 : CardDef :=
  { VEN_106.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
      (.ifThen (.matches (.slot 0) (.might .le (.const 3)))
        (.prim (.banish (.slot 0))) (.prim (.returnToHand (.slot 0))))),
    status := .drafted }

-- BEGIN GENERATED VEN-107
/--
**Decree of Discord** — Spell · Chaos · Energy 1 + Power 1
Printings: VEN-107/166

> Return any number of enemy Order (:rb_rune_order:) units with total Might 5 or less to their
> owners' hands.
-/
def VEN_107.meta : CardDef :=
  { id := ⟨"VEN-107"⟩,
    name := "Decree of Discord",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨1, [.domain .chaos]⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Decree of Discord: the effect is not written yet. -/
def VEN_107 : CardDef := VEN_107.meta

-- BEGIN GENERATED VEN-108
/--
**Forgotten Relic** — Gear · Chaos · Energy 5
Printings: VEN-108/166

> When you play this or at the start of your Beginning Phase, [Burn 1]. When you burn a unit
> this way, do this: Give a friendly unit +:rb_might: equal to the burned card's Might this
> turn. (To Burn 1, put the top card of your Main Deck into your trash.)
-/
def VEN_108.meta : CardDef :=
  { id := ⟨"VEN-108"⟩,
    name := "Forgotten Relic",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨5, []⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Forgotten Relic: the effect is not written yet. -/
def VEN_108 : CardDef := VEN_108.meta

-- BEGIN GENERATED VEN-109
/--
**Illaoi, Prophet of the Great Kraken** — Unit · Chaos · Energy 6 · Might 4
Printings: VEN-109/166, VEN-182/166

> When you play me or when I score, play a :rb_energy_1: :rb_might: Tentacle unit token from
> Bilgewater.
> I have +1 :rb_might: for each token unit you control.
-/
def VEN_109.meta : CardDef :=
  { id := ⟨"VEN-109"⟩,
    name := "Illaoi",
    subtitle := some "Prophet of the Great Kraken",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩, ⟨"Illaoi"⟩],
    domains := [.chaos],
    cost := some ⟨6, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Illaoi, Prophet of the Great Kraken: the effect is not written yet. -/
def VEN_109 : CardDef := VEN_109.meta

-- BEGIN GENERATED VEN-110
/--
**Mel, Defiant Soul** — Unit · Chaos · Energy 5 · Might 4
Printings: VEN-110/166, VEN-110a/166, VEN-188/166

> [Empower] — Discard a spell (Pay the cost: Empower me. Use only if not Empowered.)
> When I become [Empowered], banish an enemy unit at a battlefield with 3 :rb_might: or less.
-/
def VEN_110.meta : CardDef :=
  { id := ⟨"VEN-110"⟩,
    name := "Mel",
    subtitle := some "Defiant Soul",
    types := [.unit],
    tags := [⟨"Noxus"⟩, ⟨"Mel"⟩],
    domains := [.chaos],
    cost := some ⟨5, []⟩,
    might := some 4,
    keywords := [{ keyword := .empower }],
    sets := [⟨"VEN"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Mel, Defiant Soul: the effect is not written yet. -/
def VEN_110 : CardDef := VEN_110.meta

-- BEGIN GENERATED VEN-111
/--
**Minah Swiftfoot** — Unit · Chaos · Energy 6 + Power 1 · Might 6
Printings: VEN-111/166

> When I move to a battlefield, choose one —Each player discards 1.Each player draws 1.
-/
def VEN_111.meta : CardDef :=
  { id := ⟨"VEN-111"⟩,
    name := "Minah Swiftfoot",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨6, [.domain .chaos]⟩,
    might := some 6,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Minah Swiftfoot: the effect is not written yet. -/
def VEN_111 : CardDef := VEN_111.meta

-- BEGIN GENERATED VEN-112
/--
**Zed, Without a Sound** — Unit · Chaos · Energy 5 · Might 5
Printings: VEN-112/166, VEN-112a/166

> When I conquer, play a 0 :rb_might: Shadow Clone unit token to your base. (It has "When I
> attack, you may banish a unit from your trash. If you do, give me [Assault 4] this turn.")
> [Action][>] :rb_energy_1::rb_rune_chaos:: Move me and a Shadow Clone you control to each
> other's locations.
-/
def VEN_112.meta : CardDef :=
  { id := ⟨"VEN-112"⟩,
    name := "Zed",
    subtitle := some "Without a Sound",
    types := [.unit],
    tags := [⟨"Ionia"⟩, ⟨"Zed"⟩],
    domains := [.chaos],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Zed, Without a Sound: the effect is not written yet. -/
def VEN_112 : CardDef := VEN_112.meta

-- BEGIN GENERATED VEN-113
/--
**Kennen, Storm of Shuriken** — Unit · Chaos · Energy 3 + Power 1 · Might 4
Printings: VEN-113/166, VEN-113a/166

> When you play me, [Burn 2]. (Put the top 2 cards of your Main Deck into your trash.)
> When I conquer, give a spell in your trash [Flow] equal to its cost this turn. (You may play
> it from your trash for its Flow cost. Then banish it.)
-/
def VEN_113.meta : CardDef :=
  { id := ⟨"VEN-113"⟩,
    name := "Kennen",
    subtitle := some "Storm of Shuriken",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Kennen"⟩],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Kennen, Storm of Shuriken: the effect is not written yet. -/
def VEN_113 : CardDef := VEN_113.meta

-- BEGIN GENERATED VEN-114
/--
**Kharox** — Unit · Chaos · Energy 6 · Might 5
Printings: VEN-114/166

> [Empower] :rb_energy_6::rb_rune_chaos::rb_rune_chaos:
> (:rb_energy_6::rb_rune_chaos::rb_rune_chaos:: Empower me. Use only if not Empowered.)
> When I become [Empowered], choose an opponent. They [Burn 3]. Then you may do this: Choose a
> unit in their trash and play it, ignoring its cost. (To Burn 3, they put the top 3 cards of
> their Main Deck into their trash.)
-/
def VEN_114.meta : CardDef :=
  { id := ⟨"VEN-114"⟩,
    name := "Kharox",
    types := [.unit],
    tags := [⟨"Spirit"⟩, ⟨"Shadow Isles"⟩],
    domains := [.chaos],
    cost := some ⟨6, []⟩,
    might := some 5,
    keywords := [{ keyword := .empower, arg := .cost ⟨6, [.domain .chaos, .domain .chaos]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Kharox: the effect is not written yet. -/
def VEN_114 : CardDef := VEN_114.meta

-- BEGIN GENERATED VEN-115
/--
**Ocean Drake** — Unit · Chaos · Energy 8 + Power 2 · Might 7
Printings: VEN-115/166

> You may play me to an open battlefield.
> When you play me, you may return a non-Dragon unit to its owner's hand.
-/
def VEN_115.meta : CardDef :=
  { id := ⟨"VEN-115"⟩,
    name := "Ocean Drake",
    types := [.unit],
    tags := [⟨"Dragon"⟩, ⟨"Ionia"⟩],
    domains := [.chaos],
    cost := some ⟨8, [.domain .chaos, .domain .chaos]⟩,
    might := some 7,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Ocean Drake. -/
def VEN_115 : CardDef :=
  { VEN_115.meta with
    abilities := [.passive .always [.playToBf [.openBf], .playToOpenBf],
      .triggered (.onSelf .play)
        (.of [.targetOf (.upTo 1) .any .anywhere [.ofType .unit, .not (.tag ⟨"Dragon"⟩)]]
          (.prim (.returnToHand (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-116
/--
**Dragon Form** — Spell · Order · Energy 3
Printings: VEN-116/166

> Choose a unit. Its base Might becomes 5 this turn.
> [Flow] :rb_energy_3: (You may play this from your trash for its Flow cost. Then banish it.)
-/
def VEN_116.meta : CardDef :=
  { id := ⟨"VEN-116"⟩,
    name := "Dragon Form",
    types := [.spell],
    domains := [.order],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨3, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Dragon Form: the effect is not written yet. -/
def VEN_116 : CardDef := VEN_116.meta

-- BEGIN GENERATED VEN-117
/--
**Disciple of Shen** — Unit · Order · Energy 2 · Might 1
Printings: VEN-117/166

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> I have [Shield 3] while I'm at a battlefield with exactly one other unit you control. (+3
> :rb_might: while I'm a defender.)
-/
def VEN_117.meta : CardDef :=
  { id := ⟨"VEN-117"⟩,
    name := "Disciple of Shen",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Disciple of Shen. -/
def VEN_117 : CardDef :=
  { VEN_117.meta with
    abilities := [.passive
      (.and (.matches .self .onBattlefield)
        (.cmp .eq (.count (.all .friendly .here [.ofType .unit, .notSelf])) (.const 1)))
      [.keyword .self ⟨.shield, .amount 3⟩]],
    status := .drafted }

-- BEGIN GENERATED VEN-118
/--
**Horns of the Dragon** — Unit · Order · Energy 6 · Might 6
Printings: VEN-118/166

> [Tank] (I must be assigned combat damage first.)
-/
def VEN_118.meta : CardDef :=
  { id := ⟨"VEN-118"⟩,
    name := "Horns of the Dragon",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨6, []⟩,
    might := some 6,
    keywords := [{ keyword := .tank }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Horns of the Dragon. -/
def VEN_118 : CardDef :=
  { VEN_118.meta with
    status := .drafted }

-- BEGIN GENERATED VEN-119
/--
**Keeper of Law** — Unit · Order · Energy 5 + Power 1 · Might 5
Printings: VEN-119/166

> I cost :rb_energy_2::rb_rune_order: less if you control a battlefield with exactly two units
> there.
-/
def VEN_119.meta : CardDef :=
  { id := ⟨"VEN-119"⟩,
    name := "Keeper of Law",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 5,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Keeper of Law: the effect is not written yet. -/
def VEN_119 : CardDef := VEN_119.meta

-- BEGIN GENERATED VEN-120
/--
**Masa, Crashing Thunder** — Unit · Order · Energy 4 · Might 4
Printings: VEN-120/166

> You may pay :rb_rune_order: as an additional cost to play me.
> When you play me, if you paid the additional cost, [Stun] an enemy unit at a battlefield. (It
> doesn't deal combat damage this turn.)
-/
def VEN_120.meta : CardDef :=
  { id := ⟨"VEN-120"⟩,
    name := "Masa, Crashing Thunder",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Bandle City"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Masa, Crashing Thunder. -/
def VEN_120 : CardDef :=
  { VEN_120.meta with
    additionalCost := some ⟨0, [.domain .order]⟩,
    abilities := [.triggered { Trigger.onSelf .play with condition := .paid }
        (.of [.targetOf .one .enemy .atBattlefield [.ofType .unit]]
        (.prim (.stun (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-121
/--
**Reluctant Leader** — Unit · Order · Energy 4 + Power 1 · Might 3
Printings: VEN-121/166

> When you play another unit, give me +2 :rb_might: this turn.
-/
def VEN_121.meta : CardDef :=
  { id := ⟨"VEN-121"⟩,
    name := "Reluctant Leader",
    types := [.unit],
    tags := [⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order]⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Reluctant Leader. -/
def VEN_121 : CardDef :=
  { VEN_121.meta with
    abilities := [.triggered { event := .play, subject := .all .friendly .anywhere [.ofType .unit, .notSelf] }
      (.of [] (.grant .self (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-122
/--
**Solari Sunhawk** — Unit · Order · Energy 3 · Might 3
Printings: VEN-122/166

> [Empower] :rb_energy_2: (:rb_energy_2:: Empower me. Use only if not Empowered.)
> [Empowered][>] I have +1 :rb_might: and [Deflect 2]. (Opponents must pay
> :rb_rune_rainbow::rb_rune_rainbow: to choose me with a spell or ability.)
-/
def VEN_122.meta : CardDef :=
  { id := ⟨"VEN-122"⟩,
    name := "Solari Sunhawk",
    types := [.unit],
    tags := [⟨"Bird"⟩, ⟨"Mount Targon"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .empower, arg := .cost ⟨2, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Solari Sunhawk. -/
def VEN_122 : CardDef :=
  { VEN_122.meta with
    abilities := [.passive (.empowered .self)
      [.mightPlus .self (.const 1), .keyword .self ⟨.deflect, .amount 2⟩]],
    status := .drafted }

-- BEGIN GENERATED VEN-123
/--
**Soulspinner** — Unit · Order · Energy 3 · Might 3
Printings: VEN-123/166

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
-/
def VEN_123.meta : CardDef :=
  { id := ⟨"VEN-123"⟩,
    name := "Soulspinner",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Spider"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Soulspinner. -/
def VEN_123 : CardDef :=
  { VEN_123.meta with
    status := .drafted }

-- BEGIN GENERATED VEN-124
/--
**Escaped Grayback** — Unit · Order · Energy 3 · Might 3
Printings: VEN-124/166

> [Empower] — Kill a friendly unit (Pay the cost: Empower me. Use only if not Empowered.)
> [Empowered][>] I have +2 :rb_might:.
-/
def VEN_124.meta : CardDef :=
  { id := ⟨"VEN-124"⟩,
    name := "Escaped Grayback",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .empower }],
    sets := [⟨"VEN"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Escaped Grayback. -/
def VEN_124 : CardDef :=
  { VEN_124.meta with
    abilities := [.empower [.killFriendly .one (.ofList [.ofType .unit])] 1
        [.targetOf .one .friendly .anywhere [.ofType .unit]],
      .passive (.empowered .self) [.mightPlus .self (.const 2)]],
    status := .drafted }

-- BEGIN GENERATED VEN-125
/--
**Hungry Wolf** — Unit · Order · Energy 4 · Might 4
Printings: VEN-125/166

> :rb_rune_order:: Ready me and give me +1 :rb_might: this turn. Use only if you've chosen an
> enemy unit this turn and only once each turn.
-/
def VEN_125.meta : CardDef :=
  { id := ⟨"VEN-125"⟩,
    name := "Hungry Wolf",
    types := [.unit],
    tags := [⟨"Dog"⟩, ⟨"Freljord"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Hungry Wolf: the effect is not written yet. -/
def VEN_125 : CardDef := VEN_125.meta

-- BEGIN GENERATED VEN-126
/--
**Ki Barrier** — Spell · Order · Energy 2 + Power 1
Printings: VEN-126/166

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a unit. Prevent the next 7 damage that would be dealt to it this turn. (Opponents can
> assign it extra combat damage to kill it.)
-/
def VEN_126.meta : CardDef :=
  { id := ⟨"VEN-126"⟩,
    name := "Ki Barrier",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Ki Barrier. -/
def VEN_126 : CardDef :=
  { VEN_126.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
    (.preventNext (.slot 0) (.const 7) .thisTurn)),
    status := .drafted }

-- BEGIN GENERATED VEN-127
/--
**Lacerate** — Spell · Order · Energy 2 + Power 1
Printings: VEN-127/166

> Choose a unit. If it's [Empowered], disempower it. Then kill it if it has 3 :rb_might: or
> less.
> [Flow] :rb_energy_4::rb_rune_order::rb_rune_order: (You may play this from your trash for its
> Flow cost. Then banish it.)
-/
def VEN_127.meta : CardDef :=
  { id := ⟨"VEN-127"⟩,
    name := "Lacerate",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨4, [.domain .order, .domain .order]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Lacerate. -/
def VEN_127 : CardDef :=
  { VEN_127.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.prim (.disempower (.slot 0)),
        .ifThen (.matches (.slot 0) (.might .le (.const 3))) (.prim (.kill (.slot 0))) .nop])),
    status := .drafted }

-- BEGIN GENERATED VEN-128
/--
**Noxian Emissary** — Unit · Order · Energy 2 · Might 2
Printings: VEN-128/166

> [Empower] :rb_energy_1::rb_rune_order: (:rb_energy_1::rb_rune_order:: Empower me. Use only if
> not Empowered.)
> [Empowered][>][>>][Deathknell][>] Play two 1 :rb_might: Recruit unit tokens to your base.
> (When I die while Empowered, get the effect.)
-/
def VEN_128.meta : CardDef :=
  { id := ⟨"VEN-128"⟩,
    name := "Noxian Emissary",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .empower, arg := .cost ⟨1, [.domain .order]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Noxian Emissary. -/
def VEN_128 : CardDef :=
  { VEN_128.meta with
    abilities := [.triggered { event := .die, condition := .leftEmpowered }
      (.of [] (.prim (.create "Recruit" (.const 2) .atBase false))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-129
/--
**Sacred Protector** — Unit · Order · Energy 4 + Power 1 · Might 6
Printings: VEN-129/166

> I don't deal combat damage unless I'm at a battlefield with exactly one other unit you
> control.
-/
def VEN_129.meta : CardDef :=
  { id := ⟨"VEN-129"⟩,
    name := "Sacred Protector",
    types := [.unit],
    tags := [⟨"Fae"⟩, ⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨4, [.domain .order]⟩,
    might := some 6,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Sacred Protector: the effect is not written yet. -/
def VEN_129 : CardDef := VEN_129.meta

-- BEGIN GENERATED VEN-130
/--
**Aurok General** — Unit · Order · Energy 5 · Might 5
Printings: VEN-130/166

> [Empower] :rb_energy_3::rb_rune_order: (:rb_energy_3::rb_rune_order:: Empower me. Use only if
> not Empowered.)
> [Empowered][>] Your units that are [Empowered] have +2 :rb_might: (including me).
-/
def VEN_130.meta : CardDef :=
  { id := ⟨"VEN-130"⟩,
    name := "Aurok General",
    types := [.unit],
    tags := [⟨"Trifarian"⟩, ⟨"Noxus"⟩],
    domains := [.order],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .empower, arg := .cost ⟨3, [.domain .order]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Aurok General. -/
def VEN_130 : CardDef :=
  { VEN_130.meta with
    abilities := [.passive (.empowered .self)
      [.mightPlus (.all .friendly .anywhere [.ofType .unit, .empowered]) (.const 2)]],
    status := .drafted }

-- BEGIN GENERATED VEN-131
/--
**Decree of Unity** — Spell · Order · Energy 2 + Power 1
Printings: VEN-131/166

> Kill an enemy Chaos (:rb_rune_chaos:) unit or gear.
-/
def VEN_131.meta : CardDef :=
  { id := ⟨"VEN-131"⟩,
    name := "Decree of Unity",
    types := [.spell],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Decree of Unity. -/
def VEN_131 : CardDef :=
  { VEN_131.meta with
    spellEffect := some (.of
      [.targetOf .one .enemy .anywhere [.domain .chaos, .either (.ofType .unit) (.ofType .gear)]]
      (.prim (.kill (.slot 0)))),
    status := .drafted }

-- BEGIN GENERATED VEN-132
/--
**Fallen Feline** — Unit · Order · Energy 2 + Power 1 · Might 3
Printings: VEN-132/166

> When you play me, name a spell.
> While I'm at a battlefield, opponents can't play spells with that name.
-/
def VEN_132.meta : CardDef :=
  { id := ⟨"VEN-132"⟩,
    name := "Fallen Feline",
    types := [.unit],
    tags := [⟨"Cat"⟩, ⟨"Piltover"⟩],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    might := some 3,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Fallen Feline: the effect is not written yet. -/
def VEN_132 : CardDef := VEN_132.meta

-- BEGIN GENERATED VEN-133
/--
**Glowstone** — Gear · Order · Energy 2
Printings: VEN-133/166

> [Empower] :rb_rune_rainbow::rb_rune_rainbow: (:rb_rune_rainbow::rb_rune_rainbow:: Empower me.
> Use only if not Empowered.)
> Disempower this, :rb_exhaust:: Choose a player. They gain control of this and recall it. (Send
> it to their base.)
> At the end of your turn, kill this and deal 5 to all units you control.
-/
def VEN_133.meta : CardDef :=
  { id := ⟨"VEN-133"⟩,
    name := "Glowstone",
    types := [.gear],
    domains := [.order],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .empower, arg := .cost ⟨0, [.any, .any]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Glowstone: the effect is not written yet. -/
def VEN_133 : CardDef := VEN_133.meta

-- BEGIN GENERATED VEN-134
/--
**Kayle, Justified** — Unit · Order · Energy 3 · Might 3
Printings: VEN-134/166, VEN-185/166

> [Empower] :rb_energy_3: (:rb_energy_3:: Empower me.)
> I can be [Empowered] up to three times.
> I have +2 :rb_might: for each time I'm [Empowered].
> While I'm [Empowered] three times, I have [Deflect 3] and [Ganking].
-/
def VEN_134.meta : CardDef :=
  { id := ⟨"VEN-134"⟩,
    name := "Kayle",
    subtitle := some "Justified",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩, ⟨"Kayle"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .empower, arg := .cost ⟨3, []⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Kayle, Justified. -/
def VEN_134 : CardDef :=
  { VEN_134.meta with
    empowerLimit := 3,
    abilities := [.passive .always [.mightPlus .self (.mul (.const 2) .empowerCount)],
      .passive (.cmp .eq .empowerCount (.const 3))
        [.keyword .self ⟨.deflect, .amount 3⟩, .keyword .self ⟨.ganking, .none⟩]],
    status := .drafted }

-- BEGIN GENERATED VEN-135
/--
**Kennen, Keeper of Balance** — Unit · Order · Energy 3 · Might 2
Printings: VEN-135/166, VEN-135a/166

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me or I attack, you may pay :rb_energy_2: to [Stun] a unit. (It doesn't deal
> combat damage this turn.)
> While there's a stunned enemy unit here, I have +2 :rb_might:.
-/
def VEN_135.meta : CardDef :=
  { id := ⟨"VEN-135"⟩,
    name := "Kennen",
    subtitle := some "Keeper of Balance",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Ionia"⟩, ⟨"Kennen"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 2,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Kennen, Keeper of Balance: the effect is not written yet. -/
def VEN_135 : CardDef := VEN_135.meta

-- BEGIN GENERATED VEN-136
/--
**Ambessa, Respected and Feared** — Unit · Order · Energy 5 · Might 5
Printings: VEN-136/166, VEN-136a/166, VEN-187/166

> [Empower] :rb_energy_1::rb_rune_order::rb_rune_order:
> (:rb_energy_1::rb_rune_order::rb_rune_order:: Empower me. Use only if not Empowered.)
> [Empowered][>] I have [Assault 2]. (+2 :rb_might: while I'm an attacker.)
> [Empowered][>] When I attack, kill an enemy unit here with less Might than me.
-/
def VEN_136.meta : CardDef :=
  { id := ⟨"VEN-136"⟩,
    name := "Ambessa",
    subtitle := some "Respected and Feared",
    types := [.unit],
    tags := [⟨"Noxus"⟩, ⟨"Ambessa"⟩],
    domains := [.order],
    cost := some ⟨5, []⟩,
    might := some 5,
    keywords := [{ keyword := .empower, arg := .cost ⟨1, [.domain .order, .domain .order]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Ambessa, Respected and Feared. -/
def VEN_136 : CardDef :=
  { VEN_136.meta with
    abilities := [.passive (.empowered .self) [.keyword .self ⟨.assault, .amount 2⟩],
      .triggered { event := .attack, condition := .empowered .self }
        (.of [.targetOf .one .enemy .here [.ofType .unit, .mightLtOf .self]]
          (.prim (.kill (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-137
/--
**Shady Spectacles** — Gear · Order · Energy 4 · Might 0
Printings: VEN-137/166

> [Equip] :rb_energy_1::rb_rune_order: (:rb_energy_1::rb_rune_order:: Attach this to a unit you
> control.)
> As this is attached to a unit, choose another friendly unit. The equipped unit becomes a copy
> of that unit for as long as this is attached to it.

Effect (given to the unit it is attached to):

> (I am a copy of the chosen unit.)
-/
def VEN_137.meta : CardDef :=
  { id := ⟨"VEN-137"⟩,
    name := "Shady Spectacles",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 0,
    mightBonus := some 0,
    keywords := [{ keyword := .equip, arg := .cost ⟨1, [.domain .order]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shady Spectacles: the effect is not written yet. -/
def VEN_137 : CardDef := VEN_137.meta

-- BEGIN GENERATED VEN-138
/--
**Shen, Leader of the Kinkou Order** — Unit · Order · Energy 6 + Power 2 · Might 7
Printings: VEN-138/166, VEN-138a/166

> [Shield] (+1 :rb_might: while I'm a defender.)
> When I hold, if there is exactly one other unit you control here, you score 1 point.
-/
def VEN_138.meta : CardDef :=
  { id := ⟨"VEN-138"⟩,
    name := "Shen",
    subtitle := some "Leader of the Kinkou Order",
    types := [.unit],
    tags := [⟨"Shen"⟩, ⟨"Ionia"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order, .domain .order]⟩,
    might := some 7,
    keywords := [{ keyword := .shield, arg := .amount 1 }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shen, Leader of the Kinkou Order. -/
def VEN_138 : CardDef :=
  { VEN_138.meta with
    abilities := [.triggered
      { event := .hold,
        condition := .cmp .eq (.count (.all .friendly .here [.ofType .unit, .notSelf])) (.const 1) }
      (.of [] (.prim (.score .you (.const 1)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-139
/--
**Rogue Assassin** — Legend · Fury/Calm
Printings: VEN-139/166, VEN-189*/166, VEN-189/166

> [Empower] :rb_energy_3::rb_rune_rainbow: (:rb_energy_3::rb_rune_rainbow:: Empower this. Use
> only if not Empowered.)
> [Action][>] :rb_exhaust:: If it's your turn, move a friendly unit in a showdown to base and if
> I'm [Empowered], ready it.
-/
def VEN_139.meta : CardDef :=
  { id := ⟨"VEN-139"⟩,
    name := "Rogue Assassin",
    types := [.legend],
    tags := [⟨"Akali"⟩],
    domains := [.fury, .calm],
    keywords := [{ keyword := .empower, arg := .cost ⟨3, [.any]⟩ },
      { keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Rogue Assassin: the effect is not written yet. -/
def VEN_139 : CardDef := VEN_139.meta

-- BEGIN GENERATED VEN-140
/--
**Shuriken Flip** — Spell · Fury/Calm · Energy 1 + Power 1
Printings: VEN-140/166

> Deal 2 to up to one enemy unit at a battlefield, then move a friendly unit.
> [Flow] :rb_energy_3::rb_rune_rainbow: (You may play this from your trash for its Flow cost.
> Then banish it.)
-/
def VEN_140.meta : CardDef :=
  { id := ⟨"VEN-140"⟩,
    name := "Shuriken Flip",
    types := [.spell],
    tags := [⟨"Akali"⟩],
    domains := [.fury, .calm],
    cost := some ⟨1, [.any]⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨3, [.any]⟩ }],
    sets := [⟨"VEN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Shuriken Flip: the effect is not written yet. -/
def VEN_140 : CardDef := VEN_140.meta

-- BEGIN GENERATED VEN-141
/--
**Butcher of the Sands** — Legend · Fury/Body
Printings: VEN-141/166, VEN-190*/166, VEN-190/166

> [Reaction][>] :rb_rune_rainbow::rb_rune_rainbow:, :rb_exhaust:: [Add] :rb_energy_2:. Spend
> this Energy only to play units or activated abilities of units.
-/
def VEN_141.meta : CardDef :=
  { id := ⟨"VEN-141"⟩,
    name := "Butcher of the Sands",
    types := [.legend],
    tags := [⟨"Renekton"⟩],
    domains := [.fury, .body],
    keywords := [{ keyword := .reaction }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Butcher of the Sands: the effect is not written yet. -/
def VEN_141 : CardDef := VEN_141.meta

-- BEGIN GENERATED VEN-142
/--
**Dominus** — Spell · Fury/Body · Energy 4
Printings: VEN-142/166

> [Action] (Play on your turn or in showdowns.)
> This turn, double a unit's Might and give it ":rb_rune_rainbow::rb_rune_rainbow:: Ready me."
-/
def VEN_142.meta : CardDef :=
  { id := ⟨"VEN-142"⟩,
    name := "Dominus",
    types := [.spell],
    tags := [⟨"Renekton"⟩],
    domains := [.fury, .body],
    cost := some ⟨4, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Dominus: the effect is not written yet. -/
def VEN_142 : CardDef := VEN_142.meta

-- BEGIN GENERATED VEN-143
/--
**Master of Shadows** — Legend · Fury/Chaos
Printings: VEN-143/166, VEN-191*/166, VEN-191/166

> When you banish a card you own, empower me. (I become Empowered if I'm not already.)
> [Action][>] Disempower me, :rb_exhaust:: Discard 1, then draw 1.
-/
def VEN_143.meta : CardDef :=
  { id := ⟨"VEN-143"⟩,
    name := "Master of Shadows",
    types := [.legend],
    tags := [⟨"Zed"⟩],
    domains := [.fury, .chaos],
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Master of Shadows: the effect is not written yet. -/
def VEN_143 : CardDef := VEN_143.meta

-- BEGIN GENERATED VEN-144
/--
**Death Mark** — Spell · Fury/Chaos · Energy 2 + Power 1
Printings: VEN-144/166

> [Burn 3]. (Put the top 3 cards of your Main Deck into your trash.)
> Play a 0 :rb_might: Shadow Clone unit token. (It has "When I attack, you may banish a unit
> from your trash. If you do, give me [Assault 4] this turn.")
> [Flow] :rb_energy_1::rb_rune_rainbow::rb_rune_rainbow: (You may play this from your trash for
> its Flow cost. Then banish it.)
-/
def VEN_144.meta : CardDef :=
  { id := ⟨"VEN-144"⟩,
    name := "Death Mark",
    types := [.spell],
    tags := [⟨"Zed"⟩],
    domains := [.fury, .chaos],
    cost := some ⟨2, [.any]⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨1, [.any, .any]⟩ }],
    sets := [⟨"VEN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Death Mark: the effect is not written yet. -/
def VEN_144 : CardDef := VEN_144.meta

-- BEGIN GENERATED VEN-145
/--
**Curator of the Sands** — Legend · Calm/Mind
Printings: VEN-145/166, VEN-192*/166, VEN-192/166

> When you play a unit, gear, or activated ability with Energy cost :rb_energy_7: or more, you
> may exhaust me to ready up to 2 runes.
-/
def VEN_145.meta : CardDef :=
  { id := ⟨"VEN-145"⟩,
    name := "Curator of the Sands",
    types := [.legend],
    tags := [⟨"Nasus"⟩],
    domains := [.calm, .mind],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Curator of the Sands: the effect is not written yet. -/
def VEN_145 : CardDef := VEN_145.meta

-- BEGIN GENERATED VEN-146
/--
**Siphoning Strike** — Spell · Calm/Mind · Energy 4
Printings: VEN-146/166

> Deal 4 to a unit at a battlefield. If you control 7 or more runes, deal 7 to it instead. When
> it dies this turn, channel 1 rune exhausted.
-/
def VEN_146.meta : CardDef :=
  { id := ⟨"VEN-146"⟩,
    name := "Siphoning Strike",
    types := [.spell],
    tags := [⟨"Nasus"⟩],
    domains := [.calm, .mind],
    cost := some ⟨4, []⟩,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Siphoning Strike: the effect is not written yet. -/
def VEN_146 : CardDef := VEN_146.meta

-- BEGIN GENERATED VEN-147
/--
**Eye of Twilight** — Legend · Calm/Order
Printings: VEN-147/166, VEN-193*/166, VEN-193/166

> [Action][>] :rb_exhaust:: Give a friendly unit [Tank] this turn. (It must be assigned combat
> damage first.)
-/
def VEN_147.meta : CardDef :=
  { id := ⟨"VEN-147"⟩,
    name := "Eye of Twilight",
    types := [.legend],
    tags := [⟨"Shen"⟩],
    domains := [.calm, .order],
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Eye of Twilight. -/
def VEN_147 : CardDef :=
  { VEN_147.meta with
    abilities := [.activated [.exhaustSelf] .action
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.keyword .it ⟨.tank, .none⟩) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-148
/--
**Shadow Dash** — Spell · Calm/Order · Energy 2 + Power 1
Printings: VEN-148/166

> Move an enemy unit to a battlefield where you have units. If you have exactly two units there,
> they each get +1 :rb_might: this turn.
> [Flow] :rb_energy_5::rb_rune_rainbow::rb_rune_rainbow: (You may play this from your trash for
> its Flow cost. Then banish it.)
-/
def VEN_148.meta : CardDef :=
  { id := ⟨"VEN-148"⟩,
    name := "Shadow Dash",
    types := [.spell],
    tags := [⟨"Shen"⟩],
    domains := [.calm, .order],
    cost := some ⟨2, [.any]⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨5, [.any, .any]⟩ }],
    sets := [⟨"VEN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Shadow Dash: the effect is not written yet. -/
def VEN_148 : CardDef := VEN_148.meta

-- BEGIN GENERATED VEN-149
/--
**Defender of Tomorrow** — Legend · Mind/Body
Printings: VEN-149/166, VEN-194*/166, VEN-194/166

> [Empower] :rb_energy_2::rb_rune_rainbow::rb_rune_rainbow:
> (:rb_energy_2::rb_rune_rainbow::rb_rune_rainbow:: Empower me. Use only if not Empowered.)
> :rb_energy_1:, :rb_exhaust:: Ready a gear.
> [Empowered][>] :rb_energy_1:, :rb_exhaust:: Ready 2 gear.
-/
def VEN_149.meta : CardDef :=
  { id := ⟨"VEN-149"⟩,
    name := "Defender of Tomorrow",
    types := [.legend],
    tags := [⟨"Jayce"⟩],
    domains := [.mind, .body],
    keywords := [{ keyword := .empower, arg := .cost ⟨2, [.any, .any]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Defender of Tomorrow. -/
def VEN_149 : CardDef :=
  { VEN_149.meta with
    abilities := [.activated [.pay ⟨1, []⟩, .exhaustSelf] .normal
      (.of [.targetOf .one .any .anywhere [.ofType .gear]]
        (.prim (.ready (.slot 0)))) .unlimited,
      .activated [.pay ⟨1, []⟩, .exhaustSelf] .normal
        (.of [.targetOf .one .any .anywhere [.ofType .gear],
          .targetOf .one .any .anywhere [.ofType .gear, .not (.sameAs (.slot 0))]]
          (.ifThen (.empowered .self) (.prim (.ready (.slotsFrom 0))) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-150
/--
**Acceleration Gate** — Spell · Mind/Body · Energy 3 + Power 1
Printings: VEN-150/166

> Ready up to 4 units, gear, and/or runes.
-/
def VEN_150.meta : CardDef :=
  { id := ⟨"VEN-150"⟩,
    name := "Acceleration Gate",
    types := [.spell],
    tags := [⟨"Jayce"⟩],
    domains := [.mind, .body],
    cost := some ⟨3, [.any]⟩,
    sets := [⟨"VEN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Acceleration Gate. -/
def VEN_150 : CardDef :=
  { VEN_150.meta with
    spellEffect := some (.of [.targetOf (.upTo 4) .any .anywhere
      [.either (.ofType .unit) (.either (.ofType .gear) (.ofType .rune))]]
      (.prim (.ready (.slotsFrom 0)))),
    status := .drafted }

-- BEGIN GENERATED VEN-151
/--
**Soul's Reflection** — Legend · Mind/Chaos
Printings: VEN-151/166, VEN-195*/166, VEN-195/166

> When you empower something else, empower me. (I become Empowered if I'm not already.)
> Disempower me, :rb_exhaust:: Give a unit at a battlefield -2 :rb_might: this turn.
-/
def VEN_151.meta : CardDef :=
  { id := ⟨"VEN-151"⟩,
    name := "Soul's Reflection",
    types := [.legend],
    tags := [⟨"Mel"⟩],
    domains := [.mind, .chaos],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Soul's Reflection. -/
def VEN_151 : CardDef :=
  { VEN_151.meta with
    abilities := [.triggered
      { event := .becomeEmpowered, subject := .all .friendly .anywhere [.notSelf] }
      (.of [] (.prim (.empower .self))) .unlimited,
      .activated [.disempowerSelf, .exhaustSelf] .normal
        (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
          (.grant (.slot 0) (.mightMinus .it (.const 2)) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-152
/--
**Rebuttal** — Spell · Mind/Chaos · Energy 1 + Power 1
Printings: VEN-152/166

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a spell with Energy cost no more than :rb_energy_4:.  You may pay :rb_rune_rainbow:. If
> you do, gain control of it and you may make new choices for it. Otherwise, counter it.
-/
def VEN_152.meta : CardDef :=
  { id := ⟨"VEN-152"⟩,
    name := "Rebuttal",
    types := [.spell],
    tags := [⟨"Mel"⟩],
    domains := [.mind, .chaos],
    cost := some ⟨1, [.any]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"VEN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Rebuttal: the effect is not written yet. -/
def VEN_152 : CardDef := VEN_152.meta

-- BEGIN GENERATED VEN-153
/--
**Matriarch of War** — Legend · Body/Order
Printings: VEN-153/166, VEN-196*/166, VEN-196/166

> When you empower something else, empower me. (I become Empowered if I'm not already.)
> Disempower me, :rb_rune_rainbow:, :rb_exhaust:: Ready a unit.
-/
def VEN_153.meta : CardDef :=
  { id := ⟨"VEN-153"⟩,
    name := "Matriarch of War",
    types := [.legend],
    tags := [⟨"Ambessa"⟩],
    domains := [.body, .order],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Matriarch of War. -/
def VEN_153 : CardDef :=
  { VEN_153.meta with
    abilities := [.triggered
      { event := .becomeEmpowered, subject := .all .friendly .anywhere [.notSelf] }
      (.of [] (.prim (.empower .self))) .unlimited,
      .activated [.disempowerSelf, .pay ⟨0, [.any]⟩, .exhaustSelf] .normal
        (.of [.targetOf .one .any .anywhere [.ofType .unit]]
          (.prim (.ready (.slot 0)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-154
/--
**Public Execution** — Spell · Body/Order · Energy 2 + Power 1
Printings: VEN-154/166

> Choose a friendly unit. Kill an enemy unit with less Might than it.
> [Flow] :rb_energy_5::rb_rune_rainbow::rb_rune_rainbow: (You may play this from your trash for
> its Flow cost. Then banish it.)
-/
def VEN_154.meta : CardDef :=
  { id := ⟨"VEN-154"⟩,
    name := "Public Execution",
    types := [.spell],
    tags := [⟨"Ambessa"⟩],
    domains := [.body, .order],
    cost := some ⟨2, [.any]⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨5, [.any, .any]⟩ }],
    sets := [⟨"VEN"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Public Execution. -/
def VEN_154 : CardDef :=
  { VEN_154.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
      .targetOf .one .enemy .anywhere [.ofType .unit, .mightLtOf (.slot 0)]]
      (.prim (.kill (.slot 1)))),
    status := .drafted }

-- BEGIN GENERATED VEN-155
/--
**Heart of the Tempest** — Legend · Order/Chaos
Printings: VEN-155/166, VEN-197*/166, VEN-197/166

> When you play a card from anywhere other than your hand, empower me.
> [Action][>] Disempower me, :rb_exhaust:: Give a unit [Assault 2] this turn. (+2 :rb_might:
> while it's an attacker.)
-/
def VEN_155.meta : CardDef :=
  { id := ⟨"VEN-155"⟩,
    name := "Heart of the Tempest",
    types := [.legend],
    tags := [⟨"Yordle"⟩, ⟨"Kennen"⟩],
    domains := [.order, .chaos],
    keywords := [{ keyword := .action }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Heart of the Tempest. -/
def VEN_155 : CardDef :=
  { VEN_155.meta with
    abilities := [.triggered
      { event := .play, subject := .all .friendly .anywhere [.playedFromElsewhere] }
      (.of [] (.prim (.empower .self))) .unlimited,
      .activated [.disempowerSelf, .exhaustSelf] .action
        (.of [.targetOf .one .any .anywhere [.ofType .unit]]
          (.grant (.slot 0) (.keyword .it ⟨.assault, .amount 2⟩) .thisTurn)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-156
/--
**Lightning Rush** — Spell · Order/Chaos · Energy 1
Printings: VEN-156/166

> Look at the top 3 cards of your Main Deck. You may choose a card from among them and draw it.
> Put the rest into your trash.
> [Flow] :rb_energy_2::rb_rune_rainbow: (You may play this from your trash for its Flow cost.
> Then banish it.)
-/
def VEN_156.meta : CardDef :=
  { id := ⟨"VEN-156"⟩,
    name := "Lightning Rush",
    types := [.spell],
    tags := [⟨"Kennen"⟩],
    domains := [.order, .chaos],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .flow, arg := .cost ⟨2, [.any]⟩ }],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Lightning Rush: the effect is not written yet. -/
def VEN_156 : CardDef := VEN_156.meta

-- BEGIN GENERATED VEN-157
/--
**Dragon Roost** — Battlefield · Colorless
Printings: VEN-157/166

> Any player may pay :rb_rune_rainbow::rb_rune_rainbow: as an additional cost to play a Dragon.
> If they do, they play it to this battlefield.
-/
def VEN_157.meta : CardDef :=
  { id := ⟨"VEN-157"⟩,
    name := "Dragon Roost",
    types := [.battlefield],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Dragon Roost: the effect is not written yet. -/
def VEN_157 : CardDef := VEN_157.meta

-- BEGIN GENERATED VEN-158
/--
**Heisho, Shell of the World** — Battlefield · Colorless
Printings: VEN-158/166

> Players ignore [Deflect] while paying for spells and abilities choosing something here.
-/
def VEN_158.meta : CardDef :=
  { id := ⟨"VEN-158"⟩,
    name := "Heisho, Shell of the World",
    types := [.battlefield],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Heisho, Shell of the World: the effect is not written yet. -/
def VEN_158 : CardDef := VEN_158.meta

-- BEGIN GENERATED VEN-159
/--
**Kinkou Temple** — Battlefield · Colorless
Printings: VEN-159/166

> Units here with [Tank] have +1 :rb_might:.
-/
def VEN_159.meta : CardDef :=
  { id := ⟨"VEN-159"⟩,
    name := "Kinkou Temple",
    types := [.battlefield],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Kinkou Temple: the effect is not written yet. -/
def VEN_159 : CardDef := VEN_159.meta

-- BEGIN GENERATED VEN-160
/--
**Mystic Vortex** — Battlefield · Colorless
Printings: VEN-160/166

> During showdowns here, cards with [Reaction] cost :rb_rune_rainbow: more to play. (Hidden
> cards have [Reaction].)
-/
def VEN_160.meta : CardDef :=
  { id := ⟨"VEN-160"⟩,
    name := "Mystic Vortex",
    types := [.battlefield],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Mystic Vortex: the effect is not written yet. -/
def VEN_160 : CardDef := VEN_160.meta

-- BEGIN GENERATED VEN-161
/--
**Piltovan Forge** — Battlefield · Colorless
Printings: VEN-161/166

> While you control this battlefield, the first friendly gear activated ability played each turn
> costs :rb_energy_1: less.
-/
def VEN_161.meta : CardDef :=
  { id := ⟨"VEN-161"⟩,
    name := "Piltovan Forge",
    types := [.battlefield],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Piltovan Forge: the effect is not written yet. -/
def VEN_161 : CardDef := VEN_161.meta

-- BEGIN GENERATED VEN-162
/--
**Protective Sands** — Battlefield · Colorless
Printings: VEN-162/166

> When you conquer here, if you control 4 or fewer runes, you may pay :rb_energy_1: to draw 1.
-/
def VEN_162.meta : CardDef :=
  { id := ⟨"VEN-162"⟩,
    name := "Protective Sands",
    types := [.battlefield],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Protective Sands. -/
def VEN_162 : CardDef :=
  { VEN_162.meta with
    abilities := [.triggered
      { event := .youConquer,
        condition := .cmp .le (.count (.all .friendly .anywhere [.ofType .rune])) (.const 4) }
      (.of [] (.ifThen (.canPay ⟨1, []⟩)
        (.may (.seqOf [.prim (.pay ⟨1, []⟩), .prim (.draw .you (.const 1))])) .nop)) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-163
/--
**Risen Altar** — Battlefield · Colorless
Printings: VEN-163/166

> [Empower] costs of your units here cost :rb_energy_1: or :rb_rune_rainbow: less.
-/
def VEN_163.meta : CardDef :=
  { id := ⟨"VEN-163"⟩,
    name := "Risen Altar",
    types := [.battlefield],
    keywords := [{ keyword := .empower }],
    sets := [⟨"VEN"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Risen Altar: the effect is not written yet. -/
def VEN_163 : CardDef := VEN_163.meta

-- BEGIN GENERATED VEN-164
/--
**Sandswept Tomb** — Battlefield · Colorless
Printings: VEN-164/166

> Each spell that chooses one or more units here that are friendly to it costs :rb_rune_rainbow:
> less.
-/
def VEN_164.meta : CardDef :=
  { id := ⟨"VEN-164"⟩,
    name := "Sandswept Tomb",
    types := [.battlefield],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Sandswept Tomb: the effect is not written yet. -/
def VEN_164 : CardDef := VEN_164.meta

-- BEGIN GENERATED VEN-165
/--
**Shadow Temple** — Battlefield · Colorless
Printings: VEN-165/166

> When you hold here, [Burn 3]. (Put the top 3 cards of your Main Deck into your trash.)
-/
def VEN_165.meta : CardDef :=
  { id := ⟨"VEN-165"⟩,
    name := "Shadow Temple",
    types := [.battlefield],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Shadow Temple. -/
def VEN_165 : CardDef :=
  { VEN_165.meta with
    abilities := [.triggered (.onSelf .youHold)
      (.of [] (.prim (.burn .you (.const 3)))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED VEN-166
/--
**Threshold of the Gray** — Battlefield · Colorless
Printings: VEN-166/166

> When combat starts here, the attacker and defender each [Add] :rb_energy_1:.
-/
def VEN_166.meta : CardDef :=
  { id := ⟨"VEN-166"⟩,
    name := "Threshold of the Gray",
    types := [.battlefield],
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Threshold of the Gray: the effect is not written yet. -/
def VEN_166 : CardDef := VEN_166.meta

-- BEGIN GENERATED VEN-T04
/--
**Recruit** — Unit · Colorless · Might 1
Printings: VEN-T04

> (no text)
-/
def VEN_T04.meta : CardDef :=
  { id := ⟨"VEN-T04"⟩,
    name := "Recruit",
    types := [.unit],
    tags := [⟨"Recruit"⟩],
    might := some 1,
    sets := [⟨"VEN"⟩] }
-- END GENERATED

/-- Recruit. -/
def VEN_T04 : CardDef :=
  { VEN_T04.meta with
    status := .drafted }

-- BEGIN GENERATED LIST
/-- The cards first printed in Vendetta. -/
def cards : List CardDef :=
  [VEN_001,
    VEN_002,
    VEN_003,
    VEN_004,
    VEN_005,
    VEN_006,
    VEN_007,
    VEN_008,
    VEN_009,
    VEN_010,
    VEN_011,
    VEN_012,
    VEN_013,
    VEN_014,
    VEN_015,
    VEN_016,
    VEN_017,
    VEN_018,
    VEN_019,
    VEN_020,
    VEN_021,
    VEN_022,
    VEN_023,
    VEN_024,
    VEN_025,
    VEN_026,
    VEN_027,
    VEN_028,
    VEN_029,
    VEN_030,
    VEN_031,
    VEN_032,
    VEN_033,
    VEN_034,
    VEN_035,
    VEN_036,
    VEN_037,
    VEN_038,
    VEN_039,
    VEN_040,
    VEN_041,
    VEN_042,
    VEN_043,
    VEN_044,
    VEN_045,
    VEN_046,
    VEN_047,
    VEN_048,
    VEN_049,
    VEN_050,
    VEN_051,
    VEN_052,
    VEN_053,
    VEN_054,
    VEN_055,
    VEN_056,
    VEN_057,
    VEN_058,
    VEN_059,
    VEN_060,
    VEN_061,
    VEN_062,
    VEN_063,
    VEN_064,
    VEN_065,
    VEN_066,
    VEN_067,
    VEN_068,
    VEN_069,
    VEN_070,
    VEN_071,
    VEN_072,
    VEN_073,
    VEN_074,
    VEN_075,
    VEN_076,
    VEN_077,
    VEN_078,
    VEN_079,
    VEN_080,
    VEN_081,
    VEN_082,
    VEN_083,
    VEN_084,
    VEN_085,
    VEN_086,
    VEN_087,
    VEN_088,
    VEN_089,
    VEN_090,
    VEN_091,
    VEN_092,
    VEN_093,
    VEN_094,
    VEN_095,
    VEN_096,
    VEN_097,
    VEN_098,
    VEN_099,
    VEN_100,
    VEN_101,
    VEN_102,
    VEN_103,
    VEN_104,
    VEN_105,
    VEN_106,
    VEN_107,
    VEN_108,
    VEN_109,
    VEN_110,
    VEN_111,
    VEN_112,
    VEN_113,
    VEN_114,
    VEN_115,
    VEN_116,
    VEN_117,
    VEN_118,
    VEN_119,
    VEN_120,
    VEN_121,
    VEN_122,
    VEN_123,
    VEN_124,
    VEN_125,
    VEN_126,
    VEN_127,
    VEN_128,
    VEN_129,
    VEN_130,
    VEN_131,
    VEN_132,
    VEN_133,
    VEN_134,
    VEN_135,
    VEN_136,
    VEN_137,
    VEN_138,
    VEN_139,
    VEN_140,
    VEN_141,
    VEN_142,
    VEN_143,
    VEN_144,
    VEN_145,
    VEN_146,
    VEN_147,
    VEN_148,
    VEN_149,
    VEN_150,
    VEN_151,
    VEN_152,
    VEN_153,
    VEN_154,
    VEN_155,
    VEN_156,
    VEN_157,
    VEN_158,
    VEN_159,
    VEN_160,
    VEN_161,
    VEN_162,
    VEN_163,
    VEN_164,
    VEN_165,
    VEN_166,
    VEN_T04]
-- END GENERATED LIST

end RiftboundCards.Vendetta

end
