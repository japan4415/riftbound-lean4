module

public import Riftbound.Card.CardDef

/-!
# Radiance (RAD)

The cards first printed in Radiance. Each card has a generated block (the official text and
the metadata) and, right after it, the part written by hand (the effect and the
implementation status). `scripts/gen_lean.py` rewrites the generated blocks only
(docs/card-data.md §4.1).
-/

@[expose] public section

namespace RiftboundCards.Radiance

open Riftbound

/-- Place the whole group of Bombs at a single Battlefield picked during resolution. -/
def playBombs (count : Nat) : Effect :=
  .prim (.createAt "Bomb" (.const count)
    (Selector.one .any .atBattlefield [.ofType .battlefield]) true)

-- BEGIN GENERATED RAD-001
/--
**Amateur Demolitionist** — Unit · Fury · Energy 2 · Might 1
Printings: RAD-001/167

> When you play me, play a Bomb gear token to a battlefield. (It has [Deploy]. When it dies,
> deal 2 to an enemy there and kill your other Bombs there.)
-/
def RAD_001.meta : CardDef :=
  { id := ⟨"RAD-001"⟩,
    name := "Amateur Demolitionist",
    types := [.unit],
    tags := [⟨"Bandle City"⟩, ⟨"Yordle"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 1,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Amateur Demolitionist. -/
def RAD_001 : CardDef :=
  { RAD_001.meta with
    abilities := [.triggered (.onSelf .play) (.of [] (playBombs 1)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-002
/--
**Banner of Conquest** — Gear · Fury · Energy 1 + Power 1
Printings: RAD-002/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> Friendly units here have [Assault]. (+1 :rb_might: while they're attackers.)
-/
def RAD_002.meta : CardDef :=
  { id := ⟨"RAD-002"⟩,
    name := "Banner of Conquest",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨1, [.domain .fury]⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Banner of Conquest. -/
def RAD_002 : CardDef :=
  { RAD_002.meta with
    abilities := [.passive .always
      [.keyword (.all .friendly .here [.ofType .unit]) ⟨.assault, .amount 1⟩]],
    status := .full }

-- BEGIN GENERATED RAD-003
/--
**Bilgewater Tracker** — Unit · Fury · Energy 3 · Might 3
Printings: RAD-003/167

> When you play me, deal 1 to each of up to 2 units.
-/
def RAD_003.meta : CardDef :=
  { id := ⟨"RAD-003"⟩,
    name := "Bilgewater Tracker",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Bilgewater Tracker. -/
def RAD_003 : CardDef :=
  { RAD_003.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf (.upTo 2) .any .anywhere [.ofType .unit]]
        (.prim (.deal (.slotsFrom 0) (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-004
/--
**Brawl** — Spell · Fury · Energy 3 + Power 1
Printings: RAD-004/167

> [Action] (Play on your turn or in showdowns.)
> Give a unit [Assault] this turn equal to its Might. (+1 :rb_might: for each instance of
> Assault while it's an attacker.)
-/
def RAD_004.meta : CardDef :=
  { id := ⟨"RAD-004"⟩,
    name := "Brawl",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Brawl grants Assault based on the chosen Unit's Might during resolution. -/
def RAD_004 : CardDef :=
  { RAD_004.meta with
    spellEffect := some {
      choices := [.targetOf .one .any .anywhere [.ofType .unit]]
      body := .grantNumericKeyword (.slot 0) .assault (.mightOf (.slot 0)) .thisTurn
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-005
/--
**Lingering Animus** — Unit · Fury · Energy 2 · Might 2
Printings: RAD-005/167

> I enter ready if a friendly unit or gear died this turn.
-/
def RAD_005.meta : CardDef :=
  { id := ⟨"RAD-005"⟩,
    name := "Lingering Animus",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Spirit"⟩],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Lingering Animus enters ready after the player's Unit or Gear died this turn. -/
def RAD_005 : CardDef :=
  { RAD_005.meta with
    abilities := [.passive (.noted .permanentDied) [.entersReady .self]],
    status := .full }

-- BEGIN GENERATED RAD-006
/--
**Scorched Earth** — Spell · Fury · Energy 4 + Power 1
Printings: RAD-006/167

> [Action] (Play on your turn or in showdowns.)
> Deal 5 damage split among units at a single battlefield.
-/
def RAD_006.meta : CardDef :=
  { id := ⟨"RAD-006"⟩,
    name := "Scorched Earth",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Scorched Earth: the effect is not written yet. -/
def RAD_006 : CardDef := RAD_006.meta

-- BEGIN GENERATED RAD-007
/--
**Rally for War** — Spell · Fury · Energy 3 + Power 1
Printings: RAD-007/167

> Choose an occupied enemy battlefield. Play three 1 :rb_might: Recruit unit tokens there.
-/
def RAD_007.meta : CardDef :=
  { id := ⟨"RAD-007"⟩,
    name := "Rally for War",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Rally for War. -/
def RAD_007 : CardDef :=
  { RAD_007.meta with
    spellEffect := some (.of
      [.targetOf .one .any .atBattlefield [.ofType .battlefield, .controlledByOpponent, .unitsHere .gt 0]]
      (.prim (.createAt "Recruit" (.const 3) (.slot 0) false))),
    status := .full }

-- BEGIN GENERATED RAD-008
/--
**War Scout** — Unit · Fury · Energy 3 · Might 2
Printings: RAD-008/167

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> When you play me, give a unit +2 :rb_might: this turn.
-/
def RAD_008.meta : CardDef :=
  { id := ⟨"RAD-008"⟩,
    name := "War Scout",
    types := [.unit],
    tags := [⟨"Demacia"⟩, ⟨"Yordle"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 2,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- War Scout. -/
def RAD_008 : CardDef :=
  { RAD_008.meta with
    abilities := [.triggered (.onSelf .play)
        (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-009
/--
**Antagonistic Apparatus** — Unit · Fury · Energy 6 + Power 1 · Might 3
Printings: RAD-009/167

> I enter ready.
> When you play me, play a ready 3 :rb_might: Mech unit token here.
-/
def RAD_009.meta : CardDef :=
  { id := ⟨"RAD-009"⟩,
    name := "Antagonistic Apparatus",
    types := [.unit],
    tags := [⟨"Bandle City"⟩, ⟨"Yordle"⟩, ⟨"Mech"⟩],
    domains := [.fury],
    cost := some ⟨6, [.domain .fury]⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Antagonistic Apparatus. -/
def RAD_009 : CardDef :=
  { RAD_009.meta with
    abilities := [.passive .always [.entersReady .self],
      .triggered (.onSelf .play)
        (.of []
        (.prim (.create "Mech" (.const 1) .here true))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-010
/--
**Forbidden Technique** — Spell · Fury · Energy 2
Printings: RAD-010/167

> Ready a unit.
> When you play a card with Energy cost :rb_energy_7: or more, you may play this from your trash
> for :rb_energy_1::rb_rune_fury::rb_rune_fury:. Then banish this.
-/
def RAD_010.meta : CardDef :=
  { id := ⟨"RAD-010"⟩,
    name := "Forbidden Technique",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨2, []⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Forbidden Technique. -/
def RAD_010 : CardDef :=
  { RAD_010.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.prim (.ready (.slot 0)))),
    abilities := [.triggered { event := .playCardFromTrashAtEnergy 7, optional := true }
      (.of [] (.playSelfFromTrash ⟨1, [.domain .fury, .domain .fury]⟩ .banish)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-011
/--
**Incorrigible Construct** — Unit · Fury · Energy 4 · Might 4
Printings: RAD-011/167

> [Show Off] a Mech. (As you play me, you may reveal a Mech from hand or pick another friendly
> Mech.)
> I enter ready if you showed off.
-/
def RAD_011.meta : CardDef :=
  { id := ⟨"RAD-011"⟩,
    name := "Incorrigible Construct",
    types := [.unit],
    tags := [⟨"Piltover"⟩, ⟨"Mech"⟩],
    domains := [.fury],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .showOff, arg := .object "a Mech" }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Incorrigible Construct can show off a Mech to enter ready. -/
def RAD_011 : CardDef :=
  { RAD_011.meta with
    showOffRequirement := some { filters := .ofList [.tag ⟨"Mech"⟩] },
    abilities := [.passive .showedOff [.entersReady .self]],
    status := .full }

-- BEGIN GENERATED RAD-012
/--
**Runeblade Anvil** — Gear · Chaos · Energy 1
Printings: RAD-012/167

> When you play this or when this leaves the board, banish the top card of your Main Deck. Until
> your next Ending Phase, you may play that card. (You still pay its costs.)
> :rb_energy_2::rb_rune_chaos:, :rb_exhaust:: Kill this.
-/
def RAD_012.meta : CardDef :=
  { id := ⟨"RAD-012"⟩,
    name := "Runeblade Anvil",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Runeblade Anvil: the effect is not written yet. -/
def RAD_012 : CardDef := RAD_012.meta

-- BEGIN GENERATED RAD-013
/--
**Lost to the Sands** — Spell · Fury · Energy 3 + Power 1
Printings: RAD-013/167

> [Action] (Play on your turn or in showdowns.)
> Choose one —Deal 4 to a unit at a battlefield.Kill a gear.
-/
def RAD_013.meta : CardDef :=
  { id := ⟨"RAD-013"⟩,
    name := "Lost to the Sands",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨3, [.domain .fury]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Lost to the Sands damages a Unit at a Battlefield or kills Gear. -/
def RAD_013 : CardDef :=
  { RAD_013.meta with
    spellEffect := some { body := .nop, modes := [
      ⟨"Deal 4", [.targetOf .one .any .atBattlefield [.ofType .unit]], .prim (.deal (.slot 0) (.const 4))⟩,
      ⟨"Kill a gear", [.targetOf .one .any .anywhere [.ofType .gear]], .prim (.kill (.slot 0))⟩] },
    status := .full }

-- BEGIN GENERATED RAD-014
/--
**Shimmering Swimmer** — Unit · Fury · Energy 3 · Might 3
Printings: RAD-014/167

> You may kill a friendly unit or gear as an additional cost to play me.
> When you play me, if you paid the additional cost, deal 2 to a unit.
-/
def RAD_014.meta : CardDef :=
  { id := ⟨"RAD-014"⟩,
    name := "Shimmering Swimmer",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Shimmering Swimmer deals damage after its player pays for it by killing a permanent. -/
def RAD_014 : CardDef :=
  { RAD_014.meta with
    playExtra := some (.killUnitOrGear, false),
    abilities := [.triggered { Trigger.onSelf .play with condition := .paid }
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 2)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-016
/--
**Coalesced Energy** — Unit · Fury · Energy 4 + Power 2 · Might 4
Printings: RAD-016/167

> At the end of your turn, recycle all your runes, then channel 4 runes exhausted.
-/
def RAD_016.meta : CardDef :=
  { id := ⟨"RAD-016"⟩,
    name := "Coalesced Energy",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury, .domain .fury]⟩,
    might := some 4,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Coalesced Energy. -/
def RAD_016 : CardDef :=
  { RAD_016.meta with
    abilities := [.triggered { event := .at_ .endOfTurn, condition := .yourTurn }
      (.of [] (.seqOf [.recycleRunes, .prim (.channel .you (.const 0) (.const 4))])) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-017
/--
**Detonation Amplifier** — Gear · Fury · Energy 4 + Power 1
Printings: RAD-017/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> When you play this, you may kill another friendly unit or gear to draw 1.
> Friendly [Deathknell] effects here trigger an additional time.
-/
def RAD_017.meta : CardDef :=
  { id := ⟨"RAD-017"⟩,
    name := "Detonation Amplifier",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Detonation Amplifier. -/
def RAD_017 : CardDef :=
  { RAD_017.meta with
    abilities := [.triggered
      { event := .play
        optional := true
        cost := .killFriendly 1 (.ofList [.notSelf, .either (.ofType .unit) (.ofType .gear)]) }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited,
      .passive .always [.triggersExtra .deathknell .here]],
    status := .full }

-- BEGIN GENERATED RAD-018
/--
**Drakehound Packmaster** — Unit · Fury · Energy 9 + Power 2 · Might 9
Printings: RAD-018/167

> When you play me, reveal the top card of each opponent's Main Deck. Choose one and banish it,
> then play it, ignoring its cost. Recycle the rest.
-/
def RAD_018.meta : CardDef :=
  { id := ⟨"RAD-018"⟩,
    name := "Drakehound Packmaster",
    types := [.unit],
    domains := [.fury],
    cost := some ⟨9, [.domain .fury, .domain .fury]⟩,
    might := some 9,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Drakehound Packmaster: the effect is not written yet. -/
def RAD_018 : CardDef := RAD_018.meta

-- BEGIN GENERATED RAD-019
/--
**Firebrand Raider** — Unit · Fury · Energy 6 + Power 1 · Might 6
Printings: RAD-019/167

> I enter ready.
> When you play me, ready all enemy units.
> Other units enter ready.
> Units don't ready during the Awaken Phase.
-/
def RAD_019.meta : CardDef :=
  { id := ⟨"RAD-019"⟩,
    name := "Firebrand Raider",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.fury],
    cost := some ⟨6, [.domain .fury]⟩,
    might := some 6,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Firebrand Raider. -/
def RAD_019 : CardDef :=
  { RAD_019.meta with
    abilities := [
      .passive .always [.entersReady .self, .allUnitsEnterReady, .skipUnitAwaken],
      .triggered (.onSelf .play) (.of [] (.prim (.ready (.all .enemy .anywhere [.ofType .unit]))))
        .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-020
/--
**Mordekaiser, Twice Slain** — Unit · Fury · Energy 7 + Power 1 · Might 5
Printings: RAD-020/167, RAD-020a/167

> [Accelerate] (You may pay :rb_energy_1::rb_rune_fury: as an additional cost to have me enter
> ready.)
> [Assault 3] (+3 :rb_might: while I'm an attacker.)
> Once each turn, if I would die, you may kill a friendly unit to heal me, exhaust me, and
> recall me instead.
-/
def RAD_020.meta : CardDef :=
  { id := ⟨"RAD-020"⟩,
    name := "Mordekaiser",
    subtitle := some "Twice Slain",
    types := [.unit],
    tags := [⟨"Noxus"⟩, ⟨"Mordekaiser"⟩],
    domains := [.fury],
    cost := some ⟨7, [.domain .fury]⟩,
    might := some 5,
    keywords := [{ keyword := .accelerate },
      { keyword := .assault, arg := .amount 3 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Mordekaiser, Twice Slain: the effect is not written yet. -/
def RAD_020 : CardDef := RAD_020.meta

-- BEGIN GENERATED RAD-021
/--
**Ekko, Revolutionary** — Unit · Fury · Energy 5 + Power 1 · Might 4
Printings: RAD-021/167, RAD-021a/167, RAD-177/167

> I enter ready.
> [Assault] (+1 :rb_might: while I'm an attacker.)
> [Action][>] Discard 1, :rb_energy_1::rb_rune_fury:: Banish me, then play me to your base,
> ignoring my cost.
-/
def RAD_021.meta : CardDef :=
  { id := ⟨"RAD-021"⟩,
    name := "Ekko",
    subtitle := some "Revolutionary",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Ekko"⟩, ⟨"Zaun"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 4,
    keywords := [{ keyword := .assault, arg := .amount 1 },
      { keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Ekko enters ready and can pay to play himself again at his controller's base. -/
def RAD_021 : CardDef :=
  { RAD_021.meta with
    abilities := [.activated [.discard 1, .pay ⟨1, [.domain .fury]⟩] .action
      (.of [] (.prim (.banishReplay .self .toBase))) .unlimited,
      .passive .always [.entersReady .self]],
    status := .full }

-- BEGIN GENERATED RAD-022
/--
**Whirling Twirligig** — Gear · Fury · Energy 4 + Power 1
Printings: RAD-022/167

> :rb_exhaust:: Play a Gold gear token exhausted. (It has "[Reaction][>] Kill this,
> :rb_exhaust:: [Add] :rb_rune_rainbow:.")
> Kill a friendly gear, :rb_exhaust:: Play a 1 :rb_might: Recruit unit token.
> Kill a friendly unit, :rb_exhaust:: Play a 3 :rb_might: Mech unit token.
-/
def RAD_022.meta : CardDef :=
  { id := ⟨"RAD-022"⟩,
    name := "Whirling Twirligig",
    types := [.gear],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Exhaust to play Gold, or also kill a friendly Gear or Unit to play a Recruit or Mech. -/
def RAD_022 : CardDef :=
  { RAD_022.meta with
    abilities := [.activated [.exhaustSelf] .normal
        (.of [] (.prim (.create "Gold" (.const 1) .atBase false))) .unlimited,
      .activated [.killFriendlyPermanent (.ofList [.ofType .gear]), .exhaustSelf] .normal
        (.of [] (.prim (.playUnitToken "Recruit"))) .unlimited,
      .activated [.killFriendlyPermanent (.ofList [.ofType .unit]), .exhaustSelf] .normal
        (.of [] (.prim (.playUnitToken "Mech"))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-023
/--
**Ziggs, Short-Fused** — Unit · Fury · Energy 5 + Power 1 · Might 5
Printings: RAD-023/167, RAD-023a/167

> When you play me, play a Bomb gear token to a battlefield. (It has [Deploy]. When it dies,
> deal 2 to an enemy there and kill your other Bombs there.)
> Abilities of friendly gear deal 1 Bonus Damage.
-/
def RAD_023.meta : CardDef :=
  { id := ⟨"RAD-023"⟩,
    name := "Ziggs",
    subtitle := some "Short-Fused",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Ziggs"⟩, ⟨"Zaun"⟩, ⟨"Yordle"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 5,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Ziggs, Short-Fused. -/
def RAD_023 : CardDef :=
  { RAD_023.meta with
    abilities := [.triggered (.onSelf .play) (.of [] (playBombs 1)) .unlimited,
      .passive .always [.bonusAbilityDamage .gear (.const 1)]],
    status := .full }

-- BEGIN GENERATED RAD-024
/--
**Blossoming Dreamroot** — Gear · Calm · Energy 2
Printings: RAD-024/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> When you win a combat here, draw 1.
-/
def RAD_024.meta : CardDef :=
  { id := ⟨"RAD-024"⟩,
    name := "Blossoming Dreamroot",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Blossoming Dreamroot. -/
def RAD_024 : CardDef :=
  { RAD_024.meta with
    abilities := [.triggered (.onSelf .winCombat)
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-025
/--
**Consult the Heavens** — Spell · Calm · Energy 1
Printings: RAD-025/167

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a unit [Shield 2] this turn. (+2 :rb_might: while it's a defender.)
> [Predict]. (Look at the top card of your Main Deck. You may recycle it.)
-/
def RAD_025.meta : CardDef :=
  { id := ⟨"RAD-025"⟩,
    name := "Consult the Heavens",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Consult the Heavens. -/
def RAD_025 : CardDef :=
  { RAD_025.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.grant (.slot 0) (.keyword .it ⟨.shield, .amount 2⟩) .thisTurn,
        .prim (.predict (.const 1))])),
    status := .full }

-- BEGIN GENERATED RAD-026
/--
**Entrenched Boar** — Unit · Calm · Energy 2 · Might 2
Printings: RAD-026/167

> You may have me enter ready. If you do, I can't move this turn.
-/
def RAD_026.meta : CardDef :=
  { id := ⟨"RAD-026"⟩,
    name := "Entrenched Boar",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Entrenched Boar. -/
def RAD_026 : CardDef :=
  { RAD_026.meta with
    additionalCost := some Cost.zero,
    electReadyEntryNoMove := true,
    status := .full }

-- BEGIN GENERATED RAD-027
/--
**Iridescent Avian** — Unit · Calm · Energy 3 · Might 3
Printings: RAD-027/167

> :rb_exhaust:: [Buff] a unit. If it's already buffed, give it +2 :rb_might: this turn instead.
> (To buff a unit, give it a +1 :rb_might: buff if it doesn't have one.)
-/
def RAD_027.meta : CardDef :=
  { id := ⟨"RAD-027"⟩,
    name := "Iridescent Avian",
    types := [.unit],
    tags := [⟨"Ixtal"⟩, ⟨"Bird"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Iridescent Avian buffs a Unit or gives a buffed Unit +2 Might this turn. -/
def RAD_027 : CardDef :=
  { RAD_027.meta with
    abilities := [.activated [.exhaustSelf] .normal
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.ifThen (.matches (.slot 0) .buffed)
          (.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn)
          (.prim (.buff (.slot 0))))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-028
/--
**Ki Burst** — Spell · Calm · Energy 1
Printings: RAD-028/167

> [Action] (Play on your turn or in showdowns.)
> As an additional cost to play this, exhaust a friendly unit.
> [Stun] a unit. (It doesn't deal combat damage this turn.)
-/
def RAD_028.meta : CardDef :=
  { id := ⟨"RAD-028"⟩,
    name := "Ki Burst",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Ki Burst exhausts a friendly Unit as payment, then Stuns the chosen Unit. -/
def RAD_028 : CardDef :=
  { RAD_028.meta with
    playExtra := some (.exhaustUnit, true),
    spellEffect := some {
      choices := [.targetOf .one .any .anywhere [.ofType .unit]]
      body := .prim (.stun (.slot 0))
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-029
/--
**Life from Stone** — Spell · Calm · Energy 1
Printings: RAD-029/167

> [Reaction] (Play any time, even before spells and abilities resolve.)
> As an additional cost to play this, exhaust a friendly unit.
> Draw 1 and channel 1 rune exhausted.
-/
def RAD_029.meta : CardDef :=
  { id := ⟨"RAD-029"⟩,
    name := "Life from Stone",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Life from Stone exhausts a friendly Unit as payment, draws, and channels exhausted. -/
def RAD_029 : CardDef :=
  { RAD_029.meta with
    playExtra := some (.exhaustUnit, true),
    spellEffect := some (.of [] (.seqOf [.prim (.draw .you (.const 1)),
      .prim (.channel .you (.const 0) (.const 1))])),
    status := .full }

-- BEGIN GENERATED RAD-030
/--
**Sanctum Conservator** — Unit · Calm · Energy 5 · Might 5
Printings: RAD-030/167

> When you play a card with Energy cost :rb_energy_7: or more, ready me.
-/
def RAD_030.meta : CardDef :=
  { id := ⟨"RAD-030"⟩,
    name := "Sanctum Conservator",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Sanctum Conservator readies when its controller plays a card with Energy cost 7 or more. -/
def RAD_030 : CardDef :=
  { RAD_030.meta with
    abilities := [.triggered {
        event := .play
        subject := .all .friendly .anywhere [.cost .ge (.const 7)] }
      (.of [] (.prim (.ready .self))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-031
/--
**Stoic Ferryman** — Unit · Calm · Energy 4 · Might 2
Printings: RAD-031/167

> [Shield 3] (+3 :rb_might: while I'm a defender.)
> When you play me to a battlefield, you may move another unit you control here to your base.
-/
def RAD_031.meta : CardDef :=
  { id := ⟨"RAD-031"⟩,
    name := "Stoic Ferryman",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩, ⟨"Sentinel"⟩],
    domains := [.calm],
    cost := some ⟨4, []⟩,
    might := some 2,
    keywords := [{ keyword := .shield, arg := .amount 3 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Stoic Ferryman can move another friendly Unit from its entry Battlefield to Base. -/
def RAD_031 : CardDef :=
  { RAD_031.meta with
    abilities := [.triggered { event := .play, condition := .matches .self .onBattlefield, optional := true }
      { choices := [.targetOf .one .friendly .here [.ofType .unit, .notSelf]]
        body := .prim (.move (.slot 0) .base)
        recheckTargets := true } .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-032
/--
**Battle Preparations** — Spell · Calm · Energy 2
Printings: RAD-032/167

> [Reaction] (Play any time, even before spells and abilities resolve.)
> [Show Off] a gear. (As you play this, you may reveal a gear from hand or pick a friendly
> gear.)
> Give a unit +2 :rb_might: this turn. If you showed off, ready up to 2 runes.
-/
def RAD_032.meta : CardDef :=
  { id := ⟨"RAD-032"⟩,
    name := "Battle Preparations",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction },
      { keyword := .showOff, arg := .object "a gear" }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Battle Preparations boosts a Unit and, after showing off Gear, can ready two Runes. -/
def RAD_032 : CardDef :=
  { RAD_032.meta with
    showOffRequirement := some { filters := .ofList [.ofType .gear] },
    spellEffect := some {
      choices := [.targetOf .one .any .anywhere [.ofType .unit]],
      showOffChoices := [.targetOf (.upTo 2) .any .atBase [.ofType .rune]],
      body := .seqOf [.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn,
        .ifThen .showedOff (.prim (.ready (.slotsFrom 1))) .nop],
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-033
/--
**Command: Attack** — Spell · Calm · Energy 1 + Power 1
Printings: RAD-033/167

> Choose one —Move a friendly gear with [Deploy] to a battlefield.Look at the top 5 cards of
> your Main Deck. You may reveal a gear from among them and draw it. Recycle the rest.
-/
def RAD_033.meta : CardDef :=
  { id := ⟨"RAD-033"⟩,
    name := "Command: Attack",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, [.domain .calm]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Command: Attack: the effect is not written yet. -/
def RAD_033 : CardDef := RAD_033.meta

-- BEGIN GENERATED RAD-034
/--
**Hunker Down** — Spell · Calm · Energy 1
Printings: RAD-034/167

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Ready a friendly unit. It can't move this turn. Draw 1.
-/
def RAD_034.meta : CardDef :=
  { id := ⟨"RAD-034"⟩,
    name := "Hunker Down",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Hunker Down readies a friendly Unit, prevents its movement this turn, and draws. -/
def RAD_034 : CardDef :=
  { RAD_034.meta with
    spellEffect := some {
      choices := [.targetOf .one .friendly .anywhere [.ofType .unit]]
      body := .seqOf [.prim (.ready (.slot 0)), .prim (.markOn (.slot 0) .cannotMove),
        .prim (.draw .you (.const 1))]
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-035
/--
**Invigorating Bloom** — Gear · Calm · Energy 3
Printings: RAD-035/167

> When you play this, give a friendly unit +3 :rb_might: this turn.
> Exhaust a friendly [Mighty] unit, :rb_exhaust:: Draw 1. (A unit is Mighty while it has 5+
> :rb_might:.)
-/
def RAD_035.meta : CardDef :=
  { id := ⟨"RAD-035"⟩,
    name := "Invigorating Bloom",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Bloom temporarily increases Might and can exhaust itself and a friendly Mighty Unit to draw. -/
def RAD_035 : CardDef :=
  { RAD_035.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)) .unlimited,
      .activated [.exhaustFriendly (.ofList [.ofType .unit, .might .ge (.const 5)]), .exhaustSelf]
        .normal (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-036
/--
**Storm Raptor** — Unit · Calm · Energy 6 · Might 6
Printings: RAD-036/167

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> When a stunned enemy unit here dies, draw 1.
-/
def RAD_036.meta : CardDef :=
  { id := ⟨"RAD-036"⟩,
    name := "Storm Raptor",
    types := [.unit],
    tags := [⟨"Freljord"⟩, ⟨"Bird"⟩],
    domains := [.calm],
    cost := some ⟨6, []⟩,
    might := some 6,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Storm Raptor checks whether the enemy Unit at its location was stunned when it died. -/
def RAD_036 : CardDef :=
  { RAD_036.meta with
    abilities := [.triggered
      { event := .die
        subject := .all .enemy .anywhere [.ofType .unit, .at_ .self, .notedOn .stunnedUnitDied] }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-037
/--
**Watchful Curator** — Unit · Calm · Energy 3 + Power 1 · Might 4
Printings: RAD-037/167

> Your gear have [Deflect]. (Opponents must pay :rb_rune_rainbow: to choose each with a spell or
> ability.)
-/
def RAD_037.meta : CardDef :=
  { id := ⟨"RAD-037"⟩,
    name := "Watchful Curator",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.calm],
    cost := some ⟨3, [.domain .calm]⟩,
    might := some 4,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Watchful Curator gives its controller's Gear Deflect. -/
def RAD_037 : CardDef :=
  { RAD_037.meta with
    abilities := [.passive .always
      [.keyword (.all .friendly .anywhere [.ofType .gear]) ⟨.deflect, .none⟩]],
    status := .full }

-- BEGIN GENERATED RAD-039
/--
**Ephemeral Ward** — Gear · Calm · Energy 4 + Power 2
Printings: RAD-039/167

> Your units have +2 :rb_might:.
> When you play a unit, kill this.
-/
def RAD_039.meta : CardDef :=
  { id := ⟨"RAD-039"⟩,
    name := "Ephemeral Ward",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm, .domain .calm]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Ephemeral Ward boosts friendly Units until its controller plays a Unit. -/
def RAD_039 : CardDef :=
  { RAD_039.meta with
    abilities := [.passive .always [.mightPlus (.all .friendly .anywhere [.ofType .unit]) (.const 2)],
      .triggered { event := .play, subject := .all .friendly .anywhere [.ofType .unit] }
        (.of [] (.prim (.kill .self))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-040
/--
**Heartening Soul** — Unit · Calm · Energy 7 + Power 1 · Might 7
Printings: RAD-040/167

> When you play me, ready a friendly legend.
> Friendly legends have ":rb_exhaust:: Give a unit +3 :rb_might: this turn."
-/
def RAD_040.meta : CardDef :=
  { id := ⟨"RAD-040"⟩,
    name := "Heartening Soul",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Spirit"⟩],
    domains := [.calm],
    cost := some ⟨7, [.domain .calm]⟩,
    might := some 7,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Heartening Soul. -/
def RAD_040 : CardDef :=
  { RAD_040.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .friendly .boardOrLegend [.ofType .legend]] (.prim (.ready (.slot 0))))
        .unlimited,
      .passive .always [.grantFriendlyLegendsActivations]],
    grants := [.activated [.exhaustSelf] .normal
      (.of [.targetOf .one .any .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-041
/--
**Hush** — Spell · Calm · Energy 1 + Power 2
Printings: RAD-041/167

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Counter a spell with Power cost :rb_rune_rainbow::rb_rune_rainbow: or more.
-/
def RAD_041.meta : CardDef :=
  { id := ⟨"RAD-041"⟩,
    name := "Hush",
    types := [.spell],
    domains := [.calm],
    cost := some ⟨1, [.domain .calm, .domain .calm]⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Hush. -/
def RAD_041 : CardDef :=
  { RAD_041.meta with
    spellEffect := some (.of
      [.targetOf .one .any .onChain [.ofType .spell, .powerCost .ge (.const 2)]]
      (.prim (.counter (.slot 0)))),
    status := .full }

-- BEGIN GENERATED RAD-042
/--
**Orianna, Exquisite** — Unit · Calm · Energy 3 · Might 4
Printings: RAD-042/167, RAD-042a/167

> [Shield] (+1 :rb_might: while I'm a defender.)
> I don't deal combat damage unless there's a friendly gear here.
-/
def RAD_042.meta : CardDef :=
  { id := ⟨"RAD-042"⟩,
    name := "Orianna",
    subtitle := some "Exquisite",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Orianna"⟩, ⟨"Piltover"⟩],
    domains := [.calm],
    cost := some ⟨3, []⟩,
    might := some 4,
    keywords := [{ keyword := .shield, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Orianna deals combat damage only where her controller has Gear. -/
def RAD_042 : CardDef :=
  { RAD_042.meta with
    abilities := [.passive (.not (.exists (.all .friendly .here [.ofType .gear])))
      [.noCombatDamage]],
    status := .full }

-- BEGIN GENERATED RAD-043
/--
**Riven, Broken Blade** — Unit · Calm · Energy 4 · Might 4
Printings: RAD-043/167, RAD-043a/167

> When I become exhausted, choose one that hasn't been chosen this turn —[Buff] me. (Give me a
> +1 :rb_might: buff if I don't have one.)Spend my buff to [Stun] an enemy unit. (It doesn't
> deal combat damage this turn.)Spend my buff to ready me.
-/
def RAD_043.meta : CardDef :=
  { id := ⟨"RAD-043"⟩,
    name := "Riven",
    subtitle := some "Broken Blade",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Riven"⟩, ⟨"Noxus"⟩],
    domains := [.calm],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Riven, Broken Blade chooses an unused mode when exhausted and spends buffs on resolution. -/
def RAD_043 : CardDef :=
  { RAD_043.meta with
    abilities := [.triggered { event := .exhaust, separateModesPerTurn := true }
      { body := .nop, modes := [
        ⟨"Buff Riven", [], .prim (.buff .self)⟩,
        ⟨"Spend a buff to Stun", [.targetOf .one .enemy .anywhere [.ofType .unit]],
          .doThen (.prim (.spendBuff .self)) (.prim (.stun (.slot 0)))⟩,
        ⟨"Spend a buff to ready", [],
          .doThen (.prim (.spendBuff .self)) (.prim (.ready .self))⟩] }
      .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-044
/--
**Hunting Blind** — Gear · Calm · Energy 4 + Power 2
Printings: RAD-044/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> When you play this, you may move an enemy unit to this battlefield.
> Friendly units here have [Shield 2]. (+2 :rb_might: while they're defenders.)
-/
def RAD_044.meta : CardDef :=
  { id := ⟨"RAD-044"⟩,
    name := "Hunting Blind",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm, .domain .calm]⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Hunting Blind can move an enemy Unit to its Battlefield and gives friendly Units Shield 2. -/
def RAD_044 : CardDef :=
  { RAD_044.meta with
    abilities := [.triggered { event := .play, optional := true }
      (.of [.targetOf .one .enemy .anywhere [.ofType .unit, .not (.at_ .self)]]
        (.prim (.move (.slot 0) (.at_ (.locationOf .self))))) .unlimited,
      .passive .always
        [.keyword (.all .friendly .here [.ofType .unit]) ⟨.shield, .amount 2⟩]],
    status := .full }

-- BEGIN GENERATED RAD-045
/--
**K'Sante, Dauntless** — Unit · Calm · Energy 4 + Power 1 · Might 4
Printings: RAD-045/167, RAD-045a/167

> [Shield] (+1 :rb_might: while I'm a defender.)
> When I attack or defend, double the [Shield] of a unit you control here this turn.
-/
def RAD_045.meta : CardDef :=
  { id := ⟨"RAD-045"⟩,
    name := "K'Sante",
    subtitle := some "Dauntless",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"K'Sante"⟩, ⟨"Shurima"⟩],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    might := some 4,
    keywords := [{ keyword := .shield, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- K'Sante adds the chosen Unit's current Shield to its Shield for the turn. -/
def RAD_045 : CardDef :=
  let shield : VarId := ⟨"shield"⟩
  let doubleShield := EffectDef.of [.targetOf .one .friendly .here [.ofType .unit]]
    (.bind shield (.kwAmount (.slot 0) .shield)
      (.ifThen (.cmp .gt (.var shield) (.const 0))
        (.grantNumericKeyword (.slot 0) .shield (.var shield) .thisTurn) .nop))
  { RAD_045.meta with
    abilities := [.triggered (.onSelf .attack) doubleShield .unlimited,
      .triggered (.onSelf .defend) doubleShield .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-046
/--
**Resplendent Rostrum** — Gear · Calm · Energy 8 + Power 1
Printings: RAD-046/167

> :rb_exhaust:: Draw 1 and channel 1 rune exhausted.
> When I become exhausted, give a friendly unit +3 :rb_might: this turn.
-/
def RAD_046.meta : CardDef :=
  { id := ⟨"RAD-046"⟩,
    name := "Resplendent Rostrum",
    types := [.gear],
    domains := [.calm],
    cost := some ⟨8, [.domain .calm]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Resplendent Rostrum draws and channels when activated and boosts a Unit when exhausted. -/
def RAD_046 : CardDef :=
  { RAD_046.meta with
    abilities := [.activated [.exhaustSelf] .normal
        (.of [] (.seqOf [.prim (.draw .you (.const 1)),
          .prim (.channel .you (.const 0) (.const 1))])) .unlimited,
      .triggered (.onSelf .exhaust)
        (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
          (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-047
/--
**Fanfare** — Spell · Mind · Energy 3
Printings: RAD-047/167

> The next three times you play a unit this turn, draw 1.
-/
def RAD_047.meta : CardDef :=
  { id := ⟨"RAD-047"⟩,
    name := "Fanfare",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Fanfare draws through a delayed ability on each of the next three Unit plays this turn. -/
def RAD_047 : CardDef :=
  { RAD_047.meta with
    spellEffect := some (.of [] (.prim (.markOn .self (.triggerOnPlays RAD_047.meta.id 0 .unit 3)))),
    abilities := [.triggered (.onSelf .delayedPlay)
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-048
/--
**High Note** — Spell · Mind · Energy 3
Printings: RAD-048/167

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Give a unit –:rb_might: this turn equal to the number of exhausted units you control.
-/
def RAD_048.meta : CardDef :=
  { id := ⟨"RAD-048"⟩,
    name := "High Note",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- High Note. -/
def RAD_048 : CardDef :=
  { RAD_048.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0)
        (.mightMinus .it (.count (.all .friendly .anywhere [.ofType .unit, .exhausted])))
        .thisTurn)),
    status := .full }

-- BEGIN GENERATED RAD-049
/--
**Industrious Mechsmith** — Unit · Mind · Energy 4 · Might 1
Printings: RAD-049/167

> When you play me, play a 3 :rb_might: Mech unit token here.
-/
def RAD_049.meta : CardDef :=
  { id := ⟨"RAD-049"⟩,
    name := "Industrious Mechsmith",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 1,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Industrious Mechsmith. -/
def RAD_049 : CardDef :=
  { RAD_049.meta with
    abilities := [.triggered (.onSelf .play)
        (.of []
        (.prim (.create "Mech" (.const 1) .here false))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-050
/--
**Mysterious Chronomancer** — Unit · Mind · Energy 5 · Might 4
Printings: RAD-050/167

> When you play me, [Predict 2]. (Look at the top 2 cards of your Main Deck. Recycle any of them
> and put the rest back in any order.)
> [Disarm 2] (When I attack, give an enemy unit here -2 :rb_might: this turn.)
-/
def RAD_050.meta : CardDef :=
  { id := ⟨"RAD-050"⟩,
    name := "Mysterious Chronomancer",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    might := some 4,
    keywords := [{ keyword := .disarm, arg := .amount 2 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Mysterious Chronomancer. -/
def RAD_050 : CardDef :=
  { RAD_050.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.prim (.predict (.const 2)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-051
/--
**Parallel Convergence** — Spell · Mind · Energy 2 + Power 1
Printings: RAD-051/167

> As an additional cost to play this, return a friendly unit to its owner's hand.
> Deal 5 to a unit at a battlefield.
-/
def RAD_051.meta : CardDef :=
  { id := ⟨"RAD-051"⟩,
    name := "Parallel Convergence",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨2, [.domain .mind]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Parallel Convergence returns a friendly Unit as payment and damages a Unit at a Battlefield. -/
def RAD_051 : CardDef :=
  { RAD_051.meta with
    playExtra := some (.returnUnit, true),
    spellEffect := some {
      choices := [.targetOf .one .any .atBattlefield [.ofType .unit]]
      body := .prim (.deal (.slot 0) (.const 5))
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-052
/--
**Resource Extractor** — Gear · Mind · Energy 1
Printings: RAD-052/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> At the end of your turn, if you control this battlefield, play a Gold gear token exhausted.
> (It has "[Reaction][>] Kill this, :rb_exhaust:: [Add] :rb_rune_rainbow:.")
-/
def RAD_052.meta : CardDef :=
  { id := ⟨"RAD-052"⟩,
    name := "Resource Extractor",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Resource Extractor. -/
def RAD_052 : CardDef :=
  { RAD_052.meta with
    abilities := [.triggered
      { event := .at_ .endOfTurn
        condition := .matches (.locationOf .self) .controlled }
      (.of [] (.prim (.create "Gold" (.const 1) .atBase false))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-053
/--
**Strigian Oracle** — Unit · Mind · Energy 2 · Might 2
Printings: RAD-053/167

> When I become exhausted, [Predict]. (Look at the top card of your Main Deck. You may recycle
> it.)
-/
def RAD_053.meta : CardDef :=
  { id := ⟨"RAD-053"⟩,
    name := "Strigian Oracle",
    types := [.unit],
    tags := [⟨"Freljord"⟩, ⟨"Bird"⟩],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Strigian Oracle Predicts when it becomes exhausted on the Board. -/
def RAD_053 : CardDef :=
  { RAD_053.meta with
    abilities := [.triggered (.onSelf .exhaust)
      (.of [] (.prim (.predict (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-054
/--
**Trinket Peddler** — Unit · Mind · Energy 3 · Might 3
Printings: RAD-054/167

> [Disarm] (When I attack, give an enemy unit here -1 :rb_might: this turn.)
-/
def RAD_054.meta : CardDef :=
  { id := ⟨"RAD-054"⟩,
    name := "Trinket Peddler",
    types := [.unit],
    tags := [⟨"Bandle City"⟩, ⟨"Yordle"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .disarm, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Trinket Peddler. -/
def RAD_054 : CardDef :=
  { RAD_054.meta with
    status := .full }

-- BEGIN GENERATED RAD-055
/--
**Clanging Sentry** — Unit · Mind · Energy 3 · Might 2
Printings: RAD-055/167

> Your Mechs have [Disarm]. (When each of us attacks, give an enemy unit there -1 :rb_might:
> this turn.)
-/
def RAD_055.meta : CardDef :=
  { id := ⟨"RAD-055"⟩,
    name := "Clanging Sentry",
    types := [.unit],
    tags := [⟨"Piltover"⟩, ⟨"Mech"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 2,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Clanging Sentry. -/
def RAD_055 : CardDef :=
  { RAD_055.meta with
    abilities := [.passive .always
      [.keyword (.all .friendly .anywhere [.tag ⟨"Mech"⟩]) ⟨.disarm, .none⟩]],
    status := .full }

-- BEGIN GENERATED RAD-056
/--
**Improvised Projectile** — Spell · Mind · Energy 3 + Power 1
Printings: RAD-056/167

> [Action] (Play on your turn or in showdowns.)
> Choose a friendly gear. Deal damage equal to its Energy cost to a unit at a battlefield.
-/
def RAD_056.meta : CardDef :=
  { id := ⟨"RAD-056"⟩,
    name := "Improvised Projectile",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨3, [.domain .mind]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Improvised Projectile uses the chosen Gear's Energy cost as damage to a Unit at a Battlefield. -/
def RAD_056 : CardDef :=
  { RAD_056.meta with
    spellEffect := some {
      choices := [.targetOf .one .friendly .anywhere [.ofType .gear],
        .targetOf .one .any .atBattlefield [.ofType .unit]]
      body := .prim (.deal (.slot 1) (.costOf (.slot 0)))
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-057
/--
**Piltovan Guidebot** — Unit · Mind · Energy 4 · Might 3
Printings: RAD-057/167

> When you play a card, you may have my base Might become equal to that card's Energy cost this
> turn.
-/
def RAD_057.meta : CardDef :=
  { id := ⟨"RAD-057"⟩,
    name := "Piltovan Guidebot",
    types := [.unit],
    tags := [⟨"Piltover"⟩, ⟨"Mech"⟩],
    domains := [.mind],
    cost := some ⟨4, []⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Piltovan Guidebot may take the Energy cost of a card its controller played as base Might. -/
def RAD_057 : CardDef :=
  { RAD_057.meta with
    abilities := [.triggered { event := .play, subject := .all .friendly .anywhere [], optional := true }
      (.of [] (.prim (.setBaseMight .self (.costOf (.slot 0))))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-058
/--
**Riptide Mage** — Unit · Mind · Energy 4 + Power 1 · Might 3
Printings: RAD-058/167

> [Accelerate] (You may pay :rb_energy_1::rb_rune_mind: as an additional cost to have me enter
> ready.)
> When you play me, give an enemy unit -3 :rb_might: this turn.
-/
def RAD_058.meta : CardDef :=
  { id := ⟨"RAD-058"⟩,
    name := "Riptide Mage",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 3,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Riptide Mage. -/
def RAD_058 : CardDef :=
  { RAD_058.meta with
    abilities := [.triggered (.onSelf .play)
        (.of [.targetOf .one .enemy .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.mightMinus .it (.const 3)) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-059
/--
**Supernova** — Spell · Mind · Energy 9 + Power 1
Printings: RAD-059/167

> Deal 10 to a unit. Draw 2.
-/
def RAD_059.meta : CardDef :=
  { id := ⟨"RAD-059"⟩,
    name := "Supernova",
    types := [.spell],
    domains := [.mind],
    cost := some ⟨9, [.domain .mind]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Supernova. -/
def RAD_059 : CardDef :=
  { RAD_059.meta with
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.seqOf [.prim (.deal (.slot 0) (.const 10)),
        .prim (.draw .you (.const 2))])),
    status := .full }

-- BEGIN GENERATED RAD-060
/--
**The Empyrean** — Unit · Mind · Energy 8 · Might 8
Printings: RAD-060/167

> [Show Off] a card. (As you play me, you may reveal a card from hand or pick another friendly
> one.)
> When you play me, if you showed off a card, [Predict] equal to its Power cost, then draw 2.
> (Look at that many cards from your Main Deck. Recycle any of them and put the rest back in any
> order.)
-/
def RAD_060.meta : CardDef :=
  { id := ⟨"RAD-060"⟩,
    name := "The Empyrean",
    types := [.unit],
    tags := [⟨"Ionia"⟩, ⟨"Dragon"⟩],
    domains := [.mind],
    cost := some ⟨8, []⟩,
    might := some 8,
    keywords := [{ keyword := .showOff, arg := .object "a card" }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- The Empyrean Predicts the shown card's Power cost and then draws two. -/
def RAD_060 : CardDef :=
  { RAD_060.meta with
    showOffRequirement := some { cardsOnly := true },
    abilities := [.triggered { event := .play, condition := .showedOff }
      (.of [] (.seqOf [.prim (.predict .shownOffPower), .prim (.draw .you (.const 2))])) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-061
/--
**Ekko, Ingenious** — Unit · Mind · Energy 3 · Might 4
Printings: RAD-061/167, RAD-061a/167

> As an additional cost to play me, return a friendly unit to its owner's hand.
> [Ganking] (I can move from battlefield to battlefield.)
-/
def RAD_061.meta : CardDef :=
  { id := ⟨"RAD-061"⟩,
    name := "Ekko",
    subtitle := some "Ingenious",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Ekko"⟩, ⟨"Zaun"⟩],
    domains := [.mind],
    cost := some ⟨3, []⟩,
    might := some 4,
    keywords := [{ keyword := .ganking }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Ekko requires a friendly Unit to be returned to its owner's hand. -/
def RAD_061 : CardDef :=
  { RAD_061.meta with
    playExtra := some (.returnUnit, true),
    status := .full }

-- BEGIN GENERATED RAD-062
/--
**Gravity Field** — Gear · Mind · Energy 5 + Power 1
Printings: RAD-062/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> Opponents must pay :rb_energy_1::rb_rune_rainbow: to move one or more units to this
> battlefield.
> [Deathknell][>] Draw 1. (When I die, get the effect.)
-/
def RAD_062.meta : CardDef :=
  { id := ⟨"RAD-062"⟩,
    name := "Gravity Field",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨5, [.domain .mind]⟩,
    keywords := [{ keyword := .deploy },
      { keyword := .deathknell }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Gravity Field charges opponents when they move Units here and draws on Deathknell. -/
def RAD_062 : CardDef :=
  { RAD_062.meta with
    abilities := [.passive .always [.moveFeeHere ⟨1, [.any]⟩],
      .triggered (.onSelf .deathknell)
        (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-064
/--
**Scrutinizing Scope** — Gear · Mind · Energy 2
Printings: RAD-064/167

> :rb_energy_1:, :rb_exhaust:: Choose an opponent. They guess a card type. Reveal the top card
> of your Main Deck. If it has that type, recycle it. Otherwise, draw it. (Unit, gear, and spell
> are types.)
-/
def RAD_064.meta : CardDef :=
  { id := ⟨"RAD-064"⟩,
    name := "Scrutinizing Scope",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨2, []⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Scrutinizing Scope: the effect is not written yet. -/
def RAD_064 : CardDef := RAD_064.meta

-- BEGIN GENERATED RAD-065
/--
**Seraphine, Inspiring** — Unit · Mind · Energy 4 + Power 1 · Might 3
Printings: RAD-065/167, RAD-065a/167

> [Disarm 2] (When I attack, give an enemy unit here -2 :rb_might: this turn.)
> Once each turn, when you exhaust three or more friendly units at the same time, you may draw
> 1.
-/
def RAD_065.meta : CardDef :=
  { id := ⟨"RAD-065"⟩,
    name := "Seraphine",
    subtitle := some "Inspiring",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Seraphine"⟩, ⟨"Piltover"⟩],
    domains := [.mind],
    cost := some ⟨4, [.domain .mind]⟩,
    might := some 3,
    keywords := [{ keyword := .disarm, arg := .amount 2 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Seraphine, Inspiring can draw once a turn when her controller exhausts three friendly Units together. -/
def RAD_065 : CardDef :=
  { RAD_065.meta with
    abilities := [.triggered { event := .youExhaustUnits 3, optional := true }
      (.of [] (.prim (.draw .you (.const 1)))) (.perTurn 1)],
    status := .full }

-- BEGIN GENERATED RAD-066
/--
**Spirit of the Forge** — Unit · Mind · Energy 6 + Power 1 · Might 4
Printings: RAD-066/167

> You may return a friendly gear to its owner's hand as an additional cost to play me.
> When you play me, if you paid the additional cost, ready me and give me +:rb_might: this turn
> equal to the Energy cost of the gear you returned.
-/
def RAD_066.meta : CardDef :=
  { id := ⟨"RAD-066"⟩,
    name := "Spirit of the Forge",
    types := [.unit],
    tags := [⟨"Freljord"⟩, ⟨"Spirit"⟩],
    domains := [.mind],
    cost := some ⟨6, [.domain .mind]⟩,
    might := some 4,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Spirit of the Forge readies and gains Might for returning Gear as its additional cost. -/
def RAD_066 : CardDef :=
  { RAD_066.meta with
    playExtra := some (.returnGear, false),
    abilities := [.triggered { Trigger.onSelf .play with condition := .paid }
      (.of [] (.seqOf [.prim (.ready .self),
        .grant .self (.mightPlus .it .returnedGearEnergy) .thisTurn])) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-067
/--
**Clocktower Guardian** — Unit · Mind · Energy 8 + Power 2 · Might 8
Printings: RAD-067/167

> When you play me or when I hold, [Predict 3].
> [Deathknell][>] Banish the top card of your Main Deck. You may play it, ignoring its Energy
> cost.
-/
def RAD_067.meta : CardDef :=
  { id := ⟨"RAD-067"⟩,
    name := "Clocktower Guardian",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.mind],
    cost := some ⟨8, [.domain .mind, .domain .mind]⟩,
    might := some 8,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Clocktower Guardian. -/
def RAD_067 : CardDef :=
  let predict := EffectDef.of [] (.prim (.predict (.const 3)))
  { RAD_067.meta with
    abilities := [.triggered (.onSelf .play) predict .unlimited,
      .triggered (.onSelf .hold) predict .unlimited,
      .triggered (.onSelf .deathknell)
        (.of [] (.seqOf [
          .prim (.banishWith (.one .friendly .inMainDeck [.top 1])),
          .mayPlayCard (.one .friendly .inBanishment [.banishedWithMe]) .ignoreEnergy]))
        .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-068
/--
**Orianna, Mechanical Marvel** — Unit · Mind · Energy 5 · Might 5
Printings: RAD-068/167, RAD-068a/167

> Once each turn, while I'm at a battlefield, you may pay :rb_energy_1::rb_rune_rainbow: less to
> play a gear.
-/
def RAD_068.meta : CardDef :=
  { id := ⟨"RAD-068"⟩,
    name := "Orianna",
    subtitle := some "Mechanical Marvel",
    types := [.unit],
    tags := [⟨"Piltover"⟩, ⟨"Orianna"⟩],
    domains := [.mind],
    cost := some ⟨5, []⟩,
    might := some 5,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Orianna, Mechanical Marvel: the effect is not written yet. -/
def RAD_068 : CardDef := RAD_068.meta

-- BEGIN GENERATED RAD-069
/--
**Zero Point Inflection** — Gear · Mind · Energy 9 + Power 2
Printings: RAD-069/167

> When you play a card, draw 2.
> When you draw 1 or more cards with 9 or more other cards in your hand, discard your hand, kill
> this, and choose an opponent. They score 1 point.
-/
def RAD_069.meta : CardDef :=
  { id := ⟨"RAD-069"⟩,
    name := "Zero Point Inflection",
    types := [.gear],
    domains := [.mind],
    cost := some ⟨9, [.domain .mind, .domain .mind]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Zero Point Inflection: the effect is not written yet. -/
def RAD_069 : CardDef := RAD_069.meta

-- BEGIN GENERATED RAD-070
/--
**Hold 'Em** — Spell · Body · Energy 3
Printings: RAD-070/167

> [Action] (Play on your turn or in showdowns.)
> This costs :rb_energy_2: less if you've played a unit or gear to a battlefield this turn.
> Give a unit +3 :rb_might: this turn.
-/
def RAD_070.meta : CardDef :=
  { id := ⟨"RAD-070"⟩,
    name := "Hold 'Em",
    types := [.spell],
    domains := [.body],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Hold 'Em costs two less after playing a Unit or Gear to a Battlefield this turn. -/
def RAD_070 : CardDef :=
  { RAD_070.meta with
    abilities := [.passive (.noted .playedToBattlefield) [.costMinus .self (.const 2)]],
    spellEffect := some (.of [.targetOf .one .any .anywhere [.ofType .unit]]
      (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)),
    status := .full }

-- BEGIN GENERATED RAD-071
/--
**Nazuman Ntofo** — Gear · Body · Energy 1 · Might 0
Printings: RAD-071/167

> [Equip] :rb_energy_1: (:rb_energy_1:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Shield 2] (+2 :rb_might: while I'm a defender.)
-/
def RAD_071.meta : CardDef :=
  { id := ⟨"RAD-071"⟩,
    name := "Nazuman Ntofo",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.body],
    cost := some ⟨1, []⟩,
    might := some 0,
    mightBonus := some 0,
    keywords := [{ keyword := .equip, arg := .cost ⟨1, []⟩ }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Nazuman Ntofo. -/
def RAD_071 : CardDef :=
  { RAD_071.meta with
    grants := [.passive .always [.keyword .self ⟨.shield, .amount 2⟩]],
    status := .full }

-- BEGIN GENERATED RAD-072
/--
**Overloaded Traveler** — Unit · Body · Energy 2 · Might 2
Printings: RAD-072/167

> While there's a friendly gear with [Deploy] at my battlefield, I have +1 :rb_might:.
-/
def RAD_072.meta : CardDef :=
  { id := ⟨"RAD-072"⟩,
    name := "Overloaded Traveler",
    types := [.unit],
    tags := [⟨"Bandle City"⟩, ⟨"Yordle"⟩],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Overloaded Traveler. -/
def RAD_072 : CardDef :=
  { RAD_072.meta with
    abilities := [.passive (.and (.matches .self .onBattlefield)
      (.exists (.all .friendly .here [.ofType .gear, .hasKeyword .deploy])))
      [.mightPlus .self (.const 1)]],
    status := .full }

-- BEGIN GENERATED RAD-073
/--
**Pillaged Armory** — Gear · Body · Energy 1
Printings: RAD-073/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> When you play this or when you conquer here, [Buff] a friendly unit. (Give it a +1 :rb_might:
> buff if it doesn't have one.)
-/
def RAD_073.meta : CardDef :=
  { id := ⟨"RAD-073"⟩,
    name := "Pillaged Armory",
    types := [.gear],
    domains := [.body],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Pillaged Armory. -/
def RAD_073 : CardDef :=
  { RAD_073.meta with
    abilities :=
      let buff := EffectDef.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.prim (.buff (.slot 0)))
      [.triggered (.onSelf .play) buff .unlimited,
       .triggered (.onSelf .conquer) buff .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-074
/--
**Raving Witness** — Unit · Body · Energy 3 · Might 3
Printings: RAD-074/167

> When I move, reveal the top card of your Main Deck. If it's [Mighty], draw it. Otherwise,
> recycle it. (A unit is Mighty while it has 5+ :rb_might:.)
-/
def RAD_074.meta : CardDef :=
  { id := ⟨"RAD-074"⟩,
    name := "Raving Witness",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Raving Witness reveals the top card after a Move, drawing it if Mighty and recycling it otherwise. -/
def RAD_074 : CardDef :=
  let mighty := Amount.count (.all .friendly .inMainDeck [.top 1, .mighty])
  { RAD_074.meta with
    abilities := [.triggered (.onSelf .move)
      (.of [] (.seqOf [.prim (.revealTop 1),
        .ifThen (.cmp .gt mighty (.const 0)) (.prim (.draw .you (.const 1)))
          (.prim (.recycle (.one .friendly .inMainDeck [.top 1])))])) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-075
/--
**Skystrike Squadron** — Unit · Body · Energy 5 · Might 4
Printings: RAD-075/167

> You may return a friendly gear to its owner's hand as an additional cost to play me. If you
> do, I cost :rb_energy_2: less.
> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
-/
def RAD_075.meta : CardDef :=
  { id := ⟨"RAD-075"⟩,
    name := "Skystrike Squadron",
    types := [.unit],
    tags := [⟨"Demacia"⟩, ⟨"Elite"⟩, ⟨"Bird"⟩],
    domains := [.body],
    cost := some ⟨5, []⟩,
    might := some 4,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Skystrike Squadron can return friendly Gear to reduce its Energy cost by 2. -/
def RAD_075 : CardDef :=
  { RAD_075.meta with
    playExtra := some (.returnGear, false)
    paidCut := some (.energy 2)
    status := .full }

-- BEGIN GENERATED RAD-076
/--
**Sneaky Zeebles** — Unit · Body · Energy 2 · Might 1
Printings: RAD-076/167

> When I conquer, [Add] :rb_rune_rainbow:. (Abilities that add resources can't be reacted to.)
-/
def RAD_076.meta : CardDef :=
  { id := ⟨"RAD-076"⟩,
    name := "Sneaky Zeebles",
    types := [.unit],
    domains := [.body],
    cost := some ⟨2, []⟩,
    might := some 1,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Sneaky Zeebles. -/
def RAD_076 : CardDef :=
  { RAD_076.meta with
    abilities := [.triggered (.onSelf .conquer)
        (.of []
        (.prim (.addPower .you (.const 1) none none))) .unlimited],
    status := .drafted }

-- BEGIN GENERATED RAD-077
/--
**Wrath of the Freljord** — Unit · Body · Energy 9 · Might 7
Printings: RAD-077/167

> I enter ready.
> [Shield 3] (+3 :rb_might: while I'm a defender.)
-/
def RAD_077.meta : CardDef :=
  { id := ⟨"RAD-077"⟩,
    name := "Wrath of the Freljord",
    types := [.unit],
    tags := [⟨"Freljord"⟩, ⟨"Spirit"⟩],
    domains := [.body],
    cost := some ⟨9, []⟩,
    might := some 7,
    keywords := [{ keyword := .shield, arg := .amount 3 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Wrath of the Freljord. -/
def RAD_077 : CardDef :=
  { RAD_077.meta with
    abilities := [.passive .always [.entersReady .self]],
    status := .full }

-- BEGIN GENERATED RAD-078
/--
**Armored Tusker** — Unit · Body · Energy 6 + Power 1 · Might 4
Printings: RAD-078/167

> [Shield 3] (+3 :rb_might: while I'm a defender.)
> [Tank] (I must be assigned combat damage first.)
> When I move, you may deal damage equal to my [Shield] to a unit at a battlefield.
-/
def RAD_078.meta : CardDef :=
  { id := ⟨"RAD-078"⟩,
    name := "Armored Tusker",
    types := [.unit],
    tags := [⟨"Noxus"⟩],
    domains := [.body],
    cost := some ⟨6, [.domain .body]⟩,
    might := some 4,
    keywords := [{ keyword := .shield, arg := .amount 3 },
      { keyword := .tank }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Armored Tusker may deal damage equal to its current Shield after moving. -/
def RAD_078 : CardDef :=
  { RAD_078.meta with
    abilities := [.triggered { event := .move, optional := true }
      (.of [.targetOf .one .any .atBattlefield [.ofType .unit]]
        (.prim (.deal (.slot 0) (.kwAmount .self .shield)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-079
/--
**Avalanche** — Spell · Body · Energy 5 + Power 2
Printings: RAD-079/167

> Deal 3 to all units in bases.
-/
def RAD_079.meta : CardDef :=
  { id := ⟨"RAD-079"⟩,
    name := "Avalanche",
    types := [.spell],
    domains := [.body],
    cost := some ⟨5, [.domain .body, .domain .body]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Avalanche. -/
def RAD_079 : CardDef :=
  { RAD_079.meta with
    spellEffect := some (.of []
      (.prim (.deal (.all .any .atBase [.ofType .unit]) (.const 3)))),
    status := .full }

-- BEGIN GENERATED RAD-080
/--
**Bloodscent Swarm** — Unit · Body · Energy 8 + Power 2 · Might 8
Printings: RAD-080/167

> I cost :rb_energy_2: less for each battlefield you've conquered this turn.
-/
def RAD_080.meta : CardDef :=
  { id := ⟨"RAD-080"⟩,
    name := "Bloodscent Swarm",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.body],
    cost := some ⟨8, [.domain .body, .domain .body]⟩,
    might := some 8,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Bloodscent Swarm counts this player's Conquers to reduce its Energy cost. -/
def RAD_080 : CardDef :=
  { RAD_080.meta with
    abilities := [.passive .always [.costMinus .self
      (.mul (.const 2) (.count (.all .any .atBattlefield [.ofType .battlefield, .conqueredByMine])))]],
    status := .full }

-- BEGIN GENERATED RAD-081
/--
**Elnuk Herd** — Unit · Body · Energy 6 · Might 5
Printings: RAD-081/167

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me, give a friendly unit +3 :rb_might: this turn, then recycle me if I was
> played from face down.
-/
def RAD_081.meta : CardDef :=
  { id := ⟨"RAD-081"⟩,
    name := "Elnuk Herd",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨6, []⟩,
    might := some 5,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Elnuk Herd boosts a friendly Unit and Recycles itself if played from Hidden. -/
def RAD_081 : CardDef :=
  { RAD_081.meta with
    abilities := [.triggered (.onSelf .play)
      { choices := [.targetOf .one .friendly .anywhere [.ofType .unit]]
        body := .seqOf [.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn,
          .ifThen .fromHidden (.prim (.recycle .self)) .nop]
        recheckTargets := true } .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-082
/--
**Primordial Roar** — Spell · Body · Energy 4 + Power 2
Printings: RAD-082/167

> [Show Off] a unit. (As you play this, you may reveal a unit from hand or pick a friendly
> unit.)
> If you showed off a unit, deal damage equal to that unit's Might to a unit.
-/
def RAD_082.meta : CardDef :=
  { id := ⟨"RAD-082"⟩,
    name := "Primordial Roar",
    types := [.spell],
    domains := [.body],
    cost := some ⟨4, [.domain .body, .domain .body]⟩,
    keywords := [{ keyword := .showOff, arg := .object "a unit" }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Primordial Roar can use a shown Unit's captured Might to damage a chosen Unit. -/
def RAD_082 : CardDef :=
  { RAD_082.meta with
    showOffRequirement := some { filters := .ofList [.ofType .unit] },
    spellEffect := some {
      showOffChoices := [.targetOf .one .any .anywhere [.ofType .unit]],
      body := .ifThen .showedOff (.prim (.deal (.slot 0) .shownOffMight)) .nop,
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-083
/--
**Stalwart Goatherd** — Unit · Body · Energy 4 · Might 2
Printings: RAD-083/167

> [Shield 2] (+2 :rb_might: while I'm a defender.)
> When you play me, you may kill a gear with Energy cost :rb_energy_4: or less.
-/
def RAD_083.meta : CardDef :=
  { id := ⟨"RAD-083"⟩,
    name := "Stalwart Goatherd",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩],
    domains := [.body],
    cost := some ⟨4, []⟩,
    might := some 2,
    keywords := [{ keyword := .shield, arg := .amount 2 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Stalwart Goatherd can kill a chosen Gear with Energy cost 4 or less. -/
def RAD_083 : CardDef :=
  { RAD_083.meta with
    abilities := [.triggered { event := .play, optional := true }
      { choices := [.targetOf .one .any .anywhere [.ofType .gear, .cost .le (.const 4)]]
        body := .prim (.kill (.slot 0))
        recheckTargets := true } .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-084
/--
**Cataclysm** — Spell · Body · Energy 4 + Power 1
Printings: RAD-084/167

> Opponents can't play spells this turn.
> Move a friendly unit to an occupied enemy battlefield.
-/
def RAD_084.meta : CardDef :=
  { id := ⟨"RAD-084"⟩,
    name := "Cataclysm",
    types := [.spell],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Cataclysm prevents opponents' Spell plays and moves a friendly Unit to an enemy position. -/
def RAD_084 : CardDef :=
  { RAD_084.meta with
    spellEffect := some {
      choices := [.targetOf .one .friendly .anywhere [.ofType .unit]]
      moveChoice := some ⟨0, false, .ofList [.enemyOccupied]⟩
      body := .seqOf [.prim (.turnEffect .opponentsNoSpells),
        .moveChoosing 0 false (.ofList [.enemyOccupied]) .nop false]
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-085
/--
**Graves, Blasting Through** — Unit · Body · Energy 5 + Power 1 · Might 4
Printings: RAD-085/167

> When I attack or defend, deal damage equal to my Might to all enemy units here.
> I don't deal combat damage.
-/
def RAD_085.meta : CardDef :=
  { id := ⟨"RAD-085"⟩,
    name := "Graves",
    subtitle := some "Blasting Through",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Bilgewater"⟩, ⟨"Graves"⟩],
    domains := [.body],
    cost := some ⟨5, [.domain .body]⟩,
    might := some 4,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Graves, Blasting Through deals his current Might to enemies on either side of a combat. -/
def RAD_085 : CardDef :=
  { RAD_085.meta with
    abilities :=
      let blast := EffectDef.of []
        (.prim (.deal (.all .enemy .here [.ofType .unit]) (.mightOf .self)))
      [.triggered (.onSelf .attack) blast .unlimited,
        .triggered (.onSelf .defend) blast .unlimited,
        .passive .always [.noCombatDamage]],
    status := .full }

-- BEGIN GENERATED RAD-086
/--
**K'Sante, Courageous** — Unit · Body · Energy 5 · Might 4
Printings: RAD-086/167, RAD-086a/167, RAD-178/167

> [Accelerate] (You may pay :rb_energy_1::rb_rune_body: as an additional cost to have me enter
> ready.)
> [Shield 2] (+2 :rb_might: while I'm a defender.)
> When I hold, channel 1 rune.
-/
def RAD_086.meta : CardDef :=
  { id := ⟨"RAD-086"⟩,
    name := "K'Sante",
    subtitle := some "Courageous",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"K'Sante"⟩, ⟨"Shurima"⟩],
    domains := [.body],
    cost := some ⟨5, []⟩,
    might := some 4,
    keywords := [{ keyword := .accelerate },
      { keyword := .shield, arg := .amount 2 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- K'Sante, Courageous. -/
def RAD_086 : CardDef :=
  { RAD_086.meta with
    abilities := [.triggered (.onSelf .hold)
        (.of []
        (.prim (.channel .you (.const 1) (.const 0)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-087
/--
**Portable Portal** — Gear · Body · Energy 2
Printings: RAD-087/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> When you play this, you may pay :rb_rune_body: to ready a unit here.
> Friendly units here have [Ganking]. (They can move from battlefield to battlefield.)
-/
def RAD_087.meta : CardDef :=
  { id := ⟨"RAD-087"⟩,
    name := "Portable Portal",
    types := [.gear],
    domains := [.body],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Portable Portal gives Ganking here and can pay a Body Power to ready a chosen Unit here. -/
def RAD_087 : CardDef :=
  { RAD_087.meta with
    abilities := [.triggered { Trigger.onSelf .play with
        optional := true, cost := .pay ⟨0, [.domain .body]⟩ }
      { choices := [.targetOf .one .any .atBattlefield [.ofType .unit, .atEventBattlefield none]]
        body := .prim (.ready (.slot 0))
        recheckTargets := true } .unlimited,
      .passive .always [.keyword (.all .friendly .here [.ofType .unit]) ⟨.ganking, .none⟩]],
    status := .full }

-- BEGIN GENERATED RAD-088
/--
**Staunch Survivor** — Unit · Body · Energy 2 + Power 1 · Might 2
Printings: RAD-088/167

> [Assault 2], [Shield 2] (+2 :rb_might: while I'm an attacker or defender.)
-/
def RAD_088.meta : CardDef :=
  { id := ⟨"RAD-088"⟩,
    name := "Staunch Survivor",
    types := [.unit],
    tags := [⟨"Freljord"⟩],
    domains := [.body],
    cost := some ⟨2, [.domain .body]⟩,
    might := some 2,
    keywords := [{ keyword := .assault, arg := .amount 2 },
      { keyword := .shield, arg := .amount 2 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Staunch Survivor. -/
def RAD_088 : CardDef :=
  { RAD_088.meta with
    status := .full }

-- BEGIN GENERATED RAD-089
/--
**Titanic Shrine** — Gear · Body · Energy 3
Printings: RAD-089/167

> When you play a unit with Might greater than each other unit on the board, exhaust me to draw
> 1.
-/
def RAD_089.meta : CardDef :=
  { id := ⟨"RAD-089"⟩,
    name := "Titanic Shrine",
    types := [.gear],
    tags := [⟨"Device"⟩],
    domains := [.body],
    cost := some ⟨3, []⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Titanic Shrine may exhaust to draw after the player plays the uniquely strongest Unit. -/
def RAD_089 : CardDef :=
  { RAD_089.meta with
    abilities := [.triggered
      { event := .play
        subject := .all .friendly .anywhere [.ofType .unit]
        condition := .not (.exists (.all .any .anywhere
          [.ofType .unit, .not (.sameAs (.slot 0)), .not (.mightLtOf (.slot 0))]))
        optional := true
        cost := .exhaustSelf }
      (.of [] (.prim (.draw .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-090
/--
**Evelynn, Consuming** — Unit · Body · Energy 5 + Power 1 · Might 5
Printings: RAD-090/167, RAD-090a/167

> [Ambush] (You may play me as a [Reaction] to a battlefield where you have units.)
> When you play a card from face down, ready me and give me +1 :rb_might: this turn.
-/
def RAD_090.meta : CardDef :=
  { id := ⟨"RAD-090"⟩,
    name := "Evelynn",
    subtitle := some "Consuming",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Evelynn"⟩, ⟨"Demon"⟩],
    domains := [.body],
    cost := some ⟨5, [.domain .body]⟩,
    might := some 5,
    keywords := [{ keyword := .ambush }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Every card played from Hidden readies Evelynn and adds Might for the turn. -/
def RAD_090 : CardDef :=
  { RAD_090.meta with
    abilities := [.triggered (.onSelf .playHidden)
      (.of [] (.seqOf [.prim (.ready .self),
        .grant .self (.mightPlus .it (.const 1)) .thisTurn])) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-091
/--
**Jarvan IV, Martial Paragon** — Unit · Body · Energy 4 + Power 1 · Might 4
Printings: RAD-091/167, RAD-091a/167

> Your gear with [Deploy] have [Action]. (They can be played on your turn or in showdowns.)
> When I conquer, if there is a friendly gear with [Deploy] here, channel 1 rune exhausted.
-/
def RAD_091.meta : CardDef :=
  { id := ⟨"RAD-091"⟩,
    name := "Jarvan IV",
    subtitle := some "Martial Paragon",
    types := [.unit],
    tags := [⟨"Demacia"⟩, ⟨"Jarvan IV"⟩],
    domains := [.body],
    cost := some ⟨4, [.domain .body]⟩,
    might := some 4,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Jarvan IV, Martial Paragon: the effect is not written yet. -/
def RAD_091 : CardDef := RAD_091.meta

-- BEGIN GENERATED RAD-092
/--
**Seraphic Wyvern** — Unit · Body · Energy 7 · Might 7
Printings: RAD-092/167

> If you would channel runes, channel that many runes plus 1 exhausted rune instead.
-/
def RAD_092.meta : CardDef :=
  { id := ⟨"RAD-092"⟩,
    name := "Seraphic Wyvern",
    types := [.unit],
    tags := [⟨"Mount Targon"⟩, ⟨"Dragon"⟩],
    domains := [.body],
    cost := some ⟨7, []⟩,
    might := some 7,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Seraphic Wyvern. -/
def RAD_092 : CardDef :=
  { RAD_092.meta with
    abilities := [.passive .always [.additionalExhaustedRunes 1]],
    status := .full }

-- BEGIN GENERATED RAD-093
/--
**Disposal Expert** — Unit · Chaos · Energy 4 · Might 3
Printings: RAD-093/167

> I enter ready if you control no other units.
> [Disarm 2] (When I attack, give an enemy unit here -2 :rb_might: this turn.)
-/
def RAD_093.meta : CardDef :=
  { id := ⟨"RAD-093"⟩,
    name := "Disposal Expert",
    types := [.unit],
    tags := [⟨"Bandle City"⟩, ⟨"Yordle"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 3,
    keywords := [{ keyword := .disarm, arg := .amount 2 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Disposal Expert. -/
def RAD_093 : CardDef :=
  { RAD_093.meta with
    abilities := [.passive (.not (.exists (.all .friendly .anywhere [.ofType .unit, .notSelf])))
      [.entersReady .self]],
    status := .full }

-- BEGIN GENERATED RAD-094
/--
**Explosimian** — Unit · Chaos · Energy 6 · Might 6
Printings: RAD-094/167

> When I hold, play three Bomb gear tokens to a single battlefield. (They have [Deploy]. When
> each dies, deal 2 to an enemy there and kill your other Bombs there.)
-/
def RAD_094.meta : CardDef :=
  { id := ⟨"RAD-094"⟩,
    name := "Explosimian",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.chaos],
    cost := some ⟨6, []⟩,
    might := some 6,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Explosimian. -/
def RAD_094 : CardDef :=
  { RAD_094.meta with
    abilities := [.triggered (.onSelf .hold) (.of [] (playBombs 3)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-095
/--
**Momentary Companion** — Unit · Chaos · Energy 4 · Might 4
Printings: RAD-095/167

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me, if it's not your turn, give me [Temporary]. (Kill me at the start of my
> controller's Beginning Phase, before scoring.)
-/
def RAD_095.meta : CardDef :=
  { id := ⟨"RAD-095"⟩,
    name := "Momentary Companion",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Demon"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Momentary Companion gains Temporary when played outside its controller's turn. -/
def RAD_095 : CardDef :=
  { RAD_095.meta with
    abilities := [.triggered { event := .play, condition := .not .yourTurn }
      (.of [] (.grant .self (.keyword .it ⟨.temporary, .none⟩) .permanent)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-096
/--
**Satchel Charge** — Spell · Chaos · Energy 3 + Power 1
Printings: RAD-096/167

> [Action] (Play on your turn or in showdowns.)
> Move a friendly unit, then play a Bomb gear token to a battlefield. (It has [Deploy]. When it
> dies, deal 2 to an enemy there and kill your other Bombs there.)
-/
def RAD_096.meta : CardDef :=
  { id := ⟨"RAD-096"⟩,
    name := "Satchel Charge",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Satchel Charge. -/
def RAD_096 : CardDef :=
  { RAD_096.meta with
    spellEffect := some {
      choices := [.targetOf .one .friendly .anywhere [.ofType .unit]]
      moveChoice := some ⟨0, true, .nil⟩
      body := .moveChoosing 0 true .nil (playBombs 1) true },
    status := .full }

-- BEGIN GENERATED RAD-097
/--
**Siren of the Shallows** — Unit · Chaos · Energy 2 · Might 1
Printings: RAD-097/167

> [Disarm] (When I attack, give an enemy unit here -1 :rb_might: this turn.)
> [Ganking] (I can move from battlefield to battlefield.)
-/
def RAD_097.meta : CardDef :=
  { id := ⟨"RAD-097"⟩,
    name := "Siren of the Shallows",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 1,
    keywords := [{ keyword := .disarm, arg := .amount 1 },
      { keyword := .ganking }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Siren of the Shallows. -/
def RAD_097 : CardDef :=
  { RAD_097.meta with
    status := .full }

-- BEGIN GENERATED RAD-098
/--
**Siren's Song** — Spell · Chaos · Energy 2
Printings: RAD-098/167

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Move an enemy unit that moved this turn.
-/
def RAD_098.meta : CardDef :=
  { id := ⟨"RAD-098"⟩,
    name := "Siren's Song",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Siren's Song moves a chosen enemy Unit that has already moved this turn. -/
def RAD_098 : CardDef :=
  { RAD_098.meta with
    spellEffect := some {
      choices := [.targetOf .one .enemy .anywhere [.ofType .unit, .movedThisTurn]]
      moveChoice := some ⟨0, true, .nil⟩
      body := .moveChoosing 0 true .nil .nop false },
    status := .full }

-- BEGIN GENERATED RAD-099
/--
**Suave Negotiator** — Unit · Chaos · Energy 3 · Might 3
Printings: RAD-099/167

> When you play me, choose an opponent. You and that player each draw 1.
-/
def RAD_099.meta : CardDef :=
  { id := ⟨"RAD-099"⟩,
    name := "Suave Negotiator",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩, ⟨"Demon"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Suave Negotiator draws one card for its controller and one for a chosen opponent. -/
def RAD_099 : CardDef :=
  { RAD_099.meta with
    abilities := [.triggered (.onSelf .play)
      { playerTarget := some .enemy
        body := .seqOf [.prim (.draw .you (.const 1)), .prim (.draw (.chosen 0) (.const 1))] }
      .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-100
/--
**The Waters' Wage** — Spell · Chaos · Energy 1
Printings: RAD-100/167

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> Play a Gold gear token exhausted. If it's your turn and you played this from face down, play
> three ready Gold gear tokens instead. (Gold tokens have "[Reaction][>] Kill this,
> :rb_exhaust:: [Add] :rb_rune_rainbow:.")
-/
def RAD_100.meta : CardDef :=
  { id := ⟨"RAD-100"⟩,
    name := "The Waters' Wage",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- The Waters' Wage makes three ready Gold only when revealed on its controller's turn. -/
def RAD_100 : CardDef :=
  { RAD_100.meta with
    spellEffect := some (.of [] (.ifThen (.and .yourTurn .fromHidden)
      (.prim (.create "Gold" (.const 3) .atBase true))
      (.prim (.create "Gold" (.const 1) .atBase false)))),
    status := .full }

-- BEGIN GENERATED RAD-101
/--
**An Offer You Can't Refuse** — Spell · Chaos · Energy 2
Printings: RAD-101/167

> [Action] (Play on your turn or in showdowns.)
> Kill a gear. Its controller plays a Gold gear token exhausted. (It has "[Reaction][>] Kill
> this, :rb_exhaust:: [Add] :rb_rune_rainbow:.")
-/
def RAD_101.meta : CardDef :=
  { id := ⟨"RAD-101"⟩,
    name := "An Offer You Can't Refuse",
    types := [.spell],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- An Offer You Can't Refuse kills Gear and gives its controller an exhausted Gold token. -/
def RAD_101 : CardDef :=
  { RAD_101.meta with
    spellEffect := some {
      choices := [.targetOf .one .any .anywhere [.ofType .gear]]
      body := .eachPlayer (.controllerOf 0) (.seqOf [.prim (.kill (.slot 0)),
        .prim (.create "Gold" (.const 1) .atBase false)])
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-102
/--
**Demon Shade** — Spell · Fury · Energy 3
Printings: RAD-102/167

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> Choose a friendly unit, then choose one —Move it to an open battlefield.Give it [Ganking] this
> turn if there are no open battlefields. (It can move from battlefield to battlefield.)
-/
def RAD_102.meta : CardDef :=
  { id := ⟨"RAD-102"⟩,
    name := "Demon Shade",
    types := [.spell],
    domains := [.fury],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Demon Shade: the effect is not written yet. -/
def RAD_102 : CardDef := RAD_102.meta

-- BEGIN GENERATED RAD-103
/--
**Gutter Guardian** — Unit · Chaos · Energy 3 · Might 3
Printings: RAD-103/167

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> [Show Off] a card with [Hidden]. (As you play me, you may reveal such a card from hand or pick
> another friendly one on the board.)
> When you play me, if you showed off, [Add] :rb_rune_rainbow:.
-/
def RAD_103.meta : CardDef :=
  { id := ⟨"RAD-103"⟩,
    name := "Gutter Guardian",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .hidden },
      { keyword := .showOff, arg := .object "a card with [Hidden]" }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Gutter Guardian adds one Power if it showed a card with Hidden. -/
def RAD_103 : CardDef :=
  { RAD_103.meta with
    showOffRequirement := some { filters := .ofList [.hasKeyword .hidden], cardsOnly := true },
    abilities := [.triggered { event := .play, condition := .showedOff }
      (.of [] (.prim (.addPower .you (.const 1) none none))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-104
/--
**Pitiless Stalker** — Unit · Chaos · Energy 5 + Power 1 · Might 5
Printings: RAD-104/167

> :rb_exhaust:: [Stun] an enemy unit. (It doesn't deal combat damage this turn.)
-/
def RAD_104.meta : CardDef :=
  { id := ⟨"RAD-104"⟩,
    name := "Pitiless Stalker",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Cat"⟩],
    domains := [.chaos],
    cost := some ⟨5, [.domain .chaos]⟩,
    might := some 5,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Pitiless Stalker. -/
def RAD_104 : CardDef :=
  { RAD_104.meta with
    abilities := [.activated [.exhaustSelf] .normal
        (.of [.targetOf .one .enemy .anywhere [.ofType .unit]]
        (.prim (.stun (.slot 0)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-105
/--
**Reckless Innovator** — Unit · Chaos · Energy 3 · Might 3
Printings: RAD-105/167

> [Accelerate] (You may pay :rb_energy_1::rb_rune_chaos: as an additional cost to have me enter
> ready.)
> When I become exhausted, choose one —Play a Gold gear token exhausted. (It has "[Reaction][>]
> Kill this, :rb_exhaust:: [Add] :rb_rune_rainbow:.")Pay :rb_rune_chaos: to draw 1.
-/
def RAD_105.meta : CardDef :=
  { id := ⟨"RAD-105"⟩,
    name := "Reckless Innovator",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .accelerate }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Reckless Innovator can make Gold or pay Chaos Power to draw when exhausted. -/
def RAD_105 : CardDef :=
  { RAD_105.meta with
    abilities := [.triggered (.onSelf .exhaust)
      { body := .nop, modes := [
        ⟨"Play an exhausted Gold", [], .prim (.create "Gold" (.const 1) .atBase false)⟩,
        ⟨"Pay Chaos Power to draw", [], .payThen ⟨0, [.domain .chaos]⟩ (.prim (.draw .you (.const 1)))⟩] }
      .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-106
/--
**The Good Stuff** — Gear · Chaos · Energy 3 + Power 1
Printings: RAD-106/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> When you play this, discard 1, then draw 3.
> When you hold here, return this to its owner's hand.
-/
def RAD_106.meta : CardDef :=
  { id := ⟨"RAD-106"⟩,
    name := "The Good Stuff",
    types := [.gear],
    domains := [.chaos],
    cost := some ⟨3, [.domain .chaos]⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- The Good Stuff. -/
def RAD_106 : CardDef :=
  { RAD_106.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.seqOf [.prim (.discard .you (.const 1)), .prim (.draw .you (.const 3))])) .unlimited,
      .triggered (.onSelf .hold) (.of [] (.prim (.returnToHand .self))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-107
/--
**Bedeviling Stranger** — Unit · Chaos · Energy 2 · Might 2
Printings: RAD-107/167

> [Hidden] (Hide now for :rb_rune_rainbow: to react with later for :rb_energy_0:.)
> When you play me, choose a battlefield. If there are 4 or more units there, you may return an
> enemy unit there to its owner's hand.
-/
def RAD_107.meta : CardDef :=
  { id := ⟨"RAD-107"⟩,
    name := "Bedeviling Stranger",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Demon"⟩],
    domains := [.chaos],
    cost := some ⟨2, []⟩,
    might := some 2,
    keywords := [{ keyword := .hidden }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Choose a Battlefield and an enemy there, then check the Unit count on resolution. -/
def RAD_107 : CardDef :=
  let there := Selector.all .any .atBattlefield [.ofType .unit, .at_ (.slot 0)]
  { RAD_107.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .atBattlefield [.ofType .battlefield],
        .targetOf .one .enemy .atBattlefield [.ofType .unit, .at_ (.slot 0)]]
        (.ifThen (.cmp .ge (.count there) (.const 4))
          (.may (.prim (.returnToHand (.slot 1)))) .nop)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-108
/--
**Bushwhack Trap** — Gear · Fury · Energy 1
Printings: RAD-108/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> While you or an ally control this battlefield, that player may hide an additional card here.
-/
def RAD_108.meta : CardDef :=
  { id := ⟨"RAD-108"⟩,
    name := "Bushwhack Trap",
    types := [.gear],
    tags := [⟨"Device"⟩],
    domains := [.fury],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Bushwhack Trap: the effect is not written yet. -/
def RAD_108 : CardDef := RAD_108.meta

-- BEGIN GENERATED RAD-110
/--
**Lulu, Whimsical** — Unit · Chaos · Energy 3 · Might 3
Printings: RAD-110/167

> When I move, you may have another unit's base Might become 4 this turn.
-/
def RAD_110.meta : CardDef :=
  { id := ⟨"RAD-110"⟩,
    name := "Lulu",
    subtitle := some "Whimsical",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Lulu"⟩, ⟨"Bandle City"⟩, ⟨"Yordle"⟩],
    domains := [.chaos],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Lulu, Whimsical can set another Unit's base Might to 4 this turn when she moves. -/
def RAD_110 : CardDef :=
  { RAD_110.meta with
    abilities := [.triggered { event := .move, optional := true }
      (.of [.targetOf .one .any .anywhere [.ofType .unit, .notSelf]]
        (.prim (.setBaseMight (.slot 0) (.const 4)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-111
/--
**Mechanical Bandit** — Gear · Fury · Energy 4 + Power 1
Printings: RAD-111/167

> At the start of your Beginning Phase, each player reveals the top card of their Main Deck. If
> you revealed a card with the lowest Energy cost, draw it. Recycle the rest.
-/
def RAD_111.meta : CardDef :=
  { id := ⟨"RAD-111"⟩,
    name := "Mechanical Bandit",
    types := [.gear],
    tags := [⟨"Device"⟩],
    domains := [.fury],
    cost := some ⟨4, [.domain .fury]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Mechanical Bandit: the effect is not written yet. -/
def RAD_111 : CardDef := RAD_111.meta

-- BEGIN GENERATED RAD-112
/--
**Ziggs, Explosive** — Unit · Chaos · Energy 4 · Might 4
Printings: RAD-112/167, RAD-112a/167

> :rb_energy_1:, :rb_exhaust:: Play a Bomb gear token to a battlefield. (It has [Deploy]. When
> it dies, deal 2 to an enemy there and kill your other Bombs there.)
> When I defend, you may kill a friendly gear to give me +2 :rb_might: this turn.
-/
def RAD_112.meta : CardDef :=
  { id := ⟨"RAD-112"⟩,
    name := "Ziggs",
    subtitle := some "Explosive",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Ziggs"⟩, ⟨"Zaun"⟩, ⟨"Yordle"⟩],
    domains := [.chaos],
    cost := some ⟨4, []⟩,
    might := some 4,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Ziggs, Explosive. -/
def RAD_112 : CardDef :=
  { RAD_112.meta with
    abilities := [.activated [.pay ⟨1, []⟩, .exhaustSelf] .normal
        (.of [] (playBombs 1)) .unlimited,
      .triggered { event := .defend, optional := true, cost := .killFriendly 1 (.ofList [.ofType .gear]) }
        (.of [] (.grant .self (.mightPlus .it (.const 2)) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-113
/--
**Angler Wyrm** — Unit · Chaos · Energy 8 · Might 8
Printings: RAD-113/167

> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
> :rb_exhaust:: Choose an opponent. They must move a unit they control to my battlefield.
-/
def RAD_113.meta : CardDef :=
  { id := ⟨"RAD-113"⟩,
    name := "Angler Wyrm",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩, ⟨"Dragon"⟩],
    domains := [.chaos],
    cost := some ⟨8, []⟩,
    might := some 8,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Angler Wyrm names an opponent at activation. During resolution that player moves one of
their eligible Units to the Wyrm's Battlefield. -/
def RAD_113 : CardDef :=
  { RAD_113.meta with
    abilities := [.activated [.exhaustSelf] .normal
      { playerTarget := some .enemy
        body := .forceMoveToBattlefield (.chosen 0) (.locationOf .self) } .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-114
/--
**Riven, Deserter** — Unit · Chaos · Energy 5 + Power 1 · Might 5
Printings: RAD-114/167, RAD-114a/167

> When another friendly unit becomes exhausted, give me +1 :rb_might: this turn.
> Exhaust a friendly unit: Ready a unit. Use this ability only once each turn.
-/
def RAD_114.meta : CardDef :=
  { id := ⟨"RAD-114"⟩,
    name := "Riven",
    subtitle := some "Deserter",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Riven"⟩, ⟨"Noxus"⟩],
    domains := [.chaos],
    cost := some ⟨5, [.domain .chaos]⟩,
    might := some 5,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Riven grows when another ally exhausts and can exhaust an ally to ready a chosen Unit. -/
def RAD_114 : CardDef :=
  { RAD_114.meta with
    abilities := [.triggered
        { event := .exhaust, subject := .all .friendly .anywhere [.ofType .unit, .notSelf] }
        (.of [] (.grant .self (.mightPlus .it (.const 1)) .thisTurn)) .unlimited,
      .activated [.exhaustFriendly (.ofList [.ofType .unit])] .normal
        (.of [.targetOf .one .any .anywhere [.ofType .unit]] (.prim (.ready (.slot 0)))) (.perTurn 1)],
    status := .full }

-- BEGIN GENERATED RAD-115
/--
**Transpositionist** — Unit · Chaos · Energy 6 · Might 4
Printings: RAD-115/167

> :rb_rune_chaos:, :rb_exhaust:: Return a friendly unit to its owner's hand. You may play a unit
> with less Might than that unit had, ignoring its cost.
-/
def RAD_115.meta : CardDef :=
  { id := ⟨"RAD-115"⟩,
    name := "Transpositionist",
    types := [.unit],
    tags := [⟨"Bilgewater"⟩],
    domains := [.chaos],
    cost := some ⟨6, []⟩,
    might := some 4,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Transpositionist. -/
def RAD_115 : CardDef :=
  let previousMight : VarId := ⟨"previousMight"⟩
  { RAD_115.meta with
    abilities := [.activated [.pay ⟨0, [.domain .chaos]⟩, .exhaustSelf] .normal
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.bind previousMight (.mightOf (.slot 0)) (.seqOf [
          .prim (.returnToHand (.slot 0)),
          .mayPlayPermanents (.one .friendly .inHand [.ofType .unit, .might .lt (.var previousMight)])
            1 .ignoreBase]))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-116
/--
**Concert Poster** — Gear · Order · Energy 1
Printings: RAD-116/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> When you play this or when you conquer here, you may pay :rb_energy_1: to play a 1 :rb_might:
> Recruit unit token to your base.
-/
def RAD_116.meta : CardDef :=
  { id := ⟨"RAD-116"⟩,
    name := "Concert Poster",
    types := [.gear],
    domains := [.order],
    cost := some ⟨1, []⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Concert Poster. -/
def RAD_116 : CardDef :=
  { RAD_116.meta with
    abilities :=
      let recruit := EffectDef.of [] (.prim (.create "Recruit" (.const 1) .atBase false))
      [.triggered { event := .play, optional := true, cost := .energy 1 } recruit .unlimited,
       .triggered { event := .conquer, optional := true, cost := .energy 1 } recruit .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-117
/--
**For Demacia!** — Spell · Order · Energy 3
Printings: RAD-117/167

> [Reaction] (Play any time, even before spells and abilities resolve.)
> Choose a battlefield. Give friendly units there [Shield 2] this turn. (+2 :rb_might: while
> they're defenders.)
-/
def RAD_117.meta : CardDef :=
  { id := ⟨"RAD-117"⟩,
    name := "For Demacia!",
    types := [.spell],
    domains := [.order],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- For Demacia! -/
def RAD_117 : CardDef :=
  { RAD_117.meta with
    spellEffect := some (.of [.targetOf .one .any .atBattlefield [.ofType .battlefield]]
      (.grant (.all .friendly .atBattlefield [.ofType .unit, .at_ (.slot 0)])
        (.keyword .it ⟨.shield, .amount 2⟩) .thisTurn)),
    status := .full }

-- BEGIN GENERATED RAD-118
/--
**Herald of the Emperor** — Unit · Order · Energy 5 · Might 3
Printings: RAD-118/167

> When you play me, choose a friendly unit. Its base Might becomes 5 this turn.
-/
def RAD_118.meta : CardDef :=
  { id := ⟨"RAD-118"⟩,
    name := "Herald of the Emperor",
    types := [.unit],
    tags := [⟨"Shurima"⟩],
    domains := [.order],
    cost := some ⟨5, []⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Herald of the Emperor. -/
def RAD_118 : CardDef :=
  { RAD_118.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.prim (.setBaseMight (.slot 0) (.const 5)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-119
/--
**Hunting Dog** — Unit · Order · Energy 3 · Might 3
Printings: RAD-119/167

> [Deathknell][>] Play a 1 :rb_might: Bird unit token with [Deflect] to your base. (When I die,
> get the effect. Opponents must pay :rb_rune_rainbow: to choose a [Deflect] unit with a spell
> or ability.)
-/
def RAD_119.meta : CardDef :=
  { id := ⟨"RAD-119"⟩,
    name := "Hunting Dog",
    types := [.unit],
    tags := [⟨"Demacia"⟩, ⟨"Dog"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Hunting Dog. -/
def RAD_119 : CardDef :=
  { RAD_119.meta with
    abilities := [.triggered (.onSelf .die)
        (.of []
        (.prim (.create "Bird" (.const 1) .atBase false))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-120
/--
**Meticulous Restorationist** — Unit · Order · Energy 2 · Might 2
Printings: RAD-120/167

> When you play a card with Energy cost :rb_energy_7: or more, you may play me from your trash
> for :rb_rune_order:.
-/
def RAD_120.meta : CardDef :=
  { id := ⟨"RAD-120"⟩,
    name := "Meticulous Restorationist",
    types := [.unit],
    tags := [⟨"Piltover"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 2,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Meticulous Restorationist. -/
def RAD_120 : CardDef :=
  { RAD_120.meta with
    abilities := [.triggered { event := .playCardFromTrashAtEnergy 7, optional := true }
      (.of [] (.playSelfFromTrash ⟨0, [.domain .order]⟩ .normal)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-121
/--
**One-Two Punch** — Spell · Order · Energy 3
Printings: RAD-121/167

> [Action] (Play on your turn or in showdowns.)
> [Buff] a friendly unit and [Stun] an enemy unit. (Give the friendly unit a +1 :rb_might: buff
> if it doesn't have one. The enemy unit doesn't deal combat damage this turn.)
-/
def RAD_121.meta : CardDef :=
  { id := ⟨"RAD-121"⟩,
    name := "One-Two Punch",
    types := [.spell],
    domains := [.order],
    cost := some ⟨3, []⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- One-Two Punch. -/
def RAD_121 : CardDef :=
  { RAD_121.meta with
    spellEffect := some (.of [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .enemy .anywhere [.ofType .unit]]
      (.seqOf [.prim (.buff (.slot 0)), .prim (.stun (.slot 1))])),
    status := .full }

-- BEGIN GENERATED RAD-122
/--
**Party Crasher** — Unit · Order · Energy 9 + Power 1 · Might 6
Printings: RAD-122/167

> I cost :rb_energy_1: less for each exhausted unit you control.
> [Tank] (I must be assigned combat damage first.)
-/
def RAD_122.meta : CardDef :=
  { id := ⟨"RAD-122"⟩,
    name := "Party Crasher",
    types := [.unit],
    tags := [⟨"Zaun"⟩],
    domains := [.order],
    cost := some ⟨9, [.domain .order]⟩,
    might := some 6,
    keywords := [{ keyword := .tank }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Party Crasher costs one less Energy per exhausted Unit on its controller's side. -/
def RAD_122 : CardDef :=
  { RAD_122.meta with
    abilities := [.passive .always
      [.costMinus .self (.count (.all .friendly .anywhere [.ofType .unit, .exhausted]))]],
    status := .full }

-- BEGIN GENERATED RAD-123
/--
**Protector's Shield** — Gear · Order · Energy 2 + Power 1 · Might 1
Printings: RAD-123/167

> [Quick-Draw] (This has [Reaction]. When you play it, attach it to a unit you control.)
> [Equip] :rb_energy_1: (:rb_energy_1:: Attach this to a unit you control.)

Effect (given to the unit it is attached to):

> [Tank] (I must be assigned combat damage first.)
-/
def RAD_123.meta : CardDef :=
  { id := ⟨"RAD-123"⟩,
    name := "Protector's Shield",
    types := [.gear],
    tags := [⟨"Equipment"⟩],
    domains := [.order],
    cost := some ⟨2, [.domain .order]⟩,
    might := some 1,
    mightBonus := some 1,
    keywords := [{ keyword := .quickDraw },
      { keyword := .equip, arg := .cost ⟨1, []⟩ }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Protector's Shield. -/
def RAD_123 : CardDef :=
  { RAD_123.meta with
    grants := [.passive .always [.keyword .self { keyword := .tank }]],
    status := .full }

-- BEGIN GENERATED RAD-124
/--
**Burn Away** — Spell · Order · Energy 3 + Power 1
Printings: RAD-124/167

> Banish a unit with 3 :rb_might: or less or a gear. [Burn 2]. (Put the top 2 cards of your Main
> Deck into your trash.)
-/
def RAD_124.meta : CardDef :=
  { id := ⟨"RAD-124"⟩,
    name := "Burn Away",
    types := [.spell],
    domains := [.order],
    cost := some ⟨3, [.domain .order]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Burn Away banishes a small Unit or Gear, then burns two cards. -/
def RAD_124 : CardDef :=
  { RAD_124.meta with
    spellEffect := some {
      choices := [.targetOf .one .any .anywhere
        [.either (.both (.ofType .unit) (.might .le (.const 3))) (.ofType .gear)]]
      body := .seqOf [.prim (.banish (.slot 0)), .prim (.burn .you (.const 2))]
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-125
/--
**Dune Devourer** — Unit · Order · Energy 7 + Power 1 · Might 7
Printings: RAD-125/167

> You may kill a friendly unit as an additional cost to play me. If you do, I cost :rb_energy_2:
> less.
> [Deflect] (Opponents must pay :rb_rune_rainbow: to choose me with a spell or ability.)
-/
def RAD_125.meta : CardDef :=
  { id := ⟨"RAD-125"⟩,
    name := "Dune Devourer",
    types := [.unit],
    tags := [⟨"The Void"⟩],
    domains := [.order],
    cost := some ⟨7, [.domain .order]⟩,
    might := some 7,
    keywords := [{ keyword := .deflect, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Dune Devourer may sacrifice a friendly Unit to reduce its Energy cost. -/
def RAD_125 : CardDef :=
  { RAD_125.meta with
    playExtra := some (.killUnit, false),
    paidCut := some (.energy 2),
    status := .full }

-- BEGIN GENERATED RAD-126
/--
**Mournful Spirit** — Unit · Order · Energy 4 · Might 1
Printings: RAD-126/167

> [Deathknell][>] You may kill a unit or gear here. (When I die, get the effect.)
-/
def RAD_126.meta : CardDef :=
  { id := ⟨"RAD-126"⟩,
    name := "Mournful Spirit",
    types := [.unit],
    tags := [⟨"Shadow Isles"⟩, ⟨"Spirit"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 1,
    keywords := [{ keyword := .deathknell }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Mournful Spirit can kill a Unit or Gear at the location where it died. -/
def RAD_126 : CardDef :=
  { RAD_126.meta with
    abilities := [.triggered { event := .deathknell, optional := true }
      (.of [.targetOf .one .any .anywhere [.at_ .self, .either (.ofType .unit) (.ofType .gear)]]
        (.prim (.kill (.slot 0)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-127
/--
**Rousing Display** — Spell · Order · Energy 5
Printings: RAD-127/167

> [Show Off] a card with Energy cost :rb_energy_7: or more. (As you play this, you may reveal
> such a card from hand or pick a friendly one.)
> Play two 1 :rb_might: Recruit unit tokens to your base. If you showed off, play four to your
> base instead.
-/
def RAD_127.meta : CardDef :=
  { id := ⟨"RAD-127"⟩,
    name := "Rousing Display",
    types := [.spell],
    domains := [.order],
    cost := some ⟨5, []⟩,
    keywords :=
      [{ keyword := .showOff, arg := .object "a card with Energy cost :rb_energy_7: or more" }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Rousing Display plays four Recruits instead of two after showing a card with base Energy 7+. -/
def RAD_127 : CardDef :=
  { RAD_127.meta with
    showOffRequirement := some { filters := .ofList [.cost .ge (.const 7)], cardsOnly := true },
    spellEffect := some (.of [] (.ifThen .showedOff
      (.prim (.create "Recruit" (.const 4) .atBase false))
      (.prim (.create "Recruit" (.const 2) .atBase false)))),
    status := .full }

-- BEGIN GENERATED RAD-128
/--
**Steadfast Outrider** — Unit · Order · Energy 4 · Might 3
Printings: RAD-128/167

> [Tank] (I must be assigned combat damage first.)
> While there are 2 or more other friendly units and/or gear at my battlefield, I have +2
> :rb_might:.
-/
def RAD_128.meta : CardDef :=
  { id := ⟨"RAD-128"⟩,
    name := "Steadfast Outrider",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨4, []⟩,
    might := some 3,
    keywords := [{ keyword := .tank }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Steadfast Outrider. -/
def RAD_128 : CardDef :=
  { RAD_128.meta with
    abilities := [.passive (.and (.matches .self .onBattlefield)
      (.cmp .ge (.count (.all .friendly .here
        [.notSelf, .either (.ofType .unit) (.ofType .gear)])) (.const 2)))
      [.mightPlus .self (.const 2)]],
    status := .full }

-- BEGIN GENERATED RAD-129
/--
**Trifarian Captain** — Unit · Order · Energy 2 · Might 1
Printings: RAD-129/167

> When you play me, look at the top 4 cards of your Main Deck. You may reveal from among them a
> unit or gear with Energy cost no more than :rb_energy_3: and with Power cost no more than
> :rb_rune_rainbow: and draw it. Recycle the rest.
-/
def RAD_129.meta : CardDef :=
  { id := ⟨"RAD-129"⟩,
    name := "Trifarian Captain",
    types := [.unit],
    tags := [⟨"Noxus"⟩, ⟨"Trifarian"⟩],
    domains := [.order],
    cost := some ⟨2, []⟩,
    might := some 1,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Trifarian Captain. -/
def RAD_129 : CardDef :=
  let eligible := [.top 4, .either (.ofType .unit) (.ofType .gear),
    .cost .le (.const 3), .powerCost .le (.const 1)]
  let picked := Selector.var pickVar
  let takeOne := Effect.chooseObject .friendly .inMainDeck (.ofList eligible)
    (.seqOf [.prim (.reveal picked), .prim (.drawLooked picked)])
  { RAD_129.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [] (.lookAtTop 4 (.seqOf [
        .ifThen (.cmp .gt (.count (.all .friendly .inMainDeck eligible)) (.const 0))
          (.may takeOne) .nop,
        .recycleLooked]))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-130
/--
**Battlefield Armorer** — Unit · Order · Energy 3 · Might 3
Printings: RAD-130/167

> When a friendly gear at a battlefield dies, you may pay :rb_energy_1: to return it to its
> owner's hand.
-/
def RAD_130.meta : CardDef :=
  { id := ⟨"RAD-130"⟩,
    name := "Battlefield Armorer",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨3, []⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Battlefield Armorer can pay when finalizing to recover the Gear that died at a Battlefield. -/
def RAD_130 : CardDef :=
  { RAD_130.meta with
    abilities := [.triggered
      { event := .die
        subject := .all .friendly .anywhere [.ofType .gear]
        condition := .exists (.locationOf (.slot 0))
        optional := true
        cost := .energy 1 }
      (.of [] (.prim (.returnToHand (.slot 0)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-131
/--
**Demacian Illuminators** — Unit · Order · Energy 3 + Power 1 · Might 3
Printings: RAD-131/167

> When one or more friendly units die, [Buff] a friendly unit. (Give it a +1 :rb_might: buff if
> it doesn't have one.)
-/
def RAD_131.meta : CardDef :=
  { id := ⟨"RAD-131"⟩,
    name := "Demacian Illuminators",
    types := [.unit],
    tags := [⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨3, [.domain .order]⟩,
    might := some 3,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Demacian Illuminators buffs one chosen friendly Unit per group of friendly deaths. -/
def RAD_131 : CardDef :=
  { RAD_131.meta with
    abilities := [.triggered
      { event := .die
        subject := .all .friendly .anywhere [.ofType .unit]
        occurrence := .deathGroup }
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit]] (.prim (.buff (.slot 0)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-132
/--
**Heimerdinger, Academy Instructor** — Unit · Order · Energy 6 + Power 1 · Might 5
Printings: RAD-132/167

> If you would play a unit token to a location while I'm at a battlefield, you may play a 3
> :rb_might: Mech unit token to that same location instead.
-/
def RAD_132.meta : CardDef :=
  { id := ⟨"RAD-132"⟩,
    name := "Heimerdinger",
    subtitle := some "Academy Instructor",
    types := [.unit],
    tags := [⟨"Yordle"⟩, ⟨"Heimerdinger"⟩, ⟨"Piltover"⟩],
    domains := [.order],
    cost := some ⟨6, [.domain .order]⟩,
    might := some 5,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Heimerdinger, Academy Instructor: the effect is not written yet. -/
def RAD_132 : CardDef := RAD_132.meta

-- BEGIN GENERATED RAD-133
/--
**Jarvan IV, Royal Heir** — Unit · Order · Energy 7 + Power 1 · Might 7
Printings: RAD-133/167, RAD-133a/167

> [Assault] (+1 :rb_might: while I'm attacking.)
> [Tank] (I must be assigned combat damage first.)
> When I attack, you may move a unit you control to my battlefield.
-/
def RAD_133.meta : CardDef :=
  { id := ⟨"RAD-133"⟩,
    name := "Jarvan IV",
    subtitle := some "Royal Heir",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Jarvan IV"⟩, ⟨"Demacia"⟩],
    domains := [.order],
    cost := some ⟨7, [.domain .order]⟩,
    might := some 7,
    keywords := [{ keyword := .assault, arg := .amount 1 },
      { keyword := .tank }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- On attack, Jarvan can move a friendly Unit to the Battlefield where he attacked. -/
def RAD_133 : CardDef :=
  { RAD_133.meta with
    abilities := [.triggered { Trigger.onSelf .attack with optional := true }
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.prim (.move (.slot 0) (.at_
          (.all .any .atBattlefield [.ofType .battlefield, .atEventBattlefield none]))))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-134
/--
**Raucous Anthem** — Spell · Order · Energy 7 + Power 1
Printings: RAD-134/167

> Ready your units and give them +3 :rb_might: this turn.
-/
def RAD_134.meta : CardDef :=
  { id := ⟨"RAD-134"⟩,
    name := "Raucous Anthem",
    types := [.spell],
    domains := [.order],
    cost := some ⟨7, [.domain .order]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Raucous Anthem. -/
def RAD_134 : CardDef :=
  { RAD_134.meta with
    spellEffect := some (.of []
      (let units := Selector.all .friendly .anywhere [.ofType .unit]
       .seqOf [.prim (.ready units), .grant units (.mightPlus .it (.const 3)) .thisTurn])),
    status := .full }

-- BEGIN GENERATED RAD-135
/--
**Remember the Fallen** — Spell · Order · Energy 8 + Power 2
Printings: RAD-135/167

> Play up to 3 units and/or gear from your trash, each with Energy cost no more than
> :rb_energy_3: and Power cost no more than :rb_rune_rainbow:, ignoring their costs.
-/
def RAD_135.meta : CardDef :=
  { id := ⟨"RAD-135"⟩,
    name := "Remember the Fallen",
    types := [.spell],
    domains := [.order],
    cost := some ⟨8, [.domain .order, .domain .order]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Remember the Fallen. -/
def RAD_135 : CardDef :=
  { RAD_135.meta with
    spellEffect := some (.of [] (.mayPlayPermanents
      (.one .friendly .inTrash [.either (.ofType .unit) (.ofType .gear),
        .cost .le (.const 3), .powerCost .le (.const 1)]) 3 .ignoreBase)),
    status := .full }

-- BEGIN GENERATED RAD-136
/--
**Dockside Lock-Up** — Gear · Order · Energy 6 + Power 2
Printings: RAD-136/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> When you play this, banish a unit here.
> When you hold here, kill this to play the banished card, ignoring its cost. (Tokens aren't
> cards.)
-/
def RAD_136.meta : CardDef :=
  { id := ⟨"RAD-136"⟩,
    name := "Dockside Lock-Up",
    types := [.gear],
    domains := [.order],
    cost := some ⟨6, [.domain .order, .domain .order]⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Dockside Lock-Up. -/
def RAD_136 : CardDef :=
  { RAD_136.meta with
    abilities := [.triggered (.onSelf .play)
      (.of [.targetOf .one .any .here [.ofType .unit]]
        (.prim (.banishWith (.slot 0)))) .unlimited,
      .triggered { event := .hold, cost := .killFriendly 1 (.ofList [.sameAs .self]) }
        (.of [] (.playCard (.one .any .inBanishment [.banishedWithMe]) .ignoreBase)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-137
/--
**Mordekaiser, Dominating** — Unit · Order · Energy 9 + Power 2 · Might 8
Printings: RAD-137/167, RAD-137a/167

> When you play me or when I attack, you may discard 1 to kill a unit or gear.
-/
def RAD_137.meta : CardDef :=
  { id := ⟨"RAD-137"⟩,
    name := "Mordekaiser",
    subtitle := some "Dominating",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Mordekaiser"⟩, ⟨"Noxus"⟩, ⟨"Spirit"⟩],
    domains := [.order],
    cost := some ⟨9, [.domain .order, .domain .order]⟩,
    might := some 8,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Mordekaiser, Dominating. -/
def RAD_137 : CardDef :=
  let kill := EffectDef.of
    [.targetOf .one .any .anywhere [.either (.ofType .unit) (.ofType .gear)]]
    (.prim (.kill (.slot 0)))
  { RAD_137.meta with
    abilities := [.triggered { event := .play, optional := true, cost := .discard 1 } kill .unlimited,
      .triggered { event := .attack, optional := true, cost := .discard 1 } kill .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-139
/--
**Boy Who Shattered Time** — Legend · Fury/Mind
Printings: RAD-139/167, RAD-168/167

> [Empower] —  :rb_energy_1:, :rb_exhaust: (Use only if not Empowered.)
> Disempower me, :rb_exhaust:: Reduce the cost of the next unit you play this turn by
> :rb_energy_2::rb_rune_rainbow: and give it "Kill me at end of turn."
-/
def RAD_139.meta : CardDef :=
  { id := ⟨"RAD-139"⟩,
    name := "Boy Who Shattered Time",
    types := [.legend],
    tags := [⟨"Ekko"⟩],
    domains := [.fury, .mind],
    keywords := [{ keyword := .empower }],
    sets := [⟨"RAD"⟩] }  -- keyword cost unread
-- END GENERATED

/-- Boy Who Shattered Time: the effect is not written yet. -/
def RAD_139 : CardDef := RAD_139.meta

-- BEGIN GENERATED RAD-140
/--
**Chronobreak** — Spell · Fury/Mind · Energy 2
Printings: RAD-140/167

> As an additional cost to play this, pay any amount of Power.
> Banish that many units you control, then for each, its owner plays that unit back to the same
> location or to their base, ignoring its cost. (You choose the order.)
-/
def RAD_140.meta : CardDef :=
  { id := ⟨"RAD-140"⟩,
    name := "Chronobreak",
    types := [.spell],
    tags := [⟨"Ekko"⟩],
    domains := [.fury, .mind],
    cost := some ⟨2, []⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Chronobreak: the effect is not written yet. -/
def RAD_140 : CardDef := RAD_140.meta

-- BEGIN GENERATED RAD-141
/--
**Hexplosives Expert** — Legend · Fury/Chaos
Printings: RAD-141/167, RAD-169/167

> :rb_energy_1::rb_rune_rainbow:, :rb_exhaust:: Play a Bomb gear token to a battlefield. (It has
> [Deploy]. When it dies, deal 2 to an enemy there and kill your other Bombs there.)
-/
def RAD_141.meta : CardDef :=
  { id := ⟨"RAD-141"⟩,
    name := "Hexplosives Expert",
    types := [.legend],
    tags := [⟨"Ziggs"⟩],
    domains := [.fury, .chaos],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Hexplosives Expert. -/
def RAD_141 : CardDef :=
  { RAD_141.meta with
    abilities := [.activated [.pay ⟨1, [.any]⟩, .exhaustSelf] .normal
      (.of [] (playBombs 1)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-142
/--
**Hexplosive Minefield** — Spell · Fury/Chaos · Energy 2 + Power 1
Printings: RAD-142/167

> [Action] (Play on your turn or in showdowns.)
> Kill any number of friendly Bomb tokens. At end of turn, play that many Bomb tokens to a
> single battlefield.
-/
def RAD_142.meta : CardDef :=
  { id := ⟨"RAD-142"⟩,
    name := "Hexplosive Minefield",
    types := [.spell],
    tags := [⟨"Ziggs"⟩],
    domains := [.fury, .chaos],
    cost := some ⟨2, [.any]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Hexplosive Minefield: the effect is not written yet. -/
def RAD_142 : CardDef := RAD_142.meta

-- BEGIN GENERATED RAD-143
/--
**Iron Revenant** — Legend · Fury/Order
Printings: RAD-143/167, RAD-170/167

> [Reaction][>] Banish a unit or gear from your trash, :rb_exhaust:: [Add] :rb_rune_rainbow:.
> Spend this Power only to play units or gear. (Abilities that add resources can't be reacted
> to.)
-/
def RAD_143.meta : CardDef :=
  { id := ⟨"RAD-143"⟩,
    name := "Iron Revenant",
    types := [.legend],
    tags := [⟨"Mordekaiser"⟩],
    domains := [.fury, .order],
    keywords := [{ keyword := .reaction }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Iron Revenant: the effect is not written yet. -/
def RAD_143 : CardDef := RAD_143.meta

-- BEGIN GENERATED RAD-144
/--
**Realm of Death** — Spell · Fury/Order · Energy 2 + Power 1
Printings: RAD-144/167

> Give an enemy unit -2 :rb_might: this turn and a friendly unit +2 :rb_might: this turn. They
> deal damage equal to their Mights to each other.
-/
def RAD_144.meta : CardDef :=
  { id := ⟨"RAD-144"⟩,
    name := "Realm of Death",
    types := [.spell],
    supertypes := [.signature],
    tags := [⟨"Mordekaiser"⟩],
    domains := [.fury, .order],
    cost := some ⟨2, [.own]⟩,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Realm of Death changes an enemy and an ally's Mights before they exchange simultaneous damage. -/
def RAD_144 : CardDef :=
  { RAD_144.meta with
    spellEffect := some {
      choices := [.targetOf .one .enemy .anywhere [.ofType .unit],
        .targetOf .one .friendly .anywhere [.ofType .unit]]
      body := .seqOf [.grant (.slot 0) (.mightMinus .it (.const 2)) .thisTurn,
        .grant (.slot 1) (.mightPlus .it (.const 2)) .thisTurn,
        .prim (.exchangeDamage (.slot 0) (.slot 1))]
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-145
/--
**Lady of Clockwork** — Legend · Calm/Mind
Printings: RAD-145/167, RAD-171/167

> At the start of your Main Phase, you may pay :rb_energy_1: to choose a friendly gear. It
> becomes a unit gear with Might equal to its Energy cost until you choose another gear with me.
-/
def RAD_145.meta : CardDef :=
  { id := ⟨"RAD-145"⟩,
    name := "Lady of Clockwork",
    types := [.legend],
    tags := [⟨"Orianna"⟩],
    domains := [.calm, .mind],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Lady of Clockwork: the effect is not written yet. -/
def RAD_145 : CardDef := RAD_145.meta

-- BEGIN GENERATED RAD-146
/--
**The Ball** — Gear · Calm/Mind · Energy 5 + Power 1
Printings: RAD-146/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> [Ganking] (While this is a unit, it can move from battlefield to battlefield.)
> When you play or move this, choose one —Draw 1.Deal 2 to enemy units here.
-/
def RAD_146.meta : CardDef :=
  { id := ⟨"RAD-146"⟩,
    name := "The Ball",
    types := [.gear],
    supertypes := [.signature],
    tags := [⟨"Orianna"⟩],
    domains := [.calm, .mind],
    cost := some ⟨5, [.own]⟩,
    keywords := [{ keyword := .deploy },
      { keyword := .ganking }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- The Ball. -/
def RAD_146 : CardDef :=
  let action : EffectDef := { body := .nop, modes := [
    ⟨"Draw 1", [], .prim (.draw .you (.const 1))⟩,
    ⟨"Deal 2 to enemy units here", [],
      .prim (.deal (.all .enemy .here [.ofType .unit]) (.const 2))⟩] }
  { RAD_146.meta with
    abilities := [.triggered (.onSelf .play) action .unlimited,
      .triggered (.onSelf .move) action .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-147
/--
**Pride of Nazumah** — Legend · Calm/Body
Printings: RAD-147/167, RAD-172/167

> :rb_energy_1:, :rb_exhaust:: Give a friendly unit "I have [Assault] equal to my [Shield]" this
> turn. (+1 :rb_might: for each instance of Assault while it's an attacker.)
-/
def RAD_147.meta : CardDef :=
  { id := ⟨"RAD-147"⟩,
    name := "Pride of Nazumah",
    types := [.legend],
    tags := [⟨"K'Sante"⟩],
    domains := [.calm, .body],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Pride of Nazumah. -/
def RAD_147 : CardDef :=
  { RAD_147.meta with
    abilities := [.activated [.pay ⟨1, []⟩, .exhaustSelf] .normal
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.grant (.slot 0) (.keyword .it ⟨.assault, .equalShield⟩) .thisTurn)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-148
/--
**Ntofo Strikes** — Spell · Calm/Body · Energy 2 + Power 1
Printings: RAD-148/167

> [Action] (Play on your turn or in showdowns.)
> Give a friendly unit [Shield 2] this turn, then deal damage equal to its [Shield] to an enemy
> unit. (A unit with Shield has +1 :rb_might: for each instance of Shield while it's a
> defender.)
-/
def RAD_148.meta : CardDef :=
  { id := ⟨"RAD-148"⟩,
    name := "Ntofo Strikes",
    types := [.spell],
    supertypes := [.signature],
    tags := [⟨"K'Sante"⟩],
    domains := [.calm, .body],
    cost := some ⟨2, [.own]⟩,
    keywords := [{ keyword := .action }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Ntofo Strikes grants Shield 2 and uses the resulting Shield count to damage an enemy. -/
def RAD_148 : CardDef :=
  { RAD_148.meta with
    spellEffect := some {
      choices := [.targetOf .one .friendly .anywhere [.ofType .unit],
        .targetOf .one .enemy .anywhere [.ofType .unit]]
      body := .seqOf [.grant (.slot 0) (.keyword .it ⟨.shield, .amount 2⟩) .thisTurn,
        .prim (.deal (.slot 1) (.kwAmount (.slot 0) .shield))]
      recheckTargets := true },
    status := .full }

-- BEGIN GENERATED RAD-149
/--
**The Exile** — Legend · Calm/Chaos
Printings: RAD-149/167, RAD-173/167

> Units you play to battlefields you control enter ready.
-/
def RAD_149.meta : CardDef :=
  { id := ⟨"RAD-149"⟩,
    name := "The Exile",
    types := [.legend],
    tags := [⟨"Riven"⟩],
    domains := [.calm, .chaos],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- The Exile. -/
def RAD_149 : CardDef :=
  { RAD_149.meta with
    abilities := [.passive .always [.unitsEnterReadyAtControlledBattlefields]],
    status := .full }

-- BEGIN GENERATED RAD-150
/--
**Blade of the Exile** — Gear · Calm/Chaos · Energy 3 + Power 1 · Might 3
Printings: RAD-150/167

> [Equip] — :rb_rune_rainbow: or exhaust a friendly unit. (Pay the cost: Attach this to a unit
> you control.)

Effect (given to the unit it is attached to):

> [Ganking] (I can move from battlefield to battlefield.)
-/
def RAD_150.meta : CardDef :=
  { id := ⟨"RAD-150"⟩,
    name := "Blade of the Exile",
    types := [.gear],
    tags := [⟨"Equipment"⟩, ⟨"Riven"⟩],
    domains := [.calm, .chaos],
    cost := some ⟨3, [.any]⟩,
    might := some 3,
    mightBonus := some 3,
    keywords := [{ keyword := .equip }],
    sets := [⟨"RAD"⟩] }  -- Power domains unknown; keyword cost unread
-- END GENERATED

/-- Blade of the Exile: the effect is not written yet. -/
def RAD_150 : CardDef := RAD_150.meta

-- BEGIN GENERATED RAD-151
/--
**Starry-Eyed Songstress** — Legend · Mind/Order
Printings: RAD-151/167, RAD-174/167

> As an additional cost to play a spell, you may exhaust me and three friendly units to reduce
> the cost of that spell by :rb_energy_2:.
-/
def RAD_151.meta : CardDef :=
  { id := ⟨"RAD-151"⟩,
    name := "Starry-Eyed Songstress",
    types := [.legend],
    tags := [⟨"Seraphine"⟩],
    domains := [.mind, .order],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Starry-Eyed Songstress: the effect is not written yet. -/
def RAD_151 : CardDef := RAD_151.meta

-- BEGIN GENERATED RAD-152
/--
**Encore** — Spell · Mind/Order · Energy 3 + Power 1
Printings: RAD-152/167

> Choose two —Deal 2 to a unit.Play two 1 :rb_might: Recruit unit tokens.Give up to two units
> each +1 :rb_might: this turn.Look at the top 2 cards of your Main Deck, draw 1 and recycle the
> other.
-/
def RAD_152.meta : CardDef :=
  { id := ⟨"RAD-152"⟩,
    name := "Encore",
    types := [.spell],
    tags := [⟨"Seraphine"⟩],
    domains := [.mind, .order],
    cost := some ⟨3, [.any]⟩,
    sets := [⟨"RAD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Encore: the effect is not written yet. -/
def RAD_152 : CardDef := RAD_152.meta

-- BEGIN GENERATED RAD-153
/--
**Agony's Embrace** — Legend · Body/Chaos
Printings: RAD-153/167, RAD-175/167

> Once each turn, when you play a card from face down, draw 1. Then, if it's not your turn,
> discard 1.
-/
def RAD_153.meta : CardDef :=
  { id := ⟨"RAD-153"⟩,
    name := "Agony's Embrace",
    types := [.legend],
    tags := [⟨"Evelynn"⟩],
    domains := [.body, .chaos],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Agony's Embrace draws once per turn when playing from Hidden and discards on another turn. -/
def RAD_153 : CardDef :=
  { RAD_153.meta with
    abilities := [.triggered (.onSelf .playHidden)
      (.of [] (.seqOf [.prim (.draw .you (.const 1)),
        .ifThen .yourTurn .nop (.prim (.discard .you (.const 1)))])) (.perTurn 1)],
    status := .full }

-- BEGIN GENERATED RAD-154
/--
**Last Caress** — Spell · Body/Chaos · Energy 2
Printings: RAD-154/167

> [Reaction] (Play any time, even before spells and abilities resolve.)
> The next unit you play this turn, even from face down, can be played to any battlefield. When
> you play it, [Buff] it. (Give it a +1 :rb_might: buff if it doesn't have one.)
-/
def RAD_154.meta : CardDef :=
  { id := ⟨"RAD-154"⟩,
    name := "Last Caress",
    types := [.spell],
    tags := [⟨"Evelynn"⟩],
    domains := [.body, .chaos],
    cost := some ⟨2, []⟩,
    keywords := [{ keyword := .reaction }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Last Caress: the effect is not written yet. -/
def RAD_154 : CardDef := RAD_154.meta

-- BEGIN GENERATED RAD-155
/--
**Exemplar of Demacia** — Legend · Body/Order
Printings: RAD-155/167, RAD-176/167

> When you play a gear with [Deploy], you may exhaust me and pay :rb_rune_rainbow: to move a
> friendly unit to that battlefield.
-/
def RAD_155.meta : CardDef :=
  { id := ⟨"RAD-155"⟩,
    name := "Exemplar of Demacia",
    types := [.legend],
    tags := [⟨"Jarvan IV"⟩],
    domains := [.body, .order],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Exemplar pays and exhausts to move a friendly Unit to the Deploy Gear's place of play. -/
def RAD_155 : CardDef :=
  { RAD_155.meta with
    abilities := [.triggered
      { event := .play
        subject := .all .friendly .anywhere [.ofType .gear, .hasKeyword .deploy, .onBattlefield]
        optional := true
        cost := .pay ⟨0, [.any]⟩ true }
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit]]
        (.prim (.move (.slot 0) (.at_
          (.all .any .atBattlefield [.ofType .battlefield, .atEventBattlefield none]))))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-156
/--
**Demacian Standard** — Gear · Body/Order · Energy 2 + Power 1
Printings: RAD-156/167

> [Deploy] (Play this only to a battlefield. When an opponent holds here, kill this.)
> When one or more friendly units attack here, give one of them +2 :rb_might: this turn.
> When you hold here, you may return this to its owner's hand.
-/
def RAD_156.meta : CardDef :=
  { id := ⟨"RAD-156"⟩,
    name := "Demacian Standard",
    types := [.gear],
    supertypes := [.signature],
    tags := [⟨"Jarvan IV"⟩],
    domains := [.body, .order],
    cost := some ⟨2, [.own]⟩,
    keywords := [{ keyword := .deploy }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Demacian Standard. -/
def RAD_156 : CardDef :=
  { RAD_156.meta with
    abilities := [.triggered (.onSelf .friendlyAttackGroupHere)
      (.of [.targetOf .one .friendly .anywhere [.ofType .unit, .inTriggerGroup []]]
        (.grant (.slot 0) (.mightPlus .it (.const 2)) .thisTurn)) .unlimited,
      .triggered { event := .hold, optional := true }
        (.of [] (.prim (.returnToHand .self))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-157
/--
**Bandle Scouts' Academy** — Battlefield · Colorless
Printings: RAD-157/167

> When you hide a card here, play a Gold gear token exhausted. (It has "[Reaction][>] Kill this,
> :rb_exhaust:: [Add] :rb_rune_rainbow:.")
-/
def RAD_157.meta : CardDef :=
  { id := ⟨"RAD-157"⟩,
    name := "Bandle Scouts' Academy",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Bandle Scouts' Academy rewards the player who hides at this Battlefield with exhausted Gold. -/
def RAD_157 : CardDef :=
  { RAD_157.meta with
    abilities := [.triggered (.onSelf .hide)
      (.of [] (.prim (.create "Gold" (.const 1) .atBase false))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-158
/--
**Black Market** — Battlefield · Colorless
Printings: RAD-158/167

> :rb_rune_rainbow::rb_rune_rainbow:: Draw 1. Each player may use this ability once on their
> turn (even if they don't control this battlefield).
-/
def RAD_158.meta : CardDef :=
  { id := ⟨"RAD-158"⟩,
    name := "Black Market",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Black Market. -/
def RAD_158 : CardDef :=
  { RAD_158.meta with
    abilities := [.passive .always [.sharedBattlefieldActivation],
      .activated [.pay ⟨0, [.any, .any]⟩] .normal
        (.of [] (.prim (.draw .you (.const 1)))) (.perTurn 1)],
    status := .full }

-- BEGIN GENERATED RAD-159
/--
**Black Rose Sanctum** — Battlefield · Colorless
Printings: RAD-159/167

> For each player, the first time each turn a non-token unit they control dies here, they play a
> 1 :rb_might: Recruit unit token to their base.
-/
def RAD_159.meta : CardDef :=
  { id := ⟨"RAD-159"⟩,
    name := "Black Rose Sanctum",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Black Rose Sanctum gives each player a Recruit after their first non-token Unit death here. -/
def RAD_159 : CardDef :=
  { RAD_159.meta with
    abilities := [.triggered
      { event := .firstUnitDeathHere
        subject := .all .any .anywhere [.ofType .unit, .at_ .self] }
      (.of [] (.prim (.create "Recruit" (.const 1) .atBase false))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-160
/--
**Cosmic Vista** — Battlefield · Colorless
Printings: RAD-160/167

> When you hold here, if your Rune Deck is empty, you score 1 point.
-/
def RAD_160.meta : CardDef :=
  { id := ⟨"RAD-160"⟩,
    name := "Cosmic Vista",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Cosmic Vista awards an extra point for holding while the Rune Deck is empty. -/
def RAD_160 : CardDef :=
  { RAD_160.meta with
    abilities := [.triggered {
        event := .youHold
        condition := .cmp .eq (.count (.all .friendly .inRuneDeck [])) (.const 0) }
        (.of [] (.prim (.score .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-161
/--
**Durand Memorial** — Battlefield · Colorless
Printings: RAD-161/167

> When you defend here, choose a unit you control here. Give it [Tank] this combat. (It must be
> assigned combat damage first.)
-/
def RAD_161.meta : CardDef :=
  { id := ⟨"RAD-161"⟩,
    name := "Durand Memorial",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Durand Memorial grants Tank to a defending player's chosen Unit at this Battlefield. -/
def RAD_161 : CardDef :=
  { RAD_161.meta with
    abilities := [.triggered (.onSelf .defend)
      (.of [.targetOf .one .friendly .here [.ofType .unit]]
        (.grant (.slot 0) (.keyword .it ⟨.tank, .none⟩) .thisCombat)) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-162
/--
**Firelights' Hideout** — Battlefield · Colorless
Printings: RAD-162/167

> When you conquer here, the next unit you play this turn has [Accelerate]. (You may pay
> :rb_energy_1: and a Power of its Domain as an additional cost to have it enter ready.)
-/
def RAD_162.meta : CardDef :=
  { id := ⟨"RAD-162"⟩,
    name := "Firelights' Hideout",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Firelights' Hideout: the effect is not written yet. -/
def RAD_162 : CardDef := RAD_162.meta

-- BEGIN GENERATED RAD-163
/--
**Hunters' Circle** — Battlefield · Colorless
Printings: RAD-163/167

> For each player, the first unit or gear they play here on their turn costs :rb_energy_1: less.
-/
def RAD_163.meta : CardDef :=
  { id := ⟨"RAD-163"⟩,
    name := "Hunters' Circle",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Each active player discounts their first Unit or Gear played to Hunters' Circle. -/
def RAD_163 : CardDef :=
  { RAD_163.meta with
    abilities := [.passive .always [.firstPermanentHereLess 1]],
    status := .full }

-- BEGIN GENERATED RAD-164
/--
**Packed Amphitheater** — Battlefield · Colorless
Printings: RAD-164/167, RAD-184/167

> Champion units here have +1 :rb_might:.
-/
def RAD_164.meta : CardDef :=
  { id := ⟨"RAD-164"⟩,
    name := "Packed Amphitheater",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Packed Amphitheater boosts every champion Unit at the Battlefield. -/
def RAD_164 : CardDef :=
  { RAD_164.meta with
    abilities := [.passive .always
      [.mightPlus (.all .any .here [.ofType .unit, .ofSupertype .champion]) (.const 1)]],
    status := .full }

-- BEGIN GENERATED RAD-165
/--
**Rakelstake** — Battlefield · Colorless
Printings: RAD-165/167

> For each player, the first time they play a unit or gear here each turn, they [Predict]. (They
> look at the top card of their Main Deck. They may recycle it.)
-/
def RAD_165.meta : CardDef :=
  { id := ⟨"RAD-165"⟩,
    name := "Rakelstake",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Rakelstake lets each player Predict on their first Unit or Gear play there each turn. -/
def RAD_165 : CardDef :=
  { RAD_165.meta with
    abilities := [.triggered (.onSelf .firstPermanentHere)
      (.of [] (.prim (.predict (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-166
/--
**Ruined Monastery** — Battlefield · Colorless
Printings: RAD-166/167

> When you conquer here, you may discard 1 and channel 1 rune exhausted.
-/
def RAD_166.meta : CardDef :=
  { id := ⟨"RAD-166"⟩,
    name := "Ruined Monastery",
    types := [.battlefield],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Ruined Monastery can discard one card and channel one exhausted Rune on conquer. -/
def RAD_166 : CardDef :=
  { RAD_166.meta with
    abilities := [.triggered { event := .youConquer, optional := true }
      (.of [] (.seqOf [.prim (.discard .you (.const 1)),
        .prim (.channel .you (.const 0) (.const 1))])) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-167
/--
**Neeko, Blending In** — Unit · Colorless · Energy 6 + Power 1 · Might 4
Printings: RAD-167/167

> (Neutral cards can go in decks of any Domain.)
> If Neeko is in your deck, choose up to 3 different legends in addition to your starting
> legend. (Different means none match names.)
> When you play me, choose one of those Legends and add it to your Legend Zone while I'm on the
> board.
-/
def RAD_167.meta : CardDef :=
  { id := ⟨"RAD-167"⟩,
    name := "Neeko",
    subtitle := some "Blending In",
    types := [.unit],
    tags := [⟨"Ixtal"⟩, ⟨"Neeko"⟩],
    cost := some ⟨6, [.any]⟩,
    might := some 4,
    sets := [⟨"RAD"⟩] }  -- Power domains unknown
-- END GENERATED

/-- Neeko, Blending In: the effect is not written yet. -/
def RAD_167 : CardDef := RAD_167.meta

-- BEGIN GENERATED RAD-SP1
/--
**Ahri, Confident** — Unit · Calm · Energy 4 + Power 1 · Might 4
Printings: RAD-SP1/005, RAD-038/167

> [Disarm]
> When you reduce the Might of an enemy unit here by 1 or more, give me +1 :rb_might: this turn.
-/
def RAD_SP1.meta : CardDef :=
  { id := ⟨"RAD-SP1"⟩,
    name := "Ahri",
    subtitle := some "Confident",
    types := [.unit],
    tags := [⟨"Ahri"⟩, ⟨"Ionia"⟩],
    domains := [.calm],
    cost := some ⟨4, [.domain .calm]⟩,
    might := some 4,
    keywords := [{ keyword := .disarm, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Ahri, Confident: the effect is not written yet. -/
def RAD_SP1 : CardDef := RAD_SP1.meta

-- BEGIN GENERATED RAD-SP2
/--
**Akali, Brash** — Unit · Fury · Energy 5 + Power 1 · Might 5
Printings: RAD-SP2/005, RAD-015/167

> The first time I move each turn, [Add] :rb_energy_1::rb_rune_rainbow:.
> The second time I move each turn, banish the top card of your Main Deck. Until your next
> Ending Phase, you may play that card.
-/
def RAD_SP2.meta : CardDef :=
  { id := ⟨"RAD-SP2"⟩,
    name := "Akali",
    subtitle := some "Brash",
    types := [.unit],
    tags := [⟨"Ionia"⟩, ⟨"Akali"⟩],
    domains := [.fury],
    cost := some ⟨5, [.domain .fury]⟩,
    might := some 5,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Akali, Brash: the effect is not written yet. -/
def RAD_SP2 : CardDef := RAD_SP2.meta

-- BEGIN GENERATED RAD-SP3
/--
**Evelynn, In Control** — Unit · Chaos · Energy 4 + Power 1 · Might 4
Printings: RAD-SP3/005, RAD-109/167, RAD-109a/167

> [Disarm]
> When I hold, if you control a facedown card here, score 1 point.
-/
def RAD_SP3.meta : CardDef :=
  { id := ⟨"RAD-SP3"⟩,
    name := "Evelynn",
    subtitle := some "In Control",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Evelynn"⟩, ⟨"Demon"⟩],
    domains := [.chaos],
    cost := some ⟨4, [.domain .chaos]⟩,
    might := some 4,
    keywords := [{ keyword := .disarm, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Evelynn, In Control scores an extra point when she holds where the player hid a card. -/
def RAD_SP3 : CardDef :=
  { RAD_SP3.meta with
    abilities := [.triggered { event := .hold, condition := .hasHiddenHere }
      (.of [] (.prim (.score .you (.const 1)))) .unlimited],
    status := .full }

-- BEGIN GENERATED RAD-SP4
/--
**Kai'Sa, Rebel** — Unit · Mind · Energy 5 + Power 1 · Might 5
Printings: RAD-SP4/005, RAD-063/167

> [Disarm]
> While I'm in a showdown, your spells have [Reaction].
-/
def RAD_SP4.meta : CardDef :=
  { id := ⟨"RAD-SP4"⟩,
    name := "Kai'Sa",
    subtitle := some "Rebel",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Kai'Sa"⟩, ⟨"The Void"⟩],
    domains := [.mind],
    cost := some ⟨5, [.domain .mind]⟩,
    might := some 5,
    keywords := [{ keyword := .disarm, arg := .amount 1 }],
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Kai'Sa gives the Spells of her controller Reaction while she is in a Showdown. -/
def RAD_SP4 : CardDef :=
  { RAD_SP4.meta with
    abilities := [.passive .inShowdown [.spellsHaveReaction]],
    status := .full }

-- BEGIN GENERATED RAD-SP5
/--
**Seraphine, Not Alone** — Unit · Order · Energy 5 + Power 1 · Might 1
Printings: RAD-SP5/005, RAD-138/167, RAD-138a/167

> When you play me or when I become exhausted, play a 1 :rb_might: Recruit unit token to your
> base.
> I have +1 :rb_might: for each other exhausted unit you control.
-/
def RAD_SP5.meta : CardDef :=
  { id := ⟨"RAD-SP5"⟩,
    name := "Seraphine",
    subtitle := some "Not Alone",
    types := [.unit],
    supertypes := [.champion],
    tags := [⟨"Seraphine"⟩, ⟨"Piltover"⟩],
    domains := [.order],
    cost := some ⟨5, [.domain .order]⟩,
    might := some 1,
    sets := [⟨"RAD"⟩] }
-- END GENERATED

/-- Seraphine, Not Alone recruits on play and exhaustion and counts other exhausted allies. -/
def RAD_SP5 : CardDef :=
  let recruit := EffectDef.of [] (.prim (.create "Recruit" (.const 1) .atBase false))
  { RAD_SP5.meta with
    abilities := [.triggered (.onSelf .play) recruit .unlimited,
      .triggered (.onSelf .exhaust) recruit .unlimited,
      .passive .always [.mightPlus .self (.count (.all .friendly .anywhere [.ofType .unit, .notSelf, .exhausted]))]],
    status := .full }

-- BEGIN GENERATED LIST
/-- The cards first printed in Radiance. -/
def cards : List CardDef :=
  [RAD_001,
    RAD_002,
    RAD_003,
    RAD_004,
    RAD_005,
    RAD_006,
    RAD_007,
    RAD_008,
    RAD_009,
    RAD_010,
    RAD_011,
    RAD_012,
    RAD_013,
    RAD_014,
    RAD_016,
    RAD_017,
    RAD_018,
    RAD_019,
    RAD_020,
    RAD_021,
    RAD_022,
    RAD_023,
    RAD_024,
    RAD_025,
    RAD_026,
    RAD_027,
    RAD_028,
    RAD_029,
    RAD_030,
    RAD_031,
    RAD_032,
    RAD_033,
    RAD_034,
    RAD_035,
    RAD_036,
    RAD_037,
    RAD_039,
    RAD_040,
    RAD_041,
    RAD_042,
    RAD_043,
    RAD_044,
    RAD_045,
    RAD_046,
    RAD_047,
    RAD_048,
    RAD_049,
    RAD_050,
    RAD_051,
    RAD_052,
    RAD_053,
    RAD_054,
    RAD_055,
    RAD_056,
    RAD_057,
    RAD_058,
    RAD_059,
    RAD_060,
    RAD_061,
    RAD_062,
    RAD_064,
    RAD_065,
    RAD_066,
    RAD_067,
    RAD_068,
    RAD_069,
    RAD_070,
    RAD_071,
    RAD_072,
    RAD_073,
    RAD_074,
    RAD_075,
    RAD_076,
    RAD_077,
    RAD_078,
    RAD_079,
    RAD_080,
    RAD_081,
    RAD_082,
    RAD_083,
    RAD_084,
    RAD_085,
    RAD_086,
    RAD_087,
    RAD_088,
    RAD_089,
    RAD_090,
    RAD_091,
    RAD_092,
    RAD_093,
    RAD_094,
    RAD_095,
    RAD_096,
    RAD_097,
    RAD_098,
    RAD_099,
    RAD_100,
    RAD_101,
    RAD_102,
    RAD_103,
    RAD_104,
    RAD_105,
    RAD_106,
    RAD_107,
    RAD_108,
    RAD_110,
    RAD_111,
    RAD_112,
    RAD_113,
    RAD_114,
    RAD_115,
    RAD_116,
    RAD_117,
    RAD_118,
    RAD_119,
    RAD_120,
    RAD_121,
    RAD_122,
    RAD_123,
    RAD_124,
    RAD_125,
    RAD_126,
    RAD_127,
    RAD_128,
    RAD_129,
    RAD_130,
    RAD_131,
    RAD_132,
    RAD_133,
    RAD_134,
    RAD_135,
    RAD_136,
    RAD_137,
    RAD_139,
    RAD_140,
    RAD_141,
    RAD_142,
    RAD_143,
    RAD_144,
    RAD_145,
    RAD_146,
    RAD_147,
    RAD_148,
    RAD_149,
    RAD_150,
    RAD_151,
    RAD_152,
    RAD_153,
    RAD_154,
    RAD_155,
    RAD_156,
    RAD_157,
    RAD_158,
    RAD_159,
    RAD_160,
    RAD_161,
    RAD_162,
    RAD_163,
    RAD_164,
    RAD_165,
    RAD_166,
    RAD_167,
    RAD_SP1,
    RAD_SP2,
    RAD_SP3,
    RAD_SP4,
    RAD_SP5]
-- END GENERATED LIST

end RiftboundCards.Radiance

end
