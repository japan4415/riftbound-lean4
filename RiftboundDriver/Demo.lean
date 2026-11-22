module

public import Riftbound

/-!
# Driver: a demo game

A small card database and a deck for showing a game: the same shape as the fixtures of the tests
(a legal Duel deck of 40 Main Deck cards, 12 Runes, 3 Battlefields), made of values that can be
run. The tests keep their own copies, which are only evaluated at compile time.
-/

@[expose] public section

namespace RiftboundDriver

open Riftbound

/-- The cards of the demo database. -/
def demoCards : List CardDef :=
  [ { id := ⟨"L1"⟩, name := "Demo Legend", types := [.legend], tags := [⟨"Hero"⟩],
      domains := [.fury, .calm] },
    { id := ⟨"C1"⟩, name := "Hero", subtitle := some "Champion", types := [.unit],
      supertypes := [.champion], tags := [⟨"Hero"⟩], domains := [.fury],
      cost := some ⟨3, [.domain .fury]⟩, might := some 4 },
    { id := ⟨"R1"⟩, name := "Fury Rune", types := [.rune], domains := [.fury] },
    { id := ⟨"S0"⟩, name := "Quick Study", types := [.spell], domains := [.fury],
      cost := some ⟨1, []⟩,
      spellEffect := some (EffectDef.of [] (.prim (.draw .you (.const 1)))) },
    { id := ⟨"S1"⟩, name := "Spark", types := [.spell], domains := [.fury],
      cost := some ⟨1, []⟩, keywords := [{ keyword := .repeat_, arg := .cost ⟨1, []⟩ }],
      spellEffect := some (EffectDef.of
        [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 2)))) },
    { id := ⟨"S2"⟩, name := "Sweep", types := [.spell], domains := [.fury],
      cost := some ⟨1, []⟩,
      spellEffect := some (EffectDef.of []
        (.ifThen (.exists (Selector.all .enemy .atBase [.ofType .unit]))
          (.forEach (Selector.all .enemy .atBase [.ofType .unit])
            (.prim (.deal .it (.const 1))))
          .nop)) },
    { id := ⟨"P0"⟩, name := "Pinger", types := [.unit], domains := [.fury],
      cost := some ⟨2, []⟩, might := some 2, keywords := [{ keyword := .accelerate }],
      abilities := [.activated [.exhaustSelf] .normal
        (EffectDef.of [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
          (.prim (.deal (.slot 0) (.const 1)))) .unlimited] },
    { id := ⟨"H0"⟩, name := "Herald", types := [.unit], domains := [.fury],
      cost := some ⟨2, []⟩, might := some 2,
      abilities := [.triggered (Trigger.onSelf .play)
        (EffectDef.of [] (.prim (.draw .you (.const 1)))) .unlimited] },
    { id := ⟨"A0"⟩, name := "Archer", types := [.unit], domains := [.fury],
      cost := some ⟨2, []⟩, might := some 2,
      abilities := [.triggered (Trigger.onSelf .play)
        (EffectDef.of [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
          (.prim (.deal (.slot 0) (.const 1)))) .unlimited] },
    { id := ⟨"M0"⟩, name := "Martyr", types := [.unit], domains := [.fury],
      cost := some ⟨1, []⟩, might := some 1,
      abilities := [.triggered (Trigger.onSelf .die)
        (EffectDef.of [] (.prim (.draw .you (.const 1)))) .unlimited] },
    { id := ⟨"TKN-Sprite"⟩, name := "Sprite", types := [.unit], might := some 3,
      keywords := [{ keyword := .temporary }] },
    { id := ⟨"G0"⟩, name := "Training Sword", types := [.gear], domains := [.fury],
      cost := some ⟨1, []⟩, keywords := [{ keyword := .equip, arg := .cost ⟨1, []⟩ }],
      mightBonus := some 2, grants := [.passive .always [.keyword .self { keyword := .tank }]] },
    { id := ⟨"T0"⟩, name := "Summoner", types := [.unit], domains := [.fury],
      cost := some ⟨2, []⟩, might := some 1,
      abilities := [.triggered (Trigger.onSelf .play)
        (EffectDef.of [] (.prim (.create "Sprite" (.const 1) .atBase true))) .unlimited] },
    { id := ⟨"SFD-T03"⟩, name := "Gold", types := [.gear],
      abilities := [.activated [.killSelf, .exhaustSelf] .reaction
        (EffectDef.of [] (.prim (.addPower .you (.const 1) none none))) .unlimited] },
    { id := ⟨"D0"⟩, name := "Guardian", types := [.unit], domains := [.fury],
      cost := some ⟨2, []⟩, might := some 3,
      keywords := [{ keyword := .deflect, arg := .amount 1 }] },
    { id := ⟨"N2"⟩, name := "Looter", types := [.unit], domains := [.fury],
      cost := some ⟨1, []⟩, might := some 2,
      abilities := [.triggered (Trigger.onSelf .play)
        (EffectDef.of [] (.seqOf [.prim (.discard .you (.const 1)),
          .prim (.draw .you (.const 1))])) .unlimited] },
    { id := ⟨"N1"⟩, name := "Prospector", types := [.unit], domains := [.fury],
      cost := some ⟨2, []⟩, might := some 2,
      abilities := [.triggered (Trigger.onSelf .play)
        (EffectDef.of [] (.prim (.create "Gold" (.const 1) .atBase false))) .unlimited] },
    { id := ⟨"N0"⟩, name := "Banner", types := [.unit], domains := [.fury],
      cost := some ⟨2, []⟩, might := some 1,
      abilities := [.passive .always
        [.mightPlus (Selector.all .friendly .anywhere [.ofType .unit, .notSelf]) (.const 1)]] },
    { id := ⟨"E0"⟩, name := "Scout", types := [.unit], domains := [.fury],
      cost := some ⟨1, []⟩, might := some 1,
      abilities := [.passive .always [.entersReady .self]] },
    { id := ⟨"G1"⟩, name := "Battery", types := [.gear], domains := [.fury],
      cost := some ⟨1, []⟩,
      abilities := [.activated [.exhaustSelf] .reaction
        (EffectDef.of [] (.prim (.addEnergy .you (.const 1) none))) .unlimited] },
    { id := ⟨"S5"⟩, name := "Chill", types := [.spell], domains := [.fury],
      cost := some ⟨1, []⟩,
      spellEffect := some (EffectDef.of
        [Choice.targetOf .one .enemy .atBase [.ofType .unit]] (.prim (.stun (.slot 0)))) },
    { id := ⟨"U0"⟩, name := "Trainer", types := [.unit], domains := [.fury],
      cost := some ⟨2, []⟩, might := some 1,
      abilities := [.triggered (Trigger.onSelf .play)
        (EffectDef.of [] (.prim (.buff .self))) .unlimited] },
    { id := ⟨"S4"⟩, name := "Surge", types := [.spell], domains := [.fury],
      cost := some ⟨1, []⟩,
      spellEffect := some (EffectDef.of
        [Choice.targetOf .one .friendly .atBase [.ofType .unit]]
        (.grant (.slot 0) (.mightPlus .it (.const 3)) .thisTurn)) },
    { id := ⟨"S3"⟩, name := "Counterstrike", types := [.spell], domains := [.fury],
      cost := some ⟨1, []⟩, keywords := [{ keyword := .reaction }],
      spellEffect := some (EffectDef.of
        [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
        (.prim (.deal (.slot 0) (.const 2)))) } ] ++
  (List.range 13).map (fun n =>
    { id := ⟨s!"V{n}"⟩, name := s!"Vanilla {n}", types := [.unit], domains := [.fury],
      cost := some ⟨1, []⟩, might := some 2 : CardDef }) ++
  (List.range 3).map (fun n =>
    { id := ⟨s!"B{n}"⟩, name := s!"Battlefield {n}", types := [.battlefield] : CardDef })

/-- The demo database. -/
def demoDB : CardDB := { cards := demoCards }

/-- The demo deck: the champion, and three copies each of: an Equipment (+2 Might and Tank); Units
that play a Sprite token (Temporary), play a Gold token (a Gear that adds Power once), discard a
card and draw one, deal 1 damage to an enemy Unit, and ping with an activated ability (with
Accelerate); a Gear that adds 1 Energy (Add); a Unit with Deflect 1; Spells that stun an enemy Unit,
give a friendly Unit +3 Might this turn, deal 2 damage to an enemy Unit (with Repeat 1 Energy), and
deal 1 damage to each enemy Unit; and a Reaction that deals 2 damage to an enemy Unit. Then 12 Runes
and 3 Battlefields. -/
def demoDeck : Deck :=
  { legend := ⟨"L1"⟩, chosenChampion := ⟨"C1"⟩,
    main := ⟨"C1"⟩ :: List.replicate 3 ⟨"G0"⟩ ++ List.replicate 3 ⟨"T0"⟩ ++
      List.replicate 3 ⟨"N1"⟩ ++ List.replicate 3 ⟨"S5"⟩ ++ List.replicate 3 ⟨"S4"⟩ ++
      List.replicate 3 ⟨"A0"⟩ ++ List.replicate 3 ⟨"N2"⟩ ++ List.replicate 3 ⟨"G1"⟩ ++
      List.replicate 3 ⟨"P0"⟩ ++
      List.replicate 3 ⟨"D0"⟩ ++ List.replicate 3 ⟨"S1"⟩ ++ List.replicate 3 ⟨"S2"⟩ ++
      List.replicate 3 ⟨"S3"⟩,
    runes := List.replicate 12 ⟨"R1"⟩,
    battlefields := [⟨"B0"⟩, ⟨"B1"⟩, ⟨"B2"⟩] }

/-- The configuration of the demo: a Duel under the Core Rules. -/
def demoConfig : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

end RiftboundDriver

end
