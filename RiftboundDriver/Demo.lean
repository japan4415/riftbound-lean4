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
      cost := some ⟨1, []⟩,
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
      cost := some ⟨2, []⟩, might := some 2,
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

/-- The demo deck: the champion, three copies of each of 5 vanilla Units, three copies each of a
Unit that draws when it is played, a Unit that deals 1 damage to an enemy Unit when it is played,
a Unit that draws when it dies, a Unit that pings (an activated ability), a Spell that draws a
card, a Spell that deals 2 damage to
an enemy Unit, a Spell that deals 1 damage to each enemy Unit, and a Reaction that deals 2 damage
to an enemy Unit, 12 Runes and 3 Battlefields. -/
def demoDeck : Deck :=
  { legend := ⟨"L1"⟩, chosenChampion := ⟨"C1"⟩,
    main := ⟨"C1"⟩ :: (List.range 5).flatMap (fun n => List.replicate 3 ⟨s!"V{n}"⟩) ++
      List.replicate 3 ⟨"A0"⟩ ++ List.replicate 3 ⟨"H0"⟩ ++ List.replicate 3 ⟨"M0"⟩ ++
      List.replicate 3 ⟨"P0"⟩ ++
      List.replicate 3 ⟨"S0"⟩ ++ List.replicate 3 ⟨"S1"⟩ ++ List.replicate 3 ⟨"S2"⟩ ++
      List.replicate 3 ⟨"S3"⟩,
    runes := List.replicate 12 ⟨"R1"⟩,
    battlefields := [⟨"B0"⟩, ⟨"B1"⟩, ⟨"B2"⟩] }

/-- The configuration of the demo: a Duel under the Core Rules. -/
def demoConfig : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

end RiftboundDriver

end
