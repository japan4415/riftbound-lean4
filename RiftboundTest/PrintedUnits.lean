module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests for printed cards

Exercise the printed card IDs through ordinary play, combat, targeting, and movement.
-/

namespace RiftboundTest

open Riftbound

private meta def inLab (test : GameState → Option Bool) : Bool :=
  (lab.bind test).getD false

private meta def ordinaryUnit (code : String) (energy : Nat) (might : Int) : Bool :=
  inLab fun s => do
    let (withCard, card) ← put s s.me code .hand
    let stats ← withCard.cardDef? card
    let pay : RunePool.Payment := ⟨energy, []⟩
    let funded := withCard.fund s.me energy
    let played ← cast funded s.me card pay
    let unit ← played.firstOf s.me .base code
    return stats.hasType .unit && stats.keywords.isEmpty && stats.abilities.isEmpty &&
      played.mightNow unit == some might && played.tired unit == some true &&
      (played.poolOf s.me).energy == 0 &&
      (cast (withCard.fund s.me (energy - 1)) s.me card pay).isNone

-- Playful Phantom, Mega-Mech, Mountain Drake, Shipyard Skulker, Vanguard Sergeant
#guard ordinaryUnit "OGN-049" 5 5
#guard ordinaryUnit "OGN-088" 7 8
#guard ordinaryUnit "OGN-142" 9 10
#guard ordinaryUnit "OGN-175" 3 3
#guard ordinaryUnit "OGN-219" 4 4

private meta def combatKeywords (code : String) (base assault shield : Nat)
    (tank : Bool := false) : Bool :=
  inLab fun s => do
    let bf := s.bf0
    let (withUnit, unit) ← putAt s s.me code bf
    let (withAlly, ally) ← putAt withUnit s.me "OGN-049" bf
    let (board, _) ← putAt withAlly s.you "OGN-088" bf
    let fight (attacker : PlayerId) :=
      let staged := board.modObj bf (fun o => { o with contested := some attacker })
      { staged with combat := (staged.observeCombat [.showdown bf attacker 0]).1 }
    let attack := fight s.me
    let defend := fight s.you
    let picks := (legalAssigns defend bf s.you []).filterMap (fun action =>
      match action.kind with | .assignPick u => some u | _ => none)
    return board.mightNow unit == some (Int.ofNat base) &&
      attack.mightNow unit == some (Int.ofNat (base + assault)) &&
      defend.mightNow unit == some (Int.ofNat (base + shield)) &&
      attack.combatTotal bf s.me s.me == base + assault + 5 &&
      defend.combatTotal bf s.you s.me == base + shield + 5 &&
      defend.need unit == base + shield &&
      (if tank then picks == [unit] else picks.length == 2 && picks.contains unit && picks.contains ally)

-- Assault and Shield affect both combat damage and the Might needed to kill the Unit.
-- The Tank is the only legal first target for the enemy's combat damage.
#guard combatKeywords "OGN-052" 2 0 1
#guard combatKeywords "OGN-054" 3 0 1 true
#guard combatKeywords "OGN-210" 2 1 0
#guard combatKeywords "OGN-215" 5 1 0
#guard combatKeywords "OGS-005" 6 0 1
#guard combatKeywords "OGS-007" 5 2 2
#guard combatKeywords "OGN-086" 5 0 1
#guard combatKeywords "SFD-156" 3 2 0
#guard combatKeywords "UNL-002" 1 2 0
#guard combatKeywords "UNL-006" 1 4 0
#guard combatKeywords "UNL-036" 1 0 2 true
#guard combatKeywords "UNL-099" 3 0 2 true

private meta def accelerates (code : String) (energy : Nat) : Bool :=
  inLab fun s => do
    let (board, card) ← put s s.me code .hand
    let funded := board.fund s.me (energy + 1) 1 1
    let ordinary ← cast funded s.me card ⟨energy, []⟩
    let ready ← cast funded s.me card ⟨energy + 1, [.fury]⟩
    let ordinaryUnit ← ordinary.firstOf s.me .base code
    let readyUnit ← ready.firstOf s.me .base code
    return ordinary.tired ordinaryUnit == some true && ready.tired readyUnit == some false &&
      (ordinary.poolOf s.me).fury == 1 && (ready.poolOf s.me).fury == 0 &&
      (ready.poolOf s.me).energy == 0 &&
      (cast funded s.me card ⟨energy + 1, [.calm]⟩).isNone

-- Blazing Scorcher, Legion Rearguard, Sharkling
#guard accelerates "OGN-001" 5
#guard accelerates "OGN-010" 2
#guard accelerates "UNL-006" 3

private meta def deflects (code : String) (might : Int) : Bool :=
  inLab fun s => do
    let (withFoe, foe) ← put s s.you code .base
    let (withFriend, friend) ← put withFoe s.me code .base
    let (board, spell) ← put withFriend s.me "OGN-095" .hand
    let pay : RunePool.Payment := ⟨1, []⟩
    let noPower := board.fund s.me 1
    let withPower := board.fund s.me 1 1
    let friendly ← cast noPower s.me spell pay [friend]
    let enemy ← cast withPower s.me spell pay [foe]
    return (cast noPower s.me spell pay [foe]).isNone &&
      friendly.mightNow friend == some (might - 1) && enemy.mightNow foe == some (might - 1) &&
      (enemy.poolOf s.me).totalPower == 0

-- Pouty Poro and Navori Scout both charge Deflect 1 to the opponent.
#guard deflects "OGN-013" 2
#guard deflects "SFD-037" 4

private meta def visionChoice (code : String) : Bool :=
  inLab fun s => do
    let p := s.me
    let ownDeck (t : GameState) := t.zone (.player p .mainDeck)
    let otherDeck (t : GameState) := t.zone (.player s.you .mainDeck)
    let (board, card) ← put s p code .hand
    let first ← (ownDeck board).head?
    let kept ← play board p card [] { yes := false }
    let recycled ← play board p card
    let empty ← play (board.setZone (.player p .mainDeck) []) p card
    return ownDeck kept == ownDeck board && ownDeck recycled == (ownDeck board).tail ++ [first] &&
      otherDeck kept == otherDeck board && otherDeck recycled == otherDeck board &&
      (ownDeck empty).isEmpty && kept.countIn p .base code == 1 && recycled.countIn p .base code == 1

-- Mystic Poro and Jeweled Colossus can each keep or recycle the inspected card.
#guard visionChoice "OGN-171"
#guard visionChoice "OGN-086"

private meta def printedRecruit (code : String) : Bool := inLab fun s => do
  let p := s.me
  let id : CardId := ⟨code⟩
  let token : ObjId := ⟨s.nextId⟩
  let entered := createOne id p none false s
  let d ← entered.cardDef? token
  let object ← entered.obj? token
  let (killed, events) := killOrSave entered token
  let (clean, _) ← (advance 100 { killed with pending := [.cleanup, .priority p] } []).toOption
  return d.id == id && d.isTokenCard && d.tags.contains ⟨"Recruit"⟩ &&
    object.kind == .token id && object.owner == p && object.controller == p &&
    entered.mightNow token == some (1 : Int) && entered.tired token == some true &&
    clean.countIn p .base code == 0 && clean.countIn p .trash code == 0 &&
    events.any (fun | .died _ owner => owner == p | _ => false) && clean.physIds == s.physIds

#guard printedRecruit "OGN-271"
#guard printedRecruit "OGN-272"
#guard printedRecruit "OGN-273"

-- No printed or model token can be registered or named as a Unit or Gear card (CR 185).
#guard inLab fun s => do
  let ids := [⟨"OGN-271"⟩, ⟨"OGN-272"⟩, ⟨"OGN-273"⟩, ⟨"OGN-274"⟩,
    ⟨"SFD-T03"⟩, ⟨"UNL-T02"⟩, ⟨"UNL-T06"⟩, ⟨"VEN-T04"⟩, tokenId "Sprite"]
  let invalid (id : CardId) := { goodDeck with main := goodDeck.main ++ [id] }
  let named := s.nameableCards .unit ++ s.nameableCards .gear
  return (GameState.initial s.cards s.config [goodDeck, goodDeck]).isSome &&
    named.contains ⟨"OGN-049"⟩ && ids.all (fun id =>
      (s.cards.find? id).any (·.isTokenCard) && !named.contains id &&
        (GameState.initial s.cards s.config [invalid id, goodDeck]).isNone)

-- Sprite Call creates a ready Sprite with the printed characteristics. Its controller's
-- Beginning Phase kills it (CR 315.2.a, 816).
#guard inLab fun s => do
  let p := s.me
  let (board, spell) ← put s p "OGN-094" .hand
  let played ← play board p spell
  let model ← played.tokenCard "Sprite"
  let printed ← played.cards.find? ⟨"OGN-274"⟩
  let token ← played.firstOf p .base model.id.code
  let beginning (who : PlayerId) :=
    (advance 100 { played with active := some who, pending := [.phase .beginning, .priority who] }
      []).toOption
  let (opponentTurn, _) ← beginning s.you
  let (waiting, _) ← beginning p
  let (response, _) ← (step 100 waiting ⟨.player p, .pass⟩).toOption
  let (ownTurn, events) ← (step 100 response ⟨.player s.you, .pass⟩).toOption
  return model.might == printed.might && model.keywords == printed.keywords &&
    played.mightNow token == some (3 : Int) && played.tired token == some false &&
    opponentTurn.countIn p .base model.id.code == 1 && waiting.inPlay.contains token &&
    ownTurn.countIn p .base model.id.code == 0 &&
    events.any (fun | .died _ owner => owner == p | _ => false)

-- Voracious Gromp earns XP when it helps score, once for either kind of scoring.
#guard inLab fun s => do
  let p := s.me
  let field := s.bf0
  let other ← s.battlefields.find? (· != field)
  let (s, gromp) ← putAt s p "UNL-100" field
  let (s, _) ← putAt s s.you "UNL-100" other
  let baseXP := s.xpOf p
  let rivalXP := s.xpOf s.you
  let (scored, _, conquerEvents) := scoreBf s p field true
  let conquered ← fire scored conquerEvents
  let (retry, _, replayedEvents) := scoreBf conquered p field true
  let duplicate ← fire retry replayedEvents
  let (heldField, holdEvents) := hold (s.modObj field (fun o => { o with control := some p })) p
  let held ← fire heldField holdEvents
  let (elsewhere, _, awayEvents) := scoreBf s p other true
  let away ← fire elsewhere awayEvents
  return s.mightNow gromp == some (5 : Int) && conquered.xpOf p == baseXP + 3 &&
    held.xpOf p == baseXP + 3 && duplicate.xpOf p == baseXP + 3 && away.xpOf p == baseXP &&
    conquered.xpOf s.you == rivalXP && held.xpOf s.you == rivalXP

-- Laurent Bladekeeper can standard-move directly between Battlefields with Ganking.
#guard inLab fun s => do
  let dest ← s.battlefields.find? (· != s.bf0)
  let (s1, bladekeeper) ← putAt s s.me "SFD-096" s.bf0
  let (board, ordinary) ← putAt s1 s.me "OGN-049" s.bf0
  let answer (unit : ObjId) : Action := ⟨.player s.me, .standardMove unit (.battlefield dest)⟩
  let (moved, events) ← (step 100 board (answer bladekeeper)).toOption
  return (step 100 board (answer ordinary)).toOption.isNone &&
    (moved.obj? bladekeeper).any (·.loc == some dest) &&
    moved.tired bladekeeper == some true &&
    events.contains (Event.standardMoved bladekeeper (some dest))

-- Master Yi counts controlled Runes on the Board, including exhausted Runes.
#guard inLab fun labState => do
  let s := GameState.empty { ruleSet := .coreOnly, mode := .teamDuel } labState.cards
  let p : PlayerId := ⟨0⟩
  let teammate : PlayerId := ⟨1⟩
  let (s, yi) ← put s p "OGS-004" .base
  let (s, _) ← put s teammate "OGN-042" .base
  let mut seven := s
  for _ in [:7] do
    let (next, rune) ← put seven p "OGN-042" .base
    seven := next.modObj rune (fun o => { o with exhausted := true })
  let (registered, candidate) ← put seven p "OGN-042" .runeDeck
  let (eight, channeled) ← moveObj registered candidate (.player p .base)
  let (recycled, _) ← moveObj eight channeled (.player p .runeDeck)
  return registered.mightNow yi == some 4 && eight.mightNow yi == some 8 &&
    recycled.mightNow yi == some 4

-- In team play, Annie gives Bonus Damage to her controller's spells and abilities.
#guard inLab fun labState => do
  let s := GameState.empty { ruleSet := .coreOnly, mode := .teamDuel } labState.cards
  let p : PlayerId := ⟨0⟩
  let (board, _) ← put s p "OGS-001" .base
  return board.passiveBonus p == 1 && board.passiveBonus ⟨1⟩ == 0 &&
    board.passiveBonus ⟨2⟩ == 0

-- Incinerate can damage either player's Unit at a Battlefield, and cannot choose one at a Base.
#guard inLab fun s => do
  let (s, spell) ← put s s.me "OGS-003" .hand
  let (s, friendly) ← putAt s s.me "OGN-142" s.bf0
  let (s, enemy) ← putAt s s.you "OGN-142" s.bf0
  let (s, atBase) ← put s s.you "OGN-142" .base
  let allyHit ← play s s.me spell [friendly]
  let enemyHit ← play s s.me spell [enemy]
  return (allyHit.obj? friendly).any (·.damage == 2) &&
    (enemyHit.obj? enemy).any (·.damage == 2) &&
    (play s s.me spell [atBase]).isNone

-- Final Spark can hit a Unit at a Base and leaves a larger Unit with eight damage.
#guard inLab fun s => do
  let (s, spell) ← put s s.me "OGS-022" .hand
  let (s, target) ← put s s.you "OGN-142" .base
  let (s, other) ← put s s.you "OGN-142" .base
  let after ← cast (s.fund s.me 8) s.me spell ⟨8, []⟩ [target]
  return (after.obj? target).any (·.damage == 8) && (after.obj? other).any (·.damage == 0) &&
    (after.poolOf s.me).energy == 0 && (cast (s.fund s.me 7) s.me spell ⟨8, []⟩ [target]).isNone

-- Flash moves the teammate's Unit back to the teammate's Base.
#guard inLab fun labState => do
  let p : PlayerId := ⟨0⟩
  let teammate : PlayerId := ⟨1⟩
  let enemy : PlayerId := ⟨2⟩
  let s := GameState.empty { ruleSet := .coreOnly, mode := .teamDuel } labState.cards
  let s := { s with
    phase := .main, turn := 1, active := some p, turnOrder := Mode.teamTurnOrder true,
    pending := [Frame.priority p] : GameState }
  let (s, ownField) ← putBf s p "B0"
  let (s, allyField) ← putBf s teammate "B1"
  let (s, own) ← putAt s p "OGN-142" ownField
  let (s, ally) ← putAt s teammate "OGN-142" allyField
  let (s, opponent) ← putAt s enemy "OGN-142" ownField
  let (s, spell) ← put s p "OGS-011" .hand
  let next ← play s p spell [own, ally]
  return (next.zone (.player p .base)).contains own &&
    (next.zone (.player teammate .base)).contains ally &&
    (next.obj? opponent).any (·.loc == some ownField) &&
    (play s p spell [opponent]).isNone

-- Blast of Power requires Order Power and can kill either side's Unit at a Battlefield.
#guard inLab fun s => do
  let p := s.me
  let (s, spell) ← put s p "OGS-012" .hand
  let (s, friendly) ← putAt s p "OGN-142" s.bf0
  let (s, enemy) ← putAt s s.you "OGN-142" s.bf0
  let (s, atBase) ← put s s.you "OGN-142" .base
  let killedEnemy ← play s p spell [enemy]
  let killedFriendly ← play s p spell [friendly]
  return (killedEnemy.obj? enemy).isNone && (killedEnemy.obj? friendly).isSome &&
    (killedEnemy.firstOf s.you .trash "OGN-142").isSome &&
    (killedFriendly.obj? friendly).isNone && (killedFriendly.obj? enemy).isSome &&
    (play s p spell [atBase]).isNone &&
    (cast (s.fund p 6) p spell ⟨6, [.order]⟩ [enemy]).isNone

-- Garen's aura excludes himself, opponents here, and friendly Units elsewhere.
#guard inLab fun s => do
  let other ← s.battlefields.find? (· != s.bf0)
  let (s, garen) ← putAt s s.me "OGS-013" s.bf0
  let (s, together) ← putAt s s.me "OGN-049" s.bf0
  let (s, away) ← putAt s s.me "OGN-049" other
  let (s, baseUnit) ← put s s.me "OGN-049" .base
  let (board, enemy) ← putAt s s.you "OGN-049" s.bf0
  let (atBase, _) ← applyMove board s.me garen .base
  return board.mightNow garen == some 5 && board.mightNow together == some 6 &&
    board.mightNow away == some 5 && board.mightNow enemy == some 5 &&
    board.mightNow baseUnit == some 5 && atBase.mightNow baseUnit == some 6 &&
    atBase.mightNow together == some 5

private meta def printedReadyEntry (code : String) (energy : Nat) (power : Domain)
    (might : Int) : Bool := inLab fun s => do
  let p := s.me
  let (board, card) ← put s p code .hand
  let funded := board.rich p
  let played ← cast funded p card ⟨energy, [power]⟩
  let unit ← played.firstOf p .base code
  return played.mightNow unit == some might && played.tired unit == some false &&
    (played.poolOf p).energy == (funded.poolOf p).energy - energy &&
    (played.poolOf p).totalPower + 1 == (funded.poolOf p).totalPower &&
    (cast funded p card ⟨energy, [.fury]⟩).isNone &&
    (cast funded p card ⟨energy - 1, [power]⟩).isNone

-- Master Yi, Honed and Vanguard Attendant both enter Ready.
#guard printedReadyEntry "OGS-009" 7 .body 6
#guard printedReadyEntry "OGS-016" 6 .order 5

-- Master Yi can move directly between Battlefields. Vanguard Attendant must return to Base first.
#guard inLab fun s => do
  let p := s.me
  let dest ← s.battlefields.find? (· != s.bf0)
  let (s, yi) ← putAt s p "OGS-009" s.bf0
  let (board, attendant) ← putAt s p "OGS-016" s.bf0
  let move (unit : ObjId) : Action := ⟨.player p, .standardMove unit (.battlefield dest)⟩
  let (moved, events) ← (step 100 board (move yi)).toOption
  return (step 100 board (move attendant)).toOption.isNone &&
    (moved.obj? yi).any (·.loc == some dest) && moved.tired yi == some true &&
    events.contains (Event.standardMoved yi (some dest))

-- Firestorm uses one Battlefield and deals damage only to enemy Units there.
#guard inLab fun s => do
  let p := s.me
  let field := s.bf0
  let other ← s.battlefields.find? (· != field)
  let (s, spell) ← put s p "OGS-002" .hand
  let (s, ally) ← putAt s p "OGN-142" field
  let (s, first) ← putAt s s.you "OGN-142" field
  let (s, second) ← putAt s s.you "OGN-142" field
  let (board, elsewhere) ← putAt s s.you "OGN-142" other
  let played ← play board p spell [field]
  let damage (id : ObjId) := (played.obj? id).map (·.damage)
  return damage first == some 3 && damage second == some 3 &&
    damage ally == some 0 && damage elsewhere == some 0 &&
    (play board p spell [first]).isNone

-- Annie returns one chosen Spell from her controller's Trash to their hand.
#guard inLab fun s => do
  let p := s.me
  let (s, annie) ← put s p "OGS-010" .hand
  let (s, first) ← put s p "OGN-094" .trash
  let (s, chosen) ← put s p "OGN-095" .trash
  let (s, unit) ← put s p "OGN-142" .trash
  let (board, rival) ← put s s.you "OGN-095" .trash
  let options ← castStop board p annie
  let returned ← play board p annie [] { pick := (· == [chosen]) }
  return options.trigPicks.contains chosen && !options.trigPicks.contains rival &&
    returned.countIn p .hand "OGN-095" == 1 &&
    (returned.zone (.player p .trash)).contains first &&
    (returned.zone (.player p .trash)).contains unit &&
    !(returned.zone (.player p .trash)).contains chosen &&
    (returned.zone (.player s.you .trash)).contains rival

-- In team play, Firestorm hits both opponents, Decisive Strike strengthens the teammate,
-- and Annie only returns from her controller's Trash.
#guard inLab fun labState => do
  let config : GameConfig := { ruleSet := .coreOnly, mode := .teamDuel }
  let initial ← GameState.initial labState.cards config (List.replicate 4 goodDeck)
  let s ← (RiftboundDriver.runUntilTurn 100 1 2000 (RiftboundDriver.Rng.ofSeed 1) initial).toOption
  let p := s.me
  let mate ← s.players.find? (fun q => p != q && config.mode.sameSide p q)
  let [enemyA, enemyB] := s.players.filter (fun q => !config.mode.sameSide p q) | none
  let field := s.bf0
  let (s, spell) ← put s p "OGS-002" .hand
  let (s, ally) ← putAt s mate "OGN-142" field
  let (s, first) ← putAt s enemyA "OGN-142" field
  let (s, second) ← putAt s enemyB "OGN-142" field
  let hit ← play s p spell [field]
  let (s, strike) ← put s p "OGS-024" .hand
  let strengthened ← cast (s.fund p 5 (order := 1)) p strike ⟨5, [.order]⟩
  let (s, annie) ← put s p "OGS-010" .hand
  let (s, _) ← put s p "OGN-094" .trash
  let (s, teammateSpell) ← put s mate "OGN-095" .trash
  let options ← castStop s p annie
  let returned ← play s p annie
  return [first, second].all (fun id => (hit.obj? id).any (·.damage == 3)) &&
    (hit.obj? ally).any (·.damage == 0) && strengthened.mightNow ally == some 12 &&
    strengthened.mightNow first == some 10 && returned.countIn p .hand "OGN-094" == 1 &&
    !options.trigPicks.contains teammateSpell && (returned.zone (.player mate .trash)).contains teammateSpell

-- Lux adds Spell-only Energy immediately and leaves the same player able to act.
#guard inLab fun s => do
  let p := s.me
  let (s, lux) ← put s p "OGS-014" .base
  let (s, flash) ← put s p "OGS-011" .hand
  let (s, unit) ← put s p "OGS-014" .hand
  let (s, gear) ← put s p "OGN-143" .hand
  let funded := s.fund p 2
  let add : Action := ⟨.player p, .manaAbility lux 0 ⟨0, []⟩⟩
  let (afterAdd, _) ← (step 100 funded add).toOption
  let castFlash : Action := ⟨.player p, .playCard flash ⟨2, []⟩ []⟩
  let paid ← cast afterAdd p flash ⟨2, []⟩
  let (expired, _) ← microStep0 { afterAdd with pending := [.expireTurn] }
  return (legalActions funded).contains add && afterAdd.pending == funded.pending &&
    afterAdd.tired lux == some true && !(step 100 afterAdd add).isOk &&
    (afterAdd.poolOf p).spellEnergy == 2 && (afterAdd.poolOf s.you).spellEnergy == 0 &&
    (legalActions afterAdd).contains castFlash && (paid.poolOf p).spellEnergy == 0 &&
    (paid.poolOf p).energy == 2 && paid.countIn p .trash "OGS-011" == 1 &&
    expired.poolOf p == RunePool.empty &&
    (cast afterAdd p unit ⟨4, []⟩).isNone && (cast afterAdd p gear ⟨3, []⟩).isNone

-- A limited Spell play can use the same Energy, and a resolution payment cannot.
#guard inLab fun s => do
  let p := s.me
  let (s, lux) ← put s p "OGS-014" .base
  let (s, flash) ← put s p "OGS-011" .trash
  let funded := s.fund p 0
  let (added, _) ← (step 100 funded ⟨.player p, .manaAbility lux 0 ⟨0, []⟩⟩).toOption
  let price := EffectPlayPrice.reduceEnergy 0
  let (queued, item) ← queueLimitedSpell added p flash price .normal
  let plan ← (limitedSpellOptions queued p item price).find? (fun plan => plan.targets.isEmpty)
  let (paid, events) ← commitLimitedSpell queued p item plan [] effectAddPolicy
  let (ready, readyItem) ← queueLimitedSpell funded p flash price .normal
  let luxAdd : EffectAdd := .ability lux 0 0 [] none
  let (paidWithAdd, _) ← commitLimitedSpell ready p readyItem plan [luxAdd] effectAddPolicy
  return (paid.poolOf p).spellEnergy == 0 && events.contains (.played p item) &&
    (queued.payNow p item ⟨1, []⟩).isNone &&
    (fundLimitedOptions ready p readyItem plan [] effectAddPolicy).contains
      (.fundLimitedSpell readyItem plan [luxAdd]) &&
    (paidWithAdd.poolOf p).spellEnergy == 0 && paidWithAdd.tired lux == some true &&
    (commitLimitedSpell ready p readyItem plan [] effectAddPolicy).isNone

-- Both Lux cards watch the controller's spells after resolution and read printed Energy.
#guard inLab fun s => do
  let p := s.me
  let (s, lux) ← put s p "OGS-006" .base
  let (s, _) ← put s p "OGS-021" .legendZone
  let (s, _) ← put s s.you "OGS-021" .legendZone
  let (s, cheap) ← put s p "OGS-011" .hand
  let (s, dear) ← put s p "OGS-024" .hand
  let cheapPlayed ← play s p cheap []
  let discounted := cheapPlayed.addTurnFx p (.nextSpellCostMinus 2)
  let dearPlayed ← cast (discounted.fund p 3 (body := 1)) p dear ⟨3, [.body]⟩
  return cheapPlayed.mightNow lux == some 5 && cheapPlayed.handN p + 1 == s.handN p &&
    dearPlayed.handN p == cheapPlayed.handN p && dearPlayed.handN s.you == s.handN s.you &&
    dearPlayed.mightNow lux == some 10

-- In Gentlemen's Duel the units deal the damage themselves.
#guard inLab fun s => do
  let p := s.me
  let (s, _) ← put s p "OGS-001" .base
  let (s, duel) ← put s p "OGS-008" .hand
  let (s, ally) ← put s p "OGN-049" .base
  let (s, enemy) ← put s s.you "OGN-142" .base
  let resolved ← play s p duel [ally, enemy]
  return (play s p duel [enemy, ally]).isNone && (play s p duel [ally]).isNone &&
    (resolved.obj? enemy).any (·.damage == 8) && resolved.countIn p .trash "OGN-049" == 1

-- Dark Child targets two different runes when its controller ends their turn.
#guard inLab fun initial => do
  let p := initial.me
  let s := (initial.noRunes p).noRunes initial.you
  let (s, _) ← put s p "OGS-017" .legendZone
  let (s, a) ← put s p "OGN-042" .base
  let (s, b) ← put s p "OGN-042" .base
  let (s, c) ← put s s.you "OGN-042" .base
  let ready := ((s.tire a).tire b).tire c
  let event := Event.phaseStarted p .ending
  let prepared ← firePicks ready [event]
  let resolved ← fire ready [event] { pick := fun ts => ts.contains a && ts.contains c }
  return prepared.contains a && prepared.contains b && prepared.contains c &&
    (ready.detect [Event.phaseStarted s.you .ending]).isEmpty &&
    resolved.tired a == some false && resolved.tired c == some false && resolved.tired b == some true

-- Tibbers marks damage on units at every Battlefield, including friendly units, and needs
-- two Power from its own domains.
#guard inLab fun s => do
  let p := s.me
  let other ← s.battlefields.find? (· != s.bf0)
  let (s, tibbers) ← put s p "OGS-018" .hand
  let (s, ally) ← putAt s p "OGN-142" s.bf0
  let (s, enemy) ← putAt s s.you "OGN-142" other
  let (s, baseUnit) ← put s p "OGN-142" .base
  let funded := s.rich p
  let resolved ← cast funded p tibbers ⟨8, [.fury, .chaos]⟩
  return (cast funded p tibbers ⟨8, [.fury, .order]⟩).isNone &&
    [ally, enemy].all (fun id => (resolved.obj? id).any (·.damage == 3)) &&
    (resolved.obj? baseUnit).any (·.damage == 0) && resolved.countIn p .base "OGS-018" == 1

-- Wuju Bladesman gives Might only to a friendly unit defending alone.
#guard inLab fun s => do
  let p := s.me
  let (s, _) ← put s p "OGS-019" .legendZone
  let (s, own) ← putAt s p "OGN-049" s.bf0
  let (s, foe) ← putAt s s.you "OGN-049" s.bf0
  let (crowd, _) ← putAt s p "OGN-049" s.bf0
  return s.mightNow own == some 5 && (s.inCombatAt s.bf0 s.you).mightNow own == some 7 &&
    (s.inCombatAt s.bf0 p).mightNow own == some 5 &&
    (s.inCombatAt s.bf0 p).mightNow foe == some 5 &&
    (crowd.inCombatAt s.bf0 s.you).mightNow own == some 5

-- Highlander spends its replacement on the first death and recalls the unit exhausted.
#guard inLab fun s => do
  let p := s.me
  let (s, highlander) ← put s p "OGS-020" .hand
  let (s, target) ← putAt s p "OGN-049" s.bf0
  let (s, enemy) ← putAt s s.you "OGN-049" s.bf0
  let shielded ← play s p highlander [target]
  let (recalled, first) := killOrSave shielded target
  let (killed, second) := killOrSave recalled target
  let (nextTurn, _) := killOrSave { shielded with turn := shielded.turn + 1 } target
  let discarded ← killed.firstOf p .trash "OGN-049"
  return (play s p highlander [enemy]).isNone && first.contains (.recalled target) &&
    (recalled.obj? target).any (fun o => o.loc.isNone && o.exhausted) &&
    !first.any (fun | .died .. | .standardMoved .. => true | _ => false) &&
    second.contains (.died discarded p) &&
    killed.countIn p .trash "OGN-049" == 1 && nextTurn.countIn p .trash "OGN-049" == 1

-- Might of Demacia uses the Battlefield of this Conquer, even if another was scored first.
#guard inLab fun s => do
  let p := s.me
  let field ← s.battlefields.find? (· != s.bf0)
  let (s, _) ← put s p "OGS-023" .legendZone
  let mut crowded := s
  for _ in [:4] do
    let (next, _) ← putAt crowded p "OGN-049" s.bf0
    crowded := next
  let alreadyScored := crowded.modObj s.bf0 (fun o => { o with scored := [p] })
  let (scoredEmpty, _, emptyEvents) := scoreBf alreadyScored p field true
  let empty ← fire scoredEmpty emptyEvents
  let emptyMarked := s.modObj s.bf0 (fun o => { o with scored := [p] })
  let mut three := emptyMarked
  for _ in [:3] do
    let (next, _) ← putAt three p "OGN-049" field
    three := next
  let (four, _) ← putAt three p "OGN-049" field
  let (scoredThree, _, threeEvents) := scoreBf three p field true
  let (scoredFour, _, fourEvents) := scoreBf four p field true
  let withoutDraw ← fire scoredThree threeEvents
  let draws ← fire scoredFour fourEvents
  return empty.handN p == s.handN p && withoutDraw.handN p == s.handN p &&
    draws.handN p == s.handN p + 2 &&
    (four.detect [Event.scored p field false]).isEmpty

-- Decisive Strike accepts either of its domains and increases friendly Might for the turn.
#guard inLab fun s => do
  let p := s.me
  let (s, strike) ← put s p "OGS-024" .hand
  let (s, baseUnit) ← put s p "OGN-049" .base
  let (s, fieldUnit) ← putAt s p "OGN-049" s.bf0
  let (s, enemy) ← put s s.you "OGN-049" .base
  let funded := s.rich p
  let byBody ← cast funded p strike ⟨5, [.body]⟩
  let byOrder ← cast funded p strike ⟨5, [.order]⟩
  return [byBody, byOrder].all (fun board => board.mightNow baseUnit == some 7 &&
    board.mightNow fieldUnit == some 7 && board.mightNow enemy == some 5) &&
    (cast funded p strike ⟨5, [.fury]⟩).isNone

end RiftboundTest
