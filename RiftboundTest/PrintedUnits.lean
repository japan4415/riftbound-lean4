module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests for printed Units with no effects beyond their keywords

Exercise the printed card IDs through ordinary play, combat, targeting, and movement. This
checks the base stats and keyword arguments as well as their interpretation by the engine.
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
  let (ownTurn, events) ← beginning p
  return model.might == printed.might && model.keywords == printed.keywords &&
    played.mightNow token == some (3 : Int) && played.tired token == some false &&
    opponentTurn.countIn p .base model.id.code == 1 && ownTurn.countIn p .base model.id.code == 0 &&
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

end RiftboundTest
