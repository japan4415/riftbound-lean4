module

import Riftbound.Rules.Setup
meta import Riftbound.Rules.Setup
import RiftboundCards
meta import RiftboundCards
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-! # Tests: published Constructed bans (TR 601.2.d) -/

namespace RiftboundTest

open Riftbound RiftboundCards

private meta def sets : List SetCode :=
  [testSet, ⟨"OGN"⟩, ⟨"OGS"⟩, ⟨"SFD"⟩, ⟨"UNL"⟩, ⟨"VEN"⟩, ⟨"RAD"⟩]

private meta def registrationDB : CardDB := ⟨RiftboundTest.db.cards ++ RiftboundCards.db.cards⟩

-- Each global revision applies on its first day.
#guard
  let count (m d : Nat) := (constructedBans .standard (.global ⟨2026, m, d⟩)).length
  [count 3 30, count 3 31, count 7 23, count 7 24, count 9 17, count 9 18,
    count 11 22, count 11 23] == [0, 7, 7, 10, 10, 12, 12, 22]

-- The latest Rules Hub lists differ by two entries, including the starter Legend.
#guard
  let period := BanListPeriod.global ⟨2026, 11, 23⟩
  let standard := constructedBans .standard period
  let teams := constructedBans .twoVTwo period
  standard.length == 22 && teams.length == 22 &&
    standard.filter (fun id => !teams.contains id) == [cid "OGN-168"] &&
    teams.filter (fun id => !standard.contains id) == [cid "OGS-019"] &&
    (standard ++ teams).all (fun id => (RiftboundCards.db.find? id).isSome)

#guard
  let before := constructedBans .twoVTwo (.global ⟨2026, 7, 23⟩)
  let start := constructedBans .twoVTwo (.global ⟨2026, 7, 24⟩)
  before.isEmpty && start.length == 11 &&
    start.contains (cid "OGS-019") && start.contains (cid "OGN-168")

-- Staggered events select the local season, with the Origins list reset on transition.
#guard
  let regional (season : RegionalSeason) := constructedBans .standard (.regional season)
  (regional .origins).isEmpty &&
    regional .spiritforged == constructedBans .standard (.global ⟨2026, 3, 31⟩) &&
    regional .unleashed == regional .spiritforged &&
    regional .vendetta == constructedBans .standard (.global ⟨2026, 9, 18⟩) &&
    regional .radiance == constructedBans .standard (.global ⟨2026, 11, 23⟩)

-- Registration and game setup reject a newly banned Main Deck card, sideboard card or Battlefield.
#guard
  let before := constructedLegality .standard (.global ⟨2026, 11, 22⟩) sets
  let after := constructedLegality .standard (.global ⟨2026, 11, 23⟩) sets
  let clean : ConstructedDeck := ⟨goodDeck, []⟩
  let cases : List ConstructedDeck :=
    [⟨{ goodDeck with main := goodDeck.main.take 39 ++ [cid "RAD-043"] }, []⟩,
     ⟨goodDeck, [cid "OGN-077"]⟩,
     ⟨{ goodDeck with battlefields := [cid "B0", cid "B1", cid "UNL-215"] }, []⟩]
  let config : GameConfig := { ruleSet := .tournament .constructed, mode := .duel }
  (GameState.initialConstructed registrationDB after config [clean, clean]).isSome &&
    cases.all (fun registration =>
      decide (ConstructedDeckValid registrationDB before registration) &&
      !decide (ConstructedDeckValid registrationDB after registration) &&
      (GameState.initialConstructed registrationDB before config [registration, clean]).isSome &&
      (GameState.initialConstructed registrationDB after config [registration, clean]).isNone)

-- A Constructed ban leaves the same Unit eligible in a Limited event without that ban.
#guard
  let restricted := constructedLegality .standard (.global ⟨2026, 11, 23⟩) sets
  let deck : LimitedDeck := {
    identity := [.fury, .calm, .mind], legend := none, chosenChampion := none
    main := cid "RAD-043" :: List.replicate 24 (cid "V0")
    runes := List.replicate 12 (cid "R1"), battlefields := [cid "B0"]
  }
  !decide (SealedDeckValid registrationDB restricted deck) &&
    decide (SealedDeckValid registrationDB { legalSets := sets, banned := [] } deck)

end RiftboundTest
