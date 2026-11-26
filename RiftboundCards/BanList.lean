module

public import Riftbound.Basic.RulesVersion
public import Riftbound.Tournament.Format

/-!
# Sanctioned Constructed ban lists

The official Rules Hub publishes separate lists for Standard and Constructed 2v2 (TR 601.2.d).
This data uses logical card IDs, so all printings of a banned card share its entry. See
tournament-model.md §2.1 for the announcements and the regional schedule.
-/

public section

namespace RiftboundCards

open Riftbound

/-- The sanctioned Constructed formats that have published ban lists. -/
inductive ConstructedFormat where
  /-- Standard Constructed. -/
  | standard
  /-- Constructed 2v2. -/
  | twoVTwo
deriving DecidableEq, Repr

/-- The set season in effect at an event on a staggered competitive circuit. -/
inductive RegionalSeason where
  /-- Origins. -/
  | origins
  /-- Spiritforged. -/
  | spiritforged
  /-- Unleashed. -/
  | unleashed
  /-- Vendetta. -/
  | vendetta
  /-- Radiance. -/
  | radiance
deriving DecidableEq, Repr

/-- Select the global list by event-local date or the list for an event's staggered set season.
Use the regional season once the organizer applies the policy announced on November 13, 2026. -/
inductive BanListPeriod where
  /-- An event following the global schedule. -/
  | global (date : RulesDate)
  /-- An event following a staggered circuit's local set season. -/
  | regional (season : RegionalSeason)
deriving DecidableEq, Repr

private def firstBans : List CardId := [
  ⟨"SFD-122"⟩, -- Called Shot
  ⟨"SFD-020"⟩, -- Draven, Vanquisher
  ⟨"OGN-168"⟩, -- Fight or Flight
  ⟨"OGN-182"⟩, -- Scrapheap
  ⟨"OGN-292"⟩, -- The Dreaming Tree
  ⟨"OGN-284"⟩, -- Obelisk of Power
  ⟨"OGN-285"⟩  -- Reaver's Row
]

private def julyBans : List CardId := firstBans ++ [
  ⟨"OGN-177"⟩, -- Stealthy Pursuer
  ⟨"OGN-290"⟩, -- The Arena's Greatest
  ⟨"OGN-276"⟩  -- Aspirant's Climb
]

private def septemberBans : List CardId := julyBans ++ [
  ⟨"OGN-110"⟩, -- Ekko, Recurrent
  ⟨"OGN-183"⟩  -- Stacked Deck
]

private def radianceBans : List CardId := septemberBans ++ [
  ⟨"RAD-043"⟩, -- Riven, Broken Blade
  ⟨"OGN-077"⟩, -- Zhonya's Hourglass
  ⟨"SFD-048"⟩, -- Stellacorn Herder
  ⟨"OGN-194"⟩, -- Nocturne, Horrifying
  ⟨"OGN-195"⟩, -- Rhasa the Sunderer
  ⟨"OGN-026"⟩, -- Brynhir Thundersong
  ⟨"OGN-160"⟩, -- Dazzling Aurora
  ⟨"OGN-242"⟩, -- Baited Hook
  ⟨"SFD-207"⟩, -- Emperor's Dais
  ⟨"UNL-215"⟩  -- Star Spring
]

private def reaches (date effective : RulesDate) : Bool :=
  decide (effective.year < date.year ∨ effective.year = date.year ∧
    (effective.month < date.month ∨ effective.month = date.month ∧ effective.day ≤ date.day))

private def twoVTwoLegend : CardId := ⟨"OGS-019"⟩ -- Master Yi, Wuju Bladesman

private def radianceList (format : ConstructedFormat) : List CardId :=
  match format with
  | .standard => radianceBans
  -- The November 23 Rules Hub omits Fight or Flight from the 2v2 list.
  | .twoVTwo => twoVTwoLegend :: radianceBans.erase ⟨"OGN-168"⟩

private def globalList (format : ConstructedFormat) (date : RulesDate) : List CardId :=
  if reaches date ⟨2026, 11, 23⟩ then radianceList format
  else if reaches date ⟨2026, 7, 24⟩ then
    let cards := if reaches date ⟨2026, 9, 18⟩ then septemberBans else julyBans
    match format with
    | .standard => cards
    | .twoVTwo => twoVTwoLegend :: cards
  else
    match format with
    | .standard => if reaches date ⟨2026, 3, 31⟩ then firstBans else []
    | .twoVTwo => []

/-- The published bans for a format and event. The first day of a global revision is inclusive. -/
def constructedBans (format : ConstructedFormat) : BanListPeriod → List CardId
  | .global date => globalList format date
  | .regional .origins => []
  | .regional .spiritforged | .regional .unleashed => globalList format ⟨2026, 7, 23⟩
  | .regional .vendetta => globalList format ⟨2026, 10, 22⟩
  | .regional .radiance => radianceList format

/-- The event's official ban list combined with its released sets. This is the environment for
Constructed registration, sideboard validation, and Constructed game setup. -/
def constructedLegality (format : ConstructedFormat) (period : BanListPeriod)
    (legalSets : List SetCode) : LegalityEnv :=
  { legalSets, banned := constructedBans format period }

end RiftboundCards

end
