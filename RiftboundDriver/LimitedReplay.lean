module

public import RiftboundDriver.Replay

/-! # Limited pool allocation and Battlefield history -/

public section

namespace RiftboundDriver

open Riftbound

/-- Count every copy, including when two registrations draw from the same card pool. -/
def checkLimitedCopies (available used : List CardId) (context : String) :
    Except String Unit := do
  for card in used.eraseDups do
    if used.count card > available.count card then
      throw s!"{context} uses too many copies of {card.code}"

/-- Every observed pool card must be in the pinned card database. -/
def checkLimitedPool (db : CardDB) (cards : List CardId) : Except String Unit := do
  for card in cards.eraseDups do
    if card == limitedBlankBattlefield.id || (db.find? card).isNone then
      throw s!"the pool contains an unknown product card {card.code}"

/-- The cards allocated from a Limited pool. The Chosen Champion is already in the Main Deck,
Runes may come from any source, and blank Battlefields are freely available
(TR 602.3.d, 602.4.a.4, 602.4.b.5). -/
def limitedAllocation (decks : List LimitedDeck) : List CardId :=
  decks.flatMap (fun deck => deck.legend.toList ++ deck.reserveLegends ++ deck.main ++
    deck.battlefields.filter (· != limitedBlankBattlefield.id))

/-- Check the changes before a game where sideboarding is unavailable. In Best of 3 the Battlefield
is selected for the game independently of sideboarding (TR 403.10, 602.3.e.4). -/
def sameLimitedRegistration (a b : LimitedDeck) (bestOfThree : Bool) : Bool :=
  a.legend == b.legend && a.chosenChampion == b.chosenChampion &&
    decide (a.identity.Perm b.identity) && decide (a.main.Perm b.main) &&
    decide (a.reserveLegends.Perm b.reserveLegends) && decide (a.runes.Perm b.runes) &&
    (bestOfThree || decide (a.battlefields.Perm b.battlefields))

/-- A Limited Best of 1 randomly selects from three registered Battlefields. Best of 3 uses a
single declared Battlefield for each contributing seat (TR 602.3.e.3, 602.3.e.4). -/
def checkLimitedBattlefieldCount (db : CardDB) (decks : List LimitedDeck) (contributors : List PlayerId)
    (bestOfThree : Bool) : Except String Unit := do
  if !bestOfThree then
    for deck in decks do
      unless deck.battlefields.length == 3 do
        throw "Limited Best of 1 requires three registered Battlefields per seat"
      let named := deck.battlefields.filter (· != limitedBlankBattlefield.id)
      let some cards := named.mapM db.find? | throw "the registered Battlefield is unknown"
      unless decide ((cards.map CardDef.nameKey).Nodup) do
        throw "Limited Best of 1 requires distinct named Battlefields"
  else
    for seat in contributors do
      unless decks[seat.n]?.any (fun deck => deck.battlefields.length == 1) do
        throw s!"seat {seat.n} must declare one selected Battlefield"

/-- Reserve a Limited Battlefield copy for this match. A draw reuses the same battlefield without
spending another copy (TR 406.1.b, 602.3.e.4.a). -/
def useLimitedBattlefields (pool : List CardId) (used selected : List CardId)
    (reused : Bool) : Except String (List CardId) := do
  if reused then return used
  let next := used ++ selected.filter (· != limitedBlankBattlefield.id)
  checkLimitedCopies pool next "the match's Battlefield history"
  return next

end RiftboundDriver

end
