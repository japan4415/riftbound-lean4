module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance ordered Rune Recycling -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- The player sets the order of the Runes before any move. The four channelled Runes, including
-- the originals still in the deck, are exhausted. The other player's Rune stays where it is.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let base := Zone.player p .base
  let deck := Zone.player p .runeDeck
  let original := (s.zone base ++ s.zone deck).filter
    (fun id => (s.cardDef? id).any (·.hasType .rune))
  let s ← original.foldlM (fun g id => (moveObj g id (.player p .banishment)).map Prod.fst) s
  let (s, _) ← put s p "RAD-016" .base
  let (s, a) ← put s p "OGN-007" .base
  let (s, b) ← put s p "OGN-042" .base
  let (s, c) ← put s p "OGN-089" .base
  let (s, inDeck) ← put s p "OGN-126" .runeDeck
  let (s, opponent) ← put s q "OGN-214" .base
  let endFrames : List Frame := [.phase .ending, .priority p]
  let (theirs, _) ← (advance 100 { s with active := some q, pending := endFrames } []).toOption
  let (starting, _) ← (advance 100 { s with pending := endFrames } []).toOption
  let (firstPass, _) ← (step 100 starting ⟨.player p, .pass⟩).toOption
  let (choosing, _) ← (step 100 firstPass ⟨.player q, .pass⟩).toOption
  let (next, _) ← (step 100 choosing ⟨.player p, .choose c⟩).toOption
  let (done, events) ← (step 100 next ⟨.player p, .choose a⟩).toOption
  let channeled := events.filterMap (fun
    | .moved _ id (.player who .base) =>
      if who == p then (done.cardDef? id).map (fun d => (d.id.code, (done.obj? id).any (·.exhausted)))
      else none
    | _ => none)
  let recycled := events.filterMap (fun
    | .moved id _ (.player who .runeDeck) => if who == p then some id else none
    | _ => none)
  return theirs.zone deck == [inDeck] && choosing.zone deck == [inDeck] &&
    next.zone deck == [inDeck] && [a, b, c].all (next.zone base).contains &&
    recycled == [c, a, b] && channeled == [
      ("OGN-126", true), ("OGN-089", true), ("OGN-007", true), ("OGN-042", true)] &&
    (done.zone (.player q .base)).contains opponent

end RiftboundTest
