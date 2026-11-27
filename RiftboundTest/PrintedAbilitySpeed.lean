module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Printed timing on a card and its abilities -/

namespace RiftboundTest

open Riftbound

-- A speed printed with an ability arrow belongs to the following ability.
#guard (["UNL-045", "UNL-049", "UNL-093", "UNL-161", "UNL-194", "UNL-197",
    "VEN-075", "VEN-112", "VEN-139", "VEN-141", "VEN-143", "VEN-147", "VEN-155",
    "RAD-021", "RAD-143"] : List String).all fun code =>
  (RiftboundCards.db.find? (cid code)).any fun card =>
    card.keywords.all fun kw => kw.keyword != .action && kw.keyword != .reaction

-- Earlier printings still grant the familiar card-play timing when the keyword stands alone.
#guard [
    (RiftboundCards.Origins.OGN_241, Keyword.reaction),
    (RiftboundCards.Spiritforged.SFD_025, .reaction),
    (RiftboundCards.Origins.OGN_004, .action)].all fun (card, speed) =>
  card.keywords.any fun kw => kw.keyword == speed

-- Dragonsoul Sage and Energy Conduit can be played at ordinary priority. Their Add resolves
-- immediately from the Board while the Chain is open or when their player has Focus.
private meta def printedAdd (code : String) (energy : Nat) : Option Bool := do
  let s ← lab
  let p := s.me
  let (s, source) ← put s p code .base
  let (s, inHand) ← put s p code .hand
  let (s, spell) ← put s p "UNL-103" .hand
  let (s, mover) ← put s p "V0" .base
  let s := s.fund p (energy + 2)
  let play : Action := ⟨.player p, .playCard inHand ⟨energy, []⟩ []⟩
  let (played, _) ← (step 100 s play).toOption
  let (chain, _) ← (step 100 s ⟨.player p, .playCard spell ⟨2, []⟩ [] none none (.mode 1)⟩).toOption
  let (showdown, _) ← (step 100 s ⟨.player p, .standardMove mover (.battlefield s.bf0)⟩).toOption
  let add : Action := ⟨.player p, .manaAbility source 0 ⟨0, []⟩⟩
  let works (before : GameState) (fuel : Nat) : Bool :=
    ((step fuel before add).toOption).any fun (after, events) =>
      after.pending == before.pending && after.zone .chain == before.zone .chain &&
      (after.poolOf p).energy == (before.poolOf p).energy + 1 &&
      after.tired source == some true && events == [.activated p source 0 (some 0)] &&
      !(step 100 after add).isOk
  return played.countIn p .base code == 2 &&
    !((legalFrameActions chain).contains play) && !(step 100 chain play).isOk &&
    !((legalFrameActions showdown).contains play) && !(step 100 showdown play).isOk &&
    works s 1 && works chain 0 && works showdown 0

#guard (printedAdd "OGN-098" 3).getD false
#guard (printedAdd "UNL-093" 2).getD false

-- The guest's Reaction Add leaves the invitation open and supplies the guest's own pool.
#guard (lab.bind fun labState => do
  let p : PlayerId := ⟨0⟩
  let guest : PlayerId := ⟨1⟩
  let before := GameState.empty { ruleSet := .coreOnly, mode := .teamDuel } labState.cards
  let s := { before with
    phase := .main, turn := 1, active := some p, turnOrder := Mode.teamTurnOrder true,
    pending := [.priority p] }
  let (s, sage) ← put s guest "UNL-093" .base
  let (s, conduit) ← put s guest "OGN-098" .base
  let (invited, _) ← (step 0 s ⟨.player p, .inviteTeammate guest⟩).toOption
  let use (id : ObjId) : Action := ⟨.player guest, .manaAbility id 0 ⟨0, []⟩⟩
  let (first, firstEvents) ← (step 0 invited (use sage)).toOption
  let (second, secondEvents) ← (step 0 first (use conduit)).toOption
  return second.pending == invited.pending && (second.zone .chain).isEmpty &&
    (second.poolOf guest).energy == 2 && (second.poolOf p).energy == 0 &&
    firstEvents == [.activated guest sage 0 (some 0)] &&
    secondEvents == [.activated guest conduit 0 (some 0)]).getD false

-- Vision still belongs to the Gear. Its controller can move the inspected card or leave it.
#guard (lab.bind fun s => do
  let p := s.me
  let q := s.you
  let (s, card) ← put s p "UNL-161" .hand
  let deck (state : GameState) (player : PlayerId) := state.zone (.player player .mainDeck)
  let top ← (deck s p).head?
  let recycled ← play s p card
  let kept ← play s p card [] { yes := false }
  return deck recycled p == (deck s p).tail ++ [top] &&
    deck kept p == deck s p && deck recycled q == deck s q &&
    recycled.countIn p .base "UNL-161" == 1).getD false

-- Divining Shells pays Kill before responses. The target gets its bonus only on resolution.
#guard (lab.bind fun s => do
  let p := s.me
  let (s, inHand) ← put s p "UNL-161" .hand
  let (s, fieldSource) ← put s p "UNL-161" .base
  let (s, unit) ← put s p "V0" .base
  let s := s.fund p 2
  let (showdown, _) ← (step 100 s ⟨.player p, .standardMove unit (.battlefield s.bf0)⟩).toOption
  let target ← (showdown.unitsOf p s.bf0).head?
  let might ← showdown.mightNow target
  let claim : Action := ⟨.player p, .activate fieldSource 0 ⟨0, [], none⟩ [target]⟩
  let play : Action := ⟨.player p, .playCard inHand ⟨2, []⟩ []⟩
  let (paid, events) ← (step 100 showdown claim).toOption
  let settled := settleChain {} 10 paid
  let (expired, _) ← (advance 100 { settled with pending := [.expireTurn] } []).toOption
  return !(step 100 showdown play).isOk && !(legalFrameActions showdown).contains play &&
    !(step 100 (showdown.tire fieldSource) claim).isOk &&
    paid.countIn p .trash "UNL-161" == 1 &&
    events.contains (.activated p fieldSource 0 (some 0)) &&
    paid.mightNow target == showdown.mightNow target &&
    settled.mightNow target == some (might + 2) && expired.mightNow target == some might).getD false

end RiftboundTest
