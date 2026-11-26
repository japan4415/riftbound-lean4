module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance draws from a look and hand costs on triggers -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Captain looks at exactly four cards. The chosen eligible Gear is revealed and counts as a draw.
-- Declining recycles all four, and a card beyond the look is never a choice.
#guard radianceCase fun s => do
  let p := s.me
  let (s, captain) ← put s p "RAD-129" .hand
  let (s, expensive) ← put s p "RAD-019" .mainDeck
  let (s, spell) ← put s p "RAD-047" .mainDeck
  let (s, unit) ← put s p "RAD-088" .mainDeck
  let (s, gear) ← put s p "RAD-089" .mainDeck
  let (s, outside) ← put s p "RAD-024" .mainDeck
  let deck := Zone.player p .mainDeck
  let seen := [expensive, gear, spell, unit]
  let suffix := outside :: (s.zone deck).filter (fun id => !(outside :: seen).contains id)
  let s := s.reorder deck (seen ++ suffix)
  let direct (g : GameState) (a : ActionKind) := (step 100 g ⟨.player p, a⟩).toOption
  -- Drive the optional draw and its choice separately, before the Recycle chance action.
  let (entered, _) ← (step 100 (s.fund p 2)
    ⟨.player p, .playCard captain ⟨2, []⟩ []⟩).toOption
  let (pass1, _) ← direct entered .pass
  let (mayDraw, looked) ← (step 100 pass1 ⟨.player s.you, .pass⟩).toOption
  let (choosing, _) ← direct mayDraw (.decide true)
  let (recycling, drawn) ← direct choosing (.choose gear)
  let (kept, _) ← (step 100 recycling ⟨.chance, .arrange [unit, spell, expensive]⟩).toOption
  let (declining, _) ← direct mayDraw (.decide false)
  let (declined, _) ← (step 100 declining ⟨.chance, .arrange seen⟩).toOption
  let handGear ← kept.firstOf p .hand "RAD-089"
  let draws (g : GameState) := g.drawLog.count (p, g.turn)
  return seen.all (fun id => looked.contains (.lookedAt p id)) &&
    (legalFrameActions choosing).map Action.kind == [.choose gear, .choose unit] &&
    drawn.contains (.revealed p gear) && drawn.contains (.moved gear handGear (.player p .hand)) &&
    drawn.contains (.drew p) && draws kept == draws s + 1 && draws declined == draws s &&
    kept.zone deck == suffix ++ [unit, spell, expensive] && declined.zone deck == suffix ++ seen

-- Mordekaiser's discard is paid when the trigger is finalized. Declining leaves the hand and
-- target alone. Attack exposes the same discard options as the play trigger.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, morde) ← put s p "RAD-137" .hand
  let (s, fuel) ← put s p "RAD-011" .hand
  let (s, target) ← put s q "RAD-089" .base
  let (onPlay, _) ← (step 100 (s.fund p 9 (order := 2))
    ⟨.player p, .playCard morde ⟨9, [.order, .order]⟩ []⟩).toOption
  let actions := legalFrameActions onPlay
  let use ← actions.find? (fun a => match a.kind with
    | .putTrigger _ [id] (.pay [cost] ..) => id == target && cost == fuel
    | _ => false)
  let skip ← actions.find? (fun a => match a.kind with
    | .putTrigger _ _ .skip => true
    | _ => false)
  let (paid, events) ← (step 100 onPlay use).toOption
  let (declined, _) ← (step 100 onPlay skip).toOption
  let resolved := settleChain {} 12 paid
  let source ← declined.firstOf p .base "RAD-137"
  let attack ← (triggersOf declined source p .attack).head?
  let emptyHand ← (declined.zone (.player p .hand)).foldlM
    (fun g id => (moveObj g id (.player p .mainDeck)).map Prod.fst) declined
  return !(paid.zone (.player p .hand)).contains fuel &&
    events.any (fun | .discarded who _ _ => who == p | _ => false) &&
    (paid.zone (.player q .base)).contains target && !(paid.zone .chain).isEmpty &&
    resolved.countIn q .trash "RAD-089" == 1 &&
    (declined.zone (.player p .hand)).contains fuel && (declined.zone (.player q .base)).contains target &&
    (trigPayments declined attack).contains [fuel] && (trigPayments emptyHand attack).isEmpty

end RiftboundTest
