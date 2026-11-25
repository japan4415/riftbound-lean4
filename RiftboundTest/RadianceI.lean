module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance play costs paid with permanents -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Swimmer can kill either friendly type, and its damage is conditional on that payment.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, swimmer) ← put s p "RAD-014" .hand
  let (s, unit) ← put s p "RAD-061" .base
  let (s, gear) ← put s p "RAD-012" .base
  let (s, target) ← put s q "RAD-061" .base
  let says : Says := { pick := fun ids => ids == [target] }
  let byUnit ← play s p swimmer [unit] says
  let byGear ← play s p swimmer [gear] says
  let declined ← play s p swimmer [] says
  let damage (game : GameState) := (game.obj? target).map (·.damage)
  return damage byUnit == some 2 && byUnit.countIn p .trash "RAD-061" == 1 &&
    (byUnit.fxOf p).contains .unitDied &&
    damage byGear == some 2 && byGear.countIn p .trash "RAD-012" == 1 &&
    !(byGear.fxOf p).contains .unitDied && damage declined == some 0 &&
    (play s p swimmer [target] says).isNone

-- Guardian Angel replaces the cost Unit's death, which still pays for Swimmer's trigger.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, swimmer) ← put s p "RAD-014" .hand
  let (s, saved) ← putAt (s.control p s.bf0) p "RAD-061" s.bf0
  let (s, angel) ← putAt s p "SFD-051" s.bf0
  let (s, target) ← put s q "RAD-061" .base
  let s := (s.modObj saved (fun o => { o with damage := 1 })).modObj angel
    (fun o => { o with attached := some saved })
  let after ← play s p swimmer [saved] { pick := fun ids => ids == [target] }
  return after.where? saved == some (.player p .base) && after.tired saved == some true &&
    (after.obj? saved).map (·.damage) == some 0 && (after.obj? target).map (·.damage) == some 2 &&
    after.countIn p .trash "SFD-051" == 1 && !(after.fxOf p).contains .unitDied

-- Ekko needs a friendly Unit, and a borrowed Unit returns to its owner's hand.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, ekko) ← put s p "RAD-061" .hand
  let (s, borrowed) ← putAt s q "RAD-011" s.bf0
  let s := (s.control p s.bf0).modObj borrowed (fun o => { o with controller := p })
  let (s, gear) ← put s p "RAD-012" .base
  let returned ← play s p ekko [borrowed]
  let played ← (returned.zone (.player p .base)).find? (fun id =>
    (returned.cardDef? id).any (·.id == cid "RAD-061"))
  return returned.countIn q .hand "RAD-011" == 1 && (returned.obj? borrowed).isNone &&
    returned.hasKw played .ganking &&
    (play s p ekko []).isNone && (play s p ekko [gear]).isNone

-- Ignoring the printed base price does not waive Ekko's mandatory Unit return.
#guard radianceCase fun s => do
  let p := s.me
  let (s, ekko) ← put s p "RAD-061" .hand
  let viaEffect (g : GameState) := do
    let effect : Effect := .prim (.play (.var pickVar))
    let run := Frame.run p g.bf0 (Env.empty.bind pickVar (.obj ekko)) (.cons effect .nil)
    let (t, _) ← (advance 100 { g with pending := run :: g.pending } []).toOption
    some (settleChain {} 12 t)
  let unpaid ← viaEffect s
  let (s, _) ← put s p "RAD-011" .base
  let paid ← viaEffect s
  return unpaid.countIn p .hand "RAD-061" == 1 && unpaid.countIn p .base "RAD-061" == 0 &&
    paid.countIn p .base "RAD-061" == 1 && paid.countIn p .hand "RAD-011" == 1

-- Spirit reads the returned Gear's printed Energy, excluding both its Power and Spirit's cost.
#guard radianceCase fun s => do
  let p := s.me
  let (s, spirit) ← put s p "RAD-066" .hand
  let (s, cheap) ← put s p "RAD-012" .base
  let (s, costly) ← put s p "RAD-062" .base
  let (s, unit) ← put s p "RAD-061" .base
  let withCheap ← play s p spirit [cheap]
  let withCostly ← play s p spirit [costly]
  let declined ← play s p spirit []
  let played (g : GameState) := (g.zone (.player p .base)).find? fun id =>
    (g.cardDef? id).any (·.id == cid "RAD-066")
  let a ← played withCheap
  let b ← played withCostly
  let c ← played declined
  return withCheap.mightNow a == some 5 && withCheap.tired a == some false &&
    withCostly.mightNow b == some 9 && withCostly.tired b == some false &&
    withCostly.countIn p .hand "RAD-062" == 1 &&
    declined.mightNow c == some 4 && declined.tired c == some true &&
    (play s p spirit [unit]).isNone

end RiftboundTest
