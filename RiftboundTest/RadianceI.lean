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

-- Raider's passive stops when it is returned for Ekko, before Ekko enters (CR 357, 359.2).
#guard radianceCase fun s => do
  let p := s.me
  let (s, raider) ← put (s.fund p 3) p "RAD-019" .base
  let (s, other) ← put s p "RAD-011" .base
  let (s, ekko) ← put s p "RAD-061" .hand
  let action (cost : ObjId) : Action := ⟨.player p, .playCard ekko ⟨3, []⟩ [cost] none none .plain⟩
  let (paid, events) ← (step 100 s (action raider)).toOption
  let (kept, _) ← (step 100 s (action other)).toOption
  let returned ← paid.firstOf p .hand "RAD-019"
  let entered ← paid.firstOf p .base "RAD-061"
  let stillReady ← kept.firstOf p .base "RAD-061"
  let moves := events.filter (fun | .moved .. => true | _ => false)
  return paid.tired entered == some true && kept.tired stillReady == some false &&
    moves == [.moved raider returned (.player p .hand), .moved ekko entered (.player p .base)]

-- A limited play also pays the return before checking the entry effects.
#guard radianceCase fun s => do
  let p := s.me
  let (s, raider) ← put (s.fund p 0) p "RAD-019" .base
  let (s, ekko) ← put s p "RAD-061" .hand
  let plans := permanentPlayPlans s p ekko { price := .ignoreBase }
  let plan ← plans.find? (fun plan => plan.battlefield.isNone && plan.extraObject == some raider)
  let (result, entered, events) ← applyReducedPermanent s p ekko plan
  let returned ← result.firstOf p .hand "RAD-019"
  return result.tired entered == some true &&
    events == [.moved raider returned (.player p .hand), .moved ekko entered (.player p .base), .played p entered]

-- The Kill and any replacement happen before Cruel Patron enters (CR 357, 359.2).
#guard radianceCase fun s => do
  let p := s.me
  let (s, raider) ← put (s.fund p 4) p "RAD-019" .base
  let (s, patron) ← put s p "OGN-208" .hand
  let action : Action := ⟨.player p, .playCard patron ⟨4, []⟩ [raider]⟩
  let (killed, events) ← (step 100 s action).toOption
  let victim ← killed.firstOf p .trash "RAD-019"
  let entered ← killed.firstOf p .base "OGN-208"
  let (withGear, gear) ← put s p "OGN-077" .base
  let (saved, replacement) ← (step 100 withGear action).toOption
  let sacrifice ← saved.firstOf p .trash "OGN-077"
  let ready ← saved.firstOf p .base "OGN-208"
  let relevant (es : List Event) := es.filter (fun | .moved .. | .died .. => true | _ => false)
  return killed.tired entered == some true && saved.tired ready == some false &&
    saved.tired raider == some true && (saved.obj? ready).any (·.paid) &&
    relevant events == [.moved raider victim (.player p .trash), .died victim p,
      .moved patron entered (.player p .base)] &&
    relevant replacement == [.moved gear sacrifice (.player p .trash), .died sacrifice p,
      .moved patron ready (.player p .base)]

-- Paying Cruel Patron by killing Lee Sin makes an already damaged Unit lethal before priority.
#guard match lab with
  | none => false
  | some start => ((do
    let p := start.me
    let field := start.bf0
    let (s, lee) ← putAt (start.control p field) p "OGN-151" field
    let (s, ally) ← putAt s p "OGN-136" field
    let (s, patron) ← put (s.fund p 4) p "OGN-208" .hand
    let ready := (dealObj 4 (s.buff ally) ally).1
    let (after, events) ← (step 100 ready ⟨.player p, .playCard patron ⟨4, []⟩ [lee]⟩).toOption
    return (cleanupStep ready).isNone && after.pending == [.priority p] &&
      (cleanupStep after).isNone && after.locate ally == none &&
      events.any (fun
        | .moved before _ (.player owner .trash) => before == ally && owner == p
        | _ => false)) : Option Bool).getD false

-- Give Cruel Patron Reaction in this fixture to exercise the Cleanup while a Spell is on the Chain.
#guard match lab with
  | none => false
  | some start => ((do
    let p := start.me
    let field := start.bf0
    let defs := start.cards.cards.map (fun d =>
      if d.id.code == "OGN-208" then { d with keywords := d.keywords ++ [{ keyword := .reaction }] }
      else d)
    let s := { start.control p field with cards := ⟨defs⟩ }
    let (s, lee) ← putAt s p "OGN-151" field
    let (s, ally) ← putAt s p "OGN-136" field
    let (s, patron) ← put (s.fund p 4) p "OGN-208" .hand
    let (s, spell) ← onChain s p "OGN-004"
    let stack := [Frame.chainPass p 0, .priority p]
    let ready := { (dealObj 4 (s.buff ally) ally).1 with pending := stack }
    let (after, events) ← (step 100 ready ⟨.player p, .playCard patron ⟨4, []⟩ [lee]⟩).toOption
    return (cleanupStep ready).isNone && after.pending == stack && after.zone .chain == [spell] &&
      (cleanupStep after).isNone && after.locate ally == none &&
      events.any (fun
        | .moved before _ (.player owner .trash) => before == ally && owner == p
        | _ => false)) : Option Bool).getD false

-- A limited play pays the same Kill cost before it decides how Cruel Patron enters.
#guard radianceCase fun s => do
  let p := s.me
  let (s, raider) ← put (s.fund p 0) p "RAD-019" .base
  let (s, patron) ← put s p "OGN-208" .hand
  let plans := permanentPlayPlans s p patron { price := .ignoreBase }
  let plan ← plans.find? (fun plan => plan.battlefield.isNone && plan.extraObject == some raider)
  let (result, entered, events) ← applyReducedPermanent s p patron plan
  let victim ← result.firstOf p .trash "RAD-019"
  return result.tired entered == some true && (result.obj? entered).any (·.paid) &&
    events == [.moved raider victim (.player p .trash), .died victim p,
      .moved patron entered (.player p .base), .played p entered]

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
