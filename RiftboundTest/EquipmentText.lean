module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Printed and granted Rules Text on Equipment -/

namespace RiftboundTest

open Riftbound

private meta def testBoard (test : GameState → Option Bool) : Bool :=
  (lab.bind test).getD false

private meta def startBeginning (s : GameState) (p : PlayerId) : Option (GameState × List Event) :=
  (advance 100 { s with active := some p, pending := [.phase .beginning, .priority p] } []).toOption

-- The Unleashed FAQ covers Spinning Axe with printed Temporary and with Temporary from Turn to
-- Dust. Exercise both through the Beginning Phase dispatcher, including the actual death event.
#guard testBoard fun s => do
  let p := s.me
  let (s1, unit) ← put s p "OGN-049" .base
  let (s2, axe) ← put s1 p "SFD-186" .hand
  let (s3, dust) ← put s2 p "UNL-070" .hand
  let played ← play s3 p axe
  let gear ← played.firstOf p .base "SFD-186"
  let (s4, other) ← put played p "OGN-088" .base
  let held ← startBeginning s4 p
  let detached := (detachObj s4 gear).1
  let loose ← startBeginning detached p
  let granted ← play s4 p dust [gear]
  let opposingTurn ← startBeginning granted s.you
  let marked ← startBeginning granted p
  let deathCount (events : List Event) := events.countP (fun | .died .. => true | _ => false)
  let pay : RunePool.Payment := ⟨0, [.fury]⟩
  return (s4.obj? gear).any (·.attached == some unit) &&
    s4.hasKw gear .temporary && held.1.countIn p .base "SFD-186" == 1 &&
    deathCount held.2 == 0 && !activatable (s4.rich p) p gear 0 pay [other] true &&
    activatable (detached.rich p) p gear 0 pay [other] true &&
    loose.1.countIn p .trash "SFD-186" == 1 && deathCount loose.2 == 1 &&
    opposingTurn.1.countIn p .base "SFD-186" == 1 && deathCount opposingTurn.2 == 0 &&
    marked.1.countIn p .trash "SFD-186" == 1 && deathCount marked.2 == 1

-- A reference to the printed keyword still sees it. Only the granted Deflect raises the surcharge
-- while the Gear is attached. Detaching makes its printed Deflect apply again.
#guard testBoard fun s => do
  let card : CardDef :=
    { id := ⟨"TEST-ATTACH-DEFLECT"⟩, name := "Test Equipment", types := [.gear],
      keywords := [⟨.deflect, .amount 2⟩] }
  let s := { s with cards := ⟨s.cards.cards ++ [card]⟩ }
  let (s1, host) ← put s s.me "OGN-049" .base
  let (s2, gear) ← put s1 s.me card.id.code .base
  let held := (attachTo host s2 gear).1
  let granted := (addTempKw ⟨.deflect, .amount 1⟩ .never held gear).1
  let detached := (detachObj granted gear).1
  return s2.deflectCost s.you [gear] == 2 && held.hasKw gear .deflect &&
    held.deflectCost s.you [gear] == 0 && granted.deflectCost s.you [gear] == 1 &&
    granted.deflectCost s.me [gear] == 0 && detached.deflectCost s.you [gear] == 3

private meta def checkGear (code : String) (domain : Domain) (bonus : Int) : Bool :=
  testBoard fun s => do
    let p := s.me
    let (s1, gear) ← put s p code .hand
    let played ← play s1 p gear
    let item ← played.firstOf p .base code
    let (s2, target) ← put played p "OGN-049" .base
    let (s3, other) ← put s2 p "OGN-088" .base
    let pay : RunePool.Payment := ⟨0, [domain]⟩
    let equipped ← activate s3 p item 0 [target] pay
    return (equipped.obj? item).any (·.attached == some target) &&
      equipped.mightNow target == some (5 + bonus) &&
      (activate s3 p item 0 [target] ⟨0, []⟩).isNone &&
      (activate equipped p item 0 [other] pay).isNone

-- Long Sword, Sterak's Gage, Doran's Blade and B.F. Sword share ordinary Equip.
#guard checkGear "SFD-022" .fury 2
#guard checkGear "SFD-056" .calm 3
#guard checkGear "SFD-095" .body 2
#guard checkGear "SFD-161" .order 3

private meta def checkQuickDraw (code : String) (bonus : Int) : Bool :=
  testBoard fun s => do
    let p := s.me
    let q := s.you
    let opponentTurn := { s with active := some q, pending := [.priority q] }
    let (s1, reached) ← put opponentTurn p "OGN-049" .base
    let (s2, gear) ← put s1 p code .hand
    let (board, spell) ← put s2 q "OGN-095" .hand
    let (queued, _) ← (step 100 (board.rich q) ⟨.player q, .playCard spell ⟨1, []⟩ [reached]⟩).toOption
    let (priority, _) ← (step 100 queued ⟨.player q, .pass⟩).toOption
    let finished ← cast (priority.rich p) p gear (payOf priority gear)
    let equipped ← finished.firstOf p .base code
    return (finished.obj? equipped).any (·.attached == some reached) &&
      finished.mightNow reached == some (5 + bonus - 1)

#guard checkQuickDraw "SFD-022" 2
#guard checkQuickDraw "SFD-056" 3
#guard checkQuickDraw "SFD-186" 3

-- The three Equipment keywords use control, even when a friendly permanent is owned and
-- controlled by a teammate. Quick-Draw and Weaponmaster still finalize their own targets.
#guard testBoard fun duel => do
  let p := duel.me
  let mate := duel.you
  let s := GameState.empty { mode := Mode.teamDuel, ruleSet := .coreOnly } duel.cards
  let s := { s with
    phase := .main, active := some p, turn := 2,
    turnOrder := Mode.teamTurnOrder true, pending := [.priority p] }
  let (s1, mine) ← put s p "OGN-049" .base
  let (s2, theirs) ← put s1 mate "OGN-049" .base
  let (s3, gear) ← put s2 p "SFD-022" .base
  let (s4, otherGear) ← put s3 mate "SFD-022" .base
  let (s5, chef) ← put s4 p "SFD-092" .base
  let funded := s5.rich p
  let fromPlay (source : ObjId) : List ObjId := (triggersOf funded source p .play).flatMap (fun t =>
    (trigOptions funded t).flatMap Prod.fst)
  let pay : RunePool.Payment := ⟨0, [.fury]⟩
  return funded.config.mode.sameSide p mate && activatable funded p gear 0 pay [mine] true &&
    !activatable funded p gear 0 pay [theirs] true &&
    (fromPlay gear).contains mine && !(fromPlay gear).contains theirs &&
    (fromPlay chef).contains gear && !(fromPlay chef).contains otherGear

end RiftboundTest
