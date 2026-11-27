module

import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-! # Radiance card scenarios -/

namespace RiftboundTest

open Riftbound

private meta def radianceCase (f : GameState → Option Bool) : Bool :=
  (lab.bind f).getD false

-- Lost to the Sands locks a different kind of target for each mode.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, spell) ← put s p "RAD-013" .hand
  let (s, unit) ← putAt s q "RAD-060" field
  let (s, baseUnit) ← put s q "RAD-060" .base
  let (s, gear) ← put s q "SFD-117" .base
  let s := (s.control q field).fund p 3 (fury := 1)
  let pay := ⟨3, [.fury]⟩
  let hit ← cast s p spell pay [unit] (pick := .mode 0)
  let broken ← cast s p spell pay [gear] (pick := .mode 1)
  return (hit.obj? unit).any (·.damage == 4) && hit.inPlay.contains gear &&
    broken.countIn q .trash "SFD-117" == 1 && (broken.obj? unit).any (·.damage == 0) &&
    (cast s p spell pay [baseUnit] (pick := .mode 0)).isNone &&
    (cast s p spell pay [unit] (pick := .mode 1)).isNone

-- The Avian uses the target's buff status at resolution and its +2 Might expires.
#guard radianceCase fun s => do
  let p := s.me
  let (s, avian) ← put s p "RAD-027" .base
  let (s, target) ← put s s.you "RAD-011" .base
  let buffed ← activate s p avian 0 [target]
  let ready := buffed.modObj avian (fun o => { o with exhausted := false })
  let boosted ← activate ready p avian 0 [target]
  let (expired, _) ← (advance 100 { boosted with pending := [.expireTurn] } []).toOption
  return buffed.tired avian == some true && buffed.mightNow target == some 5 &&
    boosted.mightNow target == some 7 && expired.mightNow target == some 5

-- Only a qualifying play by the Conservator's controller readies it.
#guard radianceCase fun s => do
  let p := s.me
  let (s, watcher) ← put s p "RAD-030" .base
  let (s, small) ← put s p "RAD-011" .hand
  let (s, large) ← put s p "RAD-060" .hand
  let (s, enemy) ← put s s.you "RAD-060" .base
  let s := s.tire watcher
  let low ← play s p small
  let high ← play s p large
  let theirs ← fire s [.played s.you enemy]
  return low.tired watcher == some true && high.tired watcher == some false &&
    theirs.tired watcher == some true

-- The Ferryman can move a different Unit at its entry Battlefield and the move is optional.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let away ← s.battlefields.find? (· != field)
  let (s, ferryman) ← put s p "RAD-031" .hand
  let (s, nearby) ← putAt s p "RAD-011" field
  let (s, distant) ← putAt s p "RAD-011" away
  let s := (s.control p field).control p away
  let funded := s.fund p 4
  let (waiting, _) ← (step 100 funded ⟨.player p, .playCard ferryman ⟨4, []⟩ [field]⟩).toOption
  let moved := settleChain { pick := (· == [nearby]) } 12 waiting
  let skipped := settleChain { pick := (· == [nearby]), yes := false } 12 waiting
  let fromBase ← play s p ferryman
  return waiting.trigPicks == [nearby] &&
    moved.where? nearby == some (.player p .base) && skipped.where? nearby == some .battlefieldZone &&
    fromBase.where? nearby == some .battlefieldZone && moved.where? distant == some .battlefieldZone

-- The Curator gives Gear on its side the usual Deflect surcharge.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, _) ← put s p "RAD-037" .base
  let (s, own) ← put s p "SFD-117" .base
  let (s, enemy) ← put s q "SFD-117" .base
  let (s, unit) ← put s p "RAD-011" .base
  return s.deflectOf own == 1 && s.deflectOf enemy == 0 && s.deflectOf unit == 0 &&
    s.deflectCost q [own] == 1 && s.deflectCost p [own] == 0

-- The Ward boosts allied Units until its own controller completes a Unit play.
#guard radianceCase fun s => do
  let p := s.me
  let (s, ward) ← put s p "RAD-039" .base
  let (s, ally) ← put s p "RAD-011" .base
  let (s, enemy) ← put s s.you "RAD-011" .base
  let (s, newcomer) ← put s p "RAD-011" .hand
  let (s, gear) ← put s p "SFD-117" .hand
  let enemyPlay ← fire s [.played s.you enemy]
  let gearPlay ← play s p gear
  let unitPlay ← play s p newcomer
  return s.mightNow ally == some 6 && s.mightNow enemy == some 4 &&
    enemyPlay.inPlay.contains ward && gearPlay.inPlay.contains ward &&
    unitPlay.mightNow ally == some 4 && unitPlay.countIn p .trash "RAD-039" == 1

-- The Goatherd can decline the kill after choosing a Gear within the printed Energy limit.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, goatherd) ← put s p "RAD-083" .hand
  let (s, cheap) ← put s q "RAD-039" .base
  let (s, expensive) ← put s q "RAD-146" .base
  let waiting ← castStop s p goatherd
  let killed := settleChain { pick := (· == [cheap]) } 12 waiting
  let kept := settleChain { pick := (· == [cheap]), yes := false } 12 waiting
  let played ← killed.firstOf p .base "RAD-083"
  return waiting.trigPicks == [cheap] && s.kwAmount goatherd .shield == 2 &&
    killed.countIn q .trash "RAD-039" == 1 && kept.inPlay.contains cheap &&
    kept.inPlay.contains expensive && killed.inPlay.contains expensive &&
    killed.tired played == some true

-- K'Sante can Accelerate and channels a ready Rune when holding his Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, card) ← put s p "RAD-086" .hand
  let s := s.control p field
  let ordinary ← cast (s.fund p 5) p card ⟨5, []⟩ [field]
  let fast ← cast (s.fund p 6 (body := 1)) p card ⟨6, [.body]⟩ [field]
  let unit ← (fast.unitsAtOf field p).find? (fun id => (fast.cardDef? id).any (·.id == cid "RAD-086"))
  let held ← fire fast [.scored p field false]
  let newRune ← (held.zone (.player p .base)).find? (fun id => !(fast.zone (.player p .base)).contains id)
  return fast.tired unit == some false && fast.kwAmount unit .shield == 2 &&
    (ordinary.unitsAtOf field p).any (fun id => ordinary.tired id == some true) &&
    held.tired newRune == some false &&
    (held.zone (.player p .runeDeck)).length + 1 == (fast.zone (.player p .runeDeck)).length

-- Playing Companion from Hidden on the opponent's turn gives it Temporary for its next Beginning.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let field := s.bf0
  let (s, hidden) ← put s p "RAD-095" .hidden
  let (s, hand) ← put s p "RAD-095" .hand
  let (s, _) ← putAt s p "RAD-011" field
  let s := (s.control p field).modObj hidden
    (fun o => { o with hiddenAt := some field, hiddenTurn := some (s.turn - 1) })
  let ordinary ← play s p hand
  let fromHand ← ordinary.firstOf p .base "RAD-095"
  let opposing := { s with active := some q, pending := [.priority p] }
  let reacted ← activate opposing p hidden 2
  let fromHidden ← (reacted.unitsAtOf field p).find? (fun id => (reacted.cardDef? id).any (·.id == cid "RAD-095"))
  return !ordinary.hasKw fromHand .temporary && reacted.hasKw fromHidden .temporary &&
    (beginStep reacted q).1.inPlay.contains fromHidden &&
    (beginStep reacted p).1.countIn p .trash "RAD-095" == 1

-- Lulu changes base Might on move, so the target's existing buff still applies.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, lulu) ← put s p "RAD-110" .base
  let (s, _) ← putAt s p "RAD-011" field
  let (s, target) ← put s s.you "RAD-060" .base
  let s := (s.control p field).buff target
  let (waiting, _) ← (step 100 s ⟨.player p, .standardMove lulu (.battlefield field)⟩).toOption
  let done := settleChain { pick := (· == [target]) } 12 waiting
  let skipped := settleChain { pick := (· == [target]), yes := false } 12 waiting
  let (expired, _) ← (advance 100 { done with pending := [.expireTurn] } []).toOption
  return !waiting.trigPicks.contains lulu && waiting.trigPicks.contains target &&
    done.mightNow target == some 5 && skipped.mightNow target == some 9 && expired.mightNow target == some 9

-- Burn Away banishes either eligible target type, then burns from its controller's Main Deck.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, spell) ← put s p "RAD-124" .hand
  let (s, small) ← put s q "RAD-027" .base
  let (s, big) ← put s q "RAD-060" .base
  let (s, gear) ← put s q "SFD-117" .base
  let s := s.fund p 3 (order := 1)
  let pay := ⟨3, [.order]⟩
  let removed ← cast s p spell pay [small]
  let disarmed ← cast s p spell pay [gear]
  return (cast s p spell pay [big]).isNone && removed.countIn q .banishment "RAD-027" == 1 &&
    disarmed.countIn q .banishment "SFD-117" == 1 &&
    (removed.zone (.player p .mainDeck)).length + 2 == (s.zone (.player p .mainDeck)).length &&
    (removed.zone (.player p .trash)).length == (s.zone (.player p .trash)).length + 3

-- Cosmic Vista's extra point requires an empty Rune Deck and a Hold at this Battlefield.
#guard radianceCase fun s => do
  let p := s.me
  let (s, field) ← putBf s p "RAD-160"
  let (s, _) ← putAt s p "RAD-011" field
  let s := s.control p field
  let withRunes ← fire s [.scored p field false]
  let drained := (s.zone (.player p .runeDeck)).foldl
    (fun current id => (removeObj current id).getD current) s
  let held ← fire drained [.scored p field false]
  let conquered ← fire drained [.scored p field true]
  return withRunes.pointsOf p == s.pointsOf p && held.pointsOf p == s.pointsOf p + 1 &&
    conquered.pointsOf p == s.pointsOf p

-- The Monastery's optional conquer effect discards one card and channels an exhausted Rune.
#guard radianceCase fun s => do
  let p := s.me
  let (s, field) ← putBf s p "RAD-166"
  let (s, _) ← putAt s p "RAD-011" field
  let (s, _) ← put s p "RAD-011" .hand
  let s := s.control p field
  let done ← fire s [.scored p field true]
  let skipped ← fire s [.scored p field true] { yes := false }
  let held ← fire s [.scored p field false]
  let rune ← (done.zone (.player p .base)).find? (fun id => !(s.zone (.player p .base)).contains id)
  return done.handN p + 1 == s.handN p && done.tired rune == some true &&
    (done.zone (.player p .runeDeck)).length + 1 == (s.zone (.player p .runeDeck)).length &&
    skipped.handN p == s.handN p && held.handN p == s.handN p &&
    skipped.zone (.player p .base) == s.zone (.player p .base) &&
    held.zone (.player p .base) == s.zone (.player p .base)

-- Exhausting the Rostrum as a cost queues its boost above the draw and exhausted Rune.
#guard radianceCase fun s => do
  let p := s.me
  let (s, gear) ← put s p "RAD-046" .base
  let (s, ally) ← put s p "RAD-011" .base
  let (s, enemy) ← put s s.you "RAD-011" .base
  let (waiting, _) ← (step 100 s ⟨.player p, .activate gear 0 ⟨0, []⟩ []⟩).toOption
  let (stacked, _) ← (step 100 waiting ⟨.player p, .putTrigger 0 [ally]⟩).toOption
  let done := settleChain {} 12 stacked
  let fresh ← (done.zone (.player p .base)).find? (fun id => !(s.zone (.player p .base)).contains id)
  return waiting.trigPicks == [ally] && (waiting.zone .chain).length == 1 &&
    (stacked.zone .chain).length == 2 && done.tired gear == some true &&
    done.handN p == s.handN p + 1 && done.tired fresh == some true &&
    done.mightNow ally == some 7 && done.mightNow enemy == some 4

-- A Standard Move exhausts an already-present Oracle, while entering exhausted does not Predict.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, card) ← put s p "RAD-053" .hand
  let (s, _) ← putAt s p "RAD-011" field
  let entering ← play (s.control p field) p card
  let oracle ← entering.firstOf p .base "RAD-053"
  let ready := entering.modObj oracle (fun o => { o with exhausted := false })
  let (exhausted, _) ← (step 100 ready ⟨.player p, .standardMove oracle (.battlefield field)⟩).toOption
  let predicting := settleChain {} 8 exhausted
  let top ← (s.zone (.player p .mainDeck)).head?
  let (done, _) ← (step 100 predicting ⟨.player p, .predictPick top false⟩).toOption
  return entering.tired oracle == some true && (entering.zone .chain).isEmpty &&
    done.tired oracle == some true && done.where? oracle == some .battlefieldZone &&
    (setExhausted true done oracle).2.isEmpty

-- The Standard Move's exhaustion triggers are put on the Chain before its movement triggers.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, oracle) ← put (s.control p field) p "RAD-053" .base
  let (s, lulu) ← put s p "RAD-110" .base
  let send (t : GameState) (kind : ActionKind) := (step 100 t ⟨.player p, kind⟩).toOption
  let (group, _) ← send s (.startGroupMove (.battlefield field) Cost.zero)
  let (one, _) ← send group (.choose lulu)
  let (both, _) ← send one (.choose oracle)
  let (stacked, events) ← send both (.decide true)
  let first ← (stacked.zone .chain).head?
  let .triggerOrder who next [] [] _ :: .priority _ :: _ := stacked.pending | none
  let source := (stacked.obj? first).bind (fun obj => match obj.kind with
    | .chainAbility _ _ src => some src | _ => none)
  return who == p && (source.bind stacked.cardDef?).any (·.id == cid "RAD-053") &&
    (stacked.cardDef? next.source).any (·.id == cid "RAD-110") &&
    (events.filterMap (fun | .standardMoved id _ => (stacked.cardDef? id).map (·.id) | _ => none)) ==
      [cid "RAD-110", cid "RAD-053"]

-- Inspiring Seraphine needs three friendly Units exhausted by her controller in one instruction.
-- Declining at finalization saves the once-per-turn use.
#guard radianceCase fun s => do
  let p := s.me
  let q := s.you
  let (s, seraphine) ← put s p "RAD-065" .base
  let (s, a) ← put s p "RAD-011" .base
  let (s, b) ← put s p "RAD-011" .base
  let (s, c) ← put s p "RAD-011" .base
  let (s, enemy) ← put s q "RAD-011" .base
  let exhaust (g : GameState) (who : PlayerId) (ids : List ObjId) :=
    (advance 100 { g with pending := [.run who seraphine { slots := ids.map Value.obj }
      (.cons (.prim (.exhaust (.slotsFrom 0))) .nil), .priority p] } []).toOption.map Prod.fst
  let group := [a, b, c]
  let ready (g : GameState) := group.foldl
    (fun t id => t.modObj id (fun o => { o with exhausted := false })) g
  let mixed ← exhaust s p [a, b, enemy]
  let wrongPlayer ← exhaust s q group
  let waiting ← exhaust s p group
  let declined := settleChain { yes := false } 8 waiting
  let retried ← exhaust (ready declined) p group
  let drawn := settleChain {} 8 retried
  let again ← exhaust (ready drawn) p group
  return mixed.handN p == s.handN p && wrongPlayer.handN p == s.handN p &&
    (mixed.zone .chain).isEmpty && (wrongPlayer.zone .chain).isEmpty &&
    declined.handN p == s.handN p && drawn.handN p == s.handN p + 1 &&
    (settleChain {} 8 again).handN p == drawn.handN p

-- Accelerate leaves the Innovator ready; exhausting it locks either the Gold or the draw mode.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, card) ← put s p "RAD-105" .hand
  let (s, _) ← putAt s p "RAD-011" field
  let normal ← play (s.control p field) p card
  let (s, _) ← put s p "RAD-105" .hand
  let fast ← cast ((s.control p field).fund p 4 (chaos := 2)) p card ⟨4, [.chaos]⟩
  let unit ← fast.firstOf p .base "RAD-105"
  let (waiting, _) ← (step 100 fast ⟨.player p, .standardMove unit (.battlefield field)⟩).toOption
  let (goldChain, _) ← (step 100 waiting ⟨.player p, .putTrigger 0 [] (.pay [] (some 0))⟩).toOption
  let (drawChain, _) ← (step 100 waiting ⟨.player p, .putTrigger 0 [] (.pay [] (some 1))⟩).toOption
  let gold := settleChain {} 8 goldChain
  let drawn := settleChain {} 8 drawChain
  let token ← (gold.zone (.player p .base)).find? (fun id => (gold.cardDef? id).any (·.name == "Gold"))
  return normal.countNamed p .base "Gold" == 0 && fast.tired unit == some false &&
    gold.tired token == some true && gold.handN p == fast.handN p &&
    drawn.handN p == fast.handN p + 1 && drawn.countNamed p .base "Gold" == 0 &&
    (drawn.poolOf p).chaos == 0 && (gold.poolOf p).chaos == 1

-- Not Alone recruits on her play and on a later exhaustion and counts only other exhausted allies.
#guard radianceCase fun s => do
  let p := s.me
  let field := s.bf0
  let (s, card) ← put s p "RAD-SP5" .hand
  let (s, ally) ← putAt s p "RAD-011" field
  let (s, enemy) ← put s s.you "RAD-011" .base
  let played ← play (((s.control p field).tire ally).tire enemy) p card
  let champion ← played.firstOf p .base "RAD-SP5"
  let ready := played.modObj champion (fun o => { o with exhausted := false })
  let (moved, _) ← (step 100 ready ⟨.player p, .standardMove champion (.battlefield field)⟩).toOption
  let done := settleChain {} 8 moved
  return played.countNamed p .base "Recruit" == 1 && played.mightNow champion == some 3 &&
    done.countNamed p .base "Recruit" == 2 && done.mightNow champion == some 4

end RiftboundTest
