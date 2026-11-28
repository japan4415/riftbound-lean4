module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: activated abilities, the Chain, Reactions (CR 337, 340, 361, 363, 806, 813)

A player uses an activated ability: the costs are paid and the ability goes on the Chain as an
object of its own. The other players can answer with a Reaction (a Spell with Reaction, an ability
with the speed Reaction, a Rune ability). The Chain resolves from the top, one item at a time, and
an ability ceases to exist when it has resolved, even if the object it came from is gone.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def chainCfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

/-- The other player. -/
meta def otherQ (p : PlayerId) : PlayerId := if p == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- The effect of the test abilities: 1 damage to an enemy Unit on a Base. -/
meta def pingEffect : EffectDef :=
  EffectDef.of [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
    (.prim (.deal (.slot 0) (.const 1)))

/-- A Unit: "[Exhaust]: deal 1 to an enemy Unit." -/
meta def pinger : CardDef :=
  { id := cid "T-PING", name := "Pinger", types := [.unit], domains := [.fury], might := some 3,
    abilities := [.activated [.exhaustSelf] .normal pingEffect .unlimited] }

/-- A Unit with the same ability at the speed Reaction. -/
meta def reactor : CardDef :=
  { id := cid "T-REACT", name := "Reactor", types := [.unit], domains := [.fury], might := some 3,
    abilities := [.activated [.exhaustSelf] .reaction pingEffect .unlimited] }

/-- A Unit: "Pay 1: deal 1 to an enemy Unit. Once each turn." -/
meta def payer : CardDef :=
  { id := cid "T-PAY", name := "Payer", types := [.unit], domains := [.fury], might := some 3,
    abilities := [.activated [.pay ⟨1, []⟩] .normal pingEffect (.perTurn 1)] }

/-- A Unit whose ability has a cost the model cannot pay yet. -/
meta def costly : CardDef :=
  { id := cid "T-COST", name := "Costly", types := [.unit], domains := [.fury], might := some 3,
    abilities := [.activated [.discard 1] .normal pingEffect .unlimited] }

/-- A Spell with Reaction that deals 2 to an enemy Unit on a Base. -/
meta def counter : CardDef :=
  { id := cid "T-CNT", name := "Counterstrike", types := [.spell], domains := [.fury],
    cost := some ⟨1, []⟩, keywords := [{ keyword := .reaction }],
    spellEffect := some (EffectDef.of [Choice.targetOf .one .enemy .atBase [.ofType .unit]]
      (.prim (.deal (.slot 0) (.const 2)))) }

/-- The fixtures and the test cards. -/
meta def chainDB : CardDB := { cards := db.cards ++ [pinger, reactor, payer, costly, counter] }

/-- The game in the Main Phase of the first turn, with the test cards in its database. -/
meta def mainC (seed : Nat) : Option GameState :=
  match GameState.initial db chainCfg [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed seed) s with
      | .ok s => some { s with cards := chainDB }
      | .error _ => none

/-- Put a token of the card on a zone of the player. -/
meta def putTok (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s { kind := .token (cid card), owner := p, controller := p, timestamp := ⟨0⟩ }
    (.player p z)

/-- The turn player with a Pinger on their Base, and the other player with a Vanilla Unit and a
Reactor on theirs: the state, the players, the Pinger, the Vanilla Unit and the Reactor. -/
meta def scene : Option (GameState × PlayerId × PlayerId × ObjId × ObjId × ObjId) :=
  match mainC 1 with
  | none => none
  | some s =>
    let p := s.active.getD ⟨0⟩
    let q := otherQ p
    match putTok s p "T-PING" .base with
    | none => none
    | some (s1, a) =>
      match putTok s1 q "V0" .base with
      | none => none
      | some (s2, e) =>
        match putTok s2 q "T-REACT" .base with
        | none => none
        | some (s3, r) => some (s3, p, q, a, e, r)

#guard scene.isSome

/-- Take an answer, if it is legal. -/
meta def stepOk (s : GameState) (a : Action) : Option GameState :=
  match step 100 s a with | .ok (s', _) => some s' | .error _ => none

-- the ability can be used by the player who controls the Pinger, on an enemy Unit, with no cost to
-- pay but the exhaustion; not by the other player, not on its own Unit, not outside the Main Phase
#guard match scene with
  | some (s, p, q, a, e, _) =>
    activatable s p a 0 ⟨0, [], none⟩ [e] true &&
    (legalActions s).contains ⟨.player p, .activate a 0 ⟨0, [], none⟩ [e]⟩ &&
    !activatable s q a 0 ⟨0, [], none⟩ [e] true && !activatable s p a 0 ⟨0, [], none⟩ [a] true &&
    !activatable s p a 0 ⟨0, [], none⟩ [] true && !activatable s p a 1 ⟨0, [], none⟩ [e] true &&
    !activatable { s with phase := .draw } p a 0 ⟨0, [], none⟩ [e] true &&
    !activatable s p a 0 ⟨1, [], none⟩ [e] true
  | none => false

/-- The Pinger's ability used on the Vanilla Unit, and what it caused. -/
meta def afterUse : Option (GameState × List Event) :=
  match scene with
  | some (s, p, _, a, e, _) =>
    match step 100 s ⟨.player p, .activate a 0 ⟨0, [], none⟩ [e]⟩ with
    | .ok r => some r
    | .error _ => none
  | none => none

-- A resolution pick may stop the Chain, or resume its bound instruction immediately.
#guard (do
  let (_, p, q, source, target, other) ← scene
  let (queued, _) ← afterUse
  let item ← (queued.zone .chain).head?
  let selector := Selector.one .enemy .atBase [.ofType .unit]
  let program := EffectList.ofList [
    .prim (.ready (.slot 0)), .prim (.exhaust (.slot 0)), .prim (.buff (.slot 0)), .prim (.stun selector)]
  let work := Frame.run p source { slots := [.obj source] } program
  let stack := [work, Frame.finishSpell item, Frame.priority p]
  let started := { queued with pending := stack }
  let ((waiting, before), seen) ← (advanceWithDisclosures 20 started [] []).toOption
  let .pickDo owner _ _ first rest _ _ :: _ := waiting.pending | none
  let choose : Action := ⟨.player p, .choose target⟩
  let ((answered, after), laterSeen) ← (stepWithDisclosures 20 waiting choose).toOption
  let (one, _) ← moveObj started other (.player q .trash)
  let ((automatic, withoutChoice), autoSeen) ← (advanceWithDisclosures 20 one [] []).toOption
  return runFrameSupported work && chainAnswerWorkSupported waiting choose && owner == p &&
    (first :: rest).length == 2 && (first :: rest).contains target && (first :: rest).contains other &&
    before.contains (Event.readied source) && before.contains (Event.exhausted source) &&
    before.contains (Event.buffedBy source p) && !(waiting.obj? target).any (·.stunned) &&
    (answered.obj? target).any (·.stunned) && !(answered.obj? other).any (·.stunned) &&
    after.contains (Event.stunnedBy target p) && answered.pending == [Frame.priority p] &&
    (automatic.obj? target).any (·.stunned) && withoutChoice.contains (Event.stunnedBy target p) &&
    automatic.pending == [Frame.priority p] && seen.isEmpty && laterSeen.isEmpty && autoSeen.isEmpty
  : Option Bool).getD false

-- Owner-zone changes preserve the physical cards and record their order and actors.
#guard (do
  let start ← mainC 5
  let p ← start.active
  let q := otherQ p
  let base := Zone.player q .base
  let deck := Zone.player q .mainDeck
  let hand := Zone.player q .hand
  let banishment := Zone.player q .banishment
  let (s, toHand) ← addObject start (newCard start.cards start q (cid "V0")) base
  let (s, toBanish) ← addObject s (newCard s.cards s q (cid "V1")) base
  let (s, toDeck) ← addObject s (newCard s.cards s q (cid "V0")) base
  let program := EffectList.ofList [
    .prim (.returnToHand (.slot 0)), .prim (.banish (.slot 1)), .prim (.topdeck (.slot 2))]
  let frame := Frame.run p toHand { slots := [.obj toHand, .obj toBanish, .obj toDeck] } program
  let started := { s with pending := [frame, .priority p] }
  let ((finished, events), seen) ← (advanceWithDisclosures 12 started [] []).toOption
  let [Event.moved h h' hZone, Event.moved b b' bZone, Event.banished actor owner banished,
      Event.moved d d' dZone] := events | none
  let samePhysical (old new : ObjId) :=
    (s.obj? old).bind (·.kind.phys?) == (finished.obj? new).bind (·.kind.phys?)
  return runFrameSupported frame && finished.pending == [Frame.priority p] && seen.isEmpty &&
    h == toHand && hZone == hand && (finished.zone hand).contains h' && samePhysical h h' &&
    b == toBanish && bZone == banishment && (finished.zone banishment).contains b' &&
    actor == p && owner == q && banished == b' && samePhysical b b' &&
    d == toDeck && dZone == deck && (finished.zone deck).head? == some d' && samePhysical d d'
  : Option Bool).getD false

-- Status changes and hiding run through the observer without disclosing the hidden card.
#guard (do
  let (s, p, q, unit, _, _) ← scene
  let field ← s.battlefields.head?
  let card ← (s.zone (.player p .hand)).head?
  let original ← s.obj? card
  let hiddenZone := Zone.player p .hidden
  let env := ({ slots := [.obj unit, .obj field] } : Env).bindPick card false
  let program := EffectList.ofList [
    .prim (.empower (.slot 0)), .prim (.empower (.slot 0)), .prim (.disempower (.slot 0)),
    .prim (.buff (.slot 0)), .prim (.spendBuff (.slot 0)), .prim (.turnEffect .hiddenPlayed),
    .prim (.hideAt (.var pickVar) (.slot 1))]
  let frame := Frame.run p unit env program
  let started := { s with pending := [frame, .priority p] }
  let ((finished, events), seen) ← (advanceWithDisclosures 12 started [] []).toOption
  let hidden ← (finished.zone hiddenZone).head?
  return runFrameSupported frame && finished.pending == [Frame.priority p] && seen.isEmpty &&
    (finished.obj? unit).any (fun o => o.empowerCount == 0 && !o.buffed) &&
    finished.turnFx.any (fun note => note.who == p && note.kind == TurnEffect.hiddenPlayed) &&
    (finished.obj? hidden).any (fun o =>
      o.kind.phys? == original.kind.phys? && o.hiddenAt == some field && o.hiddenTurn == some s.turn) &&
    finished.zoneCardFaces q hiddenZone == some [none] &&
    finished.zoneCardFaces p hiddenZone == some [original.kind.cardId?] &&
    events == [Event.empowered p unit, Event.buffedBy unit p, Event.buffSpent p,
      Event.hiddenPlayed p, Event.moved card hidden hiddenZone]
  : Option Bool).getD false

-- A cost paid through a resolution choice runs its follow-up only if it changed the state.
#guard (do
  let (s, p, _, source, ready, tired) ← scene
  let s := s.modObj tired (fun o => { o with exhausted := true })
  let sel := Selector.one .enemy .atBase [.ofType .unit]
  let effect := Effect.doThen (.prim (.exhaust sel)) (.prim (.gainXP .you (.const 2)))
  let frame := Frame.run p source {} (.cons effect .nil)
  let started := { s with pending := [frame, .priority p] }
  let (waiting, earlier) ← (advance 10 started []).toOption
  let .pickDo _ _ _ _ _ _ _ :: _ := waiting.pending | none
  let pay : Action := ⟨.player p, .choose ready⟩
  let fail : Action := ⟨.player p, .choose tired⟩
  let ((paid, events), seen) ← (stepWithDisclosures 10 waiting pay).toOption
  let ((unpaid, skipped), otherSeen) ← (stepWithDisclosures 10 waiting fail).toOption
  return runFrameSupported frame && decisionRunAnswerWorkSupported waiting pay &&
    decisionRunAnswerWorkSupported waiting fail && earlier.isEmpty &&
    (paid.obj? ready).any (·.exhausted) && paid.xpOf p == s.xpOf p + 2 &&
    !(unpaid.obj? ready).any (·.exhausted) && unpaid.xpOf p == s.xpOf p &&
    paid.pending == [Frame.priority p] && unpaid.pending == [Frame.priority p] &&
    events == [Event.exhausted ready] && skipped.isEmpty && seen.isEmpty && otherSeen.isEmpty
  : Option Bool).getD false

-- With two available payments, the observer stops before spending either resource.
#guard (do
  let (s, p, _, source, _, _) ← scene
  let cost : Cost := ⟨0, [.domain .fury]⟩
  let effect := Effect.payThen cost (.prim (.gainXP .you (.const 2))) false
  let frame := Frame.run p source {} (.cons effect .nil)
  let started := { s with pending := [frame, .priority p] }
  let rich := started.setPool p { fury := 1, any := 1 }
  let (waiting, _) ← (advance 10 rich []).toOption
  let .eitherDo _ _ _ (.paySelected chosen _ _) _ _ :: _ := waiting.pending | none
  let expected ← spendResolutionPayment waiting p source chosen false
  let answer : Action := ⟨.player p, .decide true⟩
  let ((paid, events), seen) ← (stepWithDisclosures 10 waiting answer).toOption
  let (unique, _) ← (advance 10 (started.setPool p { fury := 1 }) []).toOption
  let (unable, _) ← (advance 10 (started.setPool p {}) []).toOption
  return runFrameSupported frame && decisionRunAnswerWorkSupported waiting answer &&
    waiting.poolOf p == rich.poolOf p && waiting.xpOf p == s.xpOf p &&
    paid.poolOf p == expected && paid.xpOf p == s.xpOf p + 2 && paid.pending == [Frame.priority p] &&
    unique.xpOf p == s.xpOf p + 2 && (unique.poolOf p).totalPower == 0 &&
    unable.xpOf p == s.xpOf p && unable.pending == [Frame.priority p] && events.isEmpty && seen.isEmpty
  : Option Bool).getD false

-- A Base-only play uses its generated plan. A directly scheduled plan binds the new identifier.
#guard (do
  let (s, p, _, source, _, _) ← scene
  let (s, card) ← addObject s (newCard s.cards s p (cid "V1")) (.player p .trash)
  let original ← s.obj? card
  let frame := Frame.run p source { slots := [.obj card] } (.cons (.prim (.playAtBase (.slot 0))) .nil)
  let terms : EffectPlayTerms := { price := .ignoreBase, requirements := [[none]] }
  let plan := Frame.run p source {} (.ofList [.planPermanentPlay card terms, .prim (.buff (.var pickVar))])
  let run (work : Frame) := advanceWithDisclosures 40 { s with pending := [work, .priority p] } [] []
  let ((atBase, baseEvents), baseSeen) ← (run frame).toOption
  let ((finished, events), seen) ← (run plan).toOption
  let newId (board : GameState) := (board.zone (.player p .base)).find? (fun id =>
    (board.obj? id).any (fun obj => obj.kind.phys? == original.kind.phys?))
  let played ← newId atBase
  let arrived ← newId finished
  return runFrameSupported frame && runFrameSupported plan && atBase.pending == [Frame.priority p] &&
    baseEvents.contains (Event.played p played) && baseSeen.isEmpty &&
    finished.pending == [Frame.priority p] && (finished.obj? arrived).any (·.buffed) &&
    events.contains (Event.played p arrived) && events.contains (Event.buffedBy arrived p) && seen.isEmpty
  : Option Bool).getD false

-- The actual Champion Zone ability uses a checked permanent Play when its Chain item resolves.
#guard (do
  let start ← mainC 11
  let p ← start.active
  let q := otherQ p
  let champion ← (start.zone (.player p .championZone)).head?
  let original ← start.obj? champion
  let funded := start.setPool p { energy := 10, fury := 3, calm := 3, any := 3 }
  let ability ← (legalActions funded).find? (fun a =>
    match a.kind with | .activate source .. => source == champion | _ => false)
  let (queued, _) ← (step 40 funded ability).toOption
  let item ← (queued.zone .chain).head?
  let (passed, _) ← (step 40 queued ⟨.player p, .pass⟩).toOption
  let last : Action := ⟨.player q, .pass⟩
  let (scheduled, earlier) ← applyDeclaredAction passed last
  let (running, resolving) ← workStep scheduled
  let ((finished, events), seen) ← (advanceWithDisclosures 40 running (earlier ++ resolving) []).toOption
  let ((normal, fromPass), passSeen) ← (stepWithDisclosures 40 passed last).toOption
  let arrived ← (finished.zone (.player p .base)).find? (fun id =>
    (finished.obj? id).any (fun obj => obj.kind.phys? == original.kind.phys?))
  let (spellState, spell) ← addObject start (newCard start.cards start p (cid "SP0")) (.player p .hand)
  let inlineSpell := { spellState with pending := [.run p spell {} (.cons (.prim (.play .self)) .nil), .priority p] }
  return permanentPlayRunSupported running && !permanentPlayRunSupported inlineSpell &&
    running.pending.tail == [Frame.finishSpell item, Frame.priority p] &&
    finished.zone (.player p .championZone) == [] && finished.zone .chain == [] &&
    finished.pending == [Frame.priority p] && normal.pending == finished.pending &&
    normal.zone (.player p .base) == finished.zone (.player p .base) &&
    events == fromPass && events.contains (Event.played p arrived) && seen.isEmpty && passSeen.isEmpty
  : Option Bool).getD false

-- A real Chain ability plays a choice-free Spell, bins it, and resumes the caller.
#guard (do
  let start ← mainC 13
  let p ← start.active
  let q := otherQ p
  let play := EffectDef.of [Choice.targetOf .one .friendly .inTrash [.ofType .spell]]
    (.prim (.play (.slot 0)))
  let launcher : CardDef := { pinger with id := cid "T-INLINE", abilities :=
    [.activated [.exhaustSelf] .normal play .unlimited] }
  let cards := { start.cards with cards := launcher :: start.cards.cards }
  let (s, source) ← putTok { start with cards := cards } p "T-INLINE" .base
  let (s, spell) ← addObject s (newCard cards s p (cid "SP0")) (.player p .trash)
  let original ← s.obj? spell
  let queued ← stepOk s ⟨.player p, .activate source 0 ⟨0, [], none⟩ [spell]⟩
  let passed ← stepOk queued ⟨.player p, .pass⟩
  let finalPass : Action := ⟨.player q, .pass⟩
  let (staged, firstEvents) ← applyDeclaredAction passed finalPass
  let (running, atRun) ← workStep staged
  let ((finished, events), seen) ← (advanceWithDisclosures 40 running (firstEvents ++ atRun) []).toOption
  let ((normal, normalEvents), normalSeen) ← (stepWithDisclosures 40 passed finalPass).toOption
  let discarded ← (finished.zone (.player p .trash)).find? (fun id =>
    (finished.obj? id).any (fun obj => obj.kind.phys? == original.kind.phys?))
  let activeSpell ← events.findSome? (fun
    | .moved from_ to .chain => if from_ == spell then some to else none
    | _ => none)
  let cast ← events.idxOf? (.played p activeSpell)
  let draw ← events.idxOf? (.drew p)
  let finish ← events.idxOf? (.spellResolved p discarded)
  let .run player src env (.cons play rest) :: tail := running.pending | none
  let continued := EffectList.cons play (rest.append (.cons (.prim (.gainXP .you (.const 2))) .nil))
  let extended := { running with pending := Frame.run player src env continued :: tail }
  let (resumed, extraEvents) ← (advance 40 extended (firstEvents ++ atRun)).toOption
  return effectPlayRunSupported running && inlineSpellPlayRunSupported extended &&
    finished.pending == [Frame.priority p] && finished.zone .chain == [] &&
    (finished.zone (.player p .hand)).length == (s.zone (.player p .hand)).length + 1 &&
    cast < draw && draw < finish &&
    resumed.xpOf p == finished.xpOf p + 2 && extraEvents == events &&
    normal.zone (.player p .hand) == finished.zone (.player p .hand) &&
    normal.zone (.player p .trash) == finished.zone (.player p .trash) &&
    normalEvents == events && seen.isEmpty && normalSeen.isEmpty
  : Option Bool).getD false

-- A separate Spell cost waits for the parent Chain item, then waits for its own input.
#guard (do
  let start ← mainC 14
  let p ← start.active
  let q := otherQ p
  let play := EffectDef.of [Choice.targetOf .one .friendly .inTrash [.ofType .spell]]
    (.prim (.play (.slot 0)))
  let launcher : CardDef := { pinger with id := cid "T-QUEUE", abilities :=
    [.activated [.exhaustSelf] .normal play .unlimited] }
  let costed := { drawSpell with id := cid "T-REQUIRES-EXHAUST", playExtra := some (.exhaustUnit, true) }
  let cards := { start.cards with cards := launcher :: costed :: start.cards.cards }
  let (s, source) ← putTok { start with cards := cards } p "T-QUEUE" .base
  let (s, first) ← putTok s p "V0" .base
  let (s, second) ← putTok s p "V1" .base
  let (s, spell) ← addObject s (newCard cards s p costed.id) (.player p .trash)
  let original ← s.obj? spell
  let queued ← stepOk s ⟨.player p, .activate source 0 ⟨0, [], none⟩ [spell]⟩
  let parent ← (queued.zone .chain).head?
  let passed ← stepOk queued ⟨.player p, .pass⟩
  let finalPass : Action := ⟨.player q, .pass⟩
  let (staged, _) ← applyDeclaredAction passed finalPass
  let (running, _) ← workStep staged
  let ((waiting, queuedEvents), queuedSeen) ← (stepWithDisclosures 40 passed finalPass).toOption
  let .eitherDo chooser _ _ (.finishLimitedSpell item selected []) (.finishLimitedSpell _ alternative []) _ :: _ :=
    waiting.pending | none
  let elected ← selected.pick.extraObject
  let unused ← alternative.pick.extraObject
  let ((cast, paidEvents), paidSeen) ← (stepWithDisclosures 40 waiting ⟨.player p, .decide true⟩).toOption
  let passedSpell ← stepOk cast ⟨.player p, .pass⟩
  let ((finished, resolvedEvents), _) ← (stepWithDisclosures 40 passedSpell ⟨.player q, .pass⟩).toOption
  let discarded ← (finished.zone (.player p .trash)).find? (fun id =>
    (finished.obj? id).any (fun obj => obj.kind.phys? == original.kind.phys?))
  return effectPlayRunSupported running && !inlineSpellPlayRunSupported running &&
    (waiting.obj? parent).isNone && (waiting.pendingSpell item).isSome && chooser == p &&
    [first, second].contains elected && [first, second].contains unused && elected != unused &&
    !(waiting.obj? elected).any (·.exhausted) && !(queuedEvents.contains (Event.played p item)) &&
    (cast.obj? elected).any (·.exhausted) && !(cast.obj? unused).any (·.exhausted) &&
    paidEvents.contains (Event.played p item) && queuedSeen.isEmpty && paidSeen.isEmpty &&
    finished.zone .chain == [] && (finished.zone (.player p .hand)).length == (s.zone (.player p .hand)).length + 1 &&
    resolvedEvents.contains (Event.spellResolved p discarded)
  : Option Bool).getD false

-- the Pinger is exhausted and the use is noted; the ability is on the Chain as an object of its own
-- with the targets chosen; the player has priority with the ability on the Chain (CR 337, 361)
#guard match scene, afterUse with
  | some (_, p, _, a, e, _), some (s1, es) =>
    es.contains (.activated p a 0 (some 0)) &&
    (s1.obj? a).any (fun o => o.exhausted && o.used == [0]) &&
    (s1.zone .chain).length == 1 &&
    (match (s1.zone .chain).head?.bind s1.obj? with
      | some o => o.kind == .chainAbility (cid "T-PING") 0 a && o.controller == p &&
          o.targets == [e]
      | none => false) &&
    (match s1.pending with
      | .chainPass r 0 :: .priority r2 :: _ => r == p && r2 == p
      | _ => false)
  | _, _ => false

-- the Pinger is exhausted, so the ability cannot be used again, and the ability on the Chain has no
-- physical card: the physical cards are as they were (I1)
#guard match scene, afterUse with
  | some (s, p, _, a, e, _), some (s1, _) =>
    !activatable s1 p a 0 ⟨0, [], none⟩ [e] false && s1.physIds.length == s.physIds.length &&
    s1.zoneIds.length == s.zoneIds.length + 1
  | _, _ => false

/-- Both players pass, and the ability resolves. -/
meta def afterResolve : Option GameState :=
  match scene, afterUse with
  | some (_, p, q, _, _, _), some (s1, _) =>
    (stepOk s1 ⟨.player p, .pass⟩).bind (fun s2 => stepOk s2 ⟨.player q, .pass⟩)
  | _, _ => none

-- the ability dealt 1 damage to its target and ceased to exist; the Chain is empty and the player
-- has priority again with nothing between (CR 340)
#guard match scene, afterUse, afterResolve with
  | some (s, p, _, _, e, _), some (s1, _), some s3 =>
    (s3.obj? e).any (·.damage == 1) && (s3.zone .chain).isEmpty &&
    s3.zoneIds.length == s.zoneIds.length &&
    ((s1.zone .chain).head?.bind s3.obj?).isNone &&
    (match s3.pending with | .priority r :: _ => r == p | _ => false)
  | _, _, _ => false

-- while the Chain holds the ability, the players can answer with a Rune ability, not with a
-- Standard Move; and the other player can answer with the Reactor, an ability of the speed
-- Reaction (CR 813, 430)
#guard match scene, afterUse with
  | some (_, p, q, a, _, r), some (s1, _) =>
    (legalFrameActions s1).any (fun x => match x.kind with | .runeAbility .. => true | _ => false)
      && !(legalFrameActions s1).any
        (fun x => match x.kind with | .standardMove .. => true | _ => false) &&
    (match stepOk s1 ⟨.player p, .pass⟩ with
      | some s2 => (legalFrameActions s2).contains ⟨.player q, .activate r 0 ⟨0, [], none⟩ [a]⟩
      | none => false)
  | _, _ => false

/-- The other player answers with the Reactor, and both pass: the Reactor's ability resolves first
(it is on top), then the Pinger's. The states after the first and the second resolution. -/
meta def afterReact : Option (GameState × GameState × GameState) :=
  match scene, afterUse with
  | some (_, p, q, a, _, r), some (s1, _) =>
    (stepOk s1 ⟨.player p, .pass⟩).bind fun s2 =>
    (stepOk s2 ⟨.player q, .activate r 0 ⟨0, [], none⟩ [a]⟩).bind fun s3 =>
    (stepOk s3 ⟨.player q, .pass⟩).bind fun s4 =>
    (stepOk s4 ⟨.player p, .pass⟩).bind fun s5 =>
    (stepOk s5 ⟨.player p, .pass⟩).bind fun s6 =>
    (stepOk s6 ⟨.player q, .pass⟩).map fun s7 => (s3, s5, s7)
  | _, _ => none

-- When the turn player's Reaction resolves, priority goes to the opponent whose item is next.
#guard ((do
  let (s, p, q, attacker, target, rival) ← scene
  let (s, reply) ← putTok s p "T-REACT" .base
  let first ← stepOk s ⟨.player p, .activate attacker 0 ⟨0, [], none⟩ [target]⟩
  let response ← stepOk first ⟨.player p, .pass⟩
  let middle ← stepOk response ⟨.player q, .activate rival 0 ⟨0, [], none⟩ [attacker]⟩
  let answer ← stepOk middle ⟨.player q, .pass⟩
  let newest ← stepOk answer ⟨.player p, .activate reply 0 ⟨0, [], none⟩ [target]⟩
  let passing ← stepOk newest ⟨.player p, .pass⟩
  let resumed ← stepOk passing ⟨.player q, .pass⟩
  let item ← (resumed.zone .chain).head?.bind resumed.obj?
  return item.controller == q && resumed.pending.head? == some (.chainPass q 0)) : Option Bool).getD false

-- two items are on the Chain, the Reactor's on top; when it has resolved, the Pinger's is still
-- there and the turn player has priority again; when both have resolved the Chain is empty (CR 340)
#guard match scene, afterReact with
  | some (_, p, _, a, e, r), some (s3, s5, s7) =>
    (s3.zone .chain).length == 2 &&
    (match (s3.zone .chain).head?.bind s3.obj? with
      | some o => o.kind == .chainAbility (cid "T-REACT") 0 r | none => false) &&
    (s5.zone .chain).length == 1 && (s5.obj? a).any (·.damage == 1) &&
    (s5.obj? e).any (·.damage == 0) &&
    (match s5.pending with
      | .chainPass x 0 :: .priority y :: _ => x == p && y == p
      | _ => false) &&
    (s7.zone .chain).isEmpty && (s7.obj? e).any (·.damage == 1) &&
    (match s7.pending with | .priority x :: _ => x == p | _ => false)
  | _, _ => false

-- the object an ability came from can be gone when the ability resolves; it resolves all the same
-- (CR 340: last known information)
#guard match scene, afterUse with
  | some (_, p, q, a, e, _), some (s1, _) =>
    match moveObj s1 a (.player p .trash) with
    | some (s2, _) =>
      match (stepOk s2 ⟨.player p, .pass⟩).bind
          (fun s3 => stepOk s3 ⟨.player q, .pass⟩) with
      | some s4 => (s4.obj? e).any (·.damage == 1) && (s4.zone .chain).isEmpty
      | none => false
    | none => false
  | _, _ => false

/-- A Reaction Spell in the hand of the other player, with the Energy to cast it. The state is
the one after the Pinger's ability, with the Pinger's player having passed. -/
meta def sceneSpell : Option (GameState × PlayerId × PlayerId × ObjId × ObjId × ObjId) :=
  match scene, afterUse with
  | some (_, p, q, a, _, _), some (s1, _) =>
    match putTok s1 q "T-CNT" .hand with
    | some (s2, c) =>
      match putTok s2 q "SP0" .hand with
      | some (s3, d) =>
        (stepOk (s3.setPool q { energy := 2 }) ⟨.player p, .pass⟩).map
          fun s4 => (s4, p, q, a, c, d)
      | none => none
    | none => none
  | _, _ => none

-- a Spell with Reaction can be cast in answer; a Spell without it cannot (CR 813)
#guard match sceneSpell with
  | some (s, _, q, a, c, d) =>
    (legalFrameActions s).contains ⟨.player q, .playCard c ⟨1, []⟩ [a]⟩ &&
    !(legalFrameActions s).any (fun x => match x.kind with
      | .playCard c' _ _ _ _ _ => c' == d | _ => false) &&
    reactable s q c ⟨1, []⟩ [a] && !reactable s q d ⟨1, []⟩ []
  | none => false

/-- The Reaction is cast, and the Chain resolves. The state after the cast and the state at the
end. -/
meta def afterSpell : Option (GameState × GameState) :=
  match sceneSpell with
  | some (s, p, q, a, c, _) =>
    (stepOk s ⟨.player q, .playCard c ⟨1, []⟩ [a]⟩).bind fun s1 =>
    (stepOk s1 ⟨.player q, .pass⟩).bind fun s2 =>
    (stepOk s2 ⟨.player p, .pass⟩).bind fun s3 =>
    (stepOk s3 ⟨.player p, .pass⟩).bind fun s4 =>
    (stepOk s4 ⟨.player q, .pass⟩).map fun s5 => (s1, s5)
  | none => none

-- the Spell is on top of the Chain over the ability, and the pool paid for it; at the end both have
-- resolved: the Pinger took 2 and the Vanilla Unit took 1 (CR 340, 357)
#guard match sceneSpell, afterSpell with
  | some (s, _, q, a, _, _), some (s1, s5) =>
    (s1.zone .chain).length == 2 && (s1.poolOf q).energy == 1 &&
    (s.zone (.player q .hand)).length == (s1.zone (.player q .hand)).length + 1 &&
    (s5.zone .chain).isEmpty && (s5.obj? a).any (·.damage == 2) &&
    -- the Spell is a token in the test: off the Board, it ceases to exist (CR 183)
    (s5.zone (.player q .trash)).length == (s.zone (.player q .trash)).length
  | _, _ => false

-- an ability with a cost in Energy and a limit of once each turn: the payment has to be the cost,
-- the Pool has to cover it, and the second use in the turn is not possible
#guard match mainC 1 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putTok s0 p "T-PAY" .base with
    | some (s1, a) =>
      match putTok s1 (otherQ p) "V0" .base with
      | some (s2, e) =>
        let s3 := s2.setPool p { energy := 2 }
        activatable s3 p a 0 ⟨1, [], none⟩ [e] true && !activatable s3 p a 0 ⟨1, [], none⟩ [e] false &&
        !activatable s3 p a 0 ⟨0, [], none⟩ [e] true &&
        !activatable s3 p a 0 ⟨2, [], none⟩ [e] true &&
        !activatable (s2.setPool p {}) p a 0 ⟨1, [], none⟩ [e] true &&
        (match stepOk s3 ⟨.player p, .activate a 0 ⟨1, [], none⟩ [e]⟩ with
          | some s4 =>
            (s4.poolOf p).energy == 1 && !(s4.obj? a).any (·.exhausted) &&
            (s4.obj? a).any (·.used == [0]) &&
            -- the second use needs the first to have resolved, and is not allowed this turn
            (match (stepOk s4 ⟨.player p, .pass⟩).bind
                (fun s5 => stepOk s5 ⟨.player (otherQ p), .pass⟩) with
              | some s6 => !activatable s6 p a 0 ⟨1, [], none⟩ [e] true &&
                  (s6.obj? a).any (fun o => (clearScored o).used == [])
              | none => false)
          | none => false)
      | none => false
    | none => false
  | none => false

-- Discard is a supported cost, and activation requires the selected hand cards (CR 423.3).
#guard match mainC 1 with
  | some s0 =>
    let p := s0.active.getD ⟨0⟩
    match putTok s0 p "T-COST" .base with
    | some (s1, a) =>
      match putTok s1 (otherQ p) "V0" .base with
      | some (s2, e) =>
        costPlan [.discard 1] == some (false, none) &&
      costPlan [.discard 1, .discard 2] == none && !activatable s2 p a 0 ⟨0, [], none⟩ [e] true &&
        costPlan [.exhaustSelf, .pay ⟨1, []⟩] == some (true, some ⟨1, []⟩) &&
        costPlan [.exhaustSelf, .exhaustSelf] == none
      | none => false
    | none => false
  | none => false

-- every answer listed is accepted by the engine, in the states with a Chain too
#guard match scene, afterUse, afterReact with
  | some (s, _, _, _, _, _), some (s1, _), some (s3, _, _) =>
    [s, s1, s3].all (fun x => (legalActions x).all (fun a => (stepOk x a).isSome))
  | _, _, _ => false

end RiftboundTest
