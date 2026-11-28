module

import RiftboundDriver.Run
meta import RiftboundDriver.Run
import RiftboundDriver.Replay
meta import RiftboundDriver.Replay
import Riftbound.Invariant.BurnOutWork
meta import Riftbound.Invariant.BurnOutWork
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: the setup of a game and the engine (CR 110-118, design.md §6)

Two players with the fixture deck. The setup is run through `step`, with the driver answering
the chance decisions from a seed.
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def cfg : GameConfig := { ruleSet := .coreOnly, mode := Mode.duel }

meta def start : Option GameState := GameState.initial db cfg [goodDeck, goodDeck]

-- In-play random orders can use a zone or only the objects named by the frame.
#guard (do
  let p : PlayerId := ⟨0⟩
  let a := cid "V0"
  let b := cid "V1"
  let pool := GameState.empty cfg db
  let trash := Zone.player p .trash
  let aside := Zone.player p .setAside
  let add (s : GameState) (code : CardId) (z : Zone) := addObject s (newCard db s p code) z .bottom
  let (s, first) ← add pool a trash
  let (s, second) ← add s a trash
  let (s, other) ← add s b trash
  let (s, held) ← add s a aside
  let (s, taken) ← add s b aside
  let check (frame : Frame) (cards : List CardId) (ids : List ObjId) (exact : Bool) :=
    let state := { s with pending := [frame] }
    match (ReplayAnswer.observedChance (.cardOrder cards)).resolveAt state 1 with
    | .ok (action, unique) =>
      action == ⟨.chance, .arrange ids⟩ && unique == exact && decide (Legal state action)
    | .error _ => false
  return check (.chanceBurnOut p) [b, a, a] [other, first, second] false &&
    check (.chanceRecycle p) [b, a] [taken, held] true &&
    check (.chancePredict p 3 [first] [second, other]) [b, a] [other, second] true &&
    check (.chanceRecycleTrash p first [second, other]) [b, a] [other, second] true
  : Option Bool).getD false

-- A card code answers only the recorded seat's current choice. Copies remain ambiguous.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let a := cid "V0"
  let b := cid "V1"
  let pool := GameState.empty cfg db
  let hand := Zone.player p .hand
  let deck := Zone.player p .mainDeck
  let add (s : GameState) (code : CardId) (z : Zone) := addObject s (newCard db s p code) z .bottom
  let (s, first) ← add pool a hand
  let (s, _) ← add s a hand
  let (s, other) ← add s b hand
  let (s, peek) ← add s b deck
  let (s, sameCode) ← add s a deck
  let state (frame : Frame) := { s with pending := [frame] }
  let byCode (seat : PlayerId) (kind : ReplayCardPickKind) (card : CardId) : ReplayCardPick :=
    { seat, kind, card }
  let check (frame : Frame) (kind : ReplayCardPickKind) (card : CardId)
      (expected : ActionKind) (exact : Bool) :=
    match (ReplayAnswer.observedCardPick (byCode p kind card)).resolveAt (state frame) 1 with
    | .ok (action, unique) =>
      action == ⟨.player p, expected⟩ && unique == exact && decide (Legal (state frame) action)
    | .error _ => false
  let mulligan := state (.mulligan p 0)
  let choice := byCode p .mulligan b
  let predict : Frame := .predict p 1 peek [] [] []
  let offered := state (.pickDo p first {} first [sameCode] .nop .nil)
  let located := { byCode p .chooseObject a with location? := some (.zone deck) }
  let wrong := { located with location? := some (.zone (.player q .mainDeck)) }
  let selectAt (pick : ReplayCardPick) := (ReplayAnswer.observedCardPick pick).resolveAt offered 2
  return check (.mulligan p 0) .mulligan a (.mulliganPick first) false &&
    check (.discard p 1) .discard b (.discardPick other) true &&
    check predict .predictTop b (.predictPick peek false) true &&
    check predict .predictRecycle b (.predictPick peek true) true &&
    (selectAt located).toOption == some (⟨.player p, .choose sameCode⟩, true) &&
    (selectAt (byCode p .chooseObject a)).toOption == some (⟨.player p, .choose first⟩, false) &&
    !(selectAt wrong).isOk &&
    ((ReplayAnswer.observedCardPick (byCode q .mulligan b)).resolveAt mulligan 2).isOk == false &&
    ((ReplayAnswer.observedCardPick choice).resolveAt (state (.mulligan p 2)) 2).isOk == false &&
    ((ReplayAnswer.observedCardPick (byCode p .predictTop a)).resolveAt (state predict) 2).isOk == false &&
    ((ReplayAnswer.inferredCardPick choice " ").resolveAt mulligan 2).isOk == false &&
    match (ReplayAnswer.inferredCardPick choice "later shown").resolveAt mulligan 2 with
    | .ok (action, exact) => action.kind == .mulliganPick other && !exact
    | .error _ => false
  : Option Bool).getD false

-- These public observations retain Chain order and Hidden location without requiring object IDs.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let battle := cid "B0"
  let spell := cid "SP0"
  let source := cid "V0"
  let hidden := cid "V1"
  let empty := GameState.empty cfg db
  let add (s : GameState) (seat : PlayerId) (card : CardId) (z : Zone) :=
    addObject s (newCard db s seat card) z
  let (s, field) ← add empty q battle .battlefieldZone
  let (s, facedown) ← add s p hidden (.player p .hidden)
  let (s, _) ← add s q spell .chain
  let (s, _) ← addObject s (abilityItem source 0 ⟨900⟩ p []) .chain
  let state := s.modObj facedown (fun o => { o with hiddenAt := some field })
  let chain := { state with pending := [.chainPass q 1] }
  let showdown := { state with pending := [.showdown field p 0] }
  let neutral := { state with pending := [.priority p] }
  let ordered : List ReplayChainItem := [.ability p source, .spell q spell]
  let check (state : GameState) (facts : List ReplayObservationFact) :=
    (ReplayObservation.checkAt [{ checkpoint := 7, source? := some "broadcast", facts }] 7 state).isOk
  return check state [.chainOrder ordered, .hiddenAt p q battle 1, .hiddenAt q q battle 0] &&
    !(check state [.chainOrder ordered.reverse]) && !(check state [.hiddenAt p q battle 0]) &&
    check chain [.priority (.chain q), .priority (.chain q (some 1))] &&
    !(check chain [.priority (.chain p)]) && !(check chain [.priority (.chain q (some 2))]) &&
    check showdown [.priority (.showdown p q battle (some 0))] &&
    !(check showdown [.priority (.showdown p p battle)]) &&
    !(check showdown [.priority (.chain p)]) && check neutral [.priority (.neutral p)] &&
    !(check state [.priority (.neutral p)]) && !(check state [.hiddenAt p p battle 1]) &&
    !(check (state.modObj facedown (fun o => { o with hiddenAt := none })) [.hiddenAt p q battle 1])
  : Option Bool).getD false

meta def count (p : PlayerId) (k : ZoneKind) (s : GameState) : Nat := (s.zone (.player p k)).length

-- Repeated copies in a Combat assignment remain ambiguous until only one is legally next.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let s := GameState.empty cfg db
  let (s, field) ← addObject s (newCard db s p (cid "B0")) .battlefieldZone
  let add (s : GameState) := addObject s
    { newCard db s q (cid "V0") with loc := some field } .battlefieldZone .bottom
  let (s, first) ← add s
  let (s, second) ← add s
  let decision (picked : List ObjId) := { s with pending := [.assign field p p picked []] }
  let answer := ReplayAnswer.observedCardPick { seat := p, kind := .assignDamage, card := cid "V0" }
  let (a, exactA) ← (answer.resolveAt (decision []) 1).toOption
  let (b, exactB) ← (answer.resolveAt (decision [first]) 2).toOption
  return a == ⟨.player p, .assignPick first⟩ && !exactA &&
    b == ⟨.player p, .assignPick second⟩ && exactB &&
    ((answer.resolveAt (decision [first, second]) 3).toOption).isNone
  : Option Bool).getD false

meta def finished (seed : Nat) : Option GameState :=
  match start with
  | none => none
  | some s => match runAuto 100 200 (Rng.ofSeed seed) s with
      | .ok s => some s
      | .error _ => none

meta def p0 : PlayerId := ⟨0⟩
meta def p1 : PlayerId := ⟨1⟩

-- the starting layout (CR 111-113): 56 objects per player
#guard match start with
  | some s => count p0 .legendZone s == 1 && count p0 .championZone s == 1 &&
      count p0 .mainDeck s == 39 && count p0 .runeDeck s == 12 && count p0 .outOfGame s == 3 &&
      count p1 .mainDeck s == 39 && s.nextId == 112 && s.pending.length == 7
  | none => false
-- the number of decks must be the number of players
#guard (GameState.initial db cfg [goodDeck]).isNone
-- a deck that is not legal (CR 101-103) is refused: no Rune Deck
#guard (GameState.initial db cfg [goodDeck, { goodDeck with runes := [] }]).isNone
-- so is a game that cannot be played: one player
#guard (GameState.initial db { cfg with mode := { Mode.duel with players := 1 } }
  [goodDeck]).isNone

-- after the setup, for several seeds: every question is answered, and
#guard (List.range 8).all fun seed => match finished seed with
  | some s =>
    -- the setup is over and the first turn has begun: the first player has priority in the Main
    -- Phase, having drawn one card for the turn (CR 118, 315.4)
    (match s.pending, s.active with
      | [.priority q], some tp => q == tp && tp == s.turnOrder.headD p0
      | _, _ => false) &&
    s.turn == 1 && s.phase == .main &&
    -- opening hands of 4 (CR 116); the first player drew one more
    (let first := s.turnOrder.headD p0
     let second := if first == p0 then p1 else p0
     count first .hand s == 5 && count second .hand s == 4 &&
     count first .mainDeck s == 34 && count second .mainDeck s == 35 &&
     -- the first player channeled two Runes (CR 315.3)
     count first .runeDeck s == 10 && count first .base s == 2 &&
     count second .runeDeck s == 12) &&
    -- one Battlefield each in play (CR 113, 487.5), the other two out of the game
    (s.zone .battlefieldZone).length == 2 && count p0 .outOfGame s == 2 &&
    count p1 .outOfGame s == 2 &&
    -- the turn order is a permutation of the players
    s.turnOrder.length == 2 && s.turnOrder.contains p0 && s.turnOrder.contains p1
  | none => false

private meta def ffaOpening (mode : Mode) : Option GameState := do
  let decks := List.replicate mode.players goodDeck
  let s ← if mode == Mode.ffa4 then
      GameState.initialFfa4 db [⟨2⟩, p0, ⟨3⟩, p1] decks
    else GameState.initial db { cfg with mode } decks
  let ready ← (runAuto 100 100 (Rng.ofSeed 7) s).toOption
  let first ← ready.turnOrder.head?
  let last ← ready.turnOrder.getLast?
  let final ← (runUntilTurn 100 mode.players 100 (Rng.ofSeed 7) ready).toOption
  let battlefieldCount := (ready.zone .battlefieldZone).length
  let candidateCount := count first .outOfGame ready
  if ready.turn == 1 && ready.active == some first && count first .hand ready == 4 &&
      count first .runeDeck ready == 10 && battlefieldCount == 3 &&
      candidateCount == (if mode == Mode.ffa4 then 3 else 2) &&
      final.turn == mode.players && final.active == some last && count last .hand final == 5 &&
      count last .runeDeck final == 9 &&
      (final.turnOrder.drop 1).all (fun seat => count seat .outOfGame final == 2) then
    some final
  else none

-- CR 489.5, 489.7, 490.5, 490.7: three Battlefields and the multiplayer first-turn rules.
#guard (ffaOpening .ffa3).isSome
#guard (ffaOpening .ffa4).any (fun s => s.turnOrder == [⟨2⟩, p0, ⟨3⟩, p1])
#guard (GameState.initialFfa4 db [p0, p1, p0, ⟨3⟩] (List.replicate 4 goodDeck)).isNone

-- the same seed gives the same game (replay, design.md §6.4)
#guard finished 5 == finished 5
-- different seeds can give different orders of the deck
#guard (finished 1).map (fun s => s.zone (.player p0 .mainDeck)) !=
  (finished 2).map (fun s => s.zone (.player p0 .mainDeck))

-- the physical cards are conserved from the start to the end (I1): the same multiset of cards
#guard match start, finished 3 with
  | some s0, some s1 =>
    ((s0.zoneIds.filterMap (fun id => (s0.obj? id).bind (·.kind.phys?))).map (·.n)).mergeSort ==
      ((s1.zoneIds.filterMap (fun id => (s1.obj? id).bind (·.kind.phys?))).map (·.n)).mergeSort &&
    s1.zoneIds.length == s0.zoneIds.length
  | _, _ => false

-- the legal answers at the first mulligan
meta def atMulligan : Option GameState :=
  match start with
  | none => none
  | some s =>
    -- run the chance decisions, stop when a player must decide
    let rec go (n : Nat) (r : Rng) (s : GameState) : Option GameState :=
      match n with
      | 0 => none
      | n + 1 =>
        match s.pending with
        | .mulligan _ _ :: _ => some s
        | _ => match autoAnswer r s with
          | some (a, r') => match step 100 s a with
            | .ok (s', _) => go n r' s'
            | .error _ => none
          | none => none
    go 100 (Rng.ofSeed 7) s

#guard match atMulligan with
  | some s =>
    -- four hand cards may be set aside, or the player may finish
    (legalActions s).length == 7 &&
    (legalActions s).all (fun a => a.actor.isPlayer) &&
    -- each listed answer is legal, and a chance answer is not
    (legalActions s).all (fun a => decide (Legal s a)) &&
    !decide (Legal s ⟨.chance, .mulliganDone⟩)
  | none => false

-- a mulligan of two cards: each is set aside at once, finishing draws two, and the two set
-- aside go to the bottom in the order chance gives (CR 117, 417.5)
#guard match atMulligan with
  | some s =>
    match s.pending with
    | .mulligan p _ :: _ =>
      let hand := s.zone (.player p .hand)
      match hand with
      | c1 :: c2 :: c3 :: _ =>
        match step 100 s ⟨.player p, .mulliganPick c1⟩ with
        | .ok (s1, _) => match step 100 s1 ⟨.player p, .mulliganPick c2⟩ with
          | .ok (s2, _) =>
            count p .setAside s2 == 2 && count p .hand s2 == 2 &&
            -- a third pick is refused, finishing is allowed
            (match step 100 s2 ⟨.player p, .mulliganPick c3⟩ with
              | .error .illegal => true | _ => false) &&
            (match step 100 s2 ⟨.player p, .mulliganDone⟩ with
              | .ok (s3, _) =>
                -- two cards were drawn; the next question is the order of the two set aside
                (match s3.pending with
                  | .chanceRecycle q :: _ => q == p
                  | _ => false) &&
                count p .hand s3 == 4 && count p .setAside s3 == 2 &&
                count p .mainDeck s3 == count p .mainDeck s - 2 &&
                -- answering puts them at the bottom, and the set-aside zone is empty
                (let order := (s3.zone (.player p .setAside)).reverse
                 match step 100 s3 ⟨.chance, .arrange order⟩ with
                 | .ok (s4, _) =>
                   count p .setAside s4 == 0 && count p .mainDeck s4 == count p .mainDeck s &&
                   -- the two last cards of the Main Deck are the two recycled ones
                   ((s4.zone (.player p .mainDeck)).drop (count p .mainDeck s4 - 2)).length == 2
                 | .error _ => false)
              | .error _ => false)
          | .error _ => false
        | .error _ => false
      | _ => false
    | _ => false
  | none => false

-- Burn Out (CR 432): a draw from an empty Main Deck recycles the Trash in a random order, an
-- opponent gains a point, and the draw goes on. Here the whole deck is put in the Trash first.
meta def burnOutScenario (resumeMain : Bool := false) : Option (GameState × GameState) :=
  match finished 4 with
  | none => none
  | some s =>
    let deck := s.zone (.player p0 .mainDeck)
    let s' : GameState :=
      { s with zones := (s.zones.insert (Zone.player p0 .mainDeck).key []).insert
                 (Zone.player p0 .trash).key deck,
               pending := .draw p0 1 :: (if resumeMain then [.phase .main, .priority p0] else []) }
    match advance 10 s' [] with
    | .error _ => none
    | .ok (s1, _) =>
      match s1.pending with
      | .chanceBurnOut q :: _ =>
        let order : Action := ⟨.chance, .arrange (s1.zone (.player p0 .trash)).reverse⟩
        match step 100 s1 order with
        | .error _ => none
        | .ok (s2, _) =>
          match s2.pending with
          | .chooseBurnOut q' :: _ =>
            let target : Action := ⟨.player p0, .burnOutTarget p1⟩
            if q == p0 && q' == p0 && burnOutAnswerWorkSupported s1 order && burnOutAnswerWorkSupported s2 target then
              match step 100 s2 target with
              | .ok (s3, _) => some (s', s3)
              | .error _ => none
            else none
          | _ => none
      | _ => none

#guard match burnOutScenario with
  | some (s', s3) =>
    -- the Trash went to the Main Deck, one card was drawn, p1 has the point, p0 has none
    count p0 .trash s3 == 0 && count p0 .mainDeck s3 == count p0 .trash s' - 1 &&
    count p0 .hand s3 == count p0 .hand s' + 1 && s3.pointsOf p1 == 1 && s3.pointsOf p0 == 0 &&
    s3.pending.isEmpty
  | none => false

#guard match burnOutScenario true with
  | some (_, final) => final.pending == [.priority p0] && final.phase == .main && final.pointsOf p1 == 1
  | none => false

-- The replacement draw for a Conquer can burn out before Combat Finish.
#guard (do
  let s ← finished 4
  let field ← s.battlefields.head?
  let (s, unit) ← addObject s { newCard s.cards s p0 (cid "V0") with loc := some field } .battlefieldZone
  let main := Zone.player p0 .mainDeck
  let trash := Zone.player p0 .trash
  let deck := s.zone main
  let s := s.gainPoints p0 (s.victoryScore - 1)
  let scoring := { s with
    zones := (s.zones.insert main.key []).insert trash.key deck
    combat := some { battlefield := field, attacker := p0, defender := p1, units := [unit] }
    pending := [.combatControl field, .combatFinish field, .priority p0] }
  let (shuffling, scored) ← (advance 100 scoring []).toOption
  let shuffle : Action := ⟨.chance, .arrange (shuffling.zone trash).reverse⟩
  let (choosing, burned) ← (step 100 shuffling shuffle).toOption
  let target : Action := ⟨.player p0, .burnOutTarget p1⟩
  let (final, finished) ← (step 100 choosing target).toOption
  return burnOutAnswerWorkSupported shuffling shuffle && burnOutAnswerWorkSupported choosing target &&
    scored.contains (.scored p0 field true) && burned.contains (.burnedOut p0) &&
    finished.contains (.pointsGained p1 1) && finished.contains (.combatEnded field [unit]) &&
    final.combat.isNone && final.pending == [.priority p0] && count p0 .hand final == count p0 .hand s + 1
  : Option Bool).getD false

-- illegal answers are refused
#guard match start with
  | some s => (match step 100 s ⟨.player p0, .mulliganDone⟩ with
      | .error .illegal => true | _ => false) &&
    -- an arrangement that is not a permutation of the zone
    (match step 100 s ⟨.chance, .arrange []⟩ with
      | .error .illegal => true | _ => false)
  | none => false

-- fuel (design.md §6.1): too little fuel stops the work between the turn order and the Main Phase
#guard match start with
  | some s => (match runAuto 0 200 (Rng.ofSeed 1) s with
      | .error .fuelExhausted => true | _ => false) &&
    (match runAuto 1 200 (Rng.ofSeed 1) s with
      | .error .fuelExhausted => true | _ => false) &&
    -- Starting the first turn takes 14 work steps after the last mulligan, including the
    -- Beginning Step and Scoring Step.
    (match runAuto 13 200 (Rng.ofSeed 1) s with
      | .error .fuelExhausted => true | _ => false) &&
    (match runAuto 14 200 (Rng.ofSeed 1) s with
      | .ok s' => s'.phase == .main && s'.pending == [.priority (s'.active.getD p0)]
      | _ => false)
  | none => false

end RiftboundTest
