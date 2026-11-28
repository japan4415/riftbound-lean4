module

import RiftboundCards
meta import RiftboundCards
import RiftboundDriver.Match
import RiftboundDriver.Run
meta import RiftboundDriver.Match
meta import RiftboundDriver.Run
import RiftboundDriver.Replay
meta import RiftboundDriver.Replay
import Riftbound.Tournament.LoopDetect
meta import Riftbound.Tournament.LoopDetect
import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# Tests: the judge's draw (TR 410.1, 505.6) and the match concession (TR 410.2)
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

meta def atTurnJ (rules : RuleSet) (n : Nat) : Option GameState :=
  match GameState.initial db { ruleSet := rules, mode := Mode.duel } [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 n 4000 (Rng.ofSeed 1) s with
      | .ok s => some s
      | .error _ => none

meta def callTimeJ : Action := ⟨.clock, .timeCalled⟩

meta def declare : Action := ⟨.judge, .declareDraw⟩

-- the judge declares a draw under the Tournament Rules: the game is over, with nothing left, even
-- when a player is ahead
#guard match atTurnJ (.tournament .constructed) 2 with
  | some s =>
    match step 100 (s.gainPoints ⟨0⟩ 3) declare with
    | .ok (s1, _) =>
      s1.result == some .draw && s1.pending.isEmpty && s1.turn == s.turn &&
      (step 100 s1 declare).toOption.isNone && (step 100 s1 callTimeJ).toOption.isNone &&
      (legalActions s1).isEmpty
    | .error _ => false
  | none => false

-- neither a player nor the clock declares a draw, and the Core Rules have no judge
#guard match atTurnJ (.tournament .constructed) 2 with
  | some s =>
    (step 100 s ⟨.player ⟨0⟩, .declareDraw⟩).toOption.isNone &&
    (step 100 s ⟨.clock, .declareDraw⟩).toOption.isNone
  | none => false
#guard match atTurnJ .coreOnly 2 with
  | some s => (step 100 s declare).toOption.isNone
  | none => false

-- The judge closes the replay even when removing Showdown would cross a Might threshold.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let crossing : CardDef := { vanilla 0 with
    id := cid "T-DRAW-THRESHOLD"
    might := some 5
    abilities := [.passive .inCombat [.mightMinus .self (.const 1)],
      .triggered { event := .becomeMighty, optional := true }
        (.of [] (.prim (.gainXP .you (.const 1)))) .unlimited] }
  let cards := { db with cards := crossing :: db.cards }
  let empty := GameState.empty { ruleSet := .tournament .constructed, mode := .duel } cards
  let (s, field) ← addObject empty (newCard cards empty p (cid "B0")) .battlefieldZone
  let (s, unit) ← addObject s { newCard cards s p crossing.id with loc := some field } .battlefieldZone
  let (s, _) ← addObject s { newCard cards s q (cid "V1") with loc := some field } .battlefieldZone
  let waiting := { s with
    active := some p, turnOrder := [p, q], turn := 1, phase := .main
    pending := [.showdown field p 0, .priority p] }
  let input : GameInputs := { decks := .core [], answers := #[] }
  let (action, completed, emitted) ←
    (input.advance [ReplayPosition.fromState waiting] (.observed declare) 1 0 true).toOption
  return waiting.mightNow unit == some 4 && completed.state.mightNow unit == some 5 &&
    action == some declare && completed.answerExact && completed.state.result == some .draw &&
    completed.state.pending.isEmpty && emitted.isEmpty && completed.disclosures.isEmpty
  : Option Bool).getD false

-- a draw can be declared in any open question, here before the first turn begins
#guard match GameState.initial db { ruleSet := .tournament .constructed, mode := Mode.duel }
    [goodDeck, goodDeck] with
  | some s => (step 100 s declare).toOption.any (fun r => r.1.result == some .draw)
  | none => false

-- a conceded match goes to the other player; an agreed draw of the match is a draw (TR 410.2)
#guard MatchState.concedeMatch ⟨0⟩ == .won ⟨1⟩
#guard MatchState.concedeMatch ⟨1⟩ == .won ⟨0⟩
#guard MatchState.agreedDrawMatch == .draw

-- A mandatory discard answer can advance the state, but only a return to the same state is a
-- loop. A choice or a chance decision cannot be one of the forced answers.
#guard
  let p : PlayerId := ⟨0⟩
  let base := GameState.empty { ruleSet := .tournament .constructed, mode := Mode.duel } db
  let waiting := { base with pending := [Frame.discard p 1] }
  let answer : Action := ⟨.player p, .discardDone⟩
  let optional := { base with pending := [Frame.mayDo p ⟨0⟩ {} .nop .nil] }
  let chance := { base with pending := [Frame.chanceRecycle p] }
  forcedAnswer waiting == some answer &&
    (runForcedAnswers 100 waiting [answer]).any (fun next => next.pending.isEmpty) &&
    (detectExactForcedLoop 100 waiting [(waiting, answer)]).isNone &&
    (forcedLoopRuling 100 waiting [(waiting, answer)]).isNone &&
    (forcedLoopRuling 100 { waiting with config := { waiting.config with ruleSet := .coreOnly } }
      [(waiting, answer)]).isNone &&
    (forcedAnswer optional).isNone && (forcedAnswer chance).isNone

-- A public Rune Deck reveal requires a remedy if the Rune was not Channeled. A one-card
-- deck can be named as the judge's explicit exception when no random portion exists.
meta def runeRewind (second channelRune : Bool) : Option Bool := do
  let seats : List PlayerId := [⟨0⟩, ⟨1⟩]
  let p : PlayerId := ⟨0⟩
  let base := GameState.empty { ruleSet := .tournament .constructed, mode := .duel }
    RiftboundCards.db
  let deck := Zone.player p .runeDeck
  let (s, rune) ← addObject base (newCard base.cards base p ⟨"OGN-007"⟩) deck
  let (s, other) ← if second then addObject s (newCard s.cards s p ⟨"OGN-126"⟩) deck .bottom
    else some (s, rune)
  let reveal : Effect := .prim (.reveal (Selector.one .friendly .inRuneDeck [.top 1]))
  let effect := if channelRune then
      .seqOf [reveal, .prim (.channel .you (.const 1) (.const 0))]
    else reveal
  let target := { s with
    active := some p, turnOrder := seats, phase := .main, turn := 1,
    pending := [.mayDo p rune {} effect .nil, .priority p] }
  let inputs : GameInputs := { decks := .core [], answers := #[] }
  let history := [ReplayPosition.fromState target]
  let (_, after, events) ← (inputs.advance history (.observed ⟨.player p, .decide true⟩)
    1 100).toOption
  let played := after :: history
  let simple := inputs.advance played (.judgeRewind 0) 2 100
  let remedy : JudgePrivateRewind := {
    target := 0, returns := [],
    shuffles? := if second then some [⟨p, .runeDeck, [0, 1], [other, rune]⟩] else none,
    unshuffledDecks? := if second then none else some [⟨p, .runeDeck⟩] }
  let (_, restored, _) ← (if channelRune then simple else
    inputs.advance played (.judgePrivateRewind remedy) 2 100).toOption
  return events.contains (.revealed p rune) && simple.isOk == channelRune &&
    restored.state.zone deck == (if channelRune then target.zone deck
      else if second then [other, rune] else [rune])

#guard (runeRewind true false).getD false
#guard (runeRewind false false).getD false
#guard (runeRewind true true).getD false

-- Burn Out returns a burned card to the deck under a new object ID. In a rewind to
-- before the Burn, the draw still belongs to that physical card's original deck slot.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let empty := GameState.empty { ruleSet := .tournament .constructed, mode := .duel }
    RiftboundCards.db
  let deck := Zone.player p .mainDeck
  let hand := Zone.player p .hand
  let trash := Zone.player p .trash
  let add (s : GameState) (zone : Zone) (code : CardId) :=
    addObject s (newCard s.cards s p code) zone
  let (s, original) ← add empty deck ⟨"OGN-136"⟩
  let (s, handCopy) ← add s hand ⟨"OGN-136"⟩
  let (s, discard) ← add s trash ⟨"OGN-001"⟩
  let effect := Effect.seqOf [.prim (.burn .you (.const 1)), .prim (.draw .you (.const 1))]
  let target := { s with
    active := some p, turnOrder := [p, q], phase := .main, turn := 1,
    pending := [.mayDo p original {} effect .nil, .priority p] }
  let atTarget : ReplayPosition := .fromState target
  let inputs : GameInputs := { decks := .core [], answers := #[] }
  let apply (history : List ReplayPosition) (action : Action) :=
    (inputs.advance history (.observed action) history.length 100).toOption
  let (_, burned, _) ← apply [atTarget] ⟨.player p, .decide true⟩
  let candidates := burned.state.zone trash
  let top ← candidates.find? (· != discard)
  let order : Action := ⟨.chance, .arrange [top, discard]⟩
  let recordedOrder : ReplayAnswer := .observedChance (.cardOrderByPosition
    [⟨candidates.idxOf top, ⟨"OGN-136"⟩⟩, ⟨candidates.idxOf discard, ⟨"OGN-001"⟩⟩])
  let (recorded, recycled, _) ← (inputs.advance [burned, atTarget] recordedOrder 2 100).toOption
  let recycledTop ← (recycled.state.zone deck).head?
  let recipient : Action := ⟨.player p, .burnOutTarget q⟩
  let (_, drawn, events) ← apply [recycled, burned, atTarget] recipient
  let drawnId ← events.findSome? (fun
    | .moved old next dst => if old == recycledTop && dst == hand then some next else none
    | _ => none)
  let rewind : ReplayAnswer := .judgePrivateRewind {
    target := 0, returns := [⟨drawnId, [original, handCopy], handCopy⟩] }
  let (_, restored, _) ← (inputs.advance [drawn, recycled, burned, atTarget] rewind 4 100).toOption
  let physical (state : GameState) (id : ObjId) := (state.obj? id).bind (·.kind.phys?)
  return recorded == some order && recycled.answerExact &&
    burnOutAnswerWorkSupported burned.state order && burnOutAnswerWorkSupported recycled.state recipient &&
    recycledTop != original && physical drawn.state drawnId == physical target original &&
    (restored.state.zone deck).map (physical restored.state) == [physical target handCopy] &&
    (restored.state.zone hand).map (physical restored.state) == [physical target original] &&
    restored.state.zone trash == [discard] && restored.state.pointsOf q == target.pointsOf q
  : Option Bool).getD false

-- A hidden card is drawn, Recycled directly from the hand, then drawn again. Undoing the
-- later draw returns another card, which follows the first card's path back through Recycle.
#guard (do
  let p : PlayerId := ⟨0⟩
  let q : PlayerId := ⟨1⟩
  let empty := GameState.empty { ruleSet := .tournament .constructed, mode := .duel }
    RiftboundCards.db
  let deck := Zone.player p .mainDeck
  let hand := Zone.player p .hand
  let add (s : GameState) (zone : Zone) (code : CardId) :=
    addObject s (newCard s.cards s p code) zone .bottom
  let (s, original) ← add empty deck ⟨"OGN-136"⟩
  let (s, later) ← add s deck ⟨"OGN-001"⟩
  let (s, inHand) ← add s hand ⟨"OGN-136"⟩
  let effect := Effect.seqOf [.prim (.draw .you (.const 1)),
    .prim (.recycle (Selector.one .you .inHand [])), .prim (.draw .you (.const 2))]
  let target := { s with
    active := some p, turnOrder := [p, q], phase := .main, turn := 1,
    pending := [.mayDo p original {} effect .nil, .priority p] }
  let atTarget : ReplayPosition := .fromState target
  let input : GameInputs := { decks := .core [], answers := #[] }
  let drawing (events : List Event) (old : ObjId) :=
    events.findSome? (fun
      | .moved source id zone => if source == old && zone == hand then some id else none
      | _ => none)
  let (_, first, firstEvents) ← (input.advance [atTarget] (.observed ⟨.player p, .decide true⟩)
    1 100).toOption
  let firstId ← drawing firstEvents original
  let (_, second, secondEvents) ← (input.advance [first, atTarget]
    (.observed ⟨.player p, .choose firstId⟩) 2 100).toOption
  let recycled ← secondEvents.findSome? (fun
    | .moved old id zone => if old == firstId && zone == deck then some id else none
    | _ => none)
  let secondId ← drawing secondEvents recycled
  let history := [second, first, atTarget]
  let cancel (choices : List JudgeDrawReturn) :=
    input.advance history (.judgePrivateRewind { target := 0, returns := choices }) 3 100
  let lastChoice : JudgeDrawReturn := ⟨secondId, [original, inHand, later], inHand⟩
  let earlier : JudgeDrawReturn := ⟨firstId, [original, inHand], original⟩
  let (_, undone, _) ← (cancel [earlier, lastChoice]).toOption
  let (_, changed, _) ← (cancel [lastChoice]).toOption
  let physical (state : GameState) (zone : Zone) :=
    (state.zone zone).filterMap (fun id => (state.obj? id).bind (·.kind.phys?))
  let invalidEarlier := { earlier with candidates := [original, later] }
  return secondId != firstId && (second.state.zone hand).length == 3 &&
    undone.state.zone deck == target.zone deck && undone.state.zone hand == target.zone hand &&
    physical changed.state deck == physical target hand ++ (physical target deck).drop 1 &&
    physical changed.state hand == (physical target deck).take 1 &&
    !(cancel [lastChoice, invalidEarlier]).isOk
  : Option Bool).getD false

end RiftboundTest
