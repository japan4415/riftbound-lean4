module

public import RiftboundCards
meta import RiftboundCards
public import RiftboundDriver.Run
meta import RiftboundDriver.Run
public import RiftboundTest.Fixtures
meta import RiftboundTest.Fixtures

/-!
# The card lab

A small kit for a scenario test of one card: the game in the Main Phase of the first turn, with
every card of the sets known; put a card into a zone; give the player Energy and Power; play a
card and let the Chain resolve; read what happened. A test of a card is a few lines.
-/

public section

namespace Riftbound

open RiftboundTest RiftboundDriver

/-- The game in the Main Phase of the first turn, with the cards of all the sets known. -/
meta def lab : Option GameState :=
  match GameState.initial db { ruleSet := .coreOnly, mode := Mode.duel } [goodDeck, goodDeck] with
  | none => none
  | some s => match runUntilTurn 100 1 2000 (Rng.ofSeed 1) s with
      | .ok s => some { s with cards := { cards := db.cards ++ RiftboundCards.db.cards } }
      | .error _ => none

/-- The player whose turn it is. -/
meta def GameState.me (s : GameState) : PlayerId := s.active.getD ⟨0⟩

/-- The other player. -/
meta def GameState.you (s : GameState) : PlayerId := if s.me == ⟨0⟩ then ⟨1⟩ else ⟨0⟩

/-- The first Battlefield of the game. -/
meta def GameState.bf0 (s : GameState) : ObjId := (s.battlefields.head?).getD ⟨0⟩

/-- Put a new card of the player into one of their zones. -/
meta def put (s : GameState) (p : PlayerId) (card : String) (z : ZoneKind) :
    Option (GameState × ObjId) :=
  addObject s (newCard s.cards s p (cid card)) (.player p z)

/-- Put a Unit of the player at a Battlefield. -/
meta def putAt (s : GameState) (p : PlayerId) (card : String) (bf : ObjId) :
    Option (GameState × ObjId) :=
  match addObject s (newCard s.cards s p (cid card)) .battlefieldZone with
  | some (s1, u) => some (s1.modObj u (fun o => { o with loc := some bf }), u)
  | none => none

/-- Put a new Battlefield card of the player on the Battlefield Zone. -/
meta def putBf (s : GameState) (p : PlayerId) (card : String) : Option (GameState × ObjId) :=
  addObject s (newCard s.cards s p (cid card)) .battlefieldZone

/-- Give the player Energy and Power of the domains in the Pool. -/
meta def GameState.fund (s : GameState) (p : PlayerId) (e : Nat)
    (fury calm body mind chaos order : Nat := 0) : GameState :=
  let a : RunePool := { energy := e, fury := fury, calm := calm }
  s.setPool p { a with body := body, mind := mind, chaos := chaos, order := order }

/-- Give the player plenty of Energy and of the Power of every domain. -/
meta def GameState.rich (s : GameState) (p : PlayerId) : GameState :=
  s.fund p 12 12 12 12 12 12 12

/-- What the players answer to the questions of the effects while the Chain resolves: the targets
of a triggered ability (the first choice `pick` accepts), "you may" (`yes`), and the object chosen
(the first `obj` accepts). -/
structure Says where
  /-- The targets of a triggered ability. -/
  pick : List ObjId → Bool := fun _ => true
  /-- The answer to "you may". -/
  yes : Bool := true
  /-- The object chosen while an effect resolves. -/
  obj : ObjId → Bool := fun _ => true

/-- Let the Chain resolve: the players pass while the Chain is being answered, and answer the
questions as `says` tells. -/
meta def settleChain (says : Says := {}) : Nat → GameState → GameState
  | 0, s => s
  | n + 1, s =>
    let go (a : Action) : GameState :=
      match step 100 s a with
      | .ok (s', _) => settleChain says n s'
      | .error _ => s
    match s.pending with
    | .chainPass q _ :: _ => go ⟨.player q, .pass⟩
    | .mayDo q .. :: _ => go ⟨.player q, .decide says.yes⟩
    | .pickDo .. :: _ =>
      let opts := (legalFrameActions s).filter (fun a => match a.kind with
        | .choose o => says.obj o | _ => false)
      match (opts.head? <|> (legalFrameActions s).head?) with
      | some a => go a
      | none => s
    | .discard .. :: _ =>
      match (legalFrameActions s).head? with
      | some a => go a
      | none => s
    | .triggerOrder .. :: _ =>
      let puts := (legalFrameActions s).filter (fun a => match a.kind with
        | .putTrigger _ _ => true | _ => false)
      let good := puts.filter (fun a =>
        match a.kind with | .putTrigger _ ts => says.pick ts | _ => false)
      match (good.head? <|> puts.head?) with
      | some a => go a
      | none => s
    | _ => s

/-- A payment of exactly the cost of the card (a Power of any domain is paid with Fury). -/
meta def payOf (s : GameState) (c : ObjId) : RunePool.Payment :=
  match (s.cardDef? c).bind (·.cost) with
  | some k =>
    ⟨k.energy, k.power.map (fun x => match x with | .domain d => d | _ => .fury)⟩
  | none => ⟨0, []⟩

/-- Play the card with the payment and the chosen targets, and let the Chain resolve. -/
meta def cast (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (ts : List ObjId := []) (says : Says := {}) : Option GameState :=
  match step 100 s ⟨.player p, .playCard c pay ts⟩ with
  | .ok (s1, _) => some (settleChain says 12 s1)
  | .error _ => none

/-- Play the card for exactly its cost (the player has plenty), and let the Chain resolve. -/
meta def play (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId := [])
    (says : Says := {}) : Option GameState :=
  cast (s.rich p) p c (payOf s c) ts says

/-- Let the events happen: the abilities they set off go on the Chain, and the Chain resolves. -/
meta def fire (s : GameState) (es : List Event) (says : Says := {}) : Option GameState :=
  let s0 := { s with pending := insertTriggers (s.detect es) s.pending }
  match advance 100 s0 [] with
  | .ok (s1, _) => some (settleChain says 12 s1)
  | .error _ => none

/-- Make the object exhausted. -/
meta def GameState.tire (s : GameState) (u : ObjId) : GameState :=
  s.modObj u (fun o => { o with exhausted := true })

/-- Play the card and stop at the first question: for example the choice of the targets of an
ability that the card set off. -/
meta def castStop (s : GameState) (p : PlayerId) (c : ObjId) : Option GameState :=
  match step 100 (s.rich p) ⟨.player p, .playCard c (payOf s c) []⟩ with
  | .ok (s1, _) => some s1
  | .error _ => none

/-- The objects a player can pick as the targets of a triggered ability, now. -/
meta def GameState.trigPicks (s : GameState) : List ObjId :=
  (legalFrameActions s).flatMap (fun a => match a.kind with | .putTrigger _ ts => ts | _ => [])

/-- The first object of the card in the zone of the player. -/
meta def GameState.firstOf (s : GameState) (p : PlayerId) (z : ZoneKind) (card : String) :
    Option ObjId :=
  (s.zone (.player p z)).find? (fun u => (s.cardDef? u).any (·.id == cid card))

/-- How many objects in the zone of the player have a card with the name (for the tokens). -/
meta def GameState.countNamed (s : GameState) (p : PlayerId) (z : ZoneKind) (name : String) : Nat :=
  ((s.zone (.player p z)).filter (fun u => (s.cardDef? u).any (·.name == name))).length

/-- Whether the object is exhausted. -/
meta def GameState.tired (s : GameState) (u : ObjId) : Option Bool := (s.obj? u).map (·.exhausted)

/-- Use an ability of the object (the player has plenty to pay), and let the Chain resolve. -/
meta def activate (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (ts : List ObjId := [])
    (pay : RunePool.Payment := ⟨0, []⟩) : Option GameState :=
  match step 100 (s.rich p) ⟨.player p, .activate src idx pay ts⟩ with
  | .ok (s1, _) => some (settleChain {} 12 s1)
  | .error _ => none

/-- Make the object buffed. -/
meta def GameState.buff (s : GameState) (u : ObjId) : GameState :=
  s.modObj u (fun o => { o with buffed := true })

/-- The zone an object is on. -/
meta def GameState.where? (s : GameState) (u : ObjId) : Option Zone := s.locate u

/-- How many objects of the card (by its identifier) are in the zone of the player. A card that
changes zone is a new object, so tests look for the card, not the old object. -/
meta def GameState.countIn (s : GameState) (p : PlayerId) (z : ZoneKind) (card : String) : Nat :=
  ((s.zone (.player p z)).filter (fun u => (s.cardDef? u).any (·.id == cid card))).length

/-- How many cards are in the hand of the player. -/
meta def GameState.handN (s : GameState) (p : PlayerId) : Nat := (s.zone (.player p .hand)).length

end Riftbound

end
