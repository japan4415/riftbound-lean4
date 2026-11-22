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

/-- Give the player Energy and Power of the domains in the Pool. -/
meta def GameState.fund (s : GameState) (p : PlayerId) (e : Nat)
    (fury calm body mind chaos order : Nat := 0) : GameState :=
  let a : RunePool := { energy := e, fury := fury, calm := calm }
  s.setPool p { a with body := body, mind := mind, chaos := chaos, order := order }

/-- Give the player plenty of Energy and of the Power of every domain. -/
meta def GameState.rich (s : GameState) (p : PlayerId) : GameState :=
  s.fund p 12 12 12 12 12 12 12

/-- Let the Chain resolve: the players pass while the Chain is being answered, and a player who
puts a triggered ability on it takes the first choice of targets that `pick` accepts (or the first
one). -/
meta def settleChain (pick : List ObjId → Bool := fun _ => true) : Nat → GameState → GameState
  | 0, s => s
  | n + 1, s =>
    match s.pending with
    | .chainPass q _ :: _ =>
      match step 100 s ⟨.player q, .pass⟩ with
      | .ok (s', _) => settleChain pick n s'
      | .error _ => s
    | .triggerOrder .. :: _ =>
      let puts := (legalFrameActions s).filter (fun a => match a.kind with
        | .putTrigger _ _ => true | _ => false)
      let good := puts.filter (fun a =>
        match a.kind with | .putTrigger _ ts => pick ts | _ => false)
      match (good.head? <|> puts.head?) with
      | some a =>
        match step 100 s a with
        | .ok (s', _) => settleChain pick n s'
        | .error _ => s
      | none => s
    | _ => s

/-- A payment of exactly the cost of the card. -/
meta def payOf (s : GameState) (c : ObjId) : RunePool.Payment :=
  match (s.cardDef? c).bind (·.cost) with
  | some k =>
    ⟨k.energy, k.power.filterMap (fun x => match x with | .domain d => some d | _ => none)⟩
  | none => ⟨0, []⟩

/-- Play the card with the payment and the chosen targets, and let the Chain resolve. -/
meta def cast (s : GameState) (p : PlayerId) (c : ObjId) (pay : RunePool.Payment)
    (ts : List ObjId := []) (pick : List ObjId → Bool := fun _ => true) : Option GameState :=
  match step 100 s ⟨.player p, .playCard c pay ts⟩ with
  | .ok (s1, _) => some (settleChain pick 12 s1)
  | .error _ => none

/-- Play the card for exactly its cost (the player has plenty), and let the Chain resolve. -/
meta def play (s : GameState) (p : PlayerId) (c : ObjId) (ts : List ObjId := [])
    (pick : List ObjId → Bool := fun _ => true) : Option GameState :=
  cast (s.rich p) p c (payOf s c) ts pick

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

/-- Whether the object is exhausted. -/
meta def GameState.tired (s : GameState) (u : ObjId) : Option Bool := (s.obj? u).map (·.exhausted)

/-- Use an ability of the object (the player has plenty to pay), and let the Chain resolve. -/
meta def activate (s : GameState) (p : PlayerId) (src : ObjId) (idx : Nat) (ts : List ObjId := []) :
    Option GameState :=
  match step 100 (s.rich p) ⟨.player p, .activate src idx ⟨0, []⟩ ts⟩ with
  | .ok (s1, _) => some (settleChain (fun _ => true) 12 s1)
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
