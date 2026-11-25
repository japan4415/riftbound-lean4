module

public import Riftbound.State.Zone
public import Riftbound.State.Phase
public import Riftbound.State.Pool
public import Riftbound.Card.IR.Value
public import Riftbound.Card.IR.Effect

/-!
# Decisions

The stack of frames the engine works through, and the actions that answer its questions
(design.md §6.2). A frame is either a **decision** (the engine waits for an `Action`) or
**work** (`microStep` advances it by itself). A decision frame holds the question only, never a
list of candidates: the candidates are computed from the board by `Legal` and `legalActions`.
-/

@[expose] public section

namespace Riftbound

/-- Who acts: a player, chance (shuffles and random picks, design.md §6.4), the clock
(TR 408) or the judge (TR 505.6). The last two are used from milestone M5b. -/
inductive Actor where
  /-- A player. -/
  | player (p : PlayerId)
  /-- A chance decision, answered from outside. -/
  | chance
  /-- The clock. -/
  | clock
  /-- The judge. -/
  | judge
deriving DecidableEq, Repr

/-- Whether the actor is a player. -/
def Actor.isPlayer : Actor → Bool
  | .player _ => true
  | _ => false

/-- The two abilities every Basic Rune has (CR 164.2). -/
inductive RuneAbility where
  /-- Exhaust the Rune to add one Energy. -/
  | exhaust
  /-- Recycle the Rune to add one Power of its domain. -/
  | recycle
deriving DecidableEq, Repr

/-- Where a Standard Move goes (CR 144): to a Battlefield, or back to the player's Base. -/
inductive MoveDest where
  /-- To the Base of the Unit's controller. -/
  | base
  /-- To a Battlefield. -/
  | battlefield (bf : ObjId)
deriving DecidableEq, Repr

/-- What an action says. -/
inductive ActionKind where
  /-- An arrangement of cards: the result of a shuffle, or the order of a Recycle. -/
  | arrange (order : List ObjId)
  /-- An arrangement of players: the turn order (CR 115). -/
  | arrangePlayers (order : List PlayerId)
  /-- A random pick: the index among the candidates. -/
  | pick (index : Nat)
  /-- Set this card aside in the mulligan (CR 117.1). -/
  | mulliganPick (card : ObjId)
  /-- Finish the mulligan. -/
  | mulliganDone
  /-- Discard this card from the hand (CR 415). -/
  | discardPick (card : ObjId)
  /-- Finish a discard: the hand is empty, so nothing more can be discarded (CR 415.1). -/
  | discardDone
  /-- Answer a "you may": do it, or do not. -/
  | decide (yes : Bool)
  /-- Choose this object, when an effect says to choose one while it resolves (CR 355). -/
  | choose (obj : ObjId)
  /-- The opponent who gains a point from a Burn Out (CR 432.2.c). -/
  | burnOutTarget (opponent : PlayerId)
  /-- Pass priority. In the Main Phase with an empty Chain, the turn player passing ends the
  phase (CR 305). -/
  | pass
  /-- Concede the game (CR 649-651). -/
  | concede
  /-- Time is called (TR 408.2). The clock says it; it is not a player's answer. -/
  | timeCalled
  /-- The game is a draw (TR 505.6, 410.1): the judge declares it, because the players agree to it
  or because a loop has no end. It is not a player's answer. -/
  | declareDraw
  /-- Use an ability of a Basic Rune on the Base (CR 164.2). -/
  | runeAbility (card : ObjId) (ability : RuneAbility)
  /-- Play a card, paying from the Rune Pool and naming the Spell's targets in order (CR 355, 357).
  For Flow from the Trash, name the unadjusted cost when several costs are available (CR 829). -/
  | playCard (card : ObjId) (pay : RunePool.Payment) (targets : List ObjId)
      (flowCost : Option Cost := none)
  /-- Move a Unit of the player's by a Standard Move: it is exhausted and goes to a Battlefield, or
  back to the Base (CR 144). One Unit at a time; moving several together (CR 144.3) is later. -/
  | standardMove (unit : ObjId) (dest : MoveDest)
  /-- In Combat Damage: the next Unit, among those of the other side, to be given lethal damage
  (CR 467.2.c). Tank Units come first (CR 815). -/
  | assignPick (unit : ObjId)
  /-- In Combat Damage: every Unit of the other side has been named; the damage is assigned
  down that order (CR 467.2.c). -/
  | assignDone
  /-- Use an activated ability of an object, paying its costs (CR 361, 363, 356-357): the ability at
  place `idx` of the card of `source`, with the Power of the domains listed, and the objects
  chosen for the choices of the ability (CR 355). The hand cards in `discards` pay the cost
  before the ability goes on the Chain (CR 423.3). -/
  | activate (source : ObjId) (idx : Nat) (pay : RunePool.Payment) (targets : List ObjId)
      (discards : List ObjId := [])
  /-- Put the `idx`-th of the triggered abilities that wait on the Chain, with the objects chosen
  for its choices (CR 383.3.d, 355). An ability with no legal pick is removed with no objects
  (CR 355). -/
  | putTrigger (idx : Nat) (targets : List ObjId)
  /-- Use an Add ability of an object: its Energy or Power is added at once, without the Chain
  (CR 430, 164.2). -/
  | manaAbility (source : ObjId) (idx : Nat) (pay : RunePool.Payment)
deriving DecidableEq, Repr

/-- An action: who acts, and what they say (design.md §6.2). -/
structure Action where
  /-- Who acts. -/
  actor : Actor
  /-- What they say. -/
  kind : ActionKind
deriving DecidableEq, Repr

/-- A triggered ability that has fired and waits to go on the Chain (CR 382-385): the object it
belongs to, the card and the place of the ability among the card's abilities, and the player who
controls it. -/
structure PendTrigger where
  /-- The object whose ability fired. -/
  source : ObjId
  /-- The card of the object (kept, so the ability resolves even if the object is gone). -/
  card : CardId
  /-- The place of the ability among the abilities of the card. -/
  idx : Nat
  /-- The player who controls the ability. -/
  controller : PlayerId
  /-- The object the ability watches, for an ability that is not about its own object: it is
  the last slot of the ability when it resolves. -/
  subject : Option ObjId := none
  /-- The amount captured by the event that fired this ability, if any (CR 388-389). -/
  eventAmount : Option Nat := none
deriving DecidableEq, Repr

/-- A frame of the stack. A frame holds no part of the board: everything a decision is about is read
from the state when the decision is made, so a frame cannot go out of date (design.md §6.2). -/
inductive Frame where
  /-- Chance: the shuffle of a zone (CR 114). The answer arranges the zone's contents. -/
  | chanceShuffle (z : Zone)
  /-- Chance: the random Battlefield of a player (CR 487.5). The answer picks an index among the
  player's Battlefields that are out of the game. -/
  | chanceBattlefield (p : PlayerId)
  /-- Chance: the turn order (CR 115). Answering it pushes `setupHands`. -/
  | chanceTurnOrder
  /-- Choice: a player's mulligan (CR 117). A card picked is set aside at once; `setAside` is how
  many have been picked so far. -/
  | mulligan (p : PlayerId) (setAside : Nat)
  /-- Chance: the order in which the cards set aside are put at the bottom of the Main Deck
  (CR 417.5). The answer arranges everything in the player's set-aside zone. -/
  | chanceRecycle (p : PlayerId)
  /-- Chance: the order in which the Trash is put into the Main Deck by a Burn Out
  (CR 432.2.b). The answer arranges the player's Trash. -/
  | chanceBurnOut (p : PlayerId)
  /-- Choice: the opponent who gains the point of a Burn Out (CR 432.2.c). -/
  | chooseBurnOut (p : PlayerId)
  /-- Work: lay out the opening hands and the mulligans of all players (CR 116-117). -/
  | setupHands
  /-- Work: player `p` draws `n` cards (CR 414); an empty deck is a Burn Out (CR 432). -/
  | draw (p : PlayerId) (n : Nat)
  /-- Work: begin the next turn: the turn player is the next in the turn order (CR 301, 118). -/
  | beginTurn
  /-- Work: the phase `ph` of the turn (CR 314-317). -/
  | phase (ph : Phase)
  /-- Work: the turn player Holds their Battlefields after Beginning Step effects (CR 315.2). -/
  | scoreHolds
  /-- Choice: the turn player has priority in the Main Phase (CR 311-312, 316). -/
  | priority (p : PlayerId)
  /-- Choice: player `p` has priority while the Chain holds a Spell (CR 311-313); `passes` players
  have passed in a row. When everyone has passed, the top of the Chain resolves (CR 340). -/
  | chainPass (p : PlayerId) (passes : Nat)
  /-- Work: resolve the item on top of the Chain (CR 340): its effect is run, then it goes to the
  Trash. -/
  | resolveChain
  /-- Work: run the effects `todo` of the item `src` for `controller`, with the variables `env`
  (design.md §6.2). -/
  | run (controller : PlayerId) (src : ObjId) (env : Env) (todo : EffectList)
  /-- Work: a Spell has resolved; put it in its owner's Trash (CR 359.3.d). -/
  | finishSpell (item : ObjId)
  /-- Work: the Cleanup (CR 318-324): do the state-based steps one at a time until none applies,
  then check for a winner and start a Showdown (CR 323). -/
  | cleanup
  /-- Choice: player `focus` has Focus in the Showdown at the Battlefield `bf` (CR 341-348);
  `passes` players have passed in a row. When everyone has passed, the Showdown ends (CR 348). -/
  | showdown (bf : ObjId) (focus : PlayerId) (passes : Nat)
  /-- Work: the Showdown at `bf` was a Combat whose Attacker is `att`: start Combat Damage
  (CR 467). -/
  | combatDamage (bf : ObjId) (att : PlayerId)
  /-- Choice: player `side` names the Units of the other side in the order they get lethal damage
  (CR 467.2.c). `acc` is the order so far; `done` is the damage assigned by the sides before,
  all dealt together when the last side has assigned (CR 467.2.c.1). -/
  | assign (bf : ObjId) (att side : PlayerId) (acc : List ObjId) (done : List (ObjId × Nat))
  /-- Work: the Combat at `bf` ends (CR 468): the Combat Cleanup, and then the Battlefield goes to
  the player whose Units are alone there. -/
  | combatResolve (bf : ObjId) (att : PlayerId)
  /-- Work: the triggered abilities that have fired go on the Chain, the turn player's first
  (CR 383.3). They wait here until a player would next receive priority (CR 383.1). -/
  | triggers (pend : List PendTrigger)
  /-- Choice: player `p` puts one of their triggered abilities `first :: more` on the Chain, and
  chooses its targets (CR 383.3.d); `others` are the abilities of the other players, still to come.
  The group is never empty. -/
  | triggerOrder (p : PlayerId) (first : PendTrigger) (more : List PendTrigger)
      (others : List PendTrigger)
  /-- Choice: player `p` discards `n` more cards of their hand, one at a time (CR 415). -/
  | discard (p : PlayerId) (n : Nat)
  /-- Choice: player `p` may do the effect `e`; the effects `rest` of the item follow (CR 355). -/
  | mayDo (p : PlayerId) (src : ObjId) (env : Env) (e : Effect) (rest : EffectList)
  /-- Choice: player `p` chooses between the effects `a` ("yes") and `b` ("no"); the effects `rest`
  of the item follow (CR 355). -/
  | eitherDo (p : PlayerId) (src : ObjId) (env : Env) (a b : Effect) (rest : EffectList)
  /-- Choice: player `p` chooses one of the objects `cands` for the effect `e`, which names it
  by the variable `pickVar`; the objects are `c :: more`; the effects `rest` of the item follow
  (CR 355). -/
  | pickDo (p : PlayerId) (src : ObjId) (env : Env) (c : ObjId) (more : List ObjId) (e : Effect)
      (rest : EffectList)
deriving DecidableEq, Repr

/-- The frames of the setup: the shuffles, the Battlefield picks and the turn order. -/
def Frame.isSetup : Frame → Bool
  | .chanceShuffle _ => true
  | .chanceBattlefield _ => true
  | .chanceTurnOrder => true
  | _ => false

/-- The frames of a Spell on the Chain: they exist only in the Main Phase. -/
def Frame.isPlay : Frame → Bool
  | .chainPass .. => true
  | .resolveChain => true
  | .run .. => true
  | .finishSpell _ => true
  | .cleanup => true
  | .showdown .. => true
  | .combatDamage .. => true
  | .assign .. => true
  | .combatResolve .. => true
  | .triggers _ => true
  | .triggerOrder .. => true
  | .discard .. => true
  | .mayDo .. => true
  | .eitherDo .. => true
  | .pickDo .. => true
  | _ => false

/-- Frames the engine advances by itself. -/
def Frame.isWork : Frame → Bool
  | .setupHands => true
  | .draw _ _ => true
  | .beginTurn => true
  | .phase _ => true
  | .scoreHolds => true
  | .resolveChain => true
  | .run .. => true
  | .finishSpell _ => true
  | .cleanup => true
  | .combatDamage .. => true
  | .combatResolve .. => true
  | .triggers _ => true
  | _ => false

end Riftbound

end
