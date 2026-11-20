module

public import Riftbound.State.Zone
public import Riftbound.State.Phase

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
  /-- The opponent who gains a point from a Burn Out (CR 432.2.c). -/
  | burnOutTarget (opponent : PlayerId)
  /-- Pass priority. In the Main Phase with an empty Chain, the turn player passing ends the
  phase (CR 305). -/
  | pass
  /-- Concede the game (CR 649-651). -/
  | concede
  /-- Use an ability of a Basic Rune on the Base (CR 164.2). -/
  | runeAbility (card : ObjId) (ability : RuneAbility)
deriving DecidableEq, Repr

/-- An action: who acts, and what they say (design.md §6.2). -/
structure Action where
  /-- Who acts. -/
  actor : Actor
  /-- What they say. -/
  kind : ActionKind
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
  /-- Choice: the turn player has priority in the Main Phase (CR 311-312, 316). -/
  | priority (p : PlayerId)
deriving DecidableEq, Repr

/-- Frames the engine advances by itself. -/
def Frame.isWork : Frame → Bool
  | .setupHands => true
  | .draw _ _ => true
  | .beginTurn => true
  | .phase _ => true
  | _ => false

end Riftbound

end
