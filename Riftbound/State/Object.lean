module

public import Riftbound.Core.Ids
public import Riftbound.Core.Domain
public import Riftbound.Core.Keyword

/-!
# Game objects

The attributes of a game object (CR 119-124), kept in a table keyed by `ObjId`
(design.md §5.2). More attributes (Attach target, counters, status effects) arrive with the
rules that use them.
-/

@[expose] public section

namespace Riftbound

/-- What an object is. -/
inductive ObjKind where
  /-- A card: a physical card of a deck, and its logical card. -/
  | card (phys : PhysId) (card : CardId)
  /-- A token (CR 179-187): it has a definition but no physical card. -/
  | token (card : CardId)
  /-- An ability on the Chain (CR 337, 361): the card it comes from (kept, so that it resolves
  even when the source has left play), the place of the ability among the card's abilities, and
  the object it was used from. -/
  | chainAbility (card : CardId) (idx : Nat) (source : ObjId)
deriving DecidableEq, Repr

/-- The physical card behind an object, if it is a card. -/
def ObjKind.phys? : ObjKind → Option PhysId
  | .card p _ => some p
  | _ => none

/-- When a lasting change of Might ends (CR 475-478). -/
inductive EndPoint where
  /-- At the end of the turn. -/
  | turn
  /-- At the end of the combat (it also ends with the turn). -/
  | combat
  /-- Never: for the rest of the game. -/
  | never
deriving DecidableEq, Repr

/-- A lasting change of an object's Might: how much, and when it ends. -/
structure MightMod where
  /-- The change: positive or negative. -/
  amount : Int
  /-- When it ends. -/
  ends : EndPoint
deriving DecidableEq, Repr

/-- The attributes of a game object. -/
structure Object where
  /-- What the object is. -/
  kind : ObjKind
  /-- The player who owns it (CR 127). -/
  owner : PlayerId
  /-- The player who controls it: the base value, before continuous effects (CR 188-192). -/
  controller : PlayerId
  /-- Whether it is exhausted (CR 415). -/
  exhausted : Bool := false
  /-- The damage it has taken (CR 142). -/
  damage : Nat := 0
  /-- When it became an object (CR 482). -/
  timestamp : Timestamp
  /-- For a Rune: its domain, the domain of the Power it adds (CR 164.2). `none` for what is not
  a Rune. A copy of the printed domain made when the object is made; the derived value comes with
  the Layers (milestone M6). -/
  runeDomain : Option Domain := none
  /-- For a Spell on the Chain: the objects chosen when it was played, in the order of its
  choices (CR 355). Slot `i` of the effect is `targets[i]`. It means nothing off the Chain. -/
  targets : List ObjId := []
  /-- For a Unit at a Battlefield: that Battlefield (CR 106, 144). `none` for a Unit on a Base and
  for what is not a Unit. Leaving the Board clears it, except into the Trash: a card there
  remembers where it was, for what it does when it dies ("here"). -/
  loc : Option ObjId := none
  /-- For a Battlefield: the player who controls it, if any (CR 190.6). -/
  control : Option PlayerId := none
  /-- For a Battlefield: the player whose Unit made it Contested (CR 190.3). -/
  contested : Option PlayerId := none
  /-- For a Battlefield: the players who have scored it this turn (CR 472). -/
  scored : List PlayerId := []
  /-- The abilities of this object that have been used this turn, by their place among the card's
  abilities: once for each use (CR 371, 386). Cleared when a turn begins. -/
  used : List Nat := []
  /-- The lasting changes of Might that effects have made to this object (CR 475-478). Leaving the
  Board clears them. -/
  mightMods : List MightMod := []
  /-- The keywords that effects gave this object for a while, and when they end (CR 479.3).
  Leaving the Board clears them. -/
  tempKws : List (KeywordInst × EndPoint) := []
  /-- For an Equipment in play: the Unit it is attached to (CR 137, 825). Leaving the Board clears
  it; a Cleanup step clears it when the Unit is gone. -/
  attached : Option ObjId := none
  /-- For an Equipment in play: the turn it was attached (Brutalizer). -/
  attachedTurn : Option Nat := none
  /-- The players who scored this Battlefield by holding it this turn. -/
  held : List PlayerId := []
  /-- Whether the Unit has a buff: +1 Might (CR 701). Leaving the Board clears it. -/
  buffed : Bool := false
  /-- Whether the Unit is stunned: it deals no combat damage this turn (CR 424). -/
  stunned : Bool := false
  /-- For a Legend: the XP of its player (CR 728). XP is not an object; the model keeps it with the
  player's Legend. -/
  xp : Nat := 0
  /-- Whether an additional cost was paid when the card was played: Repeat does the effect of a
  Spell twice (CR 820), Accelerate lets a Unit enter ready (CR 805), and a card can ask "if you
  paid the additional cost". -/
  paid : Bool := false
  /-- How many of the optional additional costs were paid when the card was played: a Spell does
  its effect once more for each Repeat that was paid (CR 820.3). -/
  extraPaid : Nat := 0
  /-- Whether another card of its owner had been played in that turn when the card was played:
  Legion (CR 812). -/
  legion : Bool := false
  /-- The turn in which the card was played, if it was. The record of a play stays with the
  object. -/
  playedTurn : Option Nat := none
  /-- The timestamp counter when the card was last played: a card played later has a greater one
  ("the next card you play"). It stays when the card moves. -/
  playedStamp : Option Nat := none
  /-- Where the Unit was before its last move: its Battlefield, or none for the Base. -/
  prevLoc : Option ObjId := none
  /-- The card was played from its owner's hand (not from the Trash, the Deck, ...). -/
  playedFromHand : Bool := true
  /-- The objects chosen by the abilities this object used in the turn `choseTurn`. -/
  chose : List ObjId := []
  /-- The turn the objects in `chose` were chosen in. -/
  choseTurn : Option Nat := none
  /-- The card was on the board when it last changed zone (it left the board by that move). -/
  leftBoard : Bool := false
  /-- The Unit that took control of this object until it leaves the board (Akshan): its identifier
  on the board. -/
  takenBy : Option ObjId := none
  /-- The identifier the card had on the board before it left it (it has a new one afterwards). -/
  formerId : Option ObjId := none
  /-- The Equipment this card was banished by, when its Unit died (The Zero Drive). -/
  banishedWith : Option ObjId := none
  /-- The Energy paid when the card was played (0 if it was played for nothing). -/
  energyPaid : Nat := 0
  /-- How many Standard Moves the Unit made in the turn `movesTurn` (CR 447). -/
  moves : Nat := 0
  /-- The turn the Standard Moves in `moves` were made in. -/
  movesTurn : Option Nat := none
  /-- For a card hidden face down: the Battlefield it is hidden at (CR 811). -/
  hiddenAt : Option ObjId := none
  /-- The buffs beyond the first, for a Unit that can have any number of buffs. -/
  extraBuffs : Nat := 0
  /-- Whether the card came into play from Hidden (it was hidden when it was played). -/
  fromHidden : Bool := false
  /-- For a card hidden face down: the turn it was hidden. -/
  hiddenTurn : Option Nat := none
deriving DecidableEq, Repr

/-- The object after it used an ability in the turn `turn` that chose the objects `ts`. -/
def Object.noteChose (turn : Nat) (ts : List ObjId) (o : Object) : Object :=
  { o with chose := (if o.choseTurn == some turn then o.chose else []) ++ ts,
           choseTurn := some turn }

/-- The object after one more move in the turn `turn` (CR 447). -/
def Object.countMove (turn : Nat) (old : Option ObjId) (o : Object) : Object :=
  { o with moves := if o.movesTurn == some turn then o.moves + 1 else 1, movesTurn := some turn,
           prevLoc := old }

end Riftbound

end
