module

public import Riftbound.Card.CardDef

/-!
# Tokens

The tokens that cards make (CR 179-187): a token has a definition and no physical card. `create`
makes the object from the card with the identifier `TKN-<name>`. Only the tokens whose rules are
written down are here: the Units with a Might and, for some, a keyword the token prints.

The Gold and Bomb gear tokens are not here yet: their abilities are not written down.
-/

@[expose] public section

namespace RiftboundCards.Tokens

open Riftbound

/-- A Unit token with the Might (CR 179). -/
def unitToken (name : String) (might : Int) (keywords : List KeywordInst := []) : CardDef :=
  { id := ⟨"TKN-" ++ name⟩, name := name, types := [.unit], might := some might,
    keywords := keywords, status := .full }

/-- The Unit tokens. -/
def cards : List CardDef :=
  [ unitToken "Recruit" 1,
    unitToken "Mech" 3,
    unitToken "Sprite" 3 [{ keyword := .temporary }],
    unitToken "Bird" 1 [{ keyword := .deflect, arg := .amount 1 }],
    unitToken "Sand Soldier" 2,
    unitToken "Shadow Clone" 0,
    unitToken "Tentacle" 1 ]

end RiftboundCards.Tokens

end
