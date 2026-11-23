module

public import Riftbound.Card.CardDef

/-!
# Tokens

The tokens that cards make (CR 179-187): a token has a definition and no physical card. `create`
looks the token up by name: first here (the identifier `TKN-<name>`), then among the tokens the
data prints (the cards whose number has a T: Gold, Bird, Recruit, Reflection). Here are the tokens
that cards name and the data does not print: the Units with the Might the cards say, and, for
some, a keyword the token prints.

The Bomb gear token is not here yet: its text is not written down in the data.
-/

@[expose] public section

namespace RiftboundCards.Tokens

open Riftbound

/-- A Unit token with the Might (CR 179). -/
def unitToken (name : String) (might : Int) (keywords : List KeywordInst := []) : CardDef :=
  { id := ⟨"TKN-" ++ name⟩, name := name, types := [.unit], tags := [⟨name⟩], might := some might,
    keywords := keywords, status := .full }

/-- The Unit tokens. -/
def cards : List CardDef :=
  [ unitToken "Mech" 3,
    unitToken "Sprite" 3 [{ keyword := .temporary }],
    unitToken "Sand Soldier" 2,
    unitToken "Shadow Clone" 0,
    unitToken "Tentacle" 1 ]

end RiftboundCards.Tokens

end
