module

public import Riftbound.Card.CardDef

/-!
# Tokens

The tokens that cards make (CR 179-187): a token has a definition and no physical card. `create`
looks the token up by name: first here (the identifier `TKN-<name>`), then among the tokens the
data prints (the cards whose number has a T: Gold, Bird, Recruit, Reflection). Here are the tokens
that cards name and the data does not print.
-/

@[expose] public section

namespace RiftboundCards.Tokens

open Riftbound

/-- A Unit token with the Might (CR 179). -/
def unitToken (name : String) (might : Int) (keywords : List KeywordInst := []) : CardDef :=
  { id := ⟨"TKN-" ++ name⟩, name := name, types := [.unit], tags := [⟨name⟩], might := some might,
    keywords := keywords, status := .full }

/-- Shadow Clone can banish a Unit card to gain Assault when it attacks (CR 187.11). -/
def shadowClone : CardDef :=
  let fodder := Selector.one .friendly .inTrash [.ofType .unit]
  { unitToken "Shadow Clone" 0 with
    tags := [],
    abilities := [.triggered (.onSelf .attack)
      (.of [] (.ifThen (.cmp .gt (.count (.all .friendly .inTrash [.ofType .unit])) (.const 0))
        (.may (.doThen (.prim (.banish fodder))
          (.grant .self (.keyword .it ⟨.assault, .amount 4⟩) .thisTurn))) .nop)) .unlimited] }

/-- Bomb (RAD-T02), from the printed token shown in the official Radiance overview. -/
def bomb : CardDef :=
  { id := ⟨"RAD-T02"⟩, name := "Bomb", types := [.gear], tags := [⟨"Bomb"⟩],
    keywords := [{ keyword := .deploy }, { keyword := .deathknell }], sets := [⟨"RAD"⟩],
    abilities := [.triggered (.onSelf .deathknell)
      (.of [.targetOf .one .enemy .atBattlefield [.ofType .unit, .atEventBattlefield]]
        (.seqOf [.prim (.deal (.slot 0) (.const 2)),
          .prim (.kill (.all .friendly .atBattlefield
            [.tag ⟨"Bomb"⟩, .notSelf, .atEventBattlefield]))])) .unlimited],
    status := .full }

/-- The tokens defined by associated cards' rules text. -/
def cards : List CardDef :=
  [ unitToken "Mech" 3,
    unitToken "Sprite" 3 [{ keyword := .temporary }],
    unitToken "Sand Soldier" 2,
    shadowClone,
    { unitToken "Tentacle" 1 with tags := [⟨"Bilgewater"⟩] },
    bomb ]

end RiftboundCards.Tokens

end
