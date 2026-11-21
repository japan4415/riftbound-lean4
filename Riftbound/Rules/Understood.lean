module

public import Riftbound.Rules.Effects

/-!
# What the interpreter understands

A static question about an effect: is it written entirely in the part of the IR that the
interpreter (`runEffect`) gives a meaning to? These functions mirror the arms of `runEffect`,
`Selector.eval`, `Amount.evalS`, `Condition.eval` and `Filter.holds`, so that the tests can count
the cards that run (roadmap.md, M4d) and the gaps are listed by name.

An effect that is understood can still be skipped at run time, for example when a selector names
an object that is not there; "understood" says that nothing in it is a construct the interpreter
does not know.
-/

@[expose] public section

namespace Riftbound

/-- The places that are understood. -/
def Place.understood : Place → Bool
  | .anywhere => true
  | .atBase => true
  | .atBattlefield => true
  | .here => true
  | _ => false

/-- The players an effect names that are understood. -/
def PlayerSel.understood : PlayerSel → Bool
  | .you => true
  | .opponent => true
  | .eachPlayer => true
  | .eachOpponent => true
  | _ => false

mutual

/-- An amount that is understood. -/
def Amount.understood : Amount → Bool
  | .const _ => true
  | .var _ => true
  | .count s => Selector.understood s
  | .handSize p => p.understood
  | .xp => true
  | .add a b => Amount.understood a && Amount.understood b
  | .sub a b => Amount.understood a && Amount.understood b
  | .mul a b => Amount.understood a && Amount.understood b
  | .min a b => Amount.understood a && Amount.understood b
  | .max a b => Amount.understood a && Amount.understood b
  | _ => false

/-- A filter that is understood. -/
def Filter.understood : Filter → Bool
  | .ofType _ => true
  | .ofSupertype _ => true
  | .tag _ => true
  | .named _ => true
  | .hasKeyword _ => true
  | .domain _ => true
  | .might _ a => Amount.understood a
  | .exhausted => true
  | .ready => true
  | .damaged => true
  | .notSelf => true
  | .stunned => true
  | .buffed => true
  | _ => false

/-- Every filter of a list is understood. -/
def FilterList.understood : FilterList → Bool
  | .nil => true
  | .cons f rest => Filter.understood f && FilterList.understood rest

/-- A selector that is understood. -/
def Selector.understood : Selector → Bool
  | .self => true
  | .slot _ => true
  | .it => true
  | .var _ => true
  | .pick .all _ place fs => place.understood && FilterList.understood fs
  | _ => false

end

/-- A condition that is understood. -/
def Condition.understood : Condition → Bool
  | .always => true
  | .not c => Condition.understood c
  | .and a b => Condition.understood a && Condition.understood b
  | .or a b => Condition.understood a && Condition.understood b
  | .cmp _ a b => a.understood && b.understood
  | .exists s => s.understood
  | .matches s f => s.understood && f.understood
  | .yourTurn => true
  | _ => false

/-- A game action that is understood. -/
def Prim.understood : Prim → Bool
  | .draw p n => p.understood && n.understood
  | .deal s n => s.understood && n.understood
  | .heal s n => s.understood && n.understood
  | .kill s => s.understood
  | .banish s => s.understood
  | .returnToHand s => s.understood
  | .ready s => s.understood
  | .exhaust s => s.understood
  | .create _ n pl _ => n.understood && (pl == .atBase || pl == .here)
  | .attach g t => g.understood && t.understood
  | .move s .base => s.understood
  | .stun s => s.understood
  | .buff s => s.understood
  | .gainXP p n => p.understood && n.understood
  | _ => false

mutual

/-- An effect that is understood. -/
def Effect.understood : Effect → Bool
  | .nop => true
  | .seq es => EffectList.understood es
  | .ifThen c t e => c.understood && Effect.understood t && Effect.understood e
  | .forEach s body => s.understood && Effect.understood body
  | .repeatN n e => n.understood && Effect.understood e
  | .bind _ a e => a.understood && Effect.understood e
  | .prim p => p.understood
  | .grant s (.mightPlus .it a) d =>
    s.understood && a.understood && d.endPoint?.isSome
  | .grant s (.mightMinus .it a) d =>
    s.understood && a.understood && d.endPoint?.isSome
  | _ => false

/-- Every effect of a list is understood. -/
def EffectList.understood : EffectList → Bool
  | .nil => true
  | .cons e rest => Effect.understood e && EffectList.understood rest

end

/-- A Spell that can be played and run: every choice is one target, and the effect is understood. -/
def CardDef.spellRuns (c : CardDef) : Bool :=
  match c.spellEffect with
  | some e => e.choices.all Choice.simple && e.body.understood
  | none => false

end Riftbound

end
