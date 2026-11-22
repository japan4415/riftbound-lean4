module

public import Riftbound.Rules.Effects
public import Riftbound.Rules.Chain

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
  | .inCombat => true
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
  | .count (.pick .all _ place fs) =>
    (place.understood || place.zoneKind?.isSome) && FilterList.understood fs
  | .count s => Selector.understood s
  | .handSize p => p.understood
  | .xp => true
  | .turnsTaken p => p.understood
  | .add a b => Amount.understood a && Amount.understood b
  | .sub a b => Amount.understood a && Amount.understood b
  | .mul a b => Amount.understood a && Amount.understood b
  | .min a b => Amount.understood a && Amount.understood b
  | .max a b => Amount.understood a && Amount.understood b
  | .mightOf s => Selector.understood s
  | _ => false

/-- An amount that is understood in a condition: the Might of objects is not (conditions read the
Might without the Layers, which they do not need yet). -/
def Amount.understoodC : Amount → Bool
  | .const _ => true
  | .var _ => true
  | .count (.pick .all _ place fs) =>
    (place.understood || place.zoneKind?.isSome) && FilterList.understood fs
  | .count s => Selector.understood s
  | .handSize p => p.understood
  | .xp => true
  | .turnsTaken p => p.understood
  | .add a b => Amount.understoodC a && Amount.understoodC b
  | .sub a b => Amount.understoodC a && Amount.understoodC b
  | .mul a b => Amount.understoodC a && Amount.understoodC b
  | .min a b => Amount.understoodC a && Amount.understoodC b
  | .max a b => Amount.understoodC a && Amount.understoodC b
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
  | .mighty => true
  | .attacker => true
  | .defender => true
  | .alone => true
  | .lethal => true
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
  | .cmp _ a b => a.understoodC && b.understoodC
  | .exists s => s.understood
  | .matches s f => s.understood && f.understood
  | .yourTurn => true
  | .legion => true
  | .paid => true
  | _ => false

/-- A selector of a primitive: it may also name one object to choose while the effect resolves
(`runEffect` asks the player), which is not understood anywhere else. -/
def Selector.understoodPick : Selector → Bool
  | .pick .one _ place fs => place.understood && FilterList.understood fs
  | s => s.understood

/-- A game action that is understood. -/
def Prim.understood : Prim → Bool
  | .draw p n => p.understood && n.understood
  | .score p n => p.understood && n.understood
  | .discard p n => p.understood && n.understood
  | .channel p n m => p.understood && n.understood && m.understood
  | .deal s n => s.understoodPick && n.understood
  | .heal s n => s.understoodPick && n.understood
  | .kill s => s.understoodPick
  | .banish s => s.understoodPick
  | .returnToHand s => s.understoodPick
  | .ready s => s.understoodPick
  | .exhaust s => s.understoodPick
  | .create _ n pl _ => n.understood && (pl == .atBase || pl == .here)
  | .attach g t => g.understood && t.understood
  | .move s .base => s.understoodPick
  | .move s (.at_ d) => s.understoodPick && d.understood
  | .stun s => s.understoodPick
  | .buff s => s.understoodPick
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
  | .may e => Effect.understood e
  | .eachPlayer w e => w.understood && Effect.understood e
  | .grant s (.mightPlus .it a) d =>
    s.understood && a.understood && d.endPoint?.isSome
  | .grant s (.mightMinus .it a) d =>
    s.understood && a.understood && d.endPoint?.isSome
  | .grant s (.mightMinusMin .it a _) d =>
    s.understood && a.understood && d.endPoint?.isSome
  | .grant s (.keyword .it _) d => s.understood && d.endPoint?.isSome
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

/-! ### What a card does when it is played

The checks below say which cards do everything their text says in this model: every ability is one
the engine carries out, and every keyword is one it knows. They are the measure of "the card works"
(docs/coverage.md); a card whose text is written down but not run is not counted. -/

/-- A passive change the engine applies. -/
def StaticMod.runs : StaticMod → Bool
  | .mightPlus s a => s.understood && a.understoodC
  | .mightMinus s a => s.understood && a.understoodC
  | .keyword s _ => s.understood
  | .entersReady .self => true
  | _ => false

/-- The points of the turn that fire a triggered ability. -/
def Timing.runs : Timing → Bool
  | .startOfTurn => true
  | .beginning => true
  | .startOfMain => true
  | .endOfTurn => true
  | _ => false

/-- A trigger the engine detects: the event, whose subject it is about, and the condition. -/
def Trigger.runs (t : Trigger) : Bool :=
  t.occurrence == .every && t.condition.understood &&
    (match t.event with
      | .play => true | .die => true | .move => true | .attack => true | .defend => true
      | .stun => true | .discard => true
      | .conquer => t.subject == .self | .hold => t.subject == .self
      | .youConquer => t.subject == .self | .youHold => t.subject == .self
      | .at_ tm => tm.runs && t.subject == .self
      | _ => false) &&
    (t.subject == .self ||
      (match t.subject with
        | .pick .all _ .anywhere fs => FilterList.understood fs
        | _ => false))

/-- An ability the engine carries out. -/
def Ability.runs : Ability → Bool
  | .passive c mods => c.understood && mods.all StaticMod.runs
  | .activated costs _ body _ =>
    (costPlan costs).isSome &&
      ((manaKind body).isSome || (body.choices.all Choice.simple && body.body.understood))
  | .triggered t body _ =>
    t.runs && body.choices.all Choice.simple && body.body.understood
  | .replacement .. => false

/-- A keyword the engine knows. -/
def Keyword.runs : Keyword → Bool
  | .reaction => true | .action => true | .assault => true | .shield => true | .ganking => true
  | .tank => true | .temporary => true | .legion => true | .deflect => true
  | .deathknell => true | .hunt => true | .level => true | .equip => true
  | _ => false

/-- The card does everything its text says: it is written down, its abilities and its Spell are
carried out, and its keywords are known. -/
def CardDef.runs (c : CardDef) : Bool :=
  c.status == .drafted && c.abilities.all Ability.runs && c.keywords.all (·.keyword.runs) &&
    (match c.spellEffect with
      | some e => e.choices.all Choice.simple && e.body.understood
      | none => !c.types.contains .spell)

end Riftbound

end
