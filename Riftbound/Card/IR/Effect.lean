module

public import Riftbound.Card.IR.Prim

/-!
# The effect IR: effects

An effect is built from primitives with combinators: a sequence, a choice of one mode, a condition,
a loop over objects, an optional step, a follow-up that needs the first step done, a bound
variable, a lasting modification, a delayed effect (design.md §7.1, §7.2). The only recursive
types of the IR are `Effect` and the list of effects, in one `mutual` block, so that they derive
`DecidableEq` (lean-guidelines.md §5.4).
-/

@[expose] public section

namespace Riftbound

mutual

/-- An effect: what happens when a spell resolves or an ability fires. -/
inductive Effect where
  /-- Nothing happens. -/
  | nop
  /-- Do the effects in order. -/
  | seq (es : EffectList)
  /-- Do the mode that was chosen when the card was played (CR 355). -/
  | chooseOne (modes : EffectList)
  /-- Do the first effect if the condition holds, the second otherwise. -/
  | ifThen (c : Condition) (t e : Effect)
  /-- Do the effect for each of the objects, with `it` the object. -/
  | forEach (s : Selector) (body : Effect)
  /-- Each of the players does the effect: the effect is done for them, so that what they choose
  is theirs ("each player kills one of their units"). -/
  | eachPlayer (who : PlayerSel) (body : Effect)
  /-- The player may do the effect. -/
  | may (e : Effect)
  /-- Do the first effect, and if it was done, the second ("if you do") (CR 387). -/
  | doThen (first rest : Effect)
  /-- Do the effect a number of times. -/
  | repeatN (n : Amount) (e : Effect)
  /-- Bind a variable to an amount, then do the effect. -/
  | bind (v : VarId) (a : Amount) (e : Effect)
  /-- A game action. -/
  | prim (p : Prim)
  /-- Change objects for a while. The modification is made to each of the objects, which the
  modification calls `it`. -/
  | grant (s : Selector) (m : StaticMod) (d : Duration)
  /-- Do the effect later, when the trigger fires (CR 390-393). -/
  | delayed (t : Trigger) (e : Effect) (d : Duration)
  /-- Prevent the next `n` damage that would be dealt to the objects, for a while (CR 438). -/
  | preventNext (s : Selector) (n : Amount) (d : Duration)
  /-- The next time the event would happen to the objects, do the effect instead (CR 367-375). -/
  | replaceNext (ev : ReplaceEvent) (s : Selector) (instead : Effect) (d : Duration)
  /-- An effect the IR cannot express: a handler of the table of custom handlers. -/
  | custom (id : CustomId) (args : ArgList)
deriving DecidableEq, Repr, Hashable

/-- A list of effects. -/
inductive EffectList where
  /-- No effect. -/
  | nil
  /-- An effect, then the rest. -/
  | cons (e : Effect) (rest : EffectList)
deriving DecidableEq, Repr, Hashable

end

end Riftbound

end
