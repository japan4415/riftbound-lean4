module

public import Riftbound.Card.IR.Ability

/-!
# The effect IR: shorthand for writing cards

The recursive types of the IR use list types of their own (`FilterList`, `EffectList`,
`ArgList`), so that they derive `DecidableEq`. These functions build them from ordinary lists, and
give a short name to the shapes that card text uses all the time.
-/

@[expose] public section

namespace Riftbound

/-- A list of filters from an ordinary list. -/
def FilterList.ofList : List Filter → FilterList
  | [] => .nil
  | f :: fs => .cons f (FilterList.ofList fs)

/-- A list of effects from an ordinary list. -/
def EffectList.ofList : List Effect → EffectList
  | [] => .nil
  | e :: es => .cons e (EffectList.ofList es)

/-- A list of arguments from an ordinary list. -/
def ArgList.ofList : List Arg → ArgList
  | [] => .nil
  | a :: as => .cons a (ArgList.ofList as)

/-- Do the effects in order. -/
def Effect.seqOf (es : List Effect) : Effect := .seq (EffectList.ofList es)

/-- Do one of the modes, as chosen. -/
def Effect.modes (es : List Effect) : Effect := .chooseOne (EffectList.ofList es)

/-- All the objects of a side at a place that have the properties. -/
def Selector.all (side : Side) (place : Place) (fs : List Filter) : Selector :=
  .pick .all side place (FilterList.ofList fs)

/-- Exactly one object, picked while the effect resolves. -/
def Selector.one (side : Side) (place : Place) (fs : List Filter) : Selector :=
  .pick .one side place (FilterList.ofList fs)

/-- A target chosen when the card is played. -/
def Choice.targetOf (q : Quantity) (side : Side) (place : Place) (fs : List Filter) : Choice :=
  .target q side place (FilterList.ofList fs)

/-- A spell with the choices it needs and what it does. -/
def EffectDef.of (choices : List Choice) (body : Effect) : EffectDef := { choices, body }

/-- Empower is usable up to the source's limit. The choices, if any, are for its costs (CR 827). -/
def Ability.empower (costs : List AbilityCost) (limit : Nat := 1)
    (choices : List Choice := []) : Ability :=
  .activated costs .normal
    (.of choices (.ifThen (.cmp .lt .empowerCount (.const limit)) (.prim (.empower .self)) .nop))
    .unlimited

/-- Whether the ability is an explicit implementation of Empower, including a guarded copy. -/
def Ability.isEmpower : Ability → Bool
  | .activated _ _ body _ => isEmpowerBody body.body
  | _ => false
where
  isEmpowerBody : Effect → Bool
    | .prim (.empower .self) => true
    | .ifThen _ body .nop => isEmpowerBody body
    | _ => false

/-- A trigger on the card itself. -/
def Trigger.onSelf (event : TriggerEvent) : Trigger := { event }

/-- One unit of "pay any amount": it may be paid for, and then it is noted on the object. -/
def payUnit (c : Cost) : Effect :=
  .ifThen (.canPay c) (.may (.seqOf [.prim (.pay c), .prim (.markOn .self .unitPaid)])) .nop

/-- Pay any amount of `c` (one unit at a time, up to 12), then do `finish`, which reads how much was
paid: `.notes .unitPaid`. -/
def payAny (c : Cost) (finish : Effect) : Effect :=
  .seqOf (List.replicate 12 (payUnit c) ++ [finish])

end Riftbound

end
