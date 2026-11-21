module

public import Riftbound.Card.IR.Basic

/-!
# The effect IR: values and the environment

What an effect computes with at run time (design.md §7.2). A value is a number, a truth value, an
object, a player or a name. The environment maps variable names to values; it is a list, so that
it is easy to print and to compare.
-/

@[expose] public section

namespace Riftbound

/-- A value an effect works with. -/
inductive Value where
  /-- A whole number. -/
  | int (n : Int)
  /-- A truth value. -/
  | bool (b : Bool)
  /-- An object. -/
  | obj (id : ObjId)
  /-- A player. -/
  | player (p : PlayerId)
  /-- A name, for example the name of a card (CR 132). -/
  | name (s : String)
deriving DecidableEq, Repr, Hashable

/-- The variables of an effect and their values. The newest binding comes first. -/
structure Env where
  /-- The bindings. -/
  bindings : List (VarId × Value) := []
  /-- The values chosen when the card was played: slot `i` is `slots[i]` (CR 355). -/
  slots : List Value := []
  /-- The object a `forEach` is about: what `Selector.it` means (design.md §7.2). -/
  it : Option ObjId := none
deriving DecidableEq, Repr

namespace Env

/-- The empty environment. -/
def empty : Env := {}

/-- Bind a variable. It shadows an older binding of the same name. -/
def bind (e : Env) (v : VarId) (x : Value) : Env := { e with bindings := (v, x) :: e.bindings }

/-- The value of a variable, if it is bound. -/
def lookup (e : Env) (v : VarId) : Option Value :=
  (e.bindings.find? (fun b => b.1 == v)).map (·.2)

/-- A variable just bound is found. -/
theorem lookup_bind (e : Env) (v : VarId) (x : Value) : (e.bind v x).lookup v = some x := by
  simp [bind, lookup]

/-- Nothing is found in the empty environment. -/
theorem lookup_empty (v : VarId) : Env.empty.lookup v = none := by
  simp [empty, lookup]

end Env

end Riftbound

end
