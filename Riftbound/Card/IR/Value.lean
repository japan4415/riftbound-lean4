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
  /-- The card that defines the resolving ability, even if its source has left play. -/
  sourceCard : Option CardId := none
  /-- The controller of the original effect when an instruction is run for another player. -/
  effectController : Option PlayerId := none
  /-- A value saved by the event that triggered the resolving ability (CR 388-389). -/
  eventAmount : Option Nat := none
  /-- The object a `forEach` is about: what `Selector.it` means (design.md §7.2). -/
  it : Option ObjId := none
  /-- What the passive abilities add to the Might of each object now (the Layers' last step). The
  filters read it with the other things that make the Might: it is filled in where an effect is
  run and where targets are chosen, and empty (nothing added) elsewhere. -/
  passMight : List (ObjId × Int) := []
deriving DecidableEq, Repr

/-- The variable that names the object chosen while an effect resolves (CR 355). -/
def pickVar : VarId := ⟨"pick"⟩

namespace Env

/-- The empty environment. -/
def empty : Env := {}

/-- What the passive abilities add to the Might of the object. -/
def passOf (e : Env) (id : ObjId) : Int :=
  ((e.passMight.find? (fun b => b.1 == id)).map (·.2)).getD 0

/-- The environment with the table of what the passive abilities add to the Might. -/
def withMight (e : Env) (t : List (ObjId × Int)) : Env := { e with passMight := t }

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
