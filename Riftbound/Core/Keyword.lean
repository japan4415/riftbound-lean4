module

public import Riftbound.Core.Cost

/-!
# Keywords

The 28 keywords of the Core Rules (CR 805-832) and keyword instances with their parameter.
The meaning of each keyword is given later (design.md §7.4).
-/

@[expose] public section

namespace Riftbound

/-- A keyword (CR 805-832). -/
inductive Keyword where
  /-- Accelerate (CR 805). -/
  | accelerate
  /-- Action (CR 806). -/
  | action
  /-- Assault X (CR 807). -/
  | assault
  /-- Deathknell (CR 808). -/
  | deathknell
  /-- Deflect X (CR 809). -/
  | deflect
  /-- Ganking (CR 810). -/
  | ganking
  /-- Hidden (CR 811). -/
  | hidden
  /-- Legion (CR 812). -/
  | legion
  /-- Reaction (CR 813). -/
  | reaction
  /-- Shield X (CR 814). -/
  | shield
  /-- Tank (CR 815). -/
  | tank
  /-- Temporary (CR 816). -/
  | temporary
  /-- Vision (CR 817). -/
  | vision
  /-- Equip [Cost] (CR 818). -/
  | equip
  /-- Quick-Draw (CR 819). -/
  | quickDraw
  /-- Repeat [Cost] (CR 820). -/
  | repeat_
  /-- Weaponmaster (CR 821). -/
  | weaponmaster
  /-- Ambush (CR 822). -/
  | ambush
  /-- Hunt X (CR 823). -/
  | hunt
  /-- Level N (CR 824). -/
  | level
  /-- Unique (CR 825). -/
  | unique
  /-- Backline (CR 826). -/
  | backline
  /-- Empower [Cost] (CR 827). -/
  | empower
  /-- Empowered (CR 828). -/
  | empowered
  /-- Flow [Cost] (CR 829). -/
  | flow
  /-- Deploy (CR 830). -/
  | deploy
  /-- Disarm X (CR 831). -/
  | disarm
  /-- Show Off [Object] (CR 832). -/
  | showOff
deriving DecidableEq, Repr, Hashable

/-- Every keyword, in rule-number order. -/
def Keyword.all : List Keyword :=
  [ .accelerate, .action, .assault, .deathknell, .deflect, .ganking, .hidden, .legion,
    .reaction, .shield, .tank, .temporary, .vision, .equip, .quickDraw, .repeat_,
    .weaponmaster, .ambush, .hunt, .level, .unique, .backline, .empower, .empowered,
    .flow, .deploy, .disarm, .showOff ]

/-- The Core Rules define exactly 28 keywords (CR 805-832). -/
theorem Keyword.all_length : Keyword.all.length = 28 := by decide

/-- `Keyword.all` lists each keyword once. -/
theorem Keyword.all_nodup : Keyword.all.Nodup := by decide

/-- Every keyword is in `Keyword.all`. -/
theorem Keyword.mem_all (k : Keyword) : k ∈ Keyword.all := by
  cases k <;> decide

/-- The parameter of a keyword. -/
inductive KeywordArg where
  /-- The keyword has no parameter. -/
  | none
  /-- A number: Assault X, Shield X, Deflect X, Hunt X, Level N, Disarm X. -/
  | amount (n : Nat)
  /-- A cost: Equip, Repeat, Empower, Flow. -/
  | cost (c : Cost)
  /-- An object description: Show Off. Provisional text until selectors exist (milestone M3b). -/
  | object (desc : String)
deriving DecidableEq, Repr, Hashable

/-- A keyword as printed on a card, with its parameter (design.md §7.4). -/
structure KeywordInst where
  /-- The keyword. -/
  keyword : Keyword
  /-- Its parameter. -/
  arg : KeywordArg := .none
deriving DecidableEq, Repr, Hashable

end Riftbound

end
