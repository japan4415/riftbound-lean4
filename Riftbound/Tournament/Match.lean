module

public import Riftbound.State.Phase
public import Riftbound.Core.Ids

/-!
# The match (TR 403, 404, 406, 407, 408)

A match is a run of games between two players. It goes on until one of them has won enough games:
2 in a Best of 3, 1 in a Best of 1 (TR 404). A draw does not count as a win (TR 404.3). The layer
is above the game: it takes the result of each game and says what comes next: whether the match is
over, whether the players may use their sideboards, who chooses who goes first, and whether the
same Battlefields are used again.

Everything here is a plain function on counts and results. How the games are played is the
engine's business.
-/

@[expose] public section

namespace Riftbound

/-- The state of a match between players 0 and 1 (TR 404). -/
structure MatchState where
  /-- The number of games a player must win: 1 for a Best of 1, 2 for a Best of 3 (TR 404.1). -/
  target : Nat
  /-- The games player 0 has won. -/
  wins0 : Nat := 0
  /-- The games player 1 has won. -/
  wins1 : Nat := 0
  /-- The games that have been played, draws included. -/
  games : Nat := 0
  /-- How the last game ended, if a game has been played. -/
  last : Option GameResult := none
  /-- Who went first in the last game, if a game has been played. -/
  lastFirst : Option PlayerId := none
deriving DecidableEq, Repr

/-- How a match ends (TR 404.4, 404.5): a winner, or a draw. -/
inductive MatchResult where
  /-- A player wins the match. -/
  | won (p : PlayerId)
  /-- Nobody wins (TR 404.5). -/
  | draw
deriving DecidableEq, Repr

namespace MatchState

/-- The games a player has won. A player other than 0 and 1 has won none. -/
def winsOf (m : MatchState) (p : PlayerId) : Nat :=
  if p.n = 0 then m.wins0 else if p.n = 1 then m.wins1 else 0

/-- The player who has won enough games, if there is one (TR 404.1). -/
def winner (m : MatchState) : Option PlayerId :=
  if m.target ≤ m.wins0 then some ⟨0⟩ else if m.target ≤ m.wins1 then some ⟨1⟩ else none

/-- The match is over: a player has won enough games. -/
def finished (m : MatchState) : Bool := m.winner.isSome

/-- The match after a game that ended with the result, and was begun by `first`. A draw is a game
played and nothing more: it counts for neither player (TR 404.3). The match stays as it is once it
is over, and for a result that names other than one winner of the two. -/
def record (m : MatchState) (r : GameResult) (first : PlayerId) : MatchState :=
  if m.finished then m
  else
    let m' := { m with games := m.games + 1, last := some r, lastFirst := some first }
    match r with
    | .draw => m'
    | .won [p] =>
      if p.n = 0 then { m' with wins0 := m.wins0 + 1 }
      else if p.n = 1 then { m' with wins1 := m.wins1 + 1 }
      else m'
    | .won _ => m'

/-- The state of a match before the first game (TR 404). -/
def start (target : Nat) : MatchState := { target }

/-- The players may use their sideboards before the next game: not before the first game of the
match (TR 403.5), not after a draw (TR 403.10), and not when the match is over. -/
def sideboardAllowed (m : MatchState) : Bool :=
  !m.finished && m.games != 0 && m.last != some .draw

/-- The next game uses the Battlefields of the last one again: after a draw (TR 406.1.b). -/
def reuseBattlefields (m : MatchState) : Bool := m.last == some .draw

/-- Who decides who goes first in the next game (TR 407). -/
inductive Order where
  /-- The first game: a player chosen at random chooses (TR 407.1-407.2). -/
  | chance
  /-- The player who lost the last game chooses (TR 407.4). -/
  | loserChooses (p : PlayerId)
  /-- The last game was a draw: the order stays (TR 407.4). -/
  | same (first : PlayerId)
deriving DecidableEq, Repr

/-- The player of the two who is not `p`. -/
def other (p : PlayerId) : PlayerId := ⟨1 - p.n⟩

/-- How the order of the next game is decided (TR 407). -/
def nextOrder (m : MatchState) : Order :=
  match m.last, m.lastFirst with
  | some (.won [w]), _ => .loserChooses (other w)
  | some .draw, some f => .same f
  | _, _ => .chance

/-- The player who chooses who goes first (TR 407): a player chosen at random for the first game,
the loser of the last game after a win; after a draw nobody chooses, and the one who went first goes
first again. `random` is the player the draw picked. -/
def Order.chooser (o : Order) (random : PlayerId) : PlayerId :=
  match o with
  | .chance => random
  | .loserChooses p => p
  | .same f => f

/-- Who goes first (TR 407): the chooser goes first or second as they choose; after a draw the
order stays. -/
def Order.first (o : Order) (random : PlayerId) (goFirst : Bool) : PlayerId :=
  match o with
  | .same f => f
  | _ => if goFirst then o.chooser random else other (o.chooser random)

/-- The turn order of a 1v1 game in which `first` goes first (CR 115). -/
def turnOrderOf (first : PlayerId) : List PlayerId := [first, other first]

/-- **After a draw the same player goes first** (TR 407.4), whatever the draw picks. -/
theorem Order.first_same (f random : PlayerId) (b : Bool) : (Order.same f).first random b = f := rfl

/-- **The loser of the last game chooses** (TR 407.4): they go first if they choose to, and the
other player goes first if they choose to go second. -/
theorem Order.first_loser (p random : PlayerId) (b : Bool) :
    (Order.loserChooses p).first random b = if b then p else other p := rfl

/-- In the first game the player the draw picked chooses (TR 407.1, 407.2). -/
theorem Order.first_chance (random : PlayerId) (b : Bool) :
    Order.chance.first random b = if b then random else other random := rfl

/-- The other player of a 1v1 game is a player of the game. -/
theorem other_lt {p : PlayerId} (h : p.n < 2) : (other p).n < 2 := by
  unfold other
  simp only
  omega

/-- The player who goes first is a player of the match when the draw picks one and the order is
about players of the match. -/
theorem Order.first_lt {o : Order} {random : PlayerId} {b : Bool} (hr : random.n < 2)
    (ho : ∀ p, o = .loserChooses p → p.n < 2) (hs : ∀ f, o = .same f → f.n < 2) :
    (o.first random b).n < 2 := by
  cases o with
  | chance =>
    unfold Order.first Order.chooser
    cases b
    · exact other_lt hr
    · exact hr
  | loserChooses p =>
    have hp := ho p rfl
    unfold Order.first Order.chooser
    cases b
    · exact other_lt hp
    · exact hp
  | same f => exact hs f rfl

/-- **The turn order names both players** (CR 115): for a player of a 1v1 game, `turnOrderOf` is an
arrangement of the two. -/
theorem turnOrderOf_perm {first : PlayerId} (h : first.n < 2) :
    (turnOrderOf first).Perm [⟨0⟩, ⟨1⟩] := by
  obtain ⟨n⟩ := first
  simp only at h
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl
  · exact List.Perm.refl _
  · exact List.Perm.swap _ _ _

/-- The result of the match when the time is up (TR 404.4, 404.5, 408.3): the player with more wins
wins; the same number is a draw. -/
def onTime (m : MatchState) : MatchResult :=
  if m.wins1 < m.wins0 then .won ⟨0⟩ else if m.wins0 < m.wins1 then .won ⟨1⟩ else .draw

/-- A player concedes the match: the other player wins it (TR 410.2). -/
def concedeMatch (p : PlayerId) : MatchResult := .won (other p)

/-- The players agree to a draw of the match (TR 410.2). -/
def agreedDrawMatch : MatchResult := .draw

/-- **The winner of a conceded match is the other player** (TR 410.2): for a player of the match,
the winner is not the one who conceded. -/
theorem concedeMatch_ne {p q : PlayerId} (hp : p.n < 2) (h : concedeMatch p = .won q) :
    q ≠ p := by
  unfold concedeMatch other at h
  simp only [MatchResult.won.injEq] at h
  subst h
  intro hq
  have := congrArg PlayerId.n hq
  simp at this
  omega

/-- The matches that are run to the end: the games played one after the other. -/
def ofGames (target : Nat) (gs : List (GameResult × PlayerId)) : MatchState :=
  gs.foldl (fun m g => m.record g.1 g.2) (start target)

/-- The match is in order: a positive target, nobody beyond the target at the same time as the
other, and no more wins than games played. -/
structure Inv (m : MatchState) : Prop where
  /-- A match asks for at least one win. -/
  target_pos : 0 < m.target
  /-- Only one of the players can have reached the target. -/
  not_both : m.wins0 < m.target ∨ m.wins1 < m.target
  /-- Every win is a game played. -/
  wins_le : m.wins0 + m.wins1 ≤ m.games

/-- A new match is in order. -/
theorem start_inv {target : Nat} (h : 0 < target) : (start target).Inv :=
  ⟨h, Or.inl h, by simp [start]⟩

/-- **A draw does not count as a win** (TR 404.3): the wins of both players stay. -/
theorem record_draw_wins (m : MatchState) (first : PlayerId) :
    (m.record .draw first).wins0 = m.wins0 ∧ (m.record .draw first).wins1 = m.wins1 := by
  by_cases hf : m.finished = true <;> simp [record, hf]

/-- A draw is a game played. -/
theorem record_draw_games {m : MatchState} (hf : m.finished = false) (first : PlayerId) :
    (m.record .draw first).games = m.games + 1 := by
  simp [record, hf]

/-- A match that is over does not change. -/
theorem record_finished {m : MatchState} (hf : m.finished = true) (r : GameResult)
    (first : PlayerId) : m.record r first = m := by
  simp [record, hf]

/-- The match stays in order after every game. -/
theorem record_inv {m : MatchState} (h : m.Inv) (r : GameResult) (first : PlayerId) :
    (m.record r first).Inv := by
  by_cases hf : m.finished = true
  · rw [record_finished hf]; exact h
  · have hf' : m.finished = false := by simpa using hf
    have h0 : m.wins0 < m.target :=
      Nat.lt_of_not_le (fun hc => hf (by simp [finished, winner, hc]))
    have h1 : m.wins1 < m.target :=
      Nat.lt_of_not_le (fun hc => hf (by
        by_cases h0' : m.target ≤ m.wins0 <;> simp [finished, winner, hc, h0']))
    obtain ⟨hp, -, hw⟩ := h
    unfold record
    simp only [hf', Bool.false_eq_true, ite_false]
    split
    · exact ⟨hp, Or.inl h0, by simp; omega⟩
    · rename_i p
      by_cases p0 : p.n = 0
      · simp only [p0, ite_true]
        exact ⟨hp, Or.inr h1, by simp; omega⟩
      · by_cases p1 : p.n = 1
        · simp only [p1, ite_true]
          exact ⟨hp, Or.inl h0, by simp; omega⟩
        · simp only [p0, p1, ite_false]
          exact ⟨hp, Or.inl h0, by simp; omega⟩
    · exact ⟨hp, Or.inl h0, by simp; omega⟩

/-- **At most one player wins the match**: when both have won enough games the match is not in
order, so in a match that is in order there is at most one winner (TR 404.1). -/
theorem Inv.winner_unique {m : MatchState} (h : m.Inv) :
    ¬ (m.target ≤ m.wins0 ∧ m.target ≤ m.wins1) := by
  have := h.not_both
  omega

/-- A winner has won at least the target, and more than the other player (TR 404.1). -/
theorem Inv.winner_spec {m : MatchState} (h : m.Inv) {p : PlayerId} (hw : m.winner = some p) :
    m.target ≤ m.winsOf p ∧ m.winsOf (other p) < m.target := by
  have hnb := h.not_both
  unfold winner at hw
  split at hw
  · rename_i h0
    simp only [Option.some.injEq] at hw
    subst hw
    simp only [winsOf, other]
    simp
    omega
  · split at hw
    · rename_i h0 h1
      simp only [Option.some.injEq] at hw
      subst hw
      simp only [winsOf, other]
      simp
      omega
    · simp at hw

/-- **Every game of a match that is in order keeps it so**: the match run from the first game, with
any list of results, is in order. -/
theorem ofGames_inv {target : Nat} (h : 0 < target) (gs : List (GameResult × PlayerId)) :
    (ofGames target gs).Inv := by
  unfold ofGames
  have key : ∀ (gs : List (GameResult × PlayerId)) (m : MatchState), m.Inv →
      (gs.foldl (fun m g => m.record g.1 g.2) m).Inv := by
    intro gs
    induction gs with
    | nil => intro m hm; exact hm
    | cons g gs ih => intro m hm; exact ih _ (record_inv hm g.1 g.2)
  exact key gs _ (start_inv h)

/-- **No sideboard before the first game** (TR 403.5). -/
theorem sideboard_not_first (target : Nat) : (start target).sideboardAllowed = false := by
  simp [sideboardAllowed, start]

/-- **No sideboard after a draw** (TR 403.10). -/
theorem sideboard_not_after_draw {m : MatchState} (h : m.last = some .draw) :
    m.sideboardAllowed = false := by
  simp [sideboardAllowed, h]

/-- After a draw, the Battlefields stay and so does the order (TR 406.1.b, 407.4). -/
theorem after_draw {m : MatchState} {f : PlayerId} (h : m.last = some .draw)
    (hf : m.lastFirst = some f) : m.reuseBattlefields = true ∧ m.nextOrder = .same f := by
  simp [reuseBattlefields, nextOrder, h, hf]

/-- After a game that a player won, the other player chooses (TR 407.4). -/
theorem after_win {m : MatchState} {w : PlayerId} (h : m.last = some (.won [w])) :
    m.nextOrder = .loserChooses (other w) := by
  simp [nextOrder, h]

/-- The winner by time is the player with more wins (TR 408.3). -/
theorem onTime_won {m : MatchState} {p : PlayerId} (h : m.onTime = .won p) :
    m.winsOf p > m.winsOf (other p) := by
  unfold onTime at h
  split at h
  · simp only [MatchResult.won.injEq] at h
    subst h
    simp only [winsOf, other]
    simp
    omega
  · split at h
    · simp only [MatchResult.won.injEq] at h
      subst h
      simp only [winsOf, other]
      simp
      omega
    · simp at h

/-- The same number of wins is a draw when the time is up (TR 404.5). -/
theorem onTime_draw_iff (m : MatchState) : m.onTime = .draw ↔ m.wins0 = m.wins1 := by
  unfold onTime
  by_cases h1 : m.wins1 < m.wins0
  · simp [h1] <;> omega
  · by_cases h2 : m.wins0 < m.wins1
    · simp [h1, h2] <;> omega
    · simp [h1, h2] <;> omega

end MatchState

/-- The result of a game that is stopped when the time is up, with the points of the two players
(TR 408.2): the player 2 points ahead wins the game; any other score is a draw. -/
def gameOnTime (points0 points1 : Nat) : GameResult :=
  if points1 + 2 ≤ points0 then .won [⟨0⟩]
  else if points0 + 2 ≤ points1 then .won [⟨1⟩]
  else .draw

/-- **A game stopped by the time is a draw exactly when neither player is 2 points ahead**
(TR 408.2). -/
theorem gameOnTime_draw_iff (a b : Nat) :
    gameOnTime a b = .draw ↔ a < b + 2 ∧ b < a + 2 := by
  unfold gameOnTime
  by_cases h1 : b + 2 ≤ a
  · simp [h1] <;> omega
  · by_cases h2 : a + 2 ≤ b
    · simp [h1, h2] <;> omega
    · simp [h1, h2] <;> omega

/-- A player who wins a game by the time is ahead by at least 2 points (TR 408.2). -/
theorem gameOnTime_won {a b : Nat} {p : PlayerId} (h : gameOnTime a b = .won [p]) :
    (p.n = 0 ∧ b + 2 ≤ a) ∨ (p.n = 1 ∧ a + 2 ≤ b) := by
  unfold gameOnTime at h
  split at h
  · simp only [GameResult.won.injEq, List.cons.injEq, and_true] at h
    subst h
    exact Or.inl ⟨rfl, by omega⟩
  · split at h
    · simp only [GameResult.won.injEq, List.cons.injEq, and_true] at h
      subst h
      exact Or.inr ⟨rfl, by omega⟩
    · simp at h

end Riftbound

end
