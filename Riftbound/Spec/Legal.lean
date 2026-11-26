module

public import Riftbound.Rules.Frames

/-!
# Legality

The specification of which answers are legal, written decision by decision from the Core Rules
(design.md §6.3). `Legal` reads the state and the frame on top of the stack; it does not use `step`
or `applyAction`. The question is the frame; the candidates are computed here from the board.

Chance answers are legal when they are an arrangement of what the rules shuffle, as a
permutation (`List.Perm`): they are not enumerated (design.md §6.4).
-/

@[expose] public section

namespace Riftbound

/-- The players of a game with `n` players, in seat order. -/
def allPlayers (n : Nat) : List PlayerId := (List.range n).map (fun i => ⟨i⟩)

/-- A player is among the players of the game exactly when the seat number is below the count. -/
@[simp] theorem mem_allPlayers (n : Nat) (p : PlayerId) : p ∈ allPlayers n ↔ p.n < n := by
  simp only [allPlayers, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro h; exact ⟨p.n, h, by cases p; rfl⟩

/-- Team play alternates sides (CR 491.5.c). Tournaments specify each team's A/B ordering
(TR 603.7). This checks the team restrictions on a permutation of the seats. -/
def GameState.turnOrderAllowed (s : GameState) (order : List PlayerId) : Bool :=
  let mode := s.config.mode
  if !mode.isTeamDuel then true
  else if s.config.ruleSet.isTournament then
    (Mode.teamTurnOrderChoices (⟨0⟩, ⟨1⟩) (⟨2⟩, ⟨3⟩)).contains order
  else
    match order with
    | [a, b, c, d] => mode.sameSide a c && mode.sameSide b d && !mode.sameSide a b
    | _ => false

/-- `a` is a legal answer to the frame on top of the stack. -/
def LegalFrame (s : GameState) (a : Action) : Prop :=
  match s.pending, a.kind with
  -- the shuffle of a zone (CR 114): an arrangement of its contents
  | .chanceShuffle z :: _, .arrange l =>
    a.actor = .chance ∧ z.Valid s.playerCount ∧ l.Perm (s.zone z)
  -- the random Battlefield of a player (CR 487.5): one of the player's Battlefields
  | .chanceBattlefield p :: _, .pick i =>
    a.actor = .chance ∧ i < (s.zone (.player p .outOfGame)).length
  -- Turn order is a permutation of the seats compatible with the game mode (CR 115, 491.5.c).
  | .chanceTurnOrder :: _, .arrangePlayers l =>
    a.actor = .chance ∧ l.Perm (allPlayers s.playerCount) ∧ s.turnOrderAllowed l = true
  -- the mulligan (CR 117): set aside up to two cards of the hand, or finish
  | .mulligan p n :: _, .mulliganPick c =>
    a.actor = .player p ∧ c ∈ s.zone (.player p .hand) ∧ n < 2
  | .mulligan p _ :: _, .mulliganDone => a.actor = .player p
  -- a discard (CR 415): a card of the hand, or, when the hand is empty or nothing is left to
  -- discard, the end of it
  | .discard p n :: _, .discardPick c =>
    a.actor = .player p ∧ c ∈ s.zone (.player p .hand) ∧ 0 < n
  | .discard p n :: _, .discardDone =>
    a.actor = .player p ∧ (s.zone (.player p .hand) = [] ∨ n = 0)
  -- a "you may" (CR 355): the player says yes or no
  | .mayDo p .. :: _, .decide _ => a.actor = .player p
  | .eitherDo p src env x y _ :: _, .decide yes =>
    a.actor = .player p ∧ eitherOk s p src env x y yes = true
  -- an object chosen while an effect resolves (CR 355): one of the candidates
  | .pickDo p _ _ c more _ _ :: _, .choose o => a.actor = .player p ∧ o ∈ c :: more
  | .guessCardType p .. :: _, .guessCardType guess =>
    a.actor = .player p ∧ guess ∈ CardTypeGuess.choices
  | .nameCard p _ _ c more _ :: _, .nameCard named => a.actor = .player p ∧ named ∈ c :: more
  -- the order of a Recycle to the Main Deck (CR 417.5): an arrangement of the cards set aside
  | .chanceRecycle p :: _, .arrange l =>
    a.actor = .chance ∧ l.Perm (s.zone (.player p .setAside))
  -- the order of the Trash in a Burn Out (CR 432.2.b): an arrangement of the Trash
  | .chanceBurnOut p :: _, .arrange l =>
    a.actor = .chance ∧ l.Perm (s.zone (.player p .trash))
  -- The opponent of a Burn Out is on an opposing side (CR 432.2.c).
  | .chooseBurnOut p :: _, .burnOutTarget opp =>
    a.actor = .player p ∧ s.config.mode.sameSide p opp = false ∧ opp.n < s.playerCount
  -- the turn player has priority in the Main Phase (CR 312, 316): passing ends the phase (CR 305)
  | .priority p :: _, .pass => a.actor = .player p
  -- a Basic Rune of the player's on the Base adds a resource (CR 164.2, 430)
  | .priority p :: _, .runeAbility c ab =>
    a.actor = .player p ∧ c ∈ s.zone (.player p .base) ∧ runeUsable s p c ab = true
  -- a Unit or Gear from hand, or a Spell with targets from hand or via Flow, in the Main Phase
  -- (CR 349-359, 829)
  | .priority p :: _, .playCard c pay ts flow discard pick =>
    a.actor = .player p ∧ c ∈ s.playSources p ∧
      PlayOk s p c pay ts flow pick ∧ s.playDiscardOk p c discard = true
  -- a Standard Move of a Unit of the player's, in the Main Phase (CR 144)
  | .priority p :: _, .standardMove u d pay =>
    a.actor = .player p ∧ moveOk s p u d = true ∧ pay ∈ s.standardMovePayments p d
  -- an activated ability of an object the player controls, paid for from the Rune Pool, when the
  -- Chain is empty (CR 361, 363, 356-357)
  | .priority p :: _, .activate src idx pay ts discards targetPlayer costBanisher costObject =>
    a.actor = .player p ∧ activatable s p src idx pay ts true discards targetPlayer costObject = true ∧
      costBanisher ∈ activationBanisherOptions s src idx ts costObject
  -- the player with priority passes while the Chain holds an item (CR 311-313)
  | .chainPass p _ :: _, .pass => a.actor = .player p
  -- in answer to the Chain: a play with Reaction from a permitted zone (CR 813, 829)
  | .chainPass p _ :: _, .playCard c pay ts flow discard pick =>
    a.actor = .player p ∧ c ∈ s.playSources p ∧
      reactable s p c pay ts flow pick = true ∧ s.playDiscardOk p c discard = true
  -- in answer to the Chain: an activated ability with Reaction (CR 813)
  | .chainPass p _ :: _, .activate src idx pay ts discards targetPlayer costBanisher costObject =>
    a.actor = .player p ∧ activatable s p src idx pay ts false discards targetPlayer costObject = true ∧
      costBanisher ∈ activationBanisherOptions s src idx ts costObject
  -- in answer to the Chain: a Basic Rune adds a resource (CR 164.2, 430)
  | .chainPass p _ :: _, .runeAbility c ab =>
    a.actor = .player p ∧ c ∈ s.zone (.player p .base) ∧ runeUsable s p c ab = true
  -- one of the abilities that wait goes on the Chain, with its targets (CR 383.3.d, 355)
  | .triggerOrder p t more _ funding :: _, .putTrigger i ts payment =>
    a.actor = .player p ∧ triggerFinishOk s (t :: more) funding i ts payment = true
  | .triggerOrder p t more _ none :: _, .prepareTrigger i ts payment =>
    a.actor = .player p ∧ ((t :: more)[i]?.any (fun g => triggerPreparation s g ts payment)) = true
  | .triggerOrder p t more _ (some plan) :: _, .triggerAdd add =>
    a.actor = .player p ∧ add ∈ triggerFundingAdds s (t :: more) plan
  | .triggerOrder p _ _ _ (some _) :: _, .decide yes =>
    a.actor = .player p ∧ yes = false
  -- an Add ability resolves at once, with the Chain empty or not (CR 430)
  | .priority p :: _, .manaAbility src idx pay chosen =>
    a.actor = .player p ∧ manaOk s p src idx pay chosen = true
  | .chainPass p _ :: _, .manaAbility src idx pay chosen =>
    a.actor = .player p ∧ manaOk s p src idx pay chosen = true
  -- the player with Focus passes in a Showdown (CR 347-348)
  | .showdown _ q _ :: _, .pass => a.actor = .player q
  -- in a Showdown: a Spell with Action, or a card with Reaction (CR 806, 813, 829)
  | .showdown _ q _ :: _, .playCard c pay ts flow discard pick =>
    a.actor = .player q ∧ c ∈ s.playSources q ∧
      showdownable s q c pay ts flow pick = true ∧ s.playDiscardOk q c discard = true
  -- in a Showdown: an activated ability with Action or Reaction (CR 806, 813)
  | .showdown _ q _ :: _, .activate src idx pay ts discards targetPlayer costBanisher costObject =>
    a.actor = .player q ∧ activatableSD s q src idx pay ts discards targetPlayer costObject = true ∧
      costBanisher ∈ activationBanisherOptions s src idx ts costObject
  -- in a Showdown: a Basic Rune adds a resource (CR 164.2, 430)
  | .showdown _ q _ :: _, .runeAbility c ab =>
    a.actor = .player q ∧ c ∈ s.zone (.player q .base) ∧ runeUsable s q c ab = true
  -- in a Showdown: an Add ability resolves at once (CR 430)
  | .showdown _ q _ :: _, .manaAbility src idx pay chosen =>
    a.actor = .player q ∧ manaOk s q src idx pay chosen = true
  -- the next Unit to be given lethal damage, Tank Units first (CR 467.2.c, 815)
  | .assign bf _ side acc _ :: _, .assignPick u =>
    a.actor = .player side ∧ s.pickOk bf side acc u = true
  -- every Unit of the other side is named (CR 467.2.c)
  | .assign bf _ side acc _ :: _, .assignDone =>
    a.actor = .player side ∧ s.doneOk bf side acc = true
  -- The clock calls time once, in a two-sided Tournament game after the first turn starts (TR 408.2).
  | _, .timeCalled =>
    a.actor = .clock ∧ s.config.ruleSet.isTournament = true ∧ s.config.mode.hasTwoSides = true ∧
      s.clock = none ∧ s.active.isSome = true
  -- the judge declares a draw, whatever question is open, under the Tournament Rules: the players
  -- agree to it (TR 410.1), or a loop has no end (TR 505.6)
  | _, .declareDraw => a.actor = .judge ∧ s.config.ruleSet.isTournament = true
  -- Predict: choose a remaining inspected card to keep next on top or Recycle (CR 437).
  | .predict p _ c cs _ _ :: _, .predictPick id _ => a.actor = .player p ∧ id ∈ c :: cs
  -- The simultaneous Recycle goes to the bottom in random order (CR 417.5).
  | .chancePredict _ _ _ bottom :: _, .arrange l => a.actor = .chance ∧ l.Perm bottom
  -- Basic Runes and Reaction Add abilities can supply a cost during resolution (CR 445.2.c).
  | .eitherDo p _ _ first _ _ :: _, .runeAbility c ab =>
    a.actor = .player p ∧ c ∈ s.zone (.player p .base) ∧ runeUsable s p c ab = true ∧
      first.isPayment = true
  | .eitherDo p _ _ first _ _ :: _, .manaAbility src idx pay chosen =>
    a.actor = .player p ∧ manaOk s p src idx pay chosen = true ∧ first.isPayment = true
  -- The turn player may invite their teammate to cast a spell or use an ability (CR 316.5.b.1, 491.8.a).
  | .priority p :: _, .inviteTeammate guest => a.actor = .player p ∧ s.teamInvitee p = some guest
  | .teamInvitation guest :: _, .pass => a.actor = .player guest
  | .teamInvitation guest :: _, .playCard c pay ts flow discard pick =>
    a.actor = .player guest ∧ c ∈ s.playSources guest ∧
      castable s guest c pay ts flow pick = true ∧ s.playDiscardOk guest c discard = true
  | .teamInvitation guest :: _, .activate src idx pay ts discards targetPlayer costBanisher costObject =>
    a.actor = .player guest ∧ activatable s guest src idx pay ts true discards targetPlayer costObject = true ∧
      costBanisher ∈ activationBanisherOptions s src idx ts costObject
  | .teamInvitation guest :: _, .runeAbility c ab =>
    a.actor = .player guest ∧ c ∈ s.zone (.player guest .base) ∧ runeUsable s guest c ab = true
  | .teamInvitation guest :: _, .manaAbility src idx pay chosen =>
    a.actor = .player guest ∧ manaOk s guest src idx pay chosen = true
  | .chooseShowdown p first more :: _, .choose bf =>
    a.actor = .player p ∧ ((first :: more).lookup bf).isSome = true
  -- A group has one destination and at least two distinct Units (CR 144.3).
  | .priority p :: _, .startGroupMove dest pay =>
    a.actor = .player p ∧ dest ∈ s.destinations ∧ 2 ≤ (s.groupMoveChoices p dest).length ∧
      pay ∈ s.standardMovePayments p dest
  | .groupMove p dest _ units :: _, .choose u =>
    a.actor = .player p ∧ u ∈ s.groupMoveChoices p dest ∧ u ∉ units
  | .groupMove p _ _ _ :: _, .decide false => a.actor = .player p
  | .groupMove p dest pay units :: _, .decide true =>
    a.actor = .player p ∧ s.groupMoveReady p dest pay units = true
  | _, _ => False

instance LegalFrame.decidable (s : GameState) (a : Action) : Decidable (LegalFrame s a) := by
  unfold LegalFrame
  split <;> infer_instance

/-- A seat can concede if it is still participating and an opposing player or side will
remain in the game (CR 649–651). -/
def GameState.canConcede (s : GameState) (p : PlayerId) : Prop :=
  if s.config.mode.isFreeForAll then
    s.participates p = true ∧ (s.withdrawSeat p).participatingSeats ≠ []
  else p.n < s.playerCount ∧ s.config.mode.hasTwoSides = true

instance GameState.canConcedeDecidable (s : GameState) (p : PlayerId) : Decidable (s.canConcede p) := by
  unfold GameState.canConcede
  split <;> infer_instance

/-- An eligible concession comes from a registered seat. -/
theorem GameState.canConcede_registered {s : GameState} {p : PlayerId} (h : s.canConcede p) :
    p.n < s.playerCount := by
  unfold GameState.canConcede at h
  split at h
  · exact of_decide_eq_true (Bool.and_eq_true_iff.mp h.1).1
  · exact h.1

/-- An eligible player may concede independently of the open decision (CR 649–651). -/
def LegalConcede (s : GameState) (a : Action) : Prop :=
  a.kind = .concede ∧
    match a.actor with
    | .player p => s.canConcede p
    | _ => False

instance LegalConcede.decidable (s : GameState) (a : Action) : Decidable (LegalConcede s a) := by
  unfold LegalConcede
  split <;> infer_instance

/-- A legal concession names a seat eligible to concede. -/
theorem LegalConcede.actor {s : GameState} {a : Action} (h : LegalConcede s a) :
    ∃ p, a.actor = .player p ∧ s.canConcede p := by
  obtain ⟨-, h2⟩ := h
  cases hac : a.actor with
  | player p =>
    rw [hac] at h2
    exact ⟨p, rfl, h2⟩
  | chance => rw [hac] at h2; exact h2.elim
  | clock => rw [hac] at h2; exact h2.elim
  | judge => rw [hac] at h2; exact h2.elim

/-- `a` is a legal answer: the game is not over, and the answer is to the open question or a
concession. -/
def Legal (s : GameState) (a : Action) : Prop :=
  s.result = none ∧ (LegalFrame s a ∨ LegalConcede s a)

instance Legal.decidable (s : GameState) (a : Action) : Decidable (Legal s a) := by
  unfold Legal
  infer_instance

/-- A legal answer that is not a concession answers the open question. -/
theorem Legal.frame {s : GameState} {a : Action} (h : Legal s a) (hk : a.kind ≠ .concede) :
    LegalFrame s a := by
  rcases h.2 with h2 | h2
  · exact h2
  · exact absurd h2.1 hk

/-- A legal concession. -/
theorem Legal.of_concede {s : GameState} {a : Action} (h : Legal s a) (hk : a.kind = .concede) :
    LegalConcede s a := by
  rcases h.2 with h2 | h2
  · -- a frame answer never concedes
    exfalso
    unfold LegalFrame at h2
    rw [hk] at h2
    split at h2 <;> first | exact h2.elim | simp_all
  · exact h2

end Riftbound

end
