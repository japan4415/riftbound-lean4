module

public import Riftbound.Spec.Legal

/-!
# Constructed setup for four seats

The tournament chooses the turn order before the game starts (TR 603.7). This identifies the three
players who contribute a Battlefield (CR 491.5). The engine takes the shuffles, picks and
mulligans as decisions in the normal way.
-/

@[expose] public section

namespace Riftbound

/-- The Legends and Battlefields on one team must have distinct names (CR 491.8.h, 491.8.i). -/
def teamRegistrationOk (db : CardDB) (decks : List ConstructedDeck) (first : Nat) : Bool :=
  (do
    let a ← decks[first]?
    let b ← decks[first + 1]?
    let la ← db.find? a.deck.legend
    let lb ← db.find? b.deck.legend
    let ba ← a.deck.battlefields.mapM db.find?
    let bb ← b.deck.battlefields.mapM db.find?
    return la.nameKey != lb.nameKey && !ba.any (fun card => bb.any (·.nameKey == card.nameKey))
  ).getD false

/-- Start a four-seat Constructed game after the tournament has chosen the turn order. Seats 0
and 1 are the A/B seats of one team, and 2 and 3 are the other team's A/B seats. -/
def GameState.initialTeamConstructed (db : CardDB) (env : LegalityEnv) (order : List PlayerId)
    (registrations : List ConstructedDeck) (ruleSet : RuleSet := .tournament .constructed) :
    Option GameState := do
  if ruleSet.tournamentFormat != some .constructed then none else
  let config : GameConfig := { ruleSet, mode := .teamDuel }
  let s ← GameState.initialConstructed db env config registrations
  if !s.turnOrderAllowed order || !teamRegistrationOk db registrations 0 ||
      !teamRegistrationOk db registrations 2 then none
  else
    let shuffles := s.pending.filter (fun | .chanceShuffle _ => true | _ => false)
    let fields := (order.drop 1).map Frame.chanceBattlefield
    some { s with turnOrder := order, pending := shuffles ++ fields ++ [.setupHands] }

/-- Constructed setup allocates the cards with the normal zone and ownership invariants. -/
theorem GameState.initialConstructed_validState {db : CardDB} {env : LegalityEnv}
    {config : GameConfig} {registrations : List ConstructedDeck} {s : GameState}
    (h : GameState.initialConstructed db env config registrations = some s) :
    s.WF ∧ s.OwnerOk := by
  unfold GameState.initialConstructed at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨base, hbase, rfl⟩ := h
    let start := GameState.empty { config with formatLegality := some env } db
    have hwf : start.WF := GameState.wf_empty _ _
    have hown : start.OwnerOk := GameState.ownerOk_empty _ _
    exact ⟨(GameState.addDecks_wf _ hwf hbase).congr rfl rfl rfl rfl,
      (GameState.addDecks_ownerOk _ hwf hown hbase).congr rfl rfl⟩
  · contradiction

/-- The four-seat start retains the zone and ownership invariants. -/
theorem GameState.initialTeamConstructed_validState {db : CardDB} {env : LegalityEnv}
    {order : List PlayerId} {registrations : List ConstructedDeck} {s : GameState} {ruleSet : RuleSet}
    (h : GameState.initialTeamConstructed db env order registrations ruleSet = some s) :
    s.WF ∧ s.OwnerOk := by
  unfold GameState.initialTeamConstructed at h
  split at h
  · contradiction
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨base, hbase, h⟩ := h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    obtain rfl := h
    have ⟨hwf, hown⟩ := GameState.initialConstructed_validState hbase
    exact ⟨hwf.congr rfl rfl rfl rfl, hown.congr rfl rfl⟩

end Riftbound

end
