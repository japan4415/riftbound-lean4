module

public import Riftbound.Spec.Legal

/-!
# Tournament setup for four seats

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

/-- The rules-only Battlefield available to Limited decks (TR 602.3.d). -/
def limitedBlankBattlefield : CardDef :=
  { id := ⟨"TKN-LimitedBlank"⟩, name := "Blank Battlefield", types := [.battlefield], status := .full }

/-- Include the blank Battlefield in the definitions available to Limited games. -/
def CardDB.withLimitedBlank (db : CardDB) : CardDB :=
  if (db.find? limitedBlankBattlefield.id).isSome then db
  else ⟨db.cards ++ [limitedBlankBattlefield]⟩

/-- In Sealed, either Legend slot may be empty. Blank Battlefields have no competitive name. -/
def teamSealedRegistrationOk (db : CardDB) (a b : LimitedDeck) : Bool :=
  (do
    let a ← a.resolve db
    let b ← b.resolve db
    let sameLegend := a.legend.any (fun card => b.legend.any (fun other =>
      CardDef.nameKey other == CardDef.nameKey card))
    return !sameLegend && !a.battlefields.any (fun (card : CardDef) =>
      card.id != limitedBlankBattlefield.id &&
        b.battlefields.any (fun other => CardDef.nameKey other == card.nameKey))
  ).getD false

/-- Arrange the common shuffles, Battlefield answers and opening hands of a team game. -/
def GameState.teamSetupOrder (s : GameState) (order : List PlayerId) : GameState :=
  let shuffles := s.pending.filter (fun | .chanceShuffle _ => true | _ => false)
  let fields := (order.drop 1).map Frame.chanceBattlefield
  { s with turnOrder := order, pending := shuffles ++ fields ++ [.setupHands] }

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
  else some (s.teamSetupOrder order)

/-- Start a four-seat Sealed game (TR 603.6). The first seat does not contribute a Battlefield
(CR 491.5). -/
def GameState.initialTeamSealed (db : CardDB) (env : LegalityEnv) (order : List PlayerId)
    (decks : List LimitedDeck) (ruleSet : RuleSet := .tournament .sealed) : Option GameState := do
  let [a, b, c, d] := decks | none
  let config : GameConfig := { ruleSet, mode := .teamDuel, formatLegality := some env }
  let s := GameState.empty config db
  if ruleSet.tournamentFormat != some .sealed || !s.turnOrderAllowed order ||
      !decks.all (fun deck => decide (SealedDeckValid db env deck)) ||
      !teamSealedRegistrationOk db a b || !teamSealedRegistrationOk db c d ||
      !(order.drop 1).all (fun p => decks[p.n]?.any (!·.battlefields.isEmpty)) then none
  else
    let s ← s.addLimitedDecks db 0 decks
    let start := { s with pending := startFrames config.mode.players }
    some (start.teamSetupOrder order)

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

/-- The Sealed start retains the zone and ownership invariants. -/
theorem GameState.initialTeamSealed_validState {db : CardDB} {env : LegalityEnv}
    {order : List PlayerId} {decks : List LimitedDeck} {s : GameState} {ruleSet : RuleSet}
    (h : GameState.initialTeamSealed db env order decks ruleSet = some s) :
    s.WF ∧ s.OwnerOk := by
  unfold GameState.initialTeamSealed at h
  split at h
  · dsimp only at h
    split at h
    · contradiction
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨base, hb, rfl⟩ := h
      have hwf := GameState.wf_empty
        { ruleSet, mode := Mode.teamDuel, formatLegality := some env } db
      have hown := GameState.ownerOk_empty
        { ruleSet, mode := Mode.teamDuel, formatLegality := some env } db
      exact ⟨(GameState.addLimitedDecks_wf _ hwf hb).congr rfl rfl rfl rfl,
        (GameState.addLimitedDecks_ownerOk _ hwf hown hb).congr rfl rfl⟩
  · contradiction

end Riftbound

end
