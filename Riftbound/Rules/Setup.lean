module

public import Riftbound.Rules.Add
public import Riftbound.Rules.Deck

/-!
# Setting up a game

The state a game starts from (CR 110-118). The cards of each deck become objects: the Legend goes
to the Legend Zone (CR 111), the Chosen Champion to the Champion Zone (CR 112), the Battlefields
to `outOfGame` until one is picked (CR 113), the rest of the Main Deck and the Rune Deck to their
decks, in the order of the lists. The shuffles, the Battlefield picks, the turn order, the
opening hands and the mulligans are not done here: they are frames on the stack, which the
engine works through (design.md §6.2).
-/

@[expose] public section

namespace Riftbound

/-- A card as an object: a physical card of its own, owned and controlled by `owner`. -/
def newCard (s : GameState) (owner : PlayerId) (c : CardId) : Object :=
  { kind := .card ⟨s.nextId⟩ c, owner := owner, controller := owner, timestamp := ⟨0⟩ }

/-- Add cards to a zone, the first card first (so a deck's head is its top). -/
def addCards (owner : PlayerId) (z : Zone) : GameState → List CardId → Option GameState
  | s, [] => some s
  | s, c :: cs => do
    let r ← addObject s (newCard s owner c) z .bottom
    addCards owner z r.1 cs

/-- Add the cards of one player's deck. -/
def GameState.addDeck (s : GameState) (p : PlayerId) (d : Deck) : Option GameState := do
  let s ← addCards p (.player p .legendZone) s [d.legend]
  let s ← addCards p (.player p .championZone) s [d.chosenChampion]
  let s ← addCards p (.player p .mainDeck) s (d.main.erase d.chosenChampion)
  let s ← addCards p (.player p .runeDeck) s d.runes
  addCards p (.player p .outOfGame) s d.battlefields

/-- Add the decks of the players, seat 0 first. -/
def GameState.addDecks : GameState → Nat → List Deck → Option GameState
  | s, _, [] => some s
  | s, i, d :: ds => do
    let s ← s.addDeck ⟨i⟩ d
    s.addDecks (i + 1) ds

/-- The frames of the setup: the shuffles, the Battlefield picks and the turn order (CR 113-115).
The first frame is the first to be answered. Answering the turn order puts the opening hands and
the mulligans on the stack (CR 116-117), so they are never laid out before the turn order is
known. -/
def startFrames (n : Nat) : List Frame :=
  (List.range n).flatMap (fun i =>
    [Frame.chanceShuffle (.player ⟨i⟩ .mainDeck),
      Frame.chanceShuffle (.player ⟨i⟩ .runeDeck)]) ++
  (List.range n).map (fun i => Frame.chanceBattlefield ⟨i⟩) ++
  [Frame.chanceTurnOrder]

/-- The state a game starts from. `none` if the number of decks is not the number of players, or
a card cannot be placed. -/
def GameState.initial (config : GameConfig) (decks : List Deck) : Option GameState :=
  if decks.length = config.mode.players then
    ((GameState.empty config).addDecks 0 decks).map
      (fun s => { s with pending := startFrames config.mode.players })
  else none

/-- Adding cards keeps the game well formed. -/
theorem addCards_wf (owner : PlayerId) (z : Zone) :
    ∀ (cs : List CardId) {s s' : GameState}, s.WF → addCards owner z s cs = some s' → s'.WF
  | [], s, s', hwf, h => by
    rw [show addCards owner z s [] = some s from rfl] at h
    cases h
    exact hwf
  | c :: cs, s, s', hwf, h => by
    cases hr : addObject s (newCard s owner c) z .bottom with
    | none => simp [addCards, hr] at h
    | some r =>
      have h' : addCards owner z r.1 cs = some s' := by simpa [addCards, hr] using h
      exact addCards_wf owner z cs (addObject_wf hwf hr) h'

/-- Adding a deck keeps the game well formed. -/
theorem GameState.addDeck_wf {s s' : GameState} {p : PlayerId} {d : Deck} (hwf : s.WF)
    (h : s.addDeck p d = some s') : s'.WF := by
  unfold GameState.addDeck at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s1, h1, s2, h2, s3, h3, s4, h4, h5⟩ := h
  exact addCards_wf _ _ _ (addCards_wf _ _ _ (addCards_wf _ _ _ (addCards_wf _ _ _
    (addCards_wf _ _ _ hwf h1) h2) h3) h4) h5

/-- Adding the decks keeps the game well formed. -/
theorem GameState.addDecks_wf :
    ∀ (ds : List Deck) {s s' : GameState} {i : Nat}, s.WF → s.addDecks i ds = some s' → s'.WF
  | [], s, s', i, hwf, h => by
    rw [show s.addDecks i [] = some s from rfl] at h
    cases h
    exact hwf
  | d :: ds, s, s', i, hwf, h => by
    cases hr : s.addDeck ⟨i⟩ d with
    | none => simp [GameState.addDecks, hr] at h
    | some s1 =>
      have h' : s1.addDecks (i + 1) ds = some s' := by simpa [GameState.addDecks, hr] using h
      exact GameState.addDecks_wf ds (GameState.addDeck_wf hwf hr) h'

/-- A game that has been set up is well formed. -/
theorem GameState.initial_wf {config : GameConfig} {decks : List Deck} {s : GameState}
    (h : GameState.initial config decks = some s) : s.WF := by
  unfold GameState.initial at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    exact GameState.WF.congr (GameState.addDecks_wf decks (GameState.wf_empty config) h1)
      rfl rfl rfl rfl
  · exact absurd h (by simp)

/-- Adding cards keeps `OwnerOk`. -/
theorem addCards_ownerOk (owner : PlayerId) (z : Zone) :
    ∀ (cs : List CardId) {s s' : GameState}, s.WF → s.OwnerOk →
      addCards owner z s cs = some s' → s'.OwnerOk
  | [], s, s', _, hown, h => by
    rw [show addCards owner z s [] = some s from rfl] at h
    cases h
    exact hown
  | c :: cs, s, s', hwf, hown, h => by
    cases hr : addObject s (newCard s owner c) z .bottom with
    | none => simp [addCards, hr] at h
    | some r =>
      have h' : addCards owner z r.1 cs = some s' := by simpa [addCards, hr] using h
      exact addCards_ownerOk owner z cs (addObject_wf hwf hr) (addObject_ownerOk hwf hown hr) h'

/-- Adding a deck keeps `OwnerOk`. -/
theorem GameState.addDeck_ownerOk {s s' : GameState} {p : PlayerId} {d : Deck} (hwf : s.WF)
    (hown : s.OwnerOk) (h : s.addDeck p d = some s') : s'.OwnerOk := by
  unfold GameState.addDeck at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s1, h1, s2, h2, s3, h3, s4, h4, h5⟩ := h
  have w1 := addCards_wf _ _ _ hwf h1
  have w2 := addCards_wf _ _ _ w1 h2
  have w3 := addCards_wf _ _ _ w2 h3
  have w4 := addCards_wf _ _ _ w3 h4
  exact addCards_ownerOk _ _ _ w4
    (addCards_ownerOk _ _ _ w3 (addCards_ownerOk _ _ _ w2
      (addCards_ownerOk _ _ _ w1 (addCards_ownerOk _ _ _ hwf hown h1) h2) h3) h4) h5

/-- Adding the decks keeps `OwnerOk`. -/
theorem GameState.addDecks_ownerOk :
    ∀ (ds : List Deck) {s s' : GameState} {i : Nat}, s.WF → s.OwnerOk →
      s.addDecks i ds = some s' → s'.OwnerOk
  | [], s, s', i, _, hown, h => by
    rw [show s.addDecks i [] = some s from rfl] at h
    cases h
    exact hown
  | d :: ds, s, s', i, hwf, hown, h => by
    cases hr : s.addDeck ⟨i⟩ d with
    | none => simp [GameState.addDecks, hr] at h
    | some s1 =>
      have h' : s1.addDecks (i + 1) ds = some s' := by simpa [GameState.addDecks, hr] using h
      exact GameState.addDecks_ownerOk ds (GameState.addDeck_wf hwf hr)
        (GameState.addDeck_ownerOk hwf hown hr) h'

/-- A game with no objects satisfies `OwnerOk`. -/
theorem GameState.ownerOk_empty (config : GameConfig) : (GameState.empty config).OwnerOk := by
  refine ⟨fun p k hk id hid o ho => ?_⟩
  have : (GameState.empty config).zone (.player p k) = [] := by
    simp [GameState.zone, GameState.empty]
  rw [this] at hid
  simp at hid

/-- A game that has been set up satisfies `OwnerOk`. -/
theorem GameState.initial_ownerOk {config : GameConfig} {decks : List Deck} {s : GameState}
    (h : GameState.initial config decks = some s) : s.OwnerOk := by
  unfold GameState.initial at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    exact (GameState.addDecks_ownerOk decks (GameState.wf_empty config)
      (GameState.ownerOk_empty config) h1).congr rfl rfl
  · exact absurd h (by simp)

end Riftbound

end
