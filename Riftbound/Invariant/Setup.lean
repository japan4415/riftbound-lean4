module

public import Riftbound.Invariant.Progress

/-!
# The set-up game

What a game that was set up from legal decks looks like (CR 101-103, 110-113): it has at least two
players, and every player's Battlefields are waiting to be picked from. This is what makes the
random Battlefield pick (CR 487.5) always possible, and so closes the last gap in progress (I5).
-/

@[expose] public section

namespace Riftbound

/-- A state grows into another: the rules stay, and no zone gets shorter. -/
structure Grows (s s' : GameState) : Prop where
  /-- The rules are the same. -/
  config : s'.config = s.config
  /-- No zone loses a card. -/
  zone : ∀ z, (s.zone z).length ≤ (s'.zone z).length

/-- Growing is reflexive. -/
theorem Grows.refl (s : GameState) : Grows s s := ⟨rfl, fun _ => Nat.le_refl _⟩

/-- Growing is transitive. -/
theorem Grows.trans {s s' s'' : GameState} (h1 : Grows s s') (h2 : Grows s' s'') :
    Grows s s'' :=
  ⟨h2.config.trans h1.config, fun z => Nat.le_trans (h1.zone z) (h2.zone z)⟩

/-- Putting an object into a list makes it one longer. -/
theorem Pos.length_insert (pos : Pos) (id : ObjId) (l : List ObjId) :
    (pos.insert id l).length = l.length + 1 :=
  (Pos.insert_perm pos id l).length_eq

/-- Adding an object grows the state, and the zone it goes to gets one longer. -/
theorem addObject_grows {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (h : addObject s o z pos = some (s', id)) :
    Grows s s' ∧ (s'.zone z).length = (s.zone z).length + 1 := by
  unfold addObject at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hself : ∀ z', z' = z → (({ s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z)) with
        objects := s.objects.insert s.nextId { o with timestamp := ⟨s.nextTimestamp⟩ },
        nextId := s.nextId + 1, nextTimestamp := s.nextTimestamp + 1 } : GameState).zone z').length
        = (s.zone z).length + 1 := by
      intro z' hz'
      subst hz'
      show ((s.setZone z' _).zone z').length = _
      rw [GameState.zone_setZone_self]
      exact Pos.length_insert _ _ _
    refine ⟨⟨rfl, fun z' => ?_⟩, hself z rfl⟩
    by_cases hz : z' = z
    · rw [hself z' hz, hz]; omega
    · show (s.zone z').length ≤ ((s.setZone z _).zone z').length
      rw [GameState.zone_setZone_ne s hz]
      exact Nat.le_refl _
  · exact absurd h (by simp)

/-- Adding cards grows the state, and the zone they go to gets as many cards longer. -/
theorem addCards_grows {db : CardDB} (owner : PlayerId) (z : Zone) :
    ∀ (cs : List CardId) {s s' : GameState}, addCards db owner z s cs = some s' →
      Grows s s' ∧ (s'.zone z).length = (s.zone z).length + cs.length
  | [], s, s', h => by
    rw [show addCards db owner z s [] = some s from rfl] at h
    cases h
    exact ⟨Grows.refl _, by simp⟩
  | c :: cs, s, s', h => by
    cases hr : addObject s (newCard db s owner c) z .bottom with
    | none => simp [addCards, hr] at h
    | some r =>
      have h' : addCards db owner z r.1 cs = some s' := by simpa [addCards, hr] using h
      obtain ⟨g1, l1⟩ := addObject_grows hr
      obtain ⟨g2, l2⟩ := addCards_grows owner z cs h'
      refine ⟨g1.trans g2, ?_⟩
      rw [l2, l1]
      simp
      omega

/-- Adding a deck grows the state, and the player's Battlefields go out of the game. -/
theorem GameState.addDeck_grows {db : CardDB} {s s' : GameState} {p : PlayerId} {d : Deck}
    (h : s.addDeck db p d = some s') :
    Grows s s' ∧ d.battlefields.length ≤ (s'.zone (.player p .outOfGame)).length := by
  unfold GameState.addDeck at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s1, h1, s2, h2, s3, h3, s4, h4, h5⟩ := h
  obtain ⟨g1, -⟩ := addCards_grows _ _ _ h1
  obtain ⟨g2, -⟩ := addCards_grows _ _ _ h2
  obtain ⟨g3, -⟩ := addCards_grows _ _ _ h3
  obtain ⟨g4, -⟩ := addCards_grows _ _ _ h4
  obtain ⟨g5, l5⟩ := addCards_grows _ _ _ h5
  exact ⟨(((g1.trans g2).trans g3).trans g4).trans g5, by omega⟩

/-- Adding the decks grows the state, and the player in seat `i + k` has the Battlefields of the
`k`-th deck out of the game. -/
theorem GameState.addDecks_grows {db : CardDB} :
    ∀ (ds : List Deck) {s s' : GameState} {i : Nat}, s.addDecks db i ds = some s' →
      Grows s s' ∧ ∀ k (hk : k < ds.length),
        (ds[k]).battlefields.length ≤ (s'.zone (.player ⟨i + k⟩ .outOfGame)).length
  | [], s, s', i, h => by
    rw [show s.addDecks db i [] = some s from rfl] at h
    cases h
    exact ⟨Grows.refl _, fun k hk => absurd hk (by simp)⟩
  | d :: ds, s, s', i, h => by
    cases hr : s.addDeck db ⟨i⟩ d with
    | none => simp [GameState.addDecks, hr] at h
    | some s1 =>
      have h' : s1.addDecks db (i + 1) ds = some s' := by simpa [GameState.addDecks, hr] using h
      obtain ⟨g1, b1⟩ := GameState.addDeck_grows hr
      obtain ⟨g2, b2⟩ := GameState.addDecks_grows ds h'
      refine ⟨g1.trans g2, fun k hk => ?_⟩
      cases k with
      | zero => exact Nat.le_trans b1 (g2.zone _)
      | succ k =>
        have := b2 k (by simpa using hk)
        have e : i + 1 + k = i + (k + 1) := by omega
        rw [e] at this
        simpa using this

/-- Adding a Limited deck grows the state, and the player's Battlefields go out of the game. -/
theorem GameState.addLimitedDeck_grows {db : CardDB} {s s' : GameState} {p : PlayerId}
    {d : LimitedDeck}
    (h : s.addLimitedDeck db p d = some s') :
    Grows s s' ∧ d.battlefields.length ≤ (s'.zone (.player p .outOfGame)).length := by
  unfold GameState.addLimitedDeck at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s1, h1, s2, h2, s3, h3, s4, h4, h5⟩ := h
  obtain ⟨g1, -⟩ := addCards_grows _ _ _ h1
  obtain ⟨g2, -⟩ := addCards_grows _ _ _ h2
  obtain ⟨g3, -⟩ := addCards_grows _ _ _ h3
  obtain ⟨g4, -⟩ := addCards_grows _ _ _ h4
  obtain ⟨g5, l5⟩ := addCards_grows _ _ _ h5
  exact ⟨(((g1.trans g2).trans g3).trans g4).trans g5, by omega⟩

/-- Adding the Limited decks grows the state, and the player in seat `i + k` has the Battlefields
of the `k`-th deck out of the game. -/
theorem GameState.addLimitedDecks_grows {db : CardDB} :
    ∀ (ds : List LimitedDeck) {s s' : GameState} {i : Nat},
      s.addLimitedDecks db i ds = some s' → Grows s s' ∧ ∀ k (hk : k < ds.length),
        (ds[k]).battlefields.length ≤ (s'.zone (.player ⟨i + k⟩ .outOfGame)).length
  | [], s, s', i, h => by
    rw [show s.addLimitedDecks db i [] = some s from rfl] at h
    cases h
    exact ⟨Grows.refl _, fun k hk => absurd hk (by simp)⟩
  | d :: ds, s, s', i, h => by
    cases hr : s.addLimitedDeck db ⟨i⟩ d with
    | none => simp [GameState.addLimitedDecks, hr] at h
    | some s1 =>
      have h' : s1.addLimitedDecks db (i + 1) ds = some s' := by
        simpa [GameState.addLimitedDecks, hr] using h
      obtain ⟨g1, b1⟩ := GameState.addLimitedDeck_grows hr
      obtain ⟨g2, b2⟩ := GameState.addLimitedDecks_grows ds h'
      refine ⟨g1.trans g2, fun k hk => ?_⟩
      cases k with
      | zero => exact Nat.le_trans b1 (g2.zone _)
      | succ k =>
        have := b2 k (by simpa using hk)
        have e : i + 1 + k = i + (k + 1) := by omega
        rw [e] at this
        simpa using this

/-- Looking up every card of a list gives a list of the same length. -/
theorem mapM_find_length (db : CardDB) :
    ∀ (l : List CardId) {bs : List CardDef}, l.mapM db.find? = some bs → bs.length = l.length
  | [], bs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | c :: cs, bs, h => by
    cases hc : db.find? c with
    | none => simp [List.mapM_cons, hc] at h
    | some x =>
      cases hr : cs.mapM db.find? with
      | none => simp [List.mapM_cons, hc, hr] at h
      | some ys =>
        simp [List.mapM_cons, hc, hr] at h
        subst h
        simp [mapM_find_length db cs hr]

/-- A legal deck has as many Battlefield cards as the mode asks for (CR 103.5). -/
theorem DeckValid.battlefields_length {db : CardDB} {mode : Mode} {d : Deck}
    (h : DeckValid db mode d) : d.battlefields.length = mode.deckBattlefields := by
  obtain ⟨r, hr, hv⟩ := h.exists_resolved
  unfold Deck.resolve at hr
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
  obtain ⟨l, -, m, -, ma, -, ru, -, bf, hbf, hfin⟩ := hr
  simp only [Option.pure_def, Option.some.injEq] at hfin
  subst hfin
  rw [← mapM_find_length db _ hbf]
  exact hv.2.2.2.2.2.2.2.2.1

/-- **A game set up from legal decks.** It has at least two players, and every player has a
Battlefield out of the game, waiting for the random pick (CR 487.5). -/
theorem GameState.initial_setup {db : CardDB} {config : GameConfig} {decks : List Deck}
    {s : GameState} (h : GameState.initial db config decks = some s) :
    2 ≤ s.playerCount ∧ ∀ p : PlayerId, p.n < s.playerCount →
      0 < (s.zone (.player p .outOfGame)).length := by
  unfold GameState.initial at h
  split at h
  · rename_i hc
    obtain ⟨hlen, hcfg, hdecks⟩ := hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    obtain ⟨g, hb⟩ := GameState.addDecks_grows decks h1
    have hcount : s1.playerCount = config.mode.players := by
      simp [GameState.playerCount, g.config, GameState.empty]
    refine ⟨?_, fun p hp => ?_⟩
    · show 2 ≤ s1.playerCount
      rw [hcount]
      exact hcfg.1
    · change p.n < s1.playerCount at hp
      rw [hcount, ← hlen] at hp
      have h2 := hb p.n hp
      rw [Nat.zero_add] at h2
      have h3 := (hdecks _ (List.getElem_mem hp)).battlefields_length
      have h4 : 0 < decks[p.n].battlefields.length := by rw [h3]; exact hcfg.2
      exact Nat.lt_of_lt_of_le h4 h2
  · exact absurd h (by simp)

/-- Every frame of the setup is a setup frame. -/
theorem startFrames_isSetup (n : Nat) : ∀ f ∈ startFrames n, f.isSetup = true := by
  intro f hf
  simp only [startFrames, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hf
  rcases hf with (⟨i, -, rfl | rfl⟩ | ⟨i, -, rfl⟩) | rfl <;> rfl

/-- The shuffles of the setup are of zones of the game. -/
theorem startFrames_valid {n : Nat} {z : Zone} (h : Frame.chanceShuffle z ∈ startFrames n) :
    z.Valid n := by
  simp only [startFrames, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at h
  rcases h with (⟨i, hi, h | h⟩ | ⟨i, -, h⟩) | h
  · cases h
    simp [Zone.Valid, allZones, hi, ZoneKind.all]
  · cases h
    simp [Zone.Valid, allZones, hi, ZoneKind.all]
  · cases h
  · cases h

/-- The shuffles of the setup are all different. -/
theorem shuffles_nodup (n : Nat) :
    ((List.range n).flatMap (fun i =>
      [Frame.chanceShuffle (.player ⟨i⟩ .mainDeck),
        Frame.chanceShuffle (.player ⟨i⟩ .runeDeck)])).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx y hy hxy
    subst hxy
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx hy
    obtain ⟨i, hi, hx⟩ := hx
    rcases hx with rfl | rfl <;> rcases hy with h | h <;> simp at h <;> omega

/-- The Battlefield picks of the setup are all different. -/
theorem battlefields_nodup (n : Nat) :
    ((List.range n).map (fun i => Frame.chanceBattlefield ⟨i⟩)).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx y hy hxy
    subst hxy
    simp only [List.mem_map, List.mem_range, List.mem_singleton] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    simp at hy
    omega

/-- Every frame of the setup is there once. -/
theorem startFrames_nodup (n : Nat) : (startFrames n).Nodup := by
  unfold startFrames
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨shuffles_nodup n, battlefields_nodup n, ?_⟩, by simp, ?_⟩
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map] at hx hy
    obtain ⟨i, -, hx⟩ := hx
    obtain ⟨j, -, hy⟩ := hy
    rcases hx with rfl | rfl <;> cases hy
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hx hy
    rcases hx with ⟨i, -, hx⟩ | ⟨i, -, hx⟩
    · rcases hx with rfl | rfl <;> cases hy
    · cases hx; cases hy

/-- What follows a frame in the suffix of the setup is the suffix after it. -/
theorem drop_succ_of_cons {l rest : List Frame} {f : Frame} {k : Nat}
    (h : l.drop k = f :: rest) : l.drop (k + 1) = rest := by
  rw [← List.drop_drop, h]
  rfl

/-- The turn order is the last frame of the setup. -/
theorem startFrames_turnOrder_last {n k : Nat} {rest : List Frame}
    (h : (startFrames n).drop k = Frame.chanceTurnOrder :: rest) : rest = [] := by
  have hnd := startFrames_nodup n
  have hsub : (Frame.chanceTurnOrder :: rest).Nodup := by
    rw [← h]; exact hnd.sublist (List.drop_sublist _ _)
  have hlast : (startFrames n).getLast? = some Frame.chanceTurnOrder := by
    simp [startFrames, List.getLast?_append]
  have hl : ((startFrames n).drop k).getLast? = some Frame.chanceTurnOrder := by
    rw [List.getLast?_drop]
    have hne : ¬ (startFrames n).length ≤ k := by
      intro hle
      rw [List.drop_eq_nil_of_le hle] at h
      exact absurd h (by simp)
    simp [hne, hlast]
  rw [h] at hl
  cases rest with
  | nil => rfl
  | cons x xs =>
    exfalso
    have hmem : Frame.chanceTurnOrder ∈ x :: xs := by
      have := List.mem_of_getLast? (by simpa [List.getLast?_cons_cons] using hl)
      exact this
    exact (List.nodup_cons.mp hsub).1 hmem

/-- **The setup invariant.** There are at least two players, and either the stack is still a suffix
of the frames of the setup, in which case every Battlefield that is still to be picked has a card
to pick from, or no frame of the setup is left. -/
def SetupInv (s : GameState) : Prop :=
  2 ≤ s.playerCount ∧
    ((∃ k, s.pending = (startFrames s.playerCount).drop k ∧
        ∀ p, Frame.chanceBattlefield p ∈ s.pending →
          0 < (s.zone (.player p .outOfGame)).length) ∨
      ∀ f ∈ s.pending, f.isSetup = false)

/-- While the stack is a suffix of the setup, its top frame is a frame of the setup. -/
theorem startFrames_drop_isSetup {n k : Nat} {f : Frame} {rest : List Frame}
    (h : (startFrames n).drop k = f :: rest) : f.isSetup = true :=
  startFrames_isSetup n f ((List.drop_sublist _ _).subset (by rw [h]; exact List.mem_cons_self))

/-- A step that takes a frame which is not a setup frame, and puts frames that are not setup frames
in its place, keeps the setup invariant. -/
theorem SetupInv.of_nonsetup {s s2 : GameState} {f : Frame} {rest new : List Frame}
    (hinv : SetupInv s) (hp : s.pending = f :: rest) (hf : f.isSetup = false)
    (hc : s2.playerCount = s.playerCount) (hq : s2.pending = new ++ rest)
    (hnew : ∀ g ∈ new, g.isSetup = false) : SetupInv s2 := by
  obtain ⟨h2, hcase⟩ := hinv
  refine ⟨hc ▸ h2, Or.inr (fun g hg => ?_)⟩
  rw [hq] at hg
  rcases List.mem_append.mp hg with h | h
  · exact hnew g h
  · rcases hcase with ⟨k, hk, -⟩ | hn
    · rw [hk] at hp
      rw [startFrames_drop_isSetup hp] at hf
      exact absurd hf (by simp)
    · exact hn g (by rw [hp]; exact List.mem_cons_of_mem _ h)

/-- Answering the shuffle on top of the stack keeps the setup invariant. -/
theorem SetupInv.of_shuffle {s : GameState} {z : Zone} {rest : List Frame} {l : List ObjId}
    (hinv : SetupInv s) (hp : s.pending = Frame.chanceShuffle z :: rest)
    (hl : l.Perm (s.zone z)) :
    SetupInv { s.reorder z l with pending := rest } := by
  obtain ⟨h2, hcase⟩ := hinv
  refine ⟨h2, ?_⟩
  rcases hcase with ⟨k, hk, hz⟩ | hn
  · refine Or.inl ⟨k + 1, ?_, fun p hpm => ?_⟩
    · show rest = (startFrames s.playerCount).drop (k + 1)
      exact (drop_succ_of_cons (hk ▸ hp)).symm
    · have := hz p (by rw [hp]; exact List.mem_cons_of_mem _ hpm)
      show 0 < ((s.reorder z l).zone (.player p .outOfGame)).length
      rw [GameState.length_reorder hl]
      exact this
  · exact absurd (hn _ (by rw [hp]; exact List.mem_cons_self)) (by simp [Frame.isSetup])

/-- Answering the turn order on top of the stack keeps the setup invariant: it is the last frame of
the setup, and the opening hands take its place. -/
theorem SetupInv.of_turnOrder {s : GameState} {rest : List Frame} {l : List PlayerId}
    (hinv : SetupInv s) (hp : s.pending = Frame.chanceTurnOrder :: rest) :
    SetupInv { s with turnOrder := l, pending := Frame.setupHands :: rest } := by
  obtain ⟨h2, hcase⟩ := hinv
  refine ⟨h2, Or.inr (fun f hf => ?_)⟩
  rcases hcase with ⟨k, hk, -⟩ | hn
  · have hr : rest = [] := startFrames_turnOrder_last (hk ▸ hp)
    change f ∈ Frame.setupHands :: rest at hf
    rw [hr] at hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    rfl
  · exact absurd (hn _ (by rw [hp]; exact List.mem_cons_self)) (by simp [Frame.isSetup])

/-- Answering the Battlefield pick on top of the stack keeps the setup invariant: the pick takes a
card of that player's only, and the player is not asked again. -/
theorem SetupInv.of_battlefield {s s2 : GameState} {p : PlayerId} {rest : List Frame}
    {id id' : ObjId} (hwf : s.WF) (hinv : SetupInv s)
    (hp : s.pending = Frame.chanceBattlefield p :: rest)
    (hid : id ∈ s.zone (.player p .outOfGame))
    (hm : moveObj s id .battlefieldZone .top = some (s2, id')) :
    SetupInv { s2 with pending := rest } := by
  obtain ⟨src, d, hs⟩ := moveObj_spec hm
  obtain ⟨h2, hcase⟩ := hinv
  have hcount : s2.playerCount = s.playerCount := by simp [GameState.playerCount, hs.config]
  refine ⟨by show 2 ≤ s2.playerCount; rw [hcount]; exact h2, ?_⟩
  rcases hcase with ⟨k, hk, hz⟩ | hn
  · refine Or.inl ⟨k + 1, ?_, fun q hq => ?_⟩
    · show rest = (startFrames s2.playerCount).drop (k + 1)
      rw [hcount]
      exact (drop_succ_of_cons (hk ▸ hp)).symm
    · have hq' : Frame.chanceBattlefield q ∈ s.pending := by
        rw [hp]; exact List.mem_cons_of_mem _ hq
      have hnd : s.pending.Nodup := by
        rw [hk]; exact (startFrames_nodup _).sublist (List.drop_sublist _ _)
      have hne : q ≠ p := by
        intro e
        subst e
        rw [hp] at hnd
        exact (List.nodup_cons.mp hnd).1 hq
      have hsame : s2.zone (.player q .outOfGame) = s.zone (.player q .outOfGame) :=
        moveObj_zone_unchanged hwf hid hm (fun e => hne (by simpa using e))
          (fun o _ => by simp [Zone.normalize])
      show 0 < (s2.zone (.player q .outOfGame)).length
      rw [hsame]
      exact hz q hq'
  · exact absurd (hn _ (by rw [hp]; exact List.mem_cons_self)) (by simp [Frame.isSetup])

/-- Applying a legal answer to the open question keeps the setup invariant. -/
theorem applyFrame_setup0 {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hinv : SetupInv s) (hl : LegalFrame s a)
    (h : applyFrame0 s a = some (s', es)) : SetupInv s' := by
  unfold applyFrame0 at h
  unfold LegalFrame at hl
  split at h
  · rename_i rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp rfl rfl (new := [Frame.phase .ending, Frame.beginTurn]) rfl
      (by simp [Frame.isSetup])
  · rename_i p rest c ab hp hk
    have hmeta := applyRune_meta h
    exact hinv.of_nonsetup hp rfl (by simp [GameState.playerCount, hmeta.1])
      (new := [Frame.priority p]) (by rw [hmeta.2.2.2.2, hp]; rfl) (by simp [Frame.isSetup])
  · rename_i p rest c pay ts flow discard pick hp hk
    obtain ⟨hcfg, -, -, -, -, hpend⟩ := applyPlayCard_discard_meta h
    rcases hpend with e | e
    · exact hinv.of_nonsetup hp rfl (by simp [GameState.playerCount, hcfg])
        (new := [Frame.priority p]) (by rw [e, hp]; rfl) (by simp [Frame.isSetup])
    · exact hinv.of_nonsetup hp rfl (by simp [GameState.playerCount, hcfg])
        (new := [Frame.chainPass p 0, Frame.priority p]) (by rw [e]; rfl)
        (by simp [Frame.isSetup])
  · rename_i p rest u d _ hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hsafe := applyMove_safe (es := es2) hm
    exact hinv.of_nonsetup hp rfl (by simp [GameState.playerCount, hsafe.same.config])
      (new := [Frame.cleanup, Frame.priority p]) rfl (by simp [Frame.isSetup])
  · rename_i bf q n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
        (new := [Frame.showdown bf (s.nextPlayer q) (n + 1)]) rfl (by simp [Frame.isSetup])
    · have hs' : s' = (showdownEnd s bf rest).1 := by
        rw [Option.some.inj h]
      subst hs'
      rcases showdownEnd_cases s bf rest with ⟨a, e⟩ | e <;> rw [e]
      · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
          (new := [Frame.combatDamage bf a]) rfl (by simp [Frame.isSetup])
      · have hP := endShowdown_safeP s bf
        exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
          (by simp [GameState.playerCount, hP.config])
          (new := (endShowdown s bf).2.1) rfl (fun g hg => by
            obtain ⟨r, rfl⟩ := endShowdown_frames s bf true g hg
            rfl)
  · rename_i bf att side acc done rest u hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
      (new := [Frame.assign bf att side (acc ++ [u]) done]) rfl (by simp [Frame.isSetup])
  · rename_i bf att side acc done rest hp hk
    have hs' : s' = (assignDoneStep s bf att side acc done rest).1 := by
      rw [Option.some.inj h]
    subst hs'
    rcases assignDoneStep_cases s bf att side acc done rest with
        ⟨b, a, q, d, e⟩ | ⟨damage, e⟩ | ⟨r, hr, e⟩ <;>
      rw [e]
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
        (new := [Frame.assign b a q [] d]) rfl (by simp [Frame.isSetup])
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
        (new := [Frame.run att bf {} damage, .cleanup, .combatResolve bf att]) rfl (by simp [Frame.isSetup])
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
        (by simp [GameState.playerCount, hr.same.config])
        (new := [Frame.cleanup, Frame.combatResolve bf att]) rfl (by simp [Frame.isSetup])
  · rename_i p n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
        (new := [Frame.chainPass (s.nextPlayer p) (n + 1)]) rfl (by simp [Frame.isSetup])
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := [Frame.resolveChain]) rfl
        (by simp [Frame.isSetup])
  · rename_i p n rest c pay ts flow discard pick hp hk
    obtain ⟨hcfg, -, -, -, -, hpend⟩ := reactStep_discard_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hcfg])
      (new := [Frame.chainPass p 0]) hpend (by simp [Frame.isSetup])
  · rename_i p n rest src idx pay ts discards targetPlayer _costBanisher _costObject hp hk
    obtain ⟨hcfg, -, -, -, -, hpend⟩ := activateStep_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hcfg])
      (new := [Frame.chainPass p 0]) hpend (by simp [Frame.isSetup])
  · rename_i p n tail c ab hp hk
    have hmeta := applyRune_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hmeta.1])
      (new := [Frame.chainPass p n]) (by rw [hmeta.2.2.2.2, hp]; rfl) (by simp [Frame.isSetup])
  · rename_i p rest src idx pay ts discards targetPlayer _costBanisher _costObject hp hk
    obtain ⟨hcfg, -, -, -, -, hpend⟩ := activateStep_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hcfg])
      (new := [Frame.chainPass p 0, Frame.priority p]) hpend (by simp [Frame.isSetup])
  · rename_i p t more others funding rest i ts payment hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp rfl
      (by simp [GameState.playerCount, (finishTrigger_safe s (t :: more) funding i ts payment).same.config])
      (new := [Frame.triggers ((t :: more).eraseIdx i ++ others)]) rfl (by simp [Frame.isSetup])
  · rename_i p t more others rest i ts payment hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp rfl rfl (new := [_]) rfl (by simp [Frame.isSetup])
  · rename_i p t more others previous rest add hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp rfl rfl (new := [_]) rfl (by simp [Frame.isSetup])
  · rename_i p t more others previous rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp rfl rfl (new := [_]) rfl (by simp [Frame.isSetup])
  · rename_i p tail src idx pay hp hk
    have hmeta := applyMana_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hmeta.1])
      (new := [Frame.priority p]) (by rw [hmeta.2.2.2.2, hp]; rfl) (by simp [Frame.isSetup])
  · rename_i p n tail src idx pay hp hk
    have hmeta := applyMana_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hmeta.1])
      (new := [Frame.chainPass p n]) (by rw [hmeta.2.2.2.2, hp]; rfl) (by simp [Frame.isSetup])
  · rename_i p n rest c hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hc : (discardObj s c).1.playerCount = s.playerCount := by
      simp [GameState.playerCount, (discardObj_safe s c).same.config]
    by_cases hn : n ≤ 1
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) hc (new := []) (by simp [hn])
        (by simp)
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) hc (new := [Frame.discard p (n - 1)])
        (by simp [hn]) (by simp [Frame.isSetup])
  · rename_i p n rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := []) rfl (by simp)
  · rename_i p src env e es rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
      (new := [Frame.run p src env (if yes = true then EffectList.cons e es else es)]) rfl
      (by simp [Frame.isSetup])
  · rename_i p src env a b es rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
      (new := [Frame.run p src env (EffectList.cons (if yes = true then a else b) es)]) rfl
      (by simp [Frame.isSetup])
  · rename_i p src env c more e es rest o hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
      (new := [Frame.run p src (env.bindPick o (e.pickIsTarget s o)) (EffectList.cons e es)]) rfl
      (by simp [Frame.isSetup])
  · rename_i z rest l hp hk
    rw [hp, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_shuffle hp hl.2.2
  · rename_i p rest i hp hk
    split at h
    · rename_i id hid
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact hinv.of_battlefield hwf hp (List.mem_of_getElem? hid) hm
    · exact absurd h (by simp)
  · rename_i rest l hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_turnOrder hp
  · rename_i p n rest c hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨src, d, hs⟩ := moveObj_spec hm
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hs.config])
      (new := [Frame.mulligan p (n + 1)]) rfl (by simp [Frame.isSetup])
  · rename_i p n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := []) rfl (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
        (new := [Frame.draw p (_ + 1), Frame.chanceRecycle p]) rfl (by simp [Frame.isSetup])
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
      (by simp [GameState.playerCount, (recycleAll_meta p _ hm).config]) (new := []) rfl
      (by simp)
  · rename_i p rest l hp hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
      (by simp [GameState.playerCount, (recycleAll_meta p _ hm).config])
      (new := [Frame.chooseBurnOut p]) rfl (by simp [Frame.isSetup])
  · rename_i p rest opp hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := []) rfl (by simp)
  · rename_i bf q n rest c pay ts flow discard pick hp hk
    obtain ⟨hcfg, -, -, -, -, hpend⟩ := reactStep_discard_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hcfg])
      (new := [Frame.chainPass q 0, Frame.showdown bf q 0]) hpend (by simp [Frame.isSetup])
  · rename_i bf q n rest src idx pay ts discards targetPlayer _costBanisher _costObject hp hk
    obtain ⟨hcfg, -, -, -, -, hpend⟩ := activateStep_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hcfg])
      (new := [Frame.chainPass q 0, Frame.showdown bf q 0]) hpend (by simp [Frame.isSetup])
  · rename_i bf q n tail c ab hp hk
    have hmeta := applyRune_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hmeta.1])
      (new := [Frame.showdown bf q n]) (by rw [hmeta.2.2.2.2, hp]; rfl) (by simp [Frame.isSetup])
  · rename_i bf q n tail src idx pay hp hk
    have hmeta := applyMana_meta h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) (by simp [GameState.playerCount, hmeta.1])
      (new := [Frame.showdown bf q n]) (by rw [hmeta.2.2.2.2, hp]; rfl) (by simp [Frame.isSetup])
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hinv.1, Or.inr (fun f hf => absurd hf (by simp))⟩
  · rename_i p n c cs top bottom rest id recycle hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hsafe := continuePrediction_safe s p n ((c :: cs).erase id)
      (if recycle then top else top ++ [id]) (if recycle then id :: bottom else bottom)
    refine hinv.of_nonsetup hp rfl (by simp [GameState.playerCount, hsafe.same.config]) rfl ?_
    intro f hf
    have hplay := continuePrediction_frames _ _ _ _ _ _ hf
    cases f <;> simp_all [Frame.isSetup, Frame.isPlay]
  · rename_i p n top old rest bottom hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hsafe := completePrediction_safe s p n top bottom
    exact hinv.of_nonsetup hp rfl (by simp [GameState.playerCount, hsafe.same.config])
      (new := []) rfl (by simp)
  · rename_i p src env first more es rest card hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
      (new := [Frame.run p src env (.cons (.rememberNamedCard card) es)]) rfl
      (by simp [Frame.isSetup])
  · rename_i p source env first other es rest c ab hp hk
    have hmeta := applyRune_meta h
    exact hinv.of_nonsetup hp rfl (by simp [GameState.playerCount, hmeta.1])
      (new := [Frame.eitherDo p source env first other es]) (by rw [hmeta.2.2.2.2, hp]; rfl) (by simp [Frame.isSetup])
  · rename_i p source env first other es rest src idx pay hp hk
    have hmeta := applyMana_meta h
    exact hinv.of_nonsetup hp rfl (by simp [GameState.playerCount, hmeta.1])
      (new := [Frame.eitherDo p source env first other es]) (by rw [hmeta.2.2.2.2, hp]; rfl) (by simp [Frame.isSetup])
  · exact absurd h (by simp)

/-- Finding the triggers a step set off keeps the setup invariant: nothing is put on the stack while
a frame of the setup is on it. -/
theorem SetupInv.withTriggers {s : GameState} (hinv : SetupInv s) (es : List Event) :
    SetupInv (s.withTriggers es) := by
  rcases withTriggers_cases s es with h | ⟨pend, h, -, hs⟩
  · rw [h]; exact hinv
  · rw [h]
    refine ⟨hinv.1, Or.inr (fun f hf => ?_)⟩
    rcases insertTriggers_mem pend _ hf with h1 | ⟨x, h1⟩
    · exact hs f h1
    · subst h1; rfl

/-- Applying a legal answer to the open question keeps the setup invariant. -/
theorem applyFrame_setup {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hinv : SetupInv s) (hl : LegalFrame s a)
    (h : applyFrame s a = some (s', es)) : SetupInv s' := by
  obtain ⟨s2, es2, s3, h0, h3, rfl, -⟩ := applyFrame_cases h
  have h5 : SetupInv s2 := applyFrame_setup0 hwf hinv hl h0
  have h4 : SetupInv s3 := by
    rcases h3 with rfl | ⟨q, pool, rfl⟩ <;> exact h5
  exact h4.withTriggers _

/-- Applying an answer keeps the setup invariant. A concession leaves no frame at all. -/
theorem applyAction_setup {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hinv : SetupInv s) (hl : Legal s a) (h : applyAction s a = some (s', es)) :
    SetupInv s' := by
  by_cases hk : a.kind = .concede
  · obtain ⟨p, hp, -⟩ := (hl.of_concede hk).actor
    rw [applyAction_concede hk hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hinv.1, Or.inr (fun f hf => absurd hf (by simp))⟩
  · rw [applyAction_of_ne hk] at h
    exact applyFrame_setup hwf hinv (hl.frame hk) h

/-- A step of work keeps the setup invariant. -/
theorem microStep_setup0 {s s' : GameState} {es : List Event} (hinv : SetupInv s)
    (h : microStep0 s = some (s', es)) : SetupInv s' := by
  unfold microStep0 at h
  split at h
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
      (new := s.turnOrder.map (fun p => Frame.draw p 4) ++
        s.turnOrder.map (fun p => Frame.mulligan p 0) ++ [Frame.beginTurn]) rfl
      (fun g hg => by
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
        rcases hg with (⟨x, -, rfl⟩ | ⟨x, -, rfl⟩) | rfl <;> rfl)
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases beginTurnStep_cases s rest with e | ⟨r, e⟩
    rotate_left
    · rw [e]
      exact ⟨hinv.1, Or.inr (fun f hf => absurd hf (by simp))⟩
    rw [e]
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := turnFrames s.nextTurnPlayer)
      rfl (fun g hg => by
        simp only [turnFrames, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := []) rfl (by simp)
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hmeta := (channelEx_safe (s.active.getD ⟨0⟩) s.channelCount 0 s).same
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
      (by simp [GameState.playerCount, hmeta.config]) (new := []) rfl (by simp)
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    by_cases hs : s.hasControlledMod (s.active.getD ⟨0⟩) .skipDrawPhase = true
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := []) (by simp [hs]) (by simp)
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
        (new := [Frame.draw (s.active.getD ⟨0⟩) 1]) (by simp [hs]) (by simp [Frame.isSetup])
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp rfl rfl (new := [Frame.cleanup, Frame.expireTurn]) rfl
      (by simp [Frame.isSetup])
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_nonsetup hp rfl rfl (new := expirationFrames s) rfl ?_
    unfold expirationFrames
    split <;> simp [Frame.isSetup]
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := []) rfl (by simp)
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
      (by simp [GameState.playerCount, (beginStep_safe s (s.active.getD ⟨0⟩)).same.config])
      (new := [Frame.cleanup, Frame.draw (s.active.getD ⟨0⟩) (s.extraDraws (s.active.getD ⟨0⟩)),
        Frame.scoreHolds]) rfl (by simp [Frame.isSetup])
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
      (by simp [GameState.playerCount, (hold_safeP s (s.active.getD ⟨0⟩)).config])
      (new := [Frame.draw (s.active.getD ⟨0⟩)
        (scoreDrawCount (s.active.getD ⟨0⟩) (hold s (s.active.getD ⟨0⟩)).2),
        Frame.cleanup]) rfl (by simp [Frame.isSetup])
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := [Frame.cleanup]) rfl
      (by simp [Frame.isSetup])
  · rename_i q rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := []) rfl (by simp)
  · rename_i q n rest hp
    split at h
    · rename_i s1 es1 hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
        (by simp [GameState.noteDraw, GameState.playerCount, (drawOne_meta hd).config])
        (new := [Frame.draw q n]) rfl (by simp [Frame.isSetup])
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
        (new := [Frame.chanceBurnOut q, Frame.draw q (n + 1)]) rfl (by simp [Frame.isSetup])
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨pre, hpre, hplay⟩ := resolveFrames_eq s rest
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := pre) hpre
      (fun g hg => by
        have := hplay g hg
        cases g <;> simp_all [Frame.isPlay, Frame.isSetup])
  · rename_i p src env rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := []) rfl (by simp)
  · rename_i p src env e es rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
      (by simp [GameState.playerCount,
        (runEffect_safe s p src (env.withMight s.mightTable) e es effectAddPolicy).same.config])
      (new := (runEffect s p src (env.withMight s.mightTable) e es effectAddPolicy).2.1) rfl (fun g hg => by
        rcases runEffect_mem hg with h1 | ⟨q, k, rfl⟩ | ⟨q, rfl⟩
        · cases g <;> simp_all [Frame.isPlay, Frame.isSetup]
        · rfl
        · rfl)
  · rename_i item rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
      (by simp [GameState.playerCount, (finishItem_sameMeta s item).config])
      (new := finishedItemFrames s item (finishItem s item)) rfl (fun g hg => by
        have hplay := finishedItemFrames_mem hg
        cases g <;> simp_all [Frame.isPlay, Frame.isSetup])
  · rename_i rest hp
    have hs' : s' = (cleanupFrame s rest).1 := by
      have := Option.some.inj h
      rw [this]
    subst hs'
    rcases cleanupFrame_cases s rest with ⟨w, e⟩ | ⟨u, p, a, b, e⟩ | ⟨r, hr, e⟩ | ⟨bf, q, e⟩ | e <;>
      rw [e]
    · exact ⟨hinv.1, Or.inr (fun g hg => by cases hg)⟩
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
        (new := [.eitherDo p u {} a b .nil, .cleanup]) rfl (by simp [Frame.isSetup])
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
        (by simp [GameState.playerCount, hr.same.config]) (new := [Frame.cleanup]) rfl
        (by simp [Frame.isSetup])
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
        (new := [Frame.showdown bf q 0, Frame.cleanup]) rfl (by simp [Frame.isSetup])
    · exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl (new := []) rfl (by simp)
  · rename_i bf att rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup]) rfl
      (new := s.startCombat bf att ++ combatSteps bf) (by simp [List.append_assoc])
      (fun g hg => by
        rcases List.mem_append.mp hg with h1 | h1
        · have play := startCombat_play s bf att h1
          cases g <;> simp_all [Frame.isPlay, Frame.isSetup]
        · simp [combatSteps] at h1
          rcases h1 with rfl | rfl | rfl <;> rfl)
  · rename_i bf att rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
      (by simp [GameState.playerCount, (combatCleanup_safe s bf att).same.config])
      (new := [Frame.cleanup]) rfl (by simp [Frame.isSetup])
  · rename_i bf rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp rfl rfl (new := []) rfl (by simp)
  · rename_i bf rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp (by simp [Frame.isSetup])
      (by simp [GameState.playerCount, (combatControl_safeP s bf).config])
      (new := (combatControl s bf).2.1 ++ [Frame.cleanup]) (by simp)
      (fun g hg => by
        rcases List.mem_append.mp hg with h1 | h1
        · obtain ⟨_, rfl⟩ := combatControl_frames s bf g h1
          rfl
        · simp only [List.mem_singleton] at h1
          subst h1
          rfl)
  · rename_i bf rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp rfl rfl (new := [Frame.cleanup]) rfl (by simp [Frame.isSetup])
  · rename_i pend rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_nonsetup hp rfl
      (by simp [GameState.playerCount, (triggersStep_spec s pend rest).1.same.config])
      (new := (triggersStep s pend rest).2) rfl (fun g hg => (triggersStep_frames hg).2)
  · exact absurd h (by simp)

/-- A step of work keeps the setup invariant. -/
theorem microStep_setup {s s' : GameState} {es : List Event} (hinv : SetupInv s)
    (h : microStep s = some (s', es)) : SetupInv s' := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  exact (microStep_setup0 hinv h0).withTriggers _

/-- The automatic work keeps the setup invariant. -/
theorem advance_setup :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event}, SetupInv s →
      advance n s es = .ok (s', es') → SetupInv s'
  | 0, s, s', es, es', hinv, h => by
    unfold advance at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hinv
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv
  | n + 1, s, s', es, es', hinv, h => by
    unfold advance at h
    split at h
    · split at h
      · split at h
        · rename_i s1 es1 hm
          exact advance_setup n (microStep_setup hinv hm) h
        · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hinv
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv

/-- A step keeps the setup invariant. -/
theorem step_setup {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hinv : SetupInv s) (h : step fuel s a = .ok (s', es)) : SetupInv s' := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      exact advance_setup fuel (applyAction_setup hwf hinv hl ha) h
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The stack at the start is the frames of the setup. -/
theorem GameState.initial_pending {db : CardDB} {config : GameConfig} {decks : List Deck}
    {s : GameState} (h : GameState.initial db config decks = some s) :
    s.pending = startFrames s.playerCount := by
  unfold GameState.initial at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    obtain ⟨g, -⟩ := GameState.addDecks_grows decks h1
    show startFrames config.mode.players = startFrames s1.playerCount
    simp [GameState.playerCount, g.config, GameState.empty]
  · exact absurd h (by simp)

/-- The setup invariant holds at the start. -/
theorem GameState.initial_setupInv {db : CardDB} {config : GameConfig} {decks : List Deck}
    {s : GameState} (h : GameState.initial db config decks = some s) : SetupInv s := by
  obtain ⟨h2, hb⟩ := GameState.initial_setup h
  have hpend := GameState.initial_pending h
  refine ⟨h2, Or.inl ⟨0, by rw [List.drop_zero]; exact hpend, fun p hp => ?_⟩⟩
  apply hb p
  rw [hpend] at hp
  simp only [startFrames, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hp
  rcases hp with (⟨i, -, h | h⟩ | ⟨i, hi, h⟩) | h
  · cases h
  · cases h
  · cases h
    exact hi
  · cases h

/-- Every deck of a game set up from Limited decks has a Battlefield. -/
theorem LimitedStartOk.battlefields {db : CardDB} {env : LegalityEnv} {config : GameConfig}
    {decks : List LimitedDeck} (h : LimitedStartOk db env config decks) :
    ∀ d ∈ decks, 1 ≤ d.battlefields.length := by
  obtain ⟨-, -, h⟩ := h
  cases hm : config.ruleSet.limitedMinMain with
  | none => rw [hm] at h; exact h.elim
  | some m => rw [hm] at h; exact fun d hd => (h d hd).2

/-- **A game set up from Limited decks.** It has at least two players, and every player has a
Battlefield out of the game, waiting for the random pick (CR 487.5). -/
theorem GameState.initialLimited_setup {db : CardDB} {env : LegalityEnv} {config : GameConfig}
    {decks : List LimitedDeck} {s : GameState}
    (h : GameState.initialLimited db env config decks = some s) :
    2 ≤ s.playerCount ∧ ∀ p : PlayerId, p.n < s.playerCount →
      0 < (s.zone (.player p .outOfGame)).length := by
  unfold GameState.initialLimited at h
  split at h
  · rename_i hc
    have hbf := hc.battlefields
    obtain ⟨hlen, hcfg, -⟩ := hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    obtain ⟨g, hb⟩ := GameState.addLimitedDecks_grows decks h1
    have hcount : s1.playerCount = config.mode.players := by
      simp [GameState.playerCount, g.config, GameState.empty]
    refine ⟨?_, fun p hp => ?_⟩
    · show 2 ≤ s1.playerCount
      rw [hcount]
      exact hcfg.1
    · change p.n < s1.playerCount at hp
      rw [hcount, ← hlen] at hp
      have h2 := hb p.n hp
      rw [Nat.zero_add] at h2
      exact Nat.lt_of_lt_of_le (hbf _ (List.getElem_mem hp)) h2
  · exact absurd h (by simp)

/-- The stack at the start of a Limited game is the frames of the setup. -/
theorem GameState.initialLimited_pending {db : CardDB} {env : LegalityEnv} {config : GameConfig}
    {decks : List LimitedDeck} {s : GameState}
    (h : GameState.initialLimited db env config decks = some s) :
    s.pending = startFrames s.playerCount := by
  unfold GameState.initialLimited at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    obtain ⟨g, -⟩ := GameState.addLimitedDecks_grows decks h1
    show startFrames config.mode.players = startFrames s1.playerCount
    simp [GameState.playerCount, g.config, GameState.empty]
  · exact absurd h (by simp)

/-- The setup invariant holds at the start of a Limited game. -/
theorem GameState.initialLimited_setupInv {db : CardDB} {env : LegalityEnv} {config : GameConfig}
    {decks : List LimitedDeck} {s : GameState}
    (h : GameState.initialLimited db env config decks = some s) : SetupInv s := by
  obtain ⟨h2, hb⟩ := GameState.initialLimited_setup h
  have hpend := GameState.initialLimited_pending h
  refine ⟨h2, Or.inl ⟨0, by rw [List.drop_zero]; exact hpend, fun p hp => ?_⟩⟩
  apply hb p
  rw [hpend] at hp
  simp only [startFrames, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hp
  rcases hp with (⟨i, -, h | h⟩ | ⟨i, hi, h⟩) | h
  · cases h
  · cases h
  · cases h
    exact hi
  · cases h

/-- Every reachable state satisfies the setup invariant. -/
theorem Reachable.setup {s : GameState} (h : Reachable s) : SetupInv s := by
  induction h with
  | init h =>
    cases h with
    | core h => exact GameState.initial_setupInv h
    | limited h => exact GameState.initialLimited_setupInv h
  | next hs h ih => exact step_setup (Reachable.inv hs).1 ih h

/-- **I5, progress.** In a reachable game that is not over, either there is an answer other than a
concession in `legalActions`, or the top frame asks for a chance decision. -/
theorem Reachable.progress {s : GameState} (h : Reachable s) (hres : s.result = none) :
    (∃ a ∈ legalActions s, a.kind ≠ .concede) ∨
      ∃ f rest, s.pending = f :: rest ∧ f.isChance = true :=
  h.progress_of_players hres h.setup.1

/-- A chance frame of a reachable game has what it needs for an answer. -/
theorem Reachable.chanceReady {s : GameState} (h : Reachable s) {f : Frame} {rest : List Frame}
    (hp : s.pending = f :: rest) (hc : f.isChance = true) : f.chanceReady s := by
  obtain ⟨-, hcase⟩ := h.setup
  rcases hcase with ⟨k, hk, hz⟩ | hn
  · cases f with
    | chanceShuffle z =>
      have hmem : Frame.chanceShuffle z ∈ startFrames s.playerCount := by
        exact (List.drop_sublist _ _).subset (by rw [← hk, hp]; exact List.mem_cons_self)
      exact startFrames_valid hmem
    | chanceBattlefield p => exact hz p (by rw [hp]; exact List.mem_cons_self)
    | chanceTurnOrder => trivial
    | chanceRecycle p => trivial
    | chanceBurnOut p => trivial
    | chancePredict p n top bottom => trivial
    | _ => exact absurd hc (by simp [Frame.isChance])
  · have := hn f (by rw [hp]; exact List.mem_cons_self)
    cases f with
    | chanceShuffle z => exact absurd this (by simp [Frame.isSetup])
    | chanceBattlefield p => exact absurd this (by simp [Frame.isSetup])
    | chanceTurnOrder => exact absurd this (by simp [Frame.isSetup])
    | chanceRecycle p => trivial
    | chanceBurnOut p => trivial
    | chancePredict p n top bottom => trivial
    | _ => exact absurd hc (by simp [Frame.isChance])

/-- **I5, in full.** A reachable game that is not over always has a legal answer other than a
concession: from `legalActions` for a player, or a chance answer. No game that was set up from legal
decks reaches a dead end. -/
theorem Reachable.exists_legal {s : GameState} (h : Reachable s) (hres : s.result = none) :
    ∃ a, Legal s a ∧ a.kind ≠ .concede := by
  rcases h.progress hres with ⟨a, ha, hk⟩ | ⟨f, rest, hp, hc⟩
  · exact ⟨a, ((legalActions_iff s a).mp ha).1, hk⟩
  · obtain ⟨a, hact, hl⟩ := chance_answer_exists hres hp hc (h.chanceReady hp hc)
    refine ⟨a, hl, fun hk => ?_⟩
    obtain ⟨p, hp', -⟩ := (hl.of_concede hk).actor
    rw [hact] at hp'
    cases hp'

end Riftbound

end
