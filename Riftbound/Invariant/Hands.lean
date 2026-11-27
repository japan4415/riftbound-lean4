module

public import Riftbound.Invariant.Sound
public import Riftbound.Rules.PlayerRemoval

/-!
# The opening hands

After the setup every player has four cards in hand (CR 116, 117): the opening draw gives four, and
a mulligan sets aside as many cards as it draws. The proof tracks the size of each hand together
with the draws that are still on the stack: the invariant `HandInv` says that the hand and the cards
the frames will still put in it add up to four, and each step keeps it.
-/

@[expose] public section

namespace Riftbound

/-- How many cards of player `p`'s hand the frame accounts for: the opening hands, the draws still
to do, and the cards a mulligan has set aside (they are drawn again when it ends). -/
def Frame.contrib (p : PlayerId) : Frame → Nat
  | .chanceTurnOrder => 4
  | .setupHands => 4
  | .draw q n _ => if q = p then n else 0
  | .mulligan q k => if q = p then k else 0
  | _ => 0

/-- What the frames on the stack account for in the hand of `p`. -/
def stackContrib (p : PlayerId) (l : List Frame) : Nat := (l.map (Frame.contrib p)).sum

/-- One more frame adds its share. -/
theorem stackContrib_cons (p : PlayerId) (f : Frame) (l : List Frame) :
    stackContrib p (f :: l) = f.contrib p + stackContrib p l := by
  simp [stackContrib]

/-- The size of a player's hand. -/
def GameState.handLen (s : GameState) (p : PlayerId) : Nat := (s.zone (.player p .hand)).length

/-- **The hand invariant.** The turn order is known when the opening hands are laid out, and, while
the game is still being set up, each participating player's hand together with what the stack still
accounts for is four cards. -/
structure HandInv (s : GameState) : Prop where
  /-- The turn order is an arrangement of the players as soon as `setupHands` is on the stack. -/
  turn : Frame.setupHands ∈ s.pending → s.turnOrder.Perm (allPlayers s.playerCount)
  /-- During the setup: each participating player's hand plus what is still to come is four. -/
  hands : s.phase = .setup → s.result = none → ∀ p : PlayerId, s.participates p = true →
    s.handLen p + stackContrib p s.pending = 4
  /-- A Spell is played in the Main Phase, so the frames of a Spell on the Chain are never on the
  stack during the setup. -/
  play : ∀ f ∈ s.pending, f.isPlay = true → s.phase ≠ .setup

/-- A step that keeps the rules, turn order, phase, result and departed seats. -/
structure Keeps (s s2 : GameState) : Prop where
  /-- The rules are the same. -/
  config : s2.config = s.config
  /-- The turn order is the same. -/
  turnOrder : s2.turnOrder = s.turnOrder
  /-- The phase is the same. -/
  phase : s2.phase = s.phase
  /-- The result is the same. -/
  result : s2.result = s.result
  /-- The departed seats are the same. -/
  departedSeats : s2.departures.seats = s.departures.seats

/-- Whatever only touches zones, objects and counters keeps all that. -/
theorem Keeps.of_sameMeta {s s2 : GameState} (h : SameMeta s s2) : Keeps s s2 :=
  ⟨h.config, h.turnOrder, h.phase, h.result, congrArg SeatDepartures.seats h.departures⟩

/-- Replacing the pending frames does not change any metadata used for opening hands. -/
theorem Keeps.withPending {s s2 : GameState} (h : Keeps s s2) (pending : List Frame) :
    Keeps s { s2 with pending } :=
  ⟨h.config, h.turnOrder, h.phase, h.result, h.departedSeats⟩

/-- Rearranging a zone does not change the length of any zone. -/
theorem GameState.length_reorder {s : GameState} {z : Zone} {l : List ObjId}
    (hp : l.Perm (s.zone z)) (z' : Zone) :
    ((s.reorder z l).zone z').length = (s.zone z').length := by
  by_cases h : z' = z
  · subst h
    have : (s.reorder z' l).zone z' = l := GameState.zone_setZone_self s z' l
    rw [this]
    exact hp.length_eq
  · rw [show (s.reorder z l).zone z' = s.zone z' from GameState.zone_setZone_ne s h l]

/-- A draw puts a card in the player's hand and leaves the other hands alone (CR 414). -/
theorem drawOne_hand {s s' : GameState} {p : PlayerId} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (h : drawOne s p = some (s', es)) :
    s'.handLen p = s.handLen p + 1 ∧
      ∀ q, q ≠ p → s'.zone (.player q .hand) = s.zone (.player q .hand) := by
  refine ⟨(drawOne_lengths_of_ownerOk hwf hown h).2, fun q hq => ?_⟩
  unfold drawOne at h
  split at h
  · exact absurd h (by simp)
  · rename_i top rest hz
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have htop : top ∈ s.zone (.player p .mainDeck) := by rw [hz]; exact List.mem_cons_self
    refine moveObj_zone_unchanged hwf htop hm (by simp) (fun o ho => ?_)
    have howner : o.owner = p := hown.owner p .mainDeck rfl top htop o ho
    rw [howner]
    simp [Zone.normalize, Zone.isBoard, hq]

/-- Setting a card aside in the mulligan takes it out of the player's hand and leaves the other
hands alone (CR 117.1). -/
theorem mulliganPick_hand {s s' : GameState} {p : PlayerId} {c id' : ObjId}
    (hwf : s.WF) (hown : s.OwnerOk) (hc : c ∈ s.zone (.player p .hand))
    (h : moveObj s c (.player p .setAside) = some (s', id')) :
    s'.handLen p + 1 = s.handLen p ∧
      ∀ q, q ≠ p → s'.zone (.player q .hand) = s.zone (.player q .hand) := by
  refine ⟨?_, fun q hq => ?_⟩
  · obtain ⟨src, d, hs, o, ho, hd⟩ := moveObj_spec_dst h
    have hsrc : src = .player p .hand :=
      Option.some.inj (hs.locate.symm.trans
        (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hc) hc))
    have h1 := hs.zone_src
    rw [hsrc] at h1
    simp only [GameState.handLen]
    rw [h1, List.length_erase_of_mem hc]
    have : 0 < (s.zone (.player p .hand)).length := List.length_pos_of_mem hc
    omega
  · refine moveObj_zone_unchanged hwf hc h (fun e => hq (by simpa using e)) (fun o ho => ?_)
    have howner : o.owner = p := hown.owner p .hand rfl c hc o ho
    rw [howner]
    simp [Zone.normalize, Zone.isBoard]

/-- Picking the Battlefield leaves every hand alone. -/
theorem battlefield_hands {s s' : GameState} {p : PlayerId} {id id' : ObjId}
    (hwf : s.WF) (hid : id ∈ s.zone (.player p .outOfGame))
    (h : moveObj s id .battlefieldZone .top = some (s', id')) (r : PlayerId) :
    s'.zone (.player r .hand) = s.zone (.player r .hand) :=
  moveObj_zone_unchanged hwf hid h (by simp) (fun o _ => by simp [Zone.normalize])

/-- The common case of a step: the turn order and the rest of what the invariant reads are kept, the
hands keep their sizes, and the stack accounts for the same. -/
theorem HandInv.of_same {s s2 : GameState} (hinv : HandInv s) (hk : Keeps s s2)
    (hlen : ∀ r, (s2.zone (.player r .hand)).length = (s.zone (.player r .hand)).length)
    (hcontrib : ∀ p : PlayerId, s.participates p = true →
      stackContrib p s2.pending = stackContrib p s.pending)
    (hsub : Frame.setupHands ∈ s2.pending → Frame.setupHands ∈ s.pending)
    (hplay : ∀ f ∈ s2.pending, f.isPlay = true → ∃ g ∈ s.pending, g.isPlay = true) :
    HandInv s2 := by
  have hcount : s2.playerCount = s.playerCount := by simp [GameState.playerCount, hk.config]
  refine ⟨fun hm => ?_, fun hph hres p hp => ?_, fun f hf hpf => ?_⟩
  · rw [hcount, hk.turnOrder]; exact hinv.turn (hsub hm)
  · have present : s.participates p = true := by
      simpa only [GameState.participates, hcount, hk.departedSeats] using hp
    rw [hk.phase] at hph
    rw [hk.result] at hres
    have := hinv.hands hph hres p present
    simp only [GameState.handLen] at this ⊢
    rw [hlen p, hcontrib p present]
    exact this
  · rw [hk.phase]
    obtain ⟨g, hg, hgp⟩ := hplay f hf hpf
    exact hinv.play g hg hgp

/-- `HandInv` for a step that leaves the setup behind or never was in it: the phase is not the
setup, so the hands are not accounted for, and what is left to check is the turn order. -/
theorem HandInv.of_play {s s2 : GameState} (hinv : HandInv s) (hph : s2.phase ≠ .setup)
    (hto : s2.turnOrder = s.turnOrder) (hc : s2.config = s.config)
    (hsub : Frame.setupHands ∈ s2.pending → Frame.setupHands ∈ s.pending) : HandInv s2 := by
  have hcount : s2.playerCount = s.playerCount := by simp [GameState.playerCount, hc]
  refine ⟨fun hm => ?_, fun hph' => absurd hph' hph, fun f _ _ => hph⟩
  rw [hcount, hto]
  exact hinv.turn (hsub hm)

/-- `HandInv` for a step that pops a frame which accounts for nothing. -/
theorem HandInv.of_pop {s s2 : GameState} {f : Frame} {rest : List Frame} (hinv : HandInv s)
    (hp : s.pending = f :: rest) (hf : ∀ p, f.contrib p = 0) (hk : Keeps s s2)
    (hlen : ∀ r, (s2.zone (.player r .hand)).length = (s.zone (.player r .hand)).length)
    (hpend : s2.pending = rest) : HandInv s2 := by
  refine hinv.of_same hk hlen (fun p _ => ?_) (fun hm => ?_) (fun g hg hgp => ?_)
  · rw [hpend, hp, stackContrib_cons, hf p]; simp
  · rw [hpend] at hm
    rw [hp]
    exact List.mem_cons_of_mem _ hm
  · rw [hpend] at hg
    exact ⟨g, by rw [hp]; exact List.mem_cons_of_mem _ hg, hgp⟩

/-- Recycling an arrangement of a Non-Board zone leaves every hand alone. -/
theorem recycleAll_hands {s s2 : GameState} {p q : PlayerId} {k : ZoneKind} {l : List ObjId}
    (hk : k.isBoard = false) (hk2 : k ≠ .mainDeck) (hk3 : k ≠ .hand) (hwf : s.WF)
    (hown : s.OwnerOk) (hperm : l.Perm (s.zone (.player q k))) (h : recycleAll p s l = some s2)
    (r : PlayerId) : s2.zone (.player r .hand) = s.zone (.player r .hand) := by
  have hnd : l.Nodup := hperm.nodup_iff.mpr (GameState.zone_nodup_any hwf _)
  obtain ⟨s3, hs3, hh⟩ := recycleAll_some (p := p) (q := q) hk hk2 hk3 l hwf hown hnd
    (fun id hid => hperm.mem_iff.mp hid)
  rw [hs3] at h
  cases h
  exact hh r

/-- Applying a legal answer to the open question keeps the hand invariant. -/
theorem applyFrame_handInv0 {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (hinv : HandInv s) (hl : LegalFrame s a)
    (h : applyFrame0 s a = some (s', es)) : HandInv s' := by
  unfold applyFrame0 at h
  unfold LegalFrame at hl
  split at h
  · rename_i rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_same ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun q _ => ?_) (fun hmem => ?_)
      (fun f hf hpf => ?_)
    · show stackContrib q (Frame.phase .ending :: Frame.beginTurn :: rest) =
        stackContrib q s.pending
      rw [hp, stackContrib_cons, stackContrib_cons, stackContrib_cons]
      simp [Frame.contrib]
    · have : Frame.setupHands ∈ rest := by simpa using hmem
      rw [hp]; exact List.mem_cons_of_mem _ this
    · have hf' : f ∈ Frame.phase .ending :: Frame.beginTurn :: rest := hf
      simp only [List.mem_cons] at hf'
      rcases hf' with rfl | rfl | h
      · simp [Frame.isPlay] at hpf
      · simp [Frame.isPlay] at hpf
      · exact ⟨f, by rw [hp]; exact List.mem_cons_of_mem _ h, hpf⟩
  · rename_i p _ c ab hp hk
    rw [hp, hk] at hl
    have hmeta := applyRune_meta h
    have hhand := applyRune_hand hwf hl.2.1 hl.2.2 h
    exact hinv.of_same (Keeps.of_sameMeta (applyRune_sameMeta h))
      (fun r => congrArg List.length (hhand r)) (fun q _ => by rw [hmeta.2.2.2.2])
      (fun hm => by rw [hmeta.2.2.2.2] at hm; exact hm)
      (fun f hf hpf => ⟨f, by rw [hmeta.2.2.2.2] at hf; exact hf, hpf⟩)
  · rename_i p _ c pay ts flow discard pick hp hk
    rw [hp, hk] at hl
    have hturn := playOk_not_setup hl.2.2.1
    obtain ⟨hcfg, hto, hphase, -, -, hpend⟩ := applyPlayCard_meta h
    have hturn' : s'.phase ≠ .setup := by simpa only [hphase] using hturn
    have hcount : s'.playerCount = s.playerCount := by simp [GameState.playerCount, hcfg]
    refine ⟨fun hm => ?_, fun hph => ?_, fun f hf hpf => ?_⟩
    · show s'.turnOrder.Perm (allPlayers s'.playerCount)
      rw [hto, hcount]
      apply hinv.turn
      rcases hpend with e | e
      · rw [e] at hm
        rcases List.mem_cons.mp hm with impossible | later
        · cases impossible
        · exact later
      · rw [e] at hm
        simp only [List.mem_cons] at hm
        rw [hp]
        rcases hm with h | h | h
        · cases h
        · cases h
        · exact List.mem_cons_of_mem _ h
    · exact (hturn' hph).elim
    · exact fun hh => (hturn' hh).elim
  · rename_i p rest u d _ hp hk
    rw [hp, hk] at hl
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, es2⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hsafe := applyMove_safe (es := es2) hm
    have hmain := moveOk_main hl.2.1
    refine hinv.of_play ?_ hsafe.same.turnOrder hsafe.same.config (fun hmem => ?_)
    · show s2.phase ≠ .setup
      rw [hsafe.same.phase, hmain]
      intro hh
      cases hh
    · have : Frame.setupHands ∈ rest := by simpa using hmem
      rw [hp]
      exact List.mem_cons_of_mem _ this
  · rename_i bf q n rest hp hk
    have hph0 := hinv.play (.showdown bf q n) (by rw [hp]; exact List.mem_cons_self) rfl
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_play hph0 rfl rfl (fun hmem => ?_)
      have : Frame.setupHands ∈ rest := by simpa using hmem
      rw [hp]
      exact List.mem_cons_of_mem _ this
    · have hs' : s' = (showdownEnd s bf rest).1 := by
        rw [Option.some.inj h]
      subst hs'
      rcases showdownEnd_cases s bf rest with ⟨a, e⟩ | e <;> rw [e]
      · refine hinv.of_play hph0 rfl rfl (fun hmem => ?_)
        have : Frame.setupHands ∈ rest := by simpa using hmem
        rw [hp]
        exact List.mem_cons_of_mem _ this
      · have hP := endShowdown_safeP s bf
        refine hinv.of_play
          (by show (endShowdown s bf).1.phase ≠ .setup; rw [hP.phase]; exact hph0)
          hP.turnOrder hP.config (fun hmem => ?_)
        have hm2 : Frame.setupHands ∈ (endShowdown s bf).2.1 ++ rest := hmem
        rcases List.mem_append.mp hm2 with h1 | h1
        · obtain ⟨r, hr⟩ := endShowdown_frames s bf true _ h1
          cases hr
        · rw [hp]
          exact List.mem_cons_of_mem _ h1
  · rename_i bf att side acc done rest u hp hk
    have hph0 := hinv.play (.assign bf att side acc done) (by rw [hp]; exact List.mem_cons_self) rfl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_play hph0 rfl rfl (fun hmem => ?_)
    have : Frame.setupHands ∈ rest := by simpa using hmem
    rw [hp]
    exact List.mem_cons_of_mem _ this
  · rename_i bf att side acc done rest hp hk
    have hph0 := hinv.play (.assign bf att side acc done) (by rw [hp]; exact List.mem_cons_self) rfl
    have hs' : s' = (assignDoneStep s bf att side acc done rest).1 := by
      rw [Option.some.inj h]
    subst hs'
    rcases assignDoneStep_cases s bf att side acc done rest with
        ⟨b, a, q, d, e⟩ | ⟨_, e⟩ | ⟨r, hr, e⟩ <;>
      rw [e]
    · refine hinv.of_play hph0 rfl rfl (fun hmem => ?_)
      have : Frame.setupHands ∈ rest := by
        rcases List.mem_append.mp hmem with h | h
        · have play := combatAssignmentChoices_play h
          simp [Frame.isPlay] at play
        · simpa using h
      rw [hp]
      exact List.mem_cons_of_mem _ this
    · refine hinv.of_play hph0 rfl rfl (fun hmem => ?_)
      have : Frame.setupHands ∈ rest := by simpa using hmem
      rw [hp]
      exact List.mem_cons_of_mem _ this
    · refine hinv.of_play (by show r.phase ≠ .setup; rw [hr.same.phase]; exact hph0)
        hr.same.turnOrder hr.same.config (fun hmem => ?_)
      have : Frame.setupHands ∈ rest := by simpa using hmem
      rw [hp]
      exact List.mem_cons_of_mem _ this
  · rename_i p n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_same ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun q _ => ?_) (fun hmem => ?_)
        (fun f hf hpf => ?_)
      · show stackContrib q (Frame.chainPass (s.nextParticipant p) (n + 1) :: rest) =
          stackContrib q s.pending
        rw [hp, stackContrib_cons, stackContrib_cons]
        simp [Frame.contrib]
      · have : Frame.setupHands ∈ rest := by simpa using hmem
        rw [hp]; exact List.mem_cons_of_mem _ this
      · exact ⟨Frame.chainPass p n, by rw [hp]; exact List.mem_cons_self, rfl⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_same ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun q _ => ?_) (fun hmem => ?_)
        (fun f hf hpf => ?_)
      · show stackContrib q (Frame.resolveChain :: rest) = stackContrib q s.pending
        rw [hp, stackContrib_cons, stackContrib_cons]
        simp [Frame.contrib]
      · have : Frame.setupHands ∈ rest := by simpa using hmem
        rw [hp]; exact List.mem_cons_of_mem _ this
      · exact ⟨Frame.chainPass p n, by rw [hp]; exact List.mem_cons_self, rfl⟩
  · rename_i p n rest c pay ts flow discard pick hp hk
    rw [hp, hk] at hl
    obtain ⟨hcfg, hto, hphase, -, -, hpend⟩ := reactStep_meta h
    have hturn : s.phase ≠ .setup := by
      rcases reactable_spec.mp hl.2.2.1 with ⟨(h0 | h0) | h0, -⟩ | ⟨h0, -⟩
      · obtain ⟨-, -, -, -, hm, -⟩ := castable_spec h0
        exact hm
      · obtain ⟨-, -, -, -, hm, -⟩ := playable_spec h0.2.2
        simp [hm]
      · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h0.2
        obtain ⟨-, -, -, -, hm, -⟩ := playable_spec hb
        simp [hm]
      · obtain ⟨b, -, hb⟩ := bfPlayOk_spec h0.2
        obtain ⟨-, -, -, -, hm, -⟩ := playable_spec hb
        simp [hm]
    refine hinv.of_play (by simpa only [hphase] using hturn) hto hcfg (fun hm => ?_)
    · rw [hpend] at hm
      simp only [List.mem_cons] at hm
      rw [hp]
      rcases hm with h1 | h1
      · cases h1
      · exact List.mem_cons_of_mem _ h1
  · rename_i p n rest src idx pay ts discards targetPlayer _costBanisher hp hk
    rw [hp, hk] at hl
    obtain ⟨hcfg, hto, hphase, -, -, hpend⟩ := activateStep_meta h
    obtain ⟨d, costs, sp, body, lim, pc, grant, hturn, -⟩ := activatable_spec hl.2.1
    refine hinv.of_play (by simpa only [hphase] using hturn) hto hcfg (fun hm => ?_)
    · rw [hpend] at hm
      have hm := (List.mem_append.mp hm).resolve_left
        (fun h => nomatch activationRecycleFrames_play h)
      simp only [List.mem_cons] at hm
      rw [hp]
      rcases hm with h1 | h1
      · cases h1
      · exact List.mem_cons_of_mem _ h1
  · rename_i p n tail c ab hp hk
    rw [hp, hk] at hl
    have hmeta := applyRune_meta h
    have hhand := applyRune_hand hwf hl.2.1 hl.2.2 h
    exact hinv.of_same (Keeps.of_sameMeta (applyRune_sameMeta h))
      (fun r => congrArg List.length (hhand r)) (fun q _ => by rw [hmeta.2.2.2.2])
      (fun hm => by rw [hmeta.2.2.2.2] at hm; exact hm)
      (fun f hf hpf => ⟨f, by rw [hmeta.2.2.2.2] at hf; exact hf, hpf⟩)
  · rename_i p rest src idx pay ts discards targetPlayer _costBanisher hp hk
    rw [hp, hk] at hl
    obtain ⟨hcfg, hto, hphase, -, -, hpend⟩ := activateStep_meta h
    obtain ⟨d, costs, sp, body, lim, pc, grant, hturn, -⟩ := activatable_spec hl.2.1
    refine hinv.of_play (by simpa only [hphase] using hturn) hto hcfg (fun hm => ?_)
    · rw [hpend] at hm
      have hm := (List.mem_append.mp hm).resolve_left
        (fun h => nomatch activationRecycleFrames_play h)
      simp only [List.mem_cons] at hm
      rw [hp]
      rcases hm with h1 | h1 | h1
      · cases h1
      · cases h1
      · exact List.mem_cons_of_mem _ h1
  · rename_i p t more others funding rest i ts payment hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hm := (finishTrigger_safe s (t :: more) funding i ts payment).same
    have hph : ((finishTrigger s (t :: more) funding i ts payment).1).phase ≠ .setup := by
      rw [hm.phase]
      exact hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph hm.turnOrder hm.config (fun hm' => ?_)
    simp only [List.mem_cons] at hm'
    rcases hm' with h1 | h1
    · cases h1
    · rw [hp]; exact List.mem_cons_of_mem _ h1
  · rename_i p t more others rest i ts payment hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph : s.phase ≠ .setup := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph rfl rfl (fun hm' => ?_)
    rw [hp]
    rcases List.mem_cons.mp hm' with h1 | h1
    · cases h1
    · exact List.mem_cons_of_mem _ h1
  · rename_i p t more others previous rest add hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph : s.phase ≠ .setup := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph rfl rfl (fun hm' => ?_)
    rw [hp]
    rcases List.mem_cons.mp hm' with h1 | h1
    · cases h1
    · exact List.mem_cons_of_mem _ h1
  · rename_i p t more others previous rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph : s.phase ≠ .setup := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph rfl rfl (fun hm' => ?_)
    rw [hp]
    rcases List.mem_cons.mp hm' with h1 | h1
    · cases h1
    · exact List.mem_cons_of_mem _ h1
  · rename_i p tail src idx pay _chosen hp hk
    rw [hp, hk] at hl
    obtain ⟨⟨next, events⟩, applied, mapped⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at mapped
    obtain ⟨rfl, -⟩ := mapped
    obtain ⟨hcfg, hto, hphase, -, -⟩ := applyMana_meta applied
    refine hinv.of_play ?_ hto hcfg (fun hm => ?_)
    · exact hphase ▸ (manaOk_not_setup hl.2)
    · rw [hp]
      simpa using hm
  · rename_i p n tail src idx pay _chosen hp hk
    rw [hp, hk] at hl
    obtain ⟨hcfg, hto, hphase, -, hpend⟩ := applyMana_meta h
    refine hinv.of_play ?_ hto hcfg (fun hm => ?_)
    · rw [hphase]
      exact manaOk_not_setup hl.2
    · rw [hpend] at hm
      exact hm
  · rename_i p n rest c hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hm := (discardObj_safe s c).same
    have hph : (discardObj s c).1.phase ≠ .setup := by
      rw [hm.phase]
      exact hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph hm.turnOrder hm.config (fun hm' => ?_)
    dsimp only at hm'
    split at hm'
    · rw [hp]; exact List.mem_cons_of_mem _ hm'
    · rw [hp]
      simp only [List.mem_cons] at hm'
      rcases hm' with h1 | h1
      · cases h1
      · exact List.mem_cons_of_mem _ h1
  · rename_i p n rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph : s.phase ≠ .setup :=
      hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    exact hinv.of_play hph rfl rfl (fun hm' => by rw [hp]; exact List.mem_cons_of_mem _ hm')
  · rename_i p src env e es rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph : s.phase ≠ .setup :=
      hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph rfl rfl (fun hm' => ?_)
    rw [hp]
    rcases List.mem_cons.mp hm' with h1 | h1
    · cases h1
    · exact List.mem_cons_of_mem _ h1
  · rename_i p src env a b es rest yes hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph : s.phase ≠ .setup :=
      hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph rfl rfl (fun hm' => ?_)
    rw [hp]
    rcases List.mem_cons.mp hm' with h1 | h1
    · cases h1
    · exact List.mem_cons_of_mem _ h1
  · rename_i p src env c more e es rest o hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph : s.phase ≠ .setup :=
      hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph rfl rfl (fun hm' => ?_)
    rw [hp]
    rcases List.mem_cons.mp hm' with h1 | h1
    · cases h1
    · exact List.mem_cons_of_mem _ h1
  · rename_i z rest l hp hk
    rw [hp, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_pop hp (by simp [Frame.contrib]) ⟨rfl, rfl, rfl, rfl, rfl⟩
      (fun r => GameState.length_reorder hl.2.2 _) rfl
  · rename_i p rest i hp hk
    split at h
    · rename_i id hid
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      obtain ⟨src, d, hs⟩ := moveObj_spec hm
      have hmem : id ∈ s.zone (.player p .outOfGame) := List.mem_of_getElem? hid
      exact hinv.of_pop hp (by simp [Frame.contrib])
        ((Keeps.of_sameMeta hs.other).withPending _)
        (fun r => congrArg List.length (battlefield_hands hwf hmem hm r)) rfl
    · exact absurd h (by simp)
  · rename_i rest l hp hk
    rw [hp, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨fun _ => hl.2.1, fun hph hres q hq => ?_, fun f hf hpf => ?_⟩
    · have h0 := hinv.hands hph hres q hq
      rw [hp, stackContrib_cons] at h0
      show s.handLen q + stackContrib q (Frame.setupHands :: rest) = 4
      rw [stackContrib_cons]
      simp only [Frame.contrib] at h0 ⊢
      exact h0
    · have hf' : f ∈ Frame.setupHands :: rest := hf
      rcases List.mem_cons.mp hf' with rfl | h
      · simp [Frame.isPlay] at hpf
      · exact hinv.play f (by rw [hp]; exact List.mem_cons_of_mem _ h) hpf
  · rename_i p n rest c hp hk
    rw [hp, hk] at hl
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨src, d, hs⟩ := moveObj_spec hm
    obtain ⟨hp1, hq⟩ := mulliganPick_hand hwf hown hl.2.1 hm
    have hcount : s2.playerCount = s.playerCount := by simp [GameState.playerCount, hs.config]
    refine ⟨fun hmem => ?_, fun hph hres q hq' => ?_, fun f hf hpf => ?_⟩
    · have : Frame.setupHands ∈ rest := by simpa using hmem
      have h1 := hinv.turn (by rw [hp]; exact List.mem_cons_of_mem _ this)
      show s2.turnOrder.Perm (allPlayers s2.playerCount)
      rw [hs.turnOrder, hcount]
      exact h1
    · change s2.phase = .setup at hph
      change s2.result = none at hres
      rw [hs.other.phase] at hph
      rw [hs.other.result] at hres
      have present : s.participates q = true := by
        change s2.participates q = true at hq'
        simpa only [GameState.participates, hcount, hs.other.departures] using hq'
      have h0 := hinv.hands hph hres q present
      rw [hp, stackContrib_cons] at h0
      show s2.handLen q + stackContrib q (Frame.mulligan p (n + 1) :: rest) = 4
      rw [stackContrib_cons]
      by_cases hqp : q = p
      · subst hqp
        simp only [Frame.contrib, ite_true] at h0 ⊢
        omega
      · simp only [GameState.handLen] at h0 ⊢
        rw [hq q hqp]
        have hpq : ¬ p = q := fun e => hqp e.symm
        simp only [Frame.contrib, hpq, ite_false] at h0 ⊢
        omega
    · have hf' : f ∈ Frame.mulligan p (n + 1) :: rest := hf
      rcases List.mem_cons.mp hf' with rfl | h
      · simp [Frame.isPlay] at hpf
      · show s2.phase ≠ .setup
        rw [hs.other.phase]
        exact hinv.play f (by rw [hp]; exact List.mem_cons_of_mem _ h) hpf
  · rename_i p n rest hp hk
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv.of_pop hp (by simp [Frame.contrib]) ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_same ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun q _ => ?_) (fun hmem => ?_)
        (fun f hf hpf => ?_)
      · show stackContrib q (Frame.draw p (_ + 1) :: Frame.chanceRecycle p :: rest) =
          stackContrib q s.pending
        rw [hp, stackContrib_cons, stackContrib_cons, stackContrib_cons]
        simp [Frame.contrib]
      · have : Frame.setupHands ∈ rest := by simpa using hmem
        rw [hp]; exact List.mem_cons_of_mem _ this
      · have hf' : f ∈ Frame.draw p (_ + 1) :: Frame.chanceRecycle p :: rest := hf
        simp only [List.mem_cons] at hf'
        rcases hf' with rfl | rfl | h
        · simp [Frame.isPlay] at hpf
        · simp [Frame.isPlay] at hpf
        · exact ⟨f, by rw [hp]; exact List.mem_cons_of_mem _ h, hpf⟩
  · rename_i p rest l hp hk
    rw [hp, hk] at hl
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hmeta := recycleAll_meta p _ hm
    exact hinv.of_pop hp (by simp [Frame.contrib])
      ((Keeps.of_sameMeta hmeta).withPending _)
      (fun r => congrArg List.length
        (recycleAll_hands (q := p) (k := .setAside) rfl (by simp) (by simp) hwf hown hl.2 hm r))
      rfl
  · rename_i p rest l hp hk
    rw [hp, hk] at hl
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hmeta := recycleAll_meta p _ hm
    have hh := recycleAll_hands (q := p) (k := .trash) rfl (by simp) (by simp) hwf hown hl.2 hm
    refine hinv.of_same ((Keeps.of_sameMeta hmeta).withPending _)
      (fun r => congrArg List.length (hh r))
      (fun q _ => ?_) (fun hmem => ?_) (fun f hf hpf => ?_)
    · show stackContrib q (s.burnOutDecision p ++ rest) = stackContrib q s.pending
      rw [hp, stackContrib_cons]
      rcases s.burnOutDecision_cases p with h | h | ⟨first, more, h⟩ <;>
        simp [h, stackContrib, Frame.contrib]
    · have hmem' : Frame.setupHands ∈ s.burnOutDecision p ++ rest := hmem
      have : Frame.setupHands ∈ rest := by
        rcases s.burnOutDecision_cases p with h | h | ⟨first, more, h⟩ <;>
          simpa [h] using hmem'
      rw [hp]; exact List.mem_cons_of_mem _ this
    · have hf' : f ∈ s.burnOutDecision p ++ rest := hf
      refine ⟨f, ?_, hpf⟩
      rw [hp]
      apply List.mem_cons_of_mem
      rcases List.mem_append.mp hf' with queued | remains
      · rcases s.burnOutDecision_cases p with h | h | ⟨first, more, h⟩ <;>
          simp [h] at queued <;> subst f <;> cases hpf
      · exact remains
  · rename_i p rest opp hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_pop hp (by simp [Frame.contrib]) ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) rfl
  · rename_i p first more rest opp hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_pop hp (by simp [Frame.contrib]) ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) rfl
  · rename_i bf q n rest c pay ts flow discard pick hp hk
    rw [hp, hk] at hl
    obtain ⟨hcfg, hto, hphase, -, -, hpend⟩ := reactStep_meta h
    have hturn : s.phase ≠ .setup := by
      rcases showdownable_spec hl.2.2.1 with h0 | ⟨dest, ts', choice, h0⟩
      · obtain ⟨-, -, -, -, hm, -⟩ := castable_spec h0
        exact hm
      · obtain ⟨-, -, -, -, hm, -⟩ := playable_spec h0
        simp [hm]
    refine hinv.of_play (by simpa only [hphase] using hturn) hto hcfg (fun hm => ?_)
    · rw [hpend] at hm
      simp only [List.mem_cons] at hm
      rw [hp]
      rcases hm with h1 | h1 | h1
      · cases h1
      · cases h1
      · exact List.mem_cons_of_mem _ h1
  · rename_i bf q rest src idx pay ts discards targetPlayer _costBanisher hp hk
    rw [hp, hk] at hl
    obtain ⟨hcfg, hto, hphase, -, -, hpend⟩ := activateStep_meta h
    simp only [activatableSD, Bool.and_eq_true] at hl
    obtain ⟨d, costs, sp, body, lim, pc, grant, hturn, -⟩ := activatable_spec hl.2.1.1
    refine hinv.of_play (by simpa only [hphase] using hturn) hto hcfg (fun hm => ?_)
    · rw [hpend] at hm
      have hm := (List.mem_append.mp hm).resolve_left
        (fun h => nomatch activationRecycleFrames_play h)
      simp only [List.mem_cons] at hm
      rw [hp]
      rcases hm with h1 | h1 | h1
      · cases h1
      · cases h1
      · exact List.mem_cons_of_mem _ h1
  · rename_i q c ab hp hk
    rw [hp, hk] at hl
    have hmeta := applyRune_meta h
    have hhand := applyRune_hand hwf hl.2.1 hl.2.2 h
    exact hinv.of_same (Keeps.of_sameMeta (applyRune_sameMeta h))
      (fun r => congrArg List.length (hhand r)) (fun q _ => by rw [hmeta.2.2.2.2])
      (fun hm => by rw [hmeta.2.2.2.2] at hm; exact hm)
      (fun f hf hpf => ⟨f, by rw [hmeta.2.2.2.2] at hf; exact hf, hpf⟩)
  · rename_i q src idx pay _chosen hp hk
    rw [hp, hk] at hl
    obtain ⟨hcfg, hto, hphase, -, hpend⟩ := applyMana_meta h
    refine hinv.of_play ?_ hto hcfg (fun hm => ?_)
    · rw [hphase]
      exact manaOk_not_setup hl.2
    · rw [hpend] at hm
      exact hm
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_same ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun _ _ => rfl) id
      (fun f hf hp => ⟨f, hf, hp⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨fun hm => by simp at hm, fun _ hres => by simp at hres, fun f hf _ => by simp at hf⟩
  · rename_i p n c cs top bottom rest id recycle hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph := hinv.play (.predict p n c cs top bottom) (by rw [hp]; exact List.mem_cons_self) rfl
    have hm := (continuePrediction_safe s p n ((c :: cs).erase id)
      (if recycle then top else top ++ [id]) (if recycle then id :: bottom else bottom)).same
    refine hinv.of_play (hm.phase ▸ hph) hm.turnOrder hm.config (fun hf => ?_)
    rcases List.mem_append.mp hf with hnew | hrest
    · have : Frame.setupHands.isPlay = true := continuePrediction_frames _ _ _ _ _ _ hnew
      contradiction
    · rw [hp]
      exact List.mem_cons_of_mem _ hrest
  · rename_i p n top old rest bottom hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph := hinv.play (.chancePredict p n top old) (by rw [hp]; exact List.mem_cons_self) rfl
    have hm := (completePrediction_safe s p n top bottom).same
    refine hinv.of_play (hm.phase ▸ hph) hm.turnOrder hm.config (fun hf => ?_)
    rw [hp]
    exact List.mem_cons_of_mem _ hf
  · rename_i p src cards rest order hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph := hinv.play (.chanceRecycleTrash p src cards) (by rw [hp]; exact List.mem_cons_self) rfl
    have hm := (recycleTrashCards_safe s order).same
    refine hinv.of_play (hm.phase ▸ hph) hm.turnOrder hm.config (fun hf => ?_)
    rw [hp]
    exact List.mem_cons_of_mem _ hf
  · rename_i p src env first more es rest card hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph : s.phase ≠ .setup :=
      hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph rfl rfl (fun hm' => ?_)
    rw [hp]
    rcases List.mem_cons.mp hm' with h1 | h1
    · cases h1
    · exact List.mem_cons_of_mem _ h1
  · rename_i guesser p src env unit gear spell es rest guess hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph : s.phase ≠ .setup :=
      hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph rfl rfl (fun hm' => ?_)
    rw [hp]
    rcases List.mem_cons.mp hm' with h1 | h1
    · cases h1
    · exact List.mem_cons_of_mem _ h1
  · rename_i c ab hp hk
    rw [hp, hk] at hl
    have hmeta := applyRune_meta h
    have hhand := applyRune_hand hwf hl.2.1 hl.2.2.1 h
    exact hinv.of_same (Keeps.of_sameMeta (applyRune_sameMeta h))
      (fun r => congrArg List.length (hhand r)) (fun q _ => by rw [hmeta.2.2.2.2])
      (fun hm => by rw [hmeta.2.2.2.2] at hm; exact hm)
      (fun f hf hpf => ⟨f, by rw [hmeta.2.2.2.2] at hf; exact hf, hpf⟩)
  · rename_i src idx pay _chosen hp hk
    rw [hp, hk] at hl
    obtain ⟨hcfg, hto, hphase, -, hpend⟩ := applyMana_meta h
    refine hinv.of_play (by rw [hphase]; exact manaOk_not_setup hl.2.1) hto hcfg (fun hm => ?_)
    rwa [hpend] at hm
  · rename_i inviter rest guest hp hk
    rw [hp, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hphase := GameState.teamInvitee_phase hl.2
    refine hinv.of_play (by change s.phase ≠ .setup; rw [hphase]; decide) rfl rfl (fun hm => ?_)
    simpa only [hp, List.mem_cons, reduceCtorEq, false_or] using hm
  · rename_i guest rest hp hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_pop hp (fun _ => rfl) ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) rfl
  · rename_i guest rest c pay ts flow discard pick hp hk
    obtain ⟨hcfg, hto, hphase, -, -, hpend⟩ := reactStep_meta h
    have hturn := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play (hphase ▸ hturn) hto hcfg (fun hm => ?_)
    rw [hpend] at hm
    rw [hp]
    simpa only [List.mem_cons, reduceCtorEq, false_or] using hm
  · rename_i guest rest src idx pay ts discards targetPlayer _costBanisher _costObject hp hk
    obtain ⟨hcfg, hto, hphase, -, -, hpend⟩ := activateStep_meta h
    have hturn := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play (hphase ▸ hturn) hto hcfg (fun hm => ?_)
    rw [hpend] at hm
    have hm := (List.mem_append.mp hm).resolve_left
      (fun h => nomatch activationRecycleFrames_play h)
    rw [hp]
    simpa only [List.mem_cons, reduceCtorEq, false_or] using hm
  · rename_i guest rest c ab hp hk
    obtain ⟨hcfg, hto, hphase, -, hpend⟩ := applyRune_meta h
    have hturn := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play (hphase ▸ hturn) hto hcfg (fun hm => ?_)
    rwa [hpend] at hm
  · rename_i guest rest src idx pay _chosen hp hk
    obtain ⟨hcfg, hto, hphase, -, hpend⟩ := applyMana_meta h
    have hturn := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play (hphase ▸ hturn) hto hcfg (fun hm => ?_)
    rwa [hpend] at hm
  · rename_i p first more rest bf hp hk
    obtain ⟨q, -, he⟩ := Option.map_eq_some_iff.mp h
    have hout : _ = s' := congrArg Prod.fst he
    rw [← hout]
    have hphase := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hphase rfl rfl (fun hm => ?_)
    rw [hp]
    simpa [continueAfterCleanup] using hm
  · rename_i p rest dest pay hp hk
    rw [hp, hk] at hl
    have hphase := GameState.groupMoveChoices_main hl.2.2.1
    cases h
    refine hinv.of_play (by change s.phase ≠ .setup; rw [hphase]; decide) rfl rfl (fun hm => ?_)
    simpa only [hp, List.mem_cons, reduceCtorEq, false_or] using hm
  · rename_i p dest pay units rest u hp hk
    have hphase := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    cases h
    refine hinv.of_play hphase rfl rfl (fun hm => ?_)
    simpa only [hp, List.mem_cons, reduceCtorEq, false_or] using hm
  · rename_i p dest pay units rest hp hk
    have hphase := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    cases h
    refine hinv.of_play hphase rfl rfl (fun hm => ?_)
    rw [hp]
    exact List.mem_cons_of_mem _ hm
  · rename_i p dest pay units rest hp hk
    have hphase := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    obtain ⟨r, hm, he⟩ := Option.map_eq_some_iff.mp h
    have hout : _ = s' := congrArg Prod.fst he
    rw [← hout]
    have hmeta := (applyGroupMove_safe hm).same
    refine hinv.of_play (hmeta.phase ▸ hphase) hmeta.turnOrder hmeta.config (fun hsetup => ?_)
    rw [hp]
    simpa only [List.mem_cons, reduceCtorEq, false_or] using hsetup
  · exact absurd h (by simp)

/-- Finding the triggers a step set off keeps the hand invariant: only `triggers` frames are put
on the stack, and not during the setup. -/
theorem HandInv.withTriggers {s : GameState} (hinv : HandInv s) (es : List Event) :
    HandInv (s.withTriggers es) := by
  rcases withTriggers_cases s es with ⟨p, h, hph⟩ | h | ⟨pend, h, hph, -⟩
  · rw [h]
    exact hinv.of_play hph rfl rfl (by simp)
  · rw [h]
    exact ⟨hinv.turn, hinv.hands, hinv.play⟩
  · rw [h]
    refine hinv.of_play hph rfl rfl (fun hm => ?_)
    rcases insertDetectedTriggers_mem hm with h1 | ⟨ts, h1⟩ | ⟨p, src, env, todo, h1⟩
    · exact h1
    · cases h1
    · cases h1

/-- Applying a legal answer to the open question keeps the hand invariant. -/
theorem applyFrame_handInv {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (hinv : HandInv s) (hl : LegalFrame s a)
    (h : applyFrame s a = some (s', es)) : HandInv s' := by
  obtain ⟨s2, es2, s3, h0, h3, rfl, -⟩ := applyFrame_cases h
  have h5 : HandInv s2 := applyFrame_handInv0 hwf hown hinv hl h0
  have h4 : HandInv s3 := by
    rcases h3 with rfl | ⟨q, pool, rfl⟩
    · exact h5
    · exact h5.of_same ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun _ _ => rfl) id
        (fun f hf hp => ⟨f, hf, hp⟩)
  exact h4.withTriggers _

/-- The stack accounts for the sum of its parts. -/
theorem stackContrib_append (p : PlayerId) (l1 l2 : List Frame) :
    stackContrib p (l1 ++ l2) = stackContrib p l1 + stackContrib p l2 := by
  simp [stackContrib]

/-- Frames that account for nothing add nothing. -/
theorem stackContrib_zero {p : PlayerId} {l : List Frame} (h : ∀ f ∈ l, f.contrib p = 0) :
    stackContrib p l = 0 := by
  induction l with
  | nil => rfl
  | cons f fs ih =>
    rw [stackContrib_cons, h f List.mem_cons_self,
      ih (fun g hg => h g (List.mem_cons_of_mem _ hg))]

private theorem withdrawal_frame_contrib (f : Frame) (before board : GameState)
    {departing p : PlayerId} (other : p ≠ departing) :
    stackContrib p (f.afterPlayerRemoval before board departing) = f.contrib p := by
  cases f <;> simp [Frame.afterPlayerRemoval, GameState.survivingBurnOutDecision, Frame.contrib,
    stackContrib]
  all_goals
    repeat' first
      | solve | simp_all [Frame.contrib]
      | split

private theorem withdrawal_stack_contrib (before board : GameState)
    {departing p : PlayerId} (other : p ≠ departing) (frames : List Frame) :
    stackContrib p (frames.flatMap (fun f => f.afterPlayerRemoval before board departing)) =
      stackContrib p frames := by
  induction frames with
  | nil => rfl
  | cons f tail ih =>
    rw [List.flatMap_cons, stackContrib_append, stackContrib_cons,
      withdrawal_frame_contrib f before board other, ih]

/-- A free-for-all concession preserves the opening-hand accounting of the remaining seats. -/
theorem HandInv.of_freeForAllConcession {s next : GameState} {departing : PlayerId}
    {blank : CardId} {events : List Event} (hinv : HandInv s) (hwf : s.WF) (howner : s.OwnerOk)
    (applied : applyFreeForAllConcession s departing blank = some (next, events)) : HandInv next := by
  obtain ⟨sameConfig, samePhase, sameOrder, _, _, sameDepartures⟩ :=
    applyFreeForAllConcession_meta applied
  rcases applyFreeForAllConcession_cases applied with ⟨_, rfl⟩ | ⟨board, removed, rfl⟩
  · exact ⟨fun h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h⟩
  · let rewrite := fun f : Frame => f.afterPlayerRemoval s board departing
    refine ⟨fun member => ?_, fun phase ongoing p present => ?_, fun f member play phase => ?_⟩
    · have retained : Frame.setupHands ∈ s.pending.flatMap rewrite := by
        change Frame.setupHands ∈ s.pendingAfterConcession board departing at member
        unfold GameState.pendingAfterConcession at member
        split at member
        · exact member
        · simpa using member
      obtain ⟨f, before, after⟩ := List.mem_flatMap.mp retained
      have h := hinv.turn (Frame.afterPlayerRemoval_setupHands after ▸ before)
      change board.turnOrder.Perm (allPlayers board.playerCount)
      have order : board.turnOrder = s.turnOrder := sameOrder
      have count : board.playerCount = s.playerCount := congrArg (·.mode.players) sameConfig
      rwa [order, count]
    · have remains : (s.withdrawSeat departing).participates p = true := by
        have config : board.config = (s.withdrawSeat departing).config := (removePlayerObjects_safe removed).same.config
        have recorded : board.departures = (s.withdrawSeat departing).departures := sameDepartures
        change board.participates p = true at present
        obtain ⟨registered, seats⟩ := Bool.and_eq_true_iff.mp present
        refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true ?_, ?_⟩
        · unfold GameState.playerCount
          rw [← config]
          exact of_decide_eq_true registered
        · rw [← recorded]
          exact seats
      rw [GameState.withdrawSeat_participates] at remains
      obtain ⟨stillRegistered, different⟩ := Bool.and_eq_true_iff.mp remains
      have other : p ≠ departing := by simpa using different
      have sq : board.phase = .setup := phase
      have beforePhase : s.phase = .setup := samePhase.symm.trans phase
      have beforeResult : s.result = none := (removalBoard_result removed).symm.trans ongoing
      have hands := hinv.hands beforePhase beforeResult p stillRegistered
      have zone : board.zone (.player p .hand) = s.zone (.player p .hand) :=
        applyFreeForAllConcession_privateZone applied p .hand other (Or.inl rfl) hwf howner
      change (board.zone (.player p .hand)).length +
        stackContrib p (s.pendingAfterConcession board departing) = 4
      rw [zone, GameState.pendingAfterConcession]
      simp only [sq, beq_self_eq_true, Bool.true_or, ↓reduceIte,
        withdrawal_stack_contrib s board other]
      exact hands
    · have sq : board.phase = .setup := phase
      have beforePhase : s.phase = .setup := samePhase.symm.trans phase
      change f ∈ s.pendingAfterConcession board departing at member
      simp only [GameState.pendingAfterConcession, sq, beq_self_eq_true, Bool.true_or, ↓reduceIte] at member
      obtain ⟨old, before, after⟩ := List.mem_flatMap.mp member
      exact hinv.play old before (Frame.afterPlayerRemoval_play beforePhase after play) beforePhase

/-- Applying a legal answer preserves the opening-hand invariant. -/
theorem applyAction_handInv {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (hinv : HandInv s) (hl : Legal s a)
    (h : applyAction s a = some (s', es)) : HandInv s' := by
  by_cases hk : a.kind = .concede
  · obtain ⟨p, hp, -⟩ := (hl.of_concede hk).actor
    by_cases ffa : s.config.mode.isFreeForAll = true
    · obtain ⟨board, _, removed, rfl⟩ := applyAction_concede_ffa_cases hk hp ffa h
      have kept := hinv.of_freeForAllConcession hwf hown removed
      have withCards : HandInv { board with cards := board.cards.withConcessionBattlefield } := ⟨kept.turn, kept.hands, kept.play⟩
      exact withCards.withTriggers _
    · have ffa : s.config.mode.isFreeForAll = false := by simpa using ffa
      rw [applyAction_concede hk hp ffa] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine ⟨fun hm => ?_, fun _ hres => ?_, fun f hf _ => ?_⟩
      · simp at hm
      · simp at hres
      · simp at hf
  · rw [applyAction_of_ne hk] at h
    exact applyFrame_handInv hwf hown hinv (hl.frame hk) h

/-- The opening draws of the players account for four cards for each player listed. -/
theorem stackContrib_draws (p : PlayerId) (l : List PlayerId) :
    stackContrib p (l.map (fun q => Frame.draw q 4)) = 4 * l.count p := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    rw [List.map_cons, stackContrib_cons, ih, List.count_cons]
    by_cases h : q = p
    · subst h; simp [Frame.contrib]; omega
    · have hpq : ¬ (q == p) = true := by simpa using h
      simp [Frame.contrib, h, hpq]

/-- The players are listed once each. -/
theorem allPlayers_nodup (n : Nat) : (allPlayers n).Nodup := by
  show List.Pairwise (· ≠ ·) _
  refine List.Pairwise.map (fun i => (⟨i⟩ : PlayerId)) ?_ List.nodup_range
  intro a b hab h
  exact hab (by simpa using h)

/-- Where the frames that resolve the Chain come from: the stack below, or the frames of a Spell. -/
theorem resolveFrames_mem {s : GameState} {rest : List Frame} {f : Frame}
    (h : f ∈ resolveFrames s rest) : f ∈ rest ∨ f.isPlay = true := by
  obtain ⟨pre, eq, play⟩ := resolveFrames_eq s rest
  rw [eq] at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inr (play f h)
  · exact Or.inl h

/-- Burning schedules only effect frames and Burn Out decisions. -/
theorem burnEffect_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {who : PlayerSel} {n : Amount} {es : EffectList} {link : Option Nat} {f : Frame}
    (h : f ∈ (burnEffect s p src env who n es link).2.1) :
    f.isPlay = true ∨ ∃ q, f = .chanceBurnOut q := by
  unfold burnEffect at h
  split at h
  · dsimp only at h
    split at h
    · simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | ⟨_, _, rfl⟩ | rfl
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    · simp only [List.mem_append, List.mem_map, List.mem_singleton] at h
      rcases h with ⟨_, _, rfl⟩ | rfl <;> exact Or.inl rfl
  · simp only [List.mem_singleton] at h
    subst f
    exact Or.inl rfl
  · simp only [List.mem_singleton] at h
    subst f
    exact Or.inl rfl

private theorem moveEffectStep_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {a : Prim} {body : Effect} {es : EffectList} {funding : EffectAddPolicy} {paid : Bool} {f : Frame}
    (h : f ∈ (moveEffectStep s p src env a body es funding paid).2.1) : f.isPlay = true := by
  unfold moveEffectStep at h
  split at h
  · obtain rfl := List.mem_singleton.mp h
    rfl
  · dsimp only at h
    split at h <;> obtain rfl := List.mem_singleton.mp h <;> rfl

private theorem fundMoveFeeStep_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {a : Prim} {body : Effect} {adds : List EffectAdd} {commit : Bool} {es : EffectList}
    {funding : EffectAddPolicy} {f : Frame}
    (h : f ∈ (fundMoveFeeStep s p src env a body adds commit es funding).2.1) :
    f.isPlay = true := by
  unfold fundMoveFeeStep at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try dsimp only at h) <;>
    (try split at h) <;> obtain rfl := List.mem_singleton.mp h <;> rfl

set_option maxHeartbeats 2500000 in
private theorem runPrimEffect_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {pr : Prim} {es : EffectList} {funding : EffectAddPolicy} {f : Frame}
    (h : f ∈ (runPrimEffect s p src env pr es funding).2.1) :
    f.isPlay = true ∨ (∃ q k, f = Frame.draw q k) ∨ ∃ q, f = .chanceBurnOut q := by
  unfold runPrimEffect at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h)
  all_goals first
    | (simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at h
       first
       | (subst h; exact Or.inl rfl)
       | (rcases h with rfl | rfl <;> exact Or.inl rfl)
       | (rcases h with ⟨q, -, rfl⟩ | rfl
          · exact Or.inr (Or.inl ⟨q, _, rfl⟩)
          · exact Or.inl rfl)
       | (rcases h with ⟨q, -, rfl⟩ | rfl <;> exact Or.inl rfl))
    | (rename_i r hr; exact Or.inl (playSpellStep_frames hr h))
    | (rename_i r hr; exact Or.inl (castReducedStep_frames hr h))
    | exact Or.inl (castInlineStep_mem h)
    | exact Or.inl (killEffectStep_mem h)
    | exact Or.inl (unitTokenPrimStep_mem h)
    | exact Or.inl (moveEffectStep_mem h)
    | (rcases List.mem_append.mp h with ha | hb
       · exact Or.inl (attachmentReplacementFrames_play ha)
       · obtain rfl := List.mem_singleton.mp hb
         exact Or.inl rfl)
    | (rcases burnEffect_mem h with hp | hb
       · exact Or.inl hp
       · exact Or.inr (Or.inr hb))

set_option maxHeartbeats 6000000 in
/-- The frames of an effect are play frames, draws, or Burn Out decisions. -/
theorem runEffect1_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {e : Effect}
    {es : EffectList} {funding : EffectAddPolicy} {f : Frame}
    (h : f ∈ (runEffect1 s p src env e es funding).2.1) :
    f.isPlay = true ∨ (∃ q k, f = Frame.draw q k) ∨ ∃ q, f = .chanceBurnOut q := by
  unfold runEffect1 at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    (try split at h)
  all_goals first
    | (simp only [List.mem_cons, List.mem_append, List.mem_map,
         List.not_mem_nil, or_false] at h
       first
       | (subst h; exact Or.inl rfl)
       | (rcases h with rfl | rfl <;> exact Or.inl rfl)
       | (subst h; exact Or.inl (requiredCardPlayFrame_play _ _ _ _ _ _ _ _ _))
       | (subst h; exact Or.inl (equipWithCostFrame_play _ _ _ _ _ _ _ _))
       | (rcases h with rfl
          left
          unfold retainTargetSetFrame
          dsimp only
          split <;> rfl)
       | (rcases h with rfl
          left
          unfold remakeSpellChoicesFrame
          dsimp only
          split <;> rfl)
       | (rcases h with rfl
          left
          unfold collectOwnPicksFrame
          dsimp only
          split
          · rfl
          · split <;> rfl)
       | (rcases h with rfl
          left
          unfold forceMoveToBattlefieldFrame
          dsimp only
          split <;> (try split) <;> (try split) <;> rfl)
       | (rcases h with ⟨q, -, rfl⟩ | rfl
          · exact Or.inr (Or.inl ⟨q, _, rfl⟩)
          · exact Or.inl rfl)
       | (rcases h with ⟨q, -, rfl⟩ | rfl
          · exact Or.inl rfl
          · exact Or.inl rfl))
    | (rcases List.mem_append.mp h with ha | hb
       · unfold spellExecutionFrames at ha
         dsimp only at ha
         split at ha
         · obtain rfl := List.mem_singleton.mp ha
           exact Or.inl rfl
         · simp at ha
       · obtain rfl := List.mem_singleton.mp hb
         exact Or.inl rfl)
    | exact runPrimEffect_mem h
    | (obtain rfl := List.mem_singleton.mp h
       exact Or.inl (addReservedLegendFrame_play _ _ _ _ _))
    | exact Or.inl (recycleLookedStep_mem h)
    | exact Or.inl (recycleTrashStep_mem h)
    | exact Or.inl (replayFrames_mem h)
    | exact Or.inl (orderBanishReplayFrames_mem h)
    | exact Or.inl (castLimitedStep_mem h)
    | exact Or.inl (finalizeLimitedStep_mem h)
    | exact Or.inl (cancelLimitedStep_mem h)
    | exact Or.inl (resolveEffectDamageStep_mem h)
    | exact Or.inl (orderCombatDamageStep_mem h)
    | exact Or.inl (killEffectStep_mem h)
    | exact Or.inl (moveEffectStep_mem h)
    | exact Or.inl (fundMoveFeeStep_mem h)
    | (unfold banishLookedStep at h
       split at h
       all_goals (try split at h) <;> obtain rfl := List.mem_singleton.mp h <;> exact Or.inl rfl)
    | (rcases List.mem_append.mp h with ha | hb
       · exact Or.inl (attachmentReplacementFrames_play ha)
       · obtain rfl := List.mem_singleton.mp hb
         exact Or.inl rfl)
    | (dsimp only at h
       split at h
       all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at h
       all_goals first
       | (subst h; exact Or.inl rfl)
       | (rcases h with rfl | rfl <;> exact Or.inl rfl))

/-- The frames of an effect are play frames, draws, or Burn Out decisions. -/
theorem runEffect_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {e : Effect}
    {es : EffectList} {funding : EffectAddPolicy} {f : Frame}
    (h : f ∈ (runEffect s p src env e es funding).2.1) :
    f.isPlay = true ∨ (∃ q k, f = Frame.draw q k) ∨ ∃ q, f = .chanceBurnOut q := by
  unfold runEffect at h
  split at h
  · split at h
    · split at h <;> simp only [List.mem_singleton] at h <;> subst h <;> exact Or.inl rfl
    · simp only [List.mem_singleton] at h
      subst h; exact Or.inl rfl
    · simp only [List.mem_singleton] at h
      subst h; exact Or.inl rfl
  · exact runEffect1_mem h

/-- `HandInv` for a step of a Spell's frames: the setup is over, so nothing is counted. -/
theorem HandInv.of_spell_step {s s2 : GameState} (hinv : HandInv s) (hph : s.phase ≠ .setup)
    (hk : Keeps s s2) (hsub : Frame.setupHands ∈ s2.pending → Frame.setupHands ∈ s.pending) :
    HandInv s2 := by
  have hcount : s2.playerCount = s.playerCount := by simp [GameState.playerCount, hk.config]
  refine ⟨fun hm => ?_, fun hph' => ?_, fun f _ _ => ?_⟩
  · rw [hcount, hk.turnOrder]; exact hinv.turn (hsub hm)
  · exact absurd (hk.phase ▸ hph') hph
  · rw [hk.phase]; exact hph

/-- A step of work keeps the hand invariant. -/
theorem microStep_handInv0 {s s' : GameState} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (hinv : HandInv s) (h : microStep0 s = some (s', es)) : HandInv s' := by
  unfold microStep0 at h
  split at h
  · -- the opening hands and the mulligans are laid out
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hto := hinv.turn (by rw [hp]; exact List.mem_cons_self)
    have order : s.participatingOrder.Perm (s.participatingSeats) :=
      hto.filter s.participates
    refine hinv.of_same ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun q hq => ?_) (fun hmem => ?_)
      (fun f hf hpf => ?_)
    · show stackContrib q (s.participatingOrder.map (fun p => Frame.draw p 4) ++
        s.participatingOrder.map (fun p => Frame.mulligan p 0) ++ [Frame.beginTurn] ++ rest) =
        stackContrib q s.pending
      rw [stackContrib_append, stackContrib_append, stackContrib_append, stackContrib_draws,
        stackContrib_zero (l := s.participatingOrder.map (fun p => Frame.mulligan p 0)) (fun f hf => by
          simp only [List.mem_map] at hf
          obtain ⟨x, -, rfl⟩ := hf
          simp [Frame.contrib]),
        order.count_eq q, hp, stackContrib_cons]
      have registered : q.n < s.playerCount := by
        simpa [GameState.participates] using (Bool.and_eq_true_iff.mp hq).1
      have member : q ∈ s.participatingSeats := by
        change q ∈ (allPlayers s.playerCount).filter s.participates
        exact List.mem_filter.mpr ⟨(mem_allPlayers _ _).mpr registered, hq⟩
      have : s.participatingSeats.count q = 1 :=
        List.Nodup.count_of_mem ((allPlayers_nodup _).sublist List.filter_sublist) member
      rw [this]
      simp [stackContrib, Frame.contrib]
    · have : Frame.setupHands ∈ rest := by simpa using hmem
      rw [hp]; exact List.mem_cons_of_mem _ this
    · have hf' : f ∈ s.participatingOrder.map (fun p => Frame.draw p 4) ++
          s.participatingOrder.map (fun p => Frame.mulligan p 0) ++ [Frame.beginTurn] ++ rest := hf
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hf'
      rcases hf' with ((⟨x, -, rfl⟩ | ⟨x, -, rfl⟩) | rfl) | h
      · simp [Frame.isPlay] at hpf
      · simp [Frame.isPlay] at hpf
      · simp [Frame.isPlay] at hpf
      · exact ⟨f, by rw [hp]; exact List.mem_cons_of_mem _ h, hpf⟩
  · -- a turn begins, or the clock ends the game
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases beginTurnStep_cases s rest with e | ⟨r, e⟩
    rotate_left
    · rw [e]
      exact ⟨fun hm => by simp at hm, fun _ hres => by simp at hres,
        fun f hf _ => by simp at hf⟩
    rw [e]
    refine hinv.of_same ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun q _ => ?_) (fun hmem => ?_)
      (fun f hf hpf => ?_)
    · show stackContrib q (turnFrames s.nextTurnPlayer ++ rest) = stackContrib q s.pending
      rw [stackContrib_append, hp, stackContrib_cons,
        stackContrib_zero (l := turnFrames s.nextTurnPlayer) (fun f hf => by
          simp only [turnFrames, List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Frame.contrib])]
      simp [Frame.contrib]
    · have : Frame.setupHands ∈ rest := by
        simp only [turnFrames, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h1 | h1
        · rcases h1 with h2 | h2 | h2 | h2 | h2 | h2 <;> simp at h2
        · exact h1
      rw [hp]; exact List.mem_cons_of_mem _ this
    · have hf' : f ∈ turnFrames s.nextTurnPlayer ++ rest := hf
      simp only [turnFrames, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf'
      rcases hf' with (rfl | rfl | rfl | rfl | rfl | rfl) | h
      · simp [Frame.isPlay] at hpf
      · simp [Frame.isPlay] at hpf
      · simp [Frame.isPlay] at hpf
      · simp [Frame.isPlay] at hpf
      · simp [Frame.isPlay] at hpf
      · simp [Frame.isPlay] at hpf
      · exact ⟨f, by rw [hp]; exact List.mem_cons_of_mem _ h, hpf⟩
  · -- Awaken
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨fun hmem => ?_, fun hph => (by cases hph), fun _ _ _ hph => (by cases hph)⟩
    have : Frame.setupHands ∈ rest := by simpa using hmem
    have h1 := hinv.turn (by rw [hp]; exact List.mem_cons_of_mem _ this)
    exact h1
  · -- Channel
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨fun hmem => ?_, fun hph => (by cases hph), fun _ _ _ hph => (by cases hph)⟩
    have : Frame.setupHands ∈ rest := by simpa using hmem
    have h1 := hinv.turn (by rw [hp]; exact List.mem_cons_of_mem _ this)
    have hmeta := (channelEx_safe (s.active.getD ⟨0⟩) s.channelCount 0 s).same
    show (channelEx (s.active.getD ⟨0⟩) s.channelCount 0 s).1.turnOrder.Perm
      (allPlayers (channelEx (s.active.getD ⟨0⟩) s.channelCount 0 s).1.playerCount)
    rw [hmeta.turnOrder]
    have hc : (channelEx (s.active.getD ⟨0⟩) s.channelCount 0 s).1.playerCount = s.playerCount := by
      simp [GameState.playerCount, hmeta.config]
    rw [hc]
    exact h1
  · -- the draw phase
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    by_cases hs : s.hasControlledMod (s.active.getD ⟨0⟩) .skipDrawPhase = true
    · simpa only [hs, ite_true] using
        (hinv.of_pop (s2 := { s with pending := rest }) hp (by simp [Frame.contrib])
          ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) rfl)
    · simp only [hs]
      refine ⟨fun hmem => ?_, fun hph => (by cases hph), fun _ _ _ hph => (by cases hph)⟩
      have : Frame.setupHands ∈ rest := by simpa using hmem
      exact hinv.turn (by rw [hp]; exact List.mem_cons_of_mem _ this)
  · -- Ending
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨fun hmem => ?_, fun hph => (by cases hph), fun _ _ _ hph => (by cases hph)⟩
    have : Frame.setupHands ∈ rest := by simpa using hmem
    have h1 := hinv.turn (by rw [hp]; exact List.mem_cons_of_mem _ this)
    exact h1
  · -- Expiration
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hph := hinv.play .expireTurn (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph rfl rfl (fun hf => ?_)
    rcases List.mem_append.mp hf with hnew | hrest
    · unfold expirationFrames at hnew
      split at hnew <;> simp at hnew
    · rw [hp]
      exact List.mem_cons_of_mem _ hrest
  · -- a phase frame for the setup: nothing to do
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_pop hp (by simp [Frame.contrib]) ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) rfl
  · -- Beginning
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_play (by intro phase; cases phase) rfl rfl ?_
    intro member
    have inRest : Frame.setupHands ∈ rest := by simpa using member
    rw [hp]
    exact List.mem_cons_of_mem _ inRest
  · -- Scoring Step
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hP := hold_safeP s (s.active.getD ⟨0⟩)
    refine ⟨fun hmem => ?_, fun hph => (by cases hph), fun _ _ _ hph => (by cases hph)⟩
    have : Frame.setupHands ∈ rest := by simpa using hmem
    have h1 := hinv.turn (by rw [hp]; exact List.mem_cons_of_mem _ this)
    show (hold s (s.active.getD ⟨0⟩)).1.turnOrder.Perm
      (allPlayers (hold s (s.active.getD ⟨0⟩)).1.playerCount)
    rw [hP.turnOrder, show (hold s (s.active.getD ⟨0⟩)).1.playerCount = s.playerCount by
      simp [GameState.playerCount, hP.config]]
    exact h1
  · -- Main
    rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨fun hmem => ?_, fun hph => (by cases hph), fun _ _ _ hph => (by cases hph)⟩
    have : Frame.setupHands ∈ rest := by simpa using hmem
    have h1 := hinv.turn (by rw [hp]; exact List.mem_cons_of_mem _ this)
    exact h1
  · rename_i q n startingHand rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hinv.of_pop hp (by simp [Frame.contrib]) ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) rfl
  · rename_i q n startingHand rest hp
    split at h
    · rename_i s1 es1 hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hmeta := drawOne_meta hd
      obtain ⟨hlen, hoth⟩ := drawOne_hand hwf hown hd
      have hcount : s1.playerCount = s.playerCount := by simp [GameState.playerCount, hmeta.config]
      refine ⟨fun hmem => ?_, fun hph hres r hr => ?_, fun f hf hpf => ?_⟩
      · have : Frame.setupHands ∈ rest := by simpa using hmem
        have h1 := hinv.turn (by rw [hp]; exact List.mem_cons_of_mem _ this)
        show s1.turnOrder.Perm (allPlayers s1.playerCount)
        rw [hmeta.turnOrder, hcount]
        exact h1
      · change s1.phase = .setup at hph
        change s1.result = none at hres
        rw [hmeta.phase] at hph
        rw [hmeta.result] at hres
        have present : s.participates r = true := by
          change s1.participates r = true at hr
          simpa only [GameState.participates, hcount, hmeta.departures] using hr
        have h0 := hinv.hands hph hres r present
        rw [hp, stackContrib_cons] at h0
        show s1.handLen r + stackContrib r (Frame.draw q n (startingHand <|> some (s.zone (.player q .hand)).length) :: rest) = 4
        rw [stackContrib_cons]
        by_cases hrq : r = q
        · subst hrq
          simp only [Frame.contrib, ite_true] at h0 ⊢
          omega
        · simp only [GameState.handLen] at h0 ⊢
          rw [hoth r hrq]
          have hqr : ¬ q = r := fun e => hrq e.symm
          simp only [Frame.contrib, hqr, ite_false] at h0 ⊢
          omega
      · have hf' : f ∈ Frame.draw q n (startingHand <|> some (s.zone (.player q .hand)).length) :: rest := hf
        rcases List.mem_cons.mp hf' with rfl | h
        · simp [Frame.isPlay] at hpf
        · show s1.phase ≠ .setup
          rw [hmeta.phase]
          exact hinv.play f (by rw [hp]; exact List.mem_cons_of_mem _ h) hpf
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine hinv.of_same ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun r _ => ?_) (fun hmem => ?_)
        (fun f hf hpf => ?_)
      · show stackContrib r (Frame.chanceBurnOut q :: Frame.draw q (n + 1) startingHand :: rest) =
          stackContrib r s.pending
        rw [hp, stackContrib_cons, stackContrib_cons]
        simp [Frame.contrib]
      · have : Frame.setupHands ∈ rest := by simpa using hmem
        rw [hp]; exact List.mem_cons_of_mem _ this
      · have hf' : f ∈ Frame.chanceBurnOut q :: Frame.draw q (n + 1) startingHand :: rest := hf
        simp only [List.mem_cons] at hf'
        rcases hf' with rfl | rfl | h
        · simp [Frame.isPlay] at hpf
        · simp [Frame.isPlay] at hpf
        · exact ⟨f, by rw [hp]; exact List.mem_cons_of_mem _ h, hpf⟩
  · rename_i rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_spell_step (hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl)
      ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun hm => ?_)
    rcases resolveFrames_mem hm with h1 | h1
    · rw [hp]; exact List.mem_cons_of_mem _ h1
    · simp [Frame.isPlay] at h1
  · rename_i p src env rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_spell_step (hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl)
      ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun hm => ?_)
    rw [hp]; exact List.mem_cons_of_mem _ hm
  · rename_i p src env e es rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hmeta := (runEffect_safe s p src (env.withMight s.mightTable) e es effectAddPolicy).same
    refine hinv.of_spell_step (hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl)
      ((Keeps.of_sameMeta hmeta).withPending _) (fun hm => ?_)
    rcases List.mem_append.mp hm with h1 | h1
    · rcases runEffect_mem h1 with h2 | ⟨q, k, h2⟩ | ⟨q, h2⟩
      · simp [Frame.isPlay] at h2
      · cases h2
      · cases h2
    · rw [hp]; exact List.mem_cons_of_mem _ h1
  · rename_i item rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hm := finishItem_sameMeta s item
    refine hinv.of_spell_step (hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl)
      ((Keeps.of_sameMeta hm).withPending _) (fun hm' => ?_)
    rcases List.mem_append.mp hm' with h1 | h1
    · have hplay := finishedItemFrames_mem h1
      simp [Frame.isPlay] at hplay
    · rw [hp]; exact List.mem_cons_of_mem _ h1
  · -- Cleanup
    rename_i rest hp
    have hs' : s' = (cleanupFrame s rest).1 := by
      have := Option.some.inj h
      rw [this]
    subst hs'
    have hph0 := hinv.play .cleanup (by rw [hp]; exact List.mem_cons_self) rfl
    have hsub : Frame.setupHands ∈ rest → Frame.setupHands ∈ s.pending := fun hm => by
      rw [hp]
      exact List.mem_cons_of_mem _ hm
    rcases cleanupFrame_cases s rest with ⟨w, e⟩ | ⟨_, _, _, _, e⟩ | ⟨r, hr, e⟩ | ⟨bf, q, e⟩ | ⟨_, _, _, e⟩ | e <;>
      rw [e]
    · exact hinv.of_play hph0 rfl rfl (fun hm => absurd hm (by simp))
    · exact hinv.of_play hph0 rfl rfl (fun hm => hsub (by simpa using hm))
    · exact hinv.of_play (by show r.phase ≠ .setup; rw [hr.same.phase]; exact hph0)
        hr.same.turnOrder hr.same.config (fun hm => hsub (by simpa using hm))
    · exact hinv.of_play hph0 rfl rfl (fun hm => hsub (by simpa using hm))
    · exact hinv.of_play hph0 rfl rfl (fun hm => hsub (by simpa using hm))
    · exact hinv.of_play hph0 rfl rfl (fun hm => hsub hm)
  · rename_i bf att rest hp
    have hph0 := hinv.play (.combatDamage bf att) (by rw [hp]; exact List.mem_cons_self) rfl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_play hph0 rfl rfl (fun hmem => ?_)
    have hm2 : Frame.setupHands ∈ s.startCombat bf att ++ combatSteps bf ++ rest := hmem
    rw [List.append_assoc] at hm2
    rcases List.mem_append.mp hm2 with h1 | h1
    · simpa [Frame.isPlay] using startCombat_play s bf att h1
    · rw [hp]
      exact List.mem_cons_of_mem _ (by simpa [combatSteps] using h1)
  · rename_i bf att rest hp
    have hph0 := hinv.play (.combatResolve bf att) (by rw [hp]; exact List.mem_cons_self) rfl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hP := (combatCleanup_safe s bf att).same
    refine hinv.of_play
      (by show (combatCleanup s bf att).1.phase ≠ .setup; rw [hP.phase]; exact hph0)
      hP.turnOrder hP.config (fun hmem => ?_)
    have hrest : Frame.setupHands ∈ rest := by simpa using hmem
    rw [hp]
    exact List.mem_cons_of_mem _ hrest
  · rename_i bf rest hp
    have hph := hinv.play (.combatResult bf) (by rw [hp]; exact List.mem_cons_self) rfl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_play hph rfl rfl (fun hmem => ?_)
    rw [hp]
    exact List.mem_cons_of_mem _ hmem
  · rename_i bf rest hp
    have hph0 := hinv.play (.combatControl bf) (by rw [hp]; exact List.mem_cons_self) rfl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hP := combatControl_safeP s bf
    refine hinv.of_play
      (by show (combatControl s bf).1.phase ≠ .setup; rw [hP.phase]; exact hph0)
      hP.turnOrder hP.config (fun hmem => ?_)
    have hm2 : Frame.setupHands ∈
        (combatControl s bf).2.1 ++ Frame.cleanup :: rest := hmem
    rcases List.mem_append.mp hm2 with h1 | h1
    · obtain ⟨r, hr⟩ := combatControl_frames s bf _ h1
      cases hr
    · have h2 : Frame.setupHands ∈ rest := by simpa using h1
      rw [hp]
      exact List.mem_cons_of_mem _ h2
  · rename_i bf rest hp
    have hph := hinv.play (.combatFinish bf) (by rw [hp]; exact List.mem_cons_self) rfl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine hinv.of_play hph rfl rfl (fun hmem => ?_)
    have hrest : Frame.setupHands ∈ rest := by simpa using hmem
    rw [hp]
    exact List.mem_cons_of_mem _ hrest
  · rename_i pend rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hm := (triggersStep_spec s pend rest).1.same
    have hph : (triggersStep s pend rest).1.phase ≠ .setup := by
      rw [hm.phase]
      exact hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    refine hinv.of_play hph hm.turnOrder hm.config (fun hm' => ?_)
    have hm2 : Frame.setupHands ∈ (triggersStep s pend rest).2 ∨
        Frame.setupHands ∈ rest := List.mem_append.mp hm'
    rcases hm2 with h1 | h1
    · exact absurd rfl (triggersStep_frames h1).1
    · rw [hp]; exact List.mem_cons_of_mem _ h1
  · rename_i bf rest hp
    have next : s' = (showdownEnd s bf rest).1 :=
      (congrArg Prod.fst (Option.some.inj h)).symm
    subst s'
    have noSetup := hinv.play _ (by rw [hp]; exact List.mem_cons_self) rfl
    rcases showdownEnd_cases s bf rest with ⟨attacker, closed⟩ | closed <;> rw [closed]
    · refine hinv.of_play noSetup rfl rfl (fun member => ?_)
      rw [hp]
      simpa only [List.mem_cons, reduceCtorEq, false_or] using member
    · have safe := endShowdown_safeP s bf
      refine hinv.of_play (safe.phase ▸ noSetup) safe.turnOrder safe.config (fun member => ?_)
      rcases List.mem_append.mp member with new | old
      · obtain ⟨remaining, impossible⟩ := endShowdown_frames s bf true _ new
        cases impossible
      · rw [hp]
        exact List.mem_cons_of_mem _ old
  · exact absurd h (by simp)

/-- A step of work keeps the hand invariant. -/
theorem microStep_handInv {s s' : GameState} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (hinv : HandInv s) (h : microStep s = some (s', es)) : HandInv s' := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  exact (microStep_handInv0 hwf hown hinv h0).withTriggers _

/-- Cost questions account for no cards and are only reached after setup. -/
theorem applyDeclaredAction_handInv {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (hinv : HandInv s) (hl : Legal s a)
    (h : applyDeclaredAction s a = some (s', es)) : HandInv s' := by
  rcases applyDeclaredAction_cases h with ordinary | ⟨_, _, _, _, choice, rfl, _⟩
  · exact applyAction_handInv hwf hown hinv hl ordinary
  · refine hinv.of_play (GameState.actionDeathCostChoice_context choice).1 rfl rfl ?_
    intro member
    simpa using member

/-- Handling or resuming the question preserves the opening-hand invariant. -/
theorem workStep_handInv {s s' : GameState} {es : List Event} (hwf : s.WF) (hown : s.OwnerOk)
    (hinv : HandInv s) (h : workStep s = some (s', es)) : HandInv s' := by
  rcases workStep_cases h with ordinary | ⟨a, rest, pending, resumed⟩
  · exact microStep_handInv hwf hown hinv ordinary
  · have before : HandInv { s with pending := rest } :=
      hinv.of_pop pending (fun _ => rfl) ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) rfl
    rcases resumed with ⟨_, legal, applied⟩ | ⟨rfl, _⟩
    · exact applyDeclaredAction_handInv (s := { s with pending := rest })
        (hwf.congr rfl rfl rfl rfl) (hown.congr rfl rfl) before legal applied
    · exact before

/-- The automatic work keeps the hand invariant. -/
theorem advance_handInv :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event}, s.WF → s.OwnerOk → HandInv s →
      advance n s es = .ok (s', es') → HandInv s'
  | 0, s, s', es, es', _, _, hinv, h => by
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
  | n + 1, s, s', es, es', hwf, hown, hinv, h => by
    unfold advance at h
    split at h
    · split at h
      · split at h
        · rename_i s1 es1 hm
          exact advance_handInv n (workStep_wf hwf hm) (workStep_ownerOk hwf hown hm)
            (workStep_handInv hwf hown hinv hm) h
        · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hinv
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hinv

/-- A step keeps the hand invariant. -/
theorem step_handInv {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (hinv : HandInv s) (h : step fuel s a = .ok (s', es)) :
    HandInv s' := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      exact advance_handInv fuel (applyDeclaredAction_wf hwf hl ha) (applyDeclaredAction_ownerOk hwf hown hl ha)
        (applyDeclaredAction_handInv hwf hown hinv hl ha) h
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Adding an object changes no zone but the one it is added to. -/
theorem addObject_zone_ne {s s' : GameState} {o : Object} {z z' : Zone} {pos : Pos} {id : ObjId}
    (h : addObject s o z pos = some (s', id)) (hz : z' ≠ z) : s'.zone z' = s.zone z' := by
  unfold addObject at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.zone_setZone_ne s hz _
  · exact absurd h (by simp)

/-- Adding cards to a zone that is not a hand leaves the hands alone. -/
theorem addCards_hand {db : CardDB} (owner : PlayerId) (z : Zone)
    (hz : ∀ r, z ≠ .player r .hand) :
    ∀ (cs : List CardId) {s s' : GameState}, addCards db owner z s cs = some s' →
      ∀ r, s'.zone (.player r .hand) = s.zone (.player r .hand)
  | [], s, s', h, r => by
    rw [show addCards db owner z s [] = some s from rfl] at h
    cases h
    rfl
  | c :: cs, s, s', h, r => by
    cases hr : addObject s (newCard db s owner c) z .bottom with
    | none => simp [addCards, hr] at h
    | some r1 =>
      have h' : addCards db owner z r1.1 cs = some s' := by simpa [addCards, hr] using h
      rw [addCards_hand owner z hz cs h' r]
      exact addObject_zone_ne hr (fun e => hz r e.symm)

/-- Registering a Chosen Champion does not add a card to a hand. -/
theorem addChosenChampion_hand {db : CardDB} {p : PlayerId} {s s' : GameState}
    {chosen : Option CardId} (placed : addChosenChampion db p s chosen = some s') (r : PlayerId) :
    s'.zone (.player r .hand) = s.zone (.player r .hand) := by
  obtain ⟨board, added, rfl⟩ := Option.map_eq_some_iff.mp placed
  have unchanged := addCards_hand _ (.player p .championZone) (fun _ => by simp) _ added r
  exact unchanged

/-- Adding a deck leaves the hands alone. -/
theorem GameState.addDeck_hand {db : CardDB} {s s' : GameState} {p : PlayerId} {d : Deck}
    (h : s.addDeck db p d = some s') (r : PlayerId) :
    s'.zone (.player r .hand) = s.zone (.player r .hand) := by
  unfold GameState.addDeck at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s1, h1, s2, h2, s3, h3, s4, h4, s5, h5, h6⟩ := h
  rw [addCards_hand _ _ (fun _ => by simp) _ h6, addCards_hand _ _ (fun _ => by simp) _ h5, addCards_hand _ _ (fun _ => by simp) _ h4,
    addChosenChampion_hand h3, addCards_hand _ _ (fun _ => by simp) _ h2,
    addCards_hand _ _ (fun _ => by simp) _ h1]

/-- Adding the decks leaves the hands alone. -/
theorem GameState.addDecks_hand {db : CardDB} :
    ∀ (ds : List Deck) {s s' : GameState} {i : Nat}, s.addDecks db i ds = some s' →
      ∀ r, s'.zone (.player r .hand) = s.zone (.player r .hand)
  | [], s, s', i, h, r => by
    rw [show s.addDecks db i [] = some s from rfl] at h
    cases h
    rfl
  | d :: ds, s, s', i, h, r => by
    cases hr : s.addDeck db ⟨i⟩ d with
    | none => simp [GameState.addDecks, hr] at h
    | some s1 =>
      have h' : s1.addDecks db (i + 1) ds = some s' := by simpa [GameState.addDecks, hr] using h
      rw [GameState.addDecks_hand ds h' r]
      exact GameState.addDeck_hand hr r

/-- Adding a Limited deck leaves the hands alone. -/
theorem GameState.addLimitedDeck_hand {db : CardDB} {s s' : GameState} {p : PlayerId}
    {d : LimitedDeck}
    (h : s.addLimitedDeck db p d = some s') (r : PlayerId) :
    s'.zone (.player r .hand) = s.zone (.player r .hand) := by
  unfold GameState.addLimitedDeck at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s1, h1, s2, h2, s3, h3, s4, h4, s5, h5, h6⟩ := h
  rw [addCards_hand _ _ (fun _ => by simp) _ h6, addCards_hand _ _ (fun _ => by simp) _ h5, addCards_hand _ _ (fun _ => by simp) _ h4,
    addChosenChampion_hand h3, addCards_hand _ _ (fun _ => by simp) _ h2,
    addCards_hand _ _ (fun _ => by simp) _ h1]

/-- Adding the Limited decks leaves the hands alone. -/
theorem GameState.addLimitedDecks_hand {db : CardDB} :
    ∀ (ds : List LimitedDeck) {s s' : GameState} {i : Nat},
      s.addLimitedDecks db i ds = some s' →
        ∀ r, s'.zone (.player r .hand) = s.zone (.player r .hand)
  | [], s, s', i, h, r => by
    rw [show s.addLimitedDecks db i [] = some s from rfl] at h
    cases h
    rfl
  | d :: ds, s, s', i, h, r => by
    cases hr : s.addLimitedDeck db ⟨i⟩ d with
    | none => simp [GameState.addLimitedDecks, hr] at h
    | some s1 =>
      have h' : s1.addLimitedDecks db (i + 1) ds = some s' := by
        simpa [GameState.addLimitedDecks, hr] using h
      rw [GameState.addLimitedDecks_hand ds h' r]
      exact GameState.addLimitedDeck_hand hr r

/-- **The hand invariant holds at the start.** No hand has a card yet, and the stack accounts for
the four opening cards through the turn order. -/
theorem GameState.initial_handInv {db : CardDB} {config : GameConfig} {decks : List Deck}
    {s : GameState} (h : GameState.initial db config decks = some s) : HandInv s := by
  unfold GameState.initial at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    have hhand : ∀ r, s1.zone (.player r .hand) = [] := fun r => by
      rw [GameState.addDecks_hand decks h1 r]
      simp [GameState.zone, GameState.empty]
    refine ⟨fun hm => ?_, fun _ _ p _ => ?_, fun f hf hpf => ?_⟩
    · simp [startFrames] at hm
    · show (s1.zone (.player p .hand)).length +
        stackContrib p (startFrames config.mode.players) = 4
      rw [hhand p]
      simp only [startFrames, stackContrib_append, List.length_nil]
      rw [stackContrib_zero (l := (List.range config.mode.players).flatMap _) (fun f hf => by
          simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
            or_false] at hf
          obtain ⟨i, -, rfl | rfl⟩ := hf <;> simp [Frame.contrib]),
        stackContrib_zero (l := (List.range config.mode.players).map _) (fun f hf => by
          simp only [List.mem_map] at hf
          obtain ⟨i, -, rfl⟩ := hf
          simp [Frame.contrib])]
      simp [stackContrib, Frame.contrib]
    · have hf' : f ∈ startFrames config.mode.players := hf
      simp only [startFrames, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_map] at hf'
      rcases hf' with (⟨i, -, rfl | rfl⟩ | ⟨i, -, rfl⟩) | rfl <;> simp [Frame.isPlay] at hpf
  · exact absurd h (by simp)

/-- **The hand invariant holds at the start of a Limited game.** No hand has a card yet, and the
stack accounts for the four opening cards through the turn order. -/
theorem GameState.initialLimited_handInv {db : CardDB} {env : LegalityEnv} {config : GameConfig}
    {decks : List LimitedDeck} {s : GameState}
    (h : GameState.initialLimited db env config decks = some s) : HandInv s := by
  unfold GameState.initialLimited at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨s1, h1, rfl⟩ := h
    have hhand : ∀ r, s1.zone (.player r .hand) = [] := fun r => by
      rw [GameState.addLimitedDecks_hand decks h1 r]
      simp [GameState.zone, GameState.empty]
    refine ⟨fun hm => ?_, fun _ _ p _ => ?_, fun f hf hpf => ?_⟩
    · simp [startFrames] at hm
    · show (s1.zone (.player p .hand)).length +
        stackContrib p (startFrames config.mode.players) = 4
      rw [hhand p]
      simp only [startFrames, stackContrib_append, List.length_nil]
      rw [stackContrib_zero (l := (List.range config.mode.players).flatMap _) (fun f hf => by
          simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
            or_false] at hf
          obtain ⟨i, -, rfl | rfl⟩ := hf <;> simp [Frame.contrib]),
        stackContrib_zero (l := (List.range config.mode.players).map _) (fun f hf => by
          simp only [List.mem_map] at hf
          obtain ⟨i, -, rfl⟩ := hf
          simp [Frame.contrib])]
      simp [stackContrib, Frame.contrib]
    · have hf' : f ∈ startFrames config.mode.players := hf
      simp only [startFrames, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_map] at hf'
      rcases hf' with (⟨i, -, rfl | rfl⟩ | ⟨i, -, rfl⟩) | rfl <;> simp [Frame.isPlay] at hpf
  · exact absurd h (by simp)

/-- Every reachable state satisfies the hand invariant. -/
theorem Reachable.handInv {s : GameState} (h : Reachable s) : HandInv s := by
  induction h with
  | init h =>
    cases h with
    | core h => exact GameState.initial_handInv h
    | limited h => exact GameState.initialLimited_handInv h
  | next hs h ih => exact step_handInv (Reachable.inv hs).1 (Reachable.inv hs).2 ih h

/-- **The opening hands.** When the setup is over, that is, when only the first turn is still to
begin, each participating player has exactly four cards in hand (CR 116, 117): the opening draw gives four, and a
mulligan draws as many cards as it sets aside. This holds for every game that runs through `step`
from a set-up game, whatever the answers. -/
theorem Reachable.opening_hands {s : GameState} (h : Reachable s) (hph : s.phase = .setup)
    (hres : s.result = none) (hdone : s.pending = [Frame.beginTurn]) (p : PlayerId)
    (hp : s.participates p = true) : (s.zone (.player p .hand)).length = 4 := by
  have := h.handInv.hands hph hres p hp
  rw [hdone] at this
  simpa [GameState.handLen, stackContrib, Frame.contrib] using this

end Riftbound

end
