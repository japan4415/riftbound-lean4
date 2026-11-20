module

public import Riftbound.Rules.Move
public import Riftbound.State.Event

/-!
# Draw

Draw one card (CR 414): the top card of the Main Deck goes to the hand. Drawing from an empty
deck is not done here: it is a Burn Out (CR 432), see `Riftbound.Rules.Actions.BurnOut`, which
the engine handles because it needs decisions.
-/

@[expose] public section

namespace Riftbound

/-- Draw the top card of the player's Main Deck into their hand (CR 414). `none` if the deck is
empty. -/
def drawOne (s : GameState) (p : PlayerId) : Option (GameState × List Event) :=
  match s.zone (.player p .mainDeck) with
  | [] => none
  | top :: _ =>
    (moveObj s top (.player p .hand)).map
      (fun r => (r.1, [Event.moved top r.2 (.player p .hand)]))

/-- Drawing keeps the game well formed. -/
theorem drawOne_wf {s s' : GameState} {p : PlayerId} {es : List Event}
    (hwf : s.WF) (h : drawOne s p = some (s', es)) : s'.WF := by
  unfold drawOne at h
  split at h
  · exact absurd h (by simp)
  · rename_i top rest hz
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact moveObj_wf hwf hm

/-- **I1** (draw). Drawing keeps the physical cards. -/
theorem drawOne_physIds {s s' : GameState} {p : PlayerId} {es : List Event}
    (hwf : s.WF) (h : drawOne s p = some (s', es)) : s'.physIds.Perm s.physIds := by
  unfold drawOne at h
  split at h
  · exact absurd h (by simp)
  · rename_i top rest hz
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact moveObj_physIds hwf hm

/-- Drawing takes one card off the Main Deck and puts one in the hand, when the card belongs to
the player (CR 414). -/
theorem drawOne_lengths {s s' : GameState} {p : PlayerId} {es : List Event}
    (hwf : s.WF) (hp : p.n < s.playerCount) (h : drawOne s p = some (s', es))
    (howner : ∀ id ∈ s.zone (.player p .mainDeck), ∀ o, s.obj? id = some o → o.owner = p) :
    (s'.zone (.player p .mainDeck)).length + 1 = (s.zone (.player p .mainDeck)).length ∧
      (s'.zone (.player p .hand)).length = (s.zone (.player p .hand)).length + 1 := by
  unfold drawOne at h
  split at h
  · exact absurd h (by simp)
  · rename_i top rest hz
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨src, d, hs, o, ho, hd⟩ := moveObj_spec_dst hm
    have htop : top ∈ s.zone (.player p .mainDeck) := by rw [hz]; exact List.mem_cons_self
    have hsrc : src = .player p .mainDeck :=
      Option.some.inj (hs.locate.symm.trans (GameState.locate_eq hwf (Zone.valid_player hp _) htop))
    have hown : o.owner = p := howner top htop o ho
    have hdst : d = .player p .hand := by
      rw [hd, hown]
      simp [Zone.normalize, Zone.isBoard]
    have h1 := hs.zone_src
    have h2 := hs.zone_dst
    rw [hsrc] at h1
    rw [hdst] at h2
    refine ⟨?_, ?_⟩
    · rw [h1, List.length_erase_of_mem htop]
      have : 0 < (s.zone (.player p .mainDeck)).length := List.length_pos_of_mem htop
      omega
    · rw [h2, (Pos.insert_perm _ _ _).length_eq]
      simp

/-- Drawing changes nothing but the zones, the object table and the counters. -/
theorem drawOne_meta {s s' : GameState} {p : PlayerId} {es : List Event}
    (h : drawOne s p = some (s', es)) : SameMeta s s' := by
  unfold drawOne at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨src, d, hs⟩ := moveObj_spec hm
    exact hs.other

end Riftbound

end
