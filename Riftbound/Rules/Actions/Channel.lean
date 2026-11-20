module

public import Riftbound.Rules.Move
public import Riftbound.State.Event

/-!
# Channel

Channel puts the top Rune of the Rune Deck onto the Base, ready (CR 431). With too few Runes it
puts as many as there are, and nothing else happens: no Burn Out (CR 431.3).
-/

@[expose] public section

namespace Riftbound

/-- Put the top Rune of the Rune Deck onto the player's Base (CR 431). `none` if the deck is
empty. A Rune comes ready: a move across a Non-Board zone resets exhaustion (CR 124.1). -/
def channelOne (s : GameState) (p : PlayerId) : Option (GameState × List Event) :=
  match s.zone (.player p .runeDeck) with
  | [] => none
  | top :: _ =>
    (moveObj s top (.player p .base)).map
      (fun r => (r.1, [Event.moved top r.2 (.player p .base)]))

/-- Channel `n` Runes: as many as the Rune Deck holds, up to `n`. It never fails (CR 431.3). -/
def channel (p : PlayerId) : Nat → GameState → GameState × List Event
  | 0, s => (s, [])
  | n + 1, s =>
    match channelOne s p with
    | none => (s, [])
    | some (s1, es1) =>
      let r := channel p n s1
      (r.1, es1 ++ r.2)

/-- One Channel keeps the game well formed. -/
theorem channelOne_wf {s s' : GameState} {p : PlayerId} {es : List Event}
    (hwf : s.WF) (h : channelOne s p = some (s', es)) : s'.WF := by
  unfold channelOne at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact moveObj_wf hwf hm

/-- **I1** (channel, one Rune). -/
theorem channelOne_physIds {s s' : GameState} {p : PlayerId} {es : List Event}
    (hwf : s.WF) (h : channelOne s p = some (s', es)) : s'.physIds.Perm s.physIds := by
  unfold channelOne at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact moveObj_physIds hwf hm

/-- Channeling keeps the game well formed. -/
theorem channel_wf (p : PlayerId) :
    ∀ (n : Nat) {s : GameState}, s.WF → (channel p n s).1.WF
  | 0, s, hwf => hwf
  | n + 1, s, hwf => by
    unfold channel
    cases hc : channelOne s p with
    | none => simpa using hwf
    | some r => simpa using channel_wf p n (channelOne_wf hwf hc)

/-- **I1** (channel). Channeling keeps the physical cards. -/
theorem channel_physIds (p : PlayerId) :
    ∀ (n : Nat) {s : GameState}, s.WF → (channel p n s).1.physIds.Perm s.physIds
  | 0, s, hwf => List.Perm.refl _
  | n + 1, s, hwf => by
    unfold channel
    cases hc : channelOne s p with
    | none => simp
    | some r =>
      simp only
      exact (channel_physIds p n (channelOne_wf hwf hc)).trans (channelOne_physIds hwf hc)

/-- One Channel changes nothing but the zones, the object table and the counters. -/
theorem channelOne_meta {s s' : GameState} {p : PlayerId} {es : List Event}
    (h : channelOne s p = some (s', es)) : SameMeta s s' := by
  unfold channelOne at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    obtain ⟨src, d, hs⟩ := moveObj_spec hm
    exact hs.other

/-- Channeling changes nothing but the zones, the object table and the counters. -/
theorem channel_sameMeta (p : PlayerId) :
    ∀ (n : Nat) (s : GameState), SameMeta s (channel p n s).1
  | 0, s => SameMeta.refl s
  | n + 1, s => by
    unfold channel
    cases hc : channelOne s p with
    | none => simpa using SameMeta.refl s
    | some r =>
      have h1 := channelOne_meta hc
      have h2 := channel_sameMeta p n r.1
      simpa using h1.trans h2

end Riftbound

end
