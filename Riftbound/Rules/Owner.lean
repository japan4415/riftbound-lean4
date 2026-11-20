module

public import Riftbound.Rules.Move
public import Riftbound.Rules.Actions.Recycle
public import Riftbound.Rules.Actions.Draw
public import Riftbound.Rules.Actions.Channel
public import Riftbound.Rules.Actions.BurnOut
public import Riftbound.Rules.Reorder

/-!
# Ownership of cards in zones

The invariant `OwnerOk` (CR 056) is kept by `moveObj`: an object that enters the Non-Board zone of a
player has that player as owner, because `moveObj` sends it to its owner's zone. This is also what
makes a move to a Non-Board zone succeed (`moveObj_isSome`).
-/

@[expose] public section

namespace Riftbound

namespace GameState

/-- Each zone of a well-formed game lists an object once. -/
theorem zone_nodup {s : GameState} (hwf : s.WF) {z : Zone}
    (hz : z ∈ allZones s.playerCount) : (s.zone z).Nodup := by
  have hperm := flatMap_split (allZones s.playerCount) s.zone z hz
  have hnd : (s.zone z ++ ((allZones s.playerCount).erase z).flatMap s.zone).Nodup :=
    hperm.nodup_iff.mp hwf.nodup
  exact (List.nodup_append.mp hnd).1

/-- A zone that holds an object is a zone of the game. -/
theorem zone_valid_of_mem {s : GameState} (hwf : s.WF) {z : Zone} {id : ObjId}
    (h : id ∈ s.zone z) : z ∈ allZones s.playerCount := by
  by_cases hk : z.key ∈ s.zones
  · obtain ⟨z', hz', hkey⟩ := hwf.zones_valid z.key hk
    have : z' = z := Zone.key_inj hkey
    exact this ▸ hz'
  · have : s.zone z = [] := by
      simp only [zone]
      exact Std.ExtTreeMap.getD_eq_fallback hk
    rw [this] at h
    simp at h

/-- Each zone lists an object once, also when it is empty. -/
theorem zone_nodup_any {s : GameState} (hwf : s.WF) (z : Zone) : (s.zone z).Nodup := by
  by_cases h : s.zone z = []
  · rw [h]; exact List.nodup_nil
  · obtain ⟨id, hid⟩ := List.exists_mem_of_ne_nil _ h
    exact zone_nodup hwf (zone_valid_of_mem hwf hid)

/-- Every object on a zone of the game has attributes. -/
theorem obj_of_mem {s : GameState} (hwf : s.WF) {z : Zone} {id : ObjId}
    (h : id ∈ s.zone z) : ∃ o, s.obj? id = some o := by
  have hm := hwf.table_of_zone id (mem_zoneIds (zone_valid_of_mem hwf h) h)
  simp only [obj?]
  exact ⟨_, Std.ExtTreeMap.getElem?_eq_some_getElem hm⟩

end GameState

/-- The zone a move asked for, once sent to the owner's zone, is a zone of a player only when the
player is the owner (CR 056). -/
theorem normalize_player_nonboard {owner p : PlayerId} {k : ZoneKind} {dst : Zone}
    (h : Zone.normalize owner dst = .player p k) (hk : k.isBoard = false) : owner = p := by
  cases dst with
  | player q k0 =>
    cases hbb : (Zone.player q k0).isBoard with
    | true =>
      simp only [Zone.normalize, hbb, ite_true, Zone.player.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [Zone.isBoard_player] at hbb
      rw [hbb] at hk
      exact absurd hk (by simp)
    | false =>
      simp only [Zone.normalize, hbb, Bool.false_eq_true, ite_false, Zone.player.injEq] at h
      exact h.1
  | battlefieldZone => simp [Zone.normalize] at h
  | chain => simp [Zone.normalize] at h

/-- Objects that are not the moved one keep their attributes. -/
theorem MoveSpec.obj_other {s s' : GameState} {id id' : ObjId} {pos : Pos} {src dst : Zone}
    (hwf : s.WF) (hs : MoveSpec s s' id id' pos src dst) {id2 : ObjId}
    (hm : id2 ∈ s.zoneIds) (hne : id2 ≠ id) : s'.obj? id2 = s.obj? id2 := by
  have hn1 : id2.n ≠ id.n := fun e => hne (by cases id2; cases id; simp_all)
  have hn2 : id2.n ≠ id'.n := by
    rcases hs.fresh with h | h
    · rw [h]; exact hn1
    · have := hwf.lt_nextId id2 hm
      omega
  simp only [GameState.obj?]
  exact hs.objects_other id2.n hn1 hn2

/-- Moving an object keeps `OwnerOk` (CR 056). -/
theorem moveObj_ownerOk {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    (hwf : s.WF) (hown : s.OwnerOk) (h : moveObj s id dst pos = some (s', id')) :
    s'.OwnerOk := by
  obtain ⟨src, d, hs, o, ho, hd⟩ := moveObj_spec_dst h
  have hcount : s'.playerCount = s.playerCount := by simp [GameState.playerCount, hs.config]
  -- the old objects, for an object that was on a zone before and is not the moved one
  have hold : ∀ {p : PlayerId} {k : ZoneKind}, k.isBoard = false → ∀ {id2 : ObjId},
      id2 ∈ s.zone (.player p k) → id2 ≠ id →
        ∀ o2, s'.obj? id2 = some o2 → o2.owner = p := by
    intro p k hk id2 hid2 hne o2 ho2
    have hm := GameState.mem_zoneIds (GameState.zone_valid_of_mem hwf hid2) hid2
    rw [hs.obj_other hwf hm hne] at ho2
    exact hown.owner p k hk id2 hid2 o2 ho2
  refine ⟨fun p k hk id2 hid2 o2 ho2 => ?_⟩
  by_cases hzd : Zone.player p k = d
  · -- the destination
    rw [hzd, hs.zone_dst] at hid2
    rcases List.mem_cons.mp ((Pos.insert_perm pos id' _).mem_iff.mp hid2) with rfl | hold2
    · -- the moved object itself
      have hown2 := hs.owner
      simp only [GameState.obj?] at ho2 ho
      rw [ho2, ho] at hown2
      simp only [Option.map_some, Option.some.injEq] at hown2
      rw [hown2]
      exact normalize_player_nonboard (hd ▸ hzd.symm) hk
    · have hne : id2 ≠ id := by
        intro e
        subst e
        exact hs.ne (GameState.zone_unique hwf hs.dst_mem hs.src_mem hold2 hs.id_mem)
      rw [← hzd] at hold2
      exact hold hk hold2 hne o2 ho2
  · by_cases hzs : Zone.player p k = src
    · rw [hzs, hs.zone_src] at hid2
      have hnd := GameState.zone_nodup hwf hs.src_mem
      obtain ⟨hne, hmem⟩ := (List.Nodup.mem_erase_iff hnd).mp hid2
      rw [← hzs] at hmem
      exact hold hk hmem hne o2 ho2
    · rw [hs.zone_other hzs hzd] at hid2
      have hne : id2 ≠ id := by
        intro e
        subst e
        exact hzs (GameState.zone_unique hwf hs.src_mem
          (GameState.zone_valid_of_mem hwf hid2) hs.id_mem hid2)
      exact hold hk hid2 hne o2 ho2

/-- A zone of a player is a zone of the game only if the player is one of the players. -/
theorem Zone.lt_of_valid_player {n : Nat} {p : PlayerId} {k : ZoneKind}
    (h : (Zone.player p k).Valid n) : p.n < n := by
  unfold Zone.Valid allZones at h
  simp only [List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map] at h
  rcases h with h | h | ⟨i, hi, k', -, hk⟩
  · simp at h
  · simp at h
  · simp only [Zone.player.injEq] at hk
    obtain ⟨hp, -⟩ := hk
    rw [← hp]
    exact hi

/-- A move succeeds when the object is on a zone and the zone it is asked to go to, sent to the
owner's zone, is a zone of the game and another zone than the one it is on. -/
theorem moveObj_isSome {s : GameState} (hwf : s.WF) {z : Zone} {id : ObjId}
    (hid : id ∈ s.zone z) (dst : Zone) (pos : Pos)
    (hdst : ∀ o, s.obj? id = some o →
      (Zone.normalize o.owner dst).Valid s.playerCount ∧ z ≠ Zone.normalize o.owner dst) :
    ∃ r, moveObj s id dst pos = some r := by
  obtain ⟨o, ho⟩ := GameState.obj_of_mem hwf hid
  have hloc : s.locate id = some z :=
    GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hid) hid
  obtain ⟨hv, hne⟩ := hdst o ho
  unfold moveObj
  rw [hloc, ho]
  dsimp only
  split
  · rename_i hc
    rcases hc with hc | hc
    · exact absurd hc hne
    · exact absurd hv hc
  · split <;> exact ⟨_, rfl⟩

/-- Recycling the objects of a Non-Board zone of a player (other than the Main Deck and the hand)
succeeds, and no hand changes. -/
theorem recycleAll_some {p q : PlayerId} {k : ZoneKind} (hk : k.isBoard = false)
    (hk2 : k ≠ .mainDeck) (hk3 : k ≠ .hand) :
    ∀ (ids : List ObjId) {s : GameState}, s.WF → s.OwnerOk → ids.Nodup →
      (∀ id ∈ ids, id ∈ s.zone (.player q k)) →
      ∃ s', recycleAll p s ids = some s' ∧
        ∀ r, s'.zone (.player r .hand) = s.zone (.player r .hand)
  | [], s, _, _, _, _ => ⟨s, rfl, fun _ => rfl⟩
  | id :: ids, s, hwf, hown, hnd, hall => by
    have hid := hall id List.mem_cons_self
    obtain ⟨o, ho⟩ := GameState.obj_of_mem hwf hid
    have howner : o.owner = q := hown.owner q k hk id hid o ho
    have hqn : q.n < s.playerCount :=
      Zone.lt_of_valid_player (GameState.zone_valid_of_mem hwf hid)
    have hnorm : Zone.normalize o.owner (.player p .mainDeck) = .player q .mainDeck := by
      rw [howner]
      simp [Zone.normalize, Zone.isBoard]
    obtain ⟨r, hr⟩ := moveObj_isSome hwf hid (.player p .mainDeck) .bottom (fun o' ho' => by
      have : o' = o := Option.some.inj (ho'.symm.trans ho)
      subst this
      rw [hnorm]
      exact ⟨Zone.valid_player hqn _, fun e => hk2 (by simpa using e)⟩)
    obtain ⟨src, d, hs, o', ho', hd⟩ := moveObj_spec_dst hr
    have hsrc : src = .player q k :=
      Option.some.inj (hs.locate.symm.trans
        (GameState.locate_eq hwf (GameState.zone_valid_of_mem hwf hid) hid))
    have hnd' : id ∉ ids ∧ ids.Nodup := List.nodup_cons.mp hnd
    have hz1 := hs.zone_src
    rw [hsrc] at hz1
    have hrest : ∀ id2 ∈ ids, id2 ∈ r.1.zone (.player q k) := by
      intro id2 hid2
      rw [hz1]
      have hne : id2 ≠ id := fun e => hnd'.1 (e ▸ hid2)
      exact (List.Nodup.mem_erase_iff (GameState.zone_nodup hwf (hsrc ▸ hs.src_mem))).mpr
        ⟨hne, hall id2 (List.mem_cons_of_mem _ hid2)⟩
    obtain ⟨s', hs', hhand⟩ := recycleAll_some hk hk2 hk3 ids (moveObj_wf hwf hr)
      (moveObj_ownerOk hwf hown hr) hnd'.2 hrest
    refine ⟨s', ?_, fun r' => ?_⟩
    · have : recycleAll p s (id :: ids) = (moveObj s id (.player p .mainDeck) .bottom).bind
          (fun r => recycleAll p r.1 ids) := rfl
      rw [this, hr]
      exact hs'
    · rw [hhand r']
      have hd2 : d = .player q .mainDeck := by
        have hoo : o' = o := Option.some.inj (ho'.symm.trans ho)
        rw [hd, hoo, hnorm]
      refine hs.zone_other ?_ ?_
      · rw [hsrc]
        intro e
        simp only [Zone.player.injEq] at e
        exact hk3 e.2.symm
      · rw [hd2]
        intro e
        simp at e

/-- Recycling keeps `OwnerOk`. -/
theorem recycleAll_ownerOk (p : PlayerId) :
    ∀ (ids : List ObjId) {s s' : GameState}, s.WF → s.OwnerOk →
      recycleAll p s ids = some s' → s'.OwnerOk
  | [], s, s', _, hown, h => by
    rw [show recycleAll p s [] = some s from rfl] at h
    cases h
    exact hown
  | id :: ids, s, s', hwf, hown, h => by
    obtain ⟨r, hr, h⟩ := recycleAll_cons h
    exact recycleAll_ownerOk p ids (moveObj_wf hwf hr) (moveObj_ownerOk hwf hown hr) h

/-- Drawing keeps `OwnerOk`. -/
theorem drawOne_ownerOk {s s' : GameState} {p : PlayerId} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (h : drawOne s p = some (s', es)) : s'.OwnerOk := by
  unfold drawOne at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact moveObj_ownerOk hwf hown hm

/-- Rearranging a zone keeps `OwnerOk`. -/
theorem GameState.ownerOk_reorder {s : GameState} (hown : s.OwnerOk) {z : Zone} {l : List ObjId}
    (hp : l.Perm (s.zone z)) : (s.reorder z l).OwnerOk := by
  refine ⟨fun p k hk id hid o ho => ?_⟩
  have hobj : (s.reorder z l).obj? id = s.obj? id := rfl
  rw [hobj] at ho
  by_cases hz : Zone.player p k = z
  · rw [hz] at hid
    have hid' : id ∈ s.zone z := hp.mem_iff.mp (by
      have : (s.reorder z l).zone z = l := GameState.zone_setZone_self s z l
      rwa [this] at hid)
    rw [← hz] at hid'
    exact hown.owner p k hk id hid' o ho
  · have : (s.reorder z l).zone (.player p k) = s.zone (.player p k) :=
      GameState.zone_setZone_ne s hz l
    rw [this] at hid
    exact hown.owner p k hk id hid o ho

/-- Gaining points keeps `OwnerOk`. -/
theorem GameState.ownerOk_gainPoints {s : GameState} (h : s.OwnerOk) (p : PlayerId) (n : Nat) :
    (s.gainPoints p n).OwnerOk := h.congr rfl rfl

/-- Drawing takes one card off the Main Deck and puts one in the hand (CR 414), in a game that keeps
`OwnerOk`: no assumption about the owner of the card is needed. -/
theorem drawOne_lengths_of_ownerOk {s s' : GameState} {p : PlayerId} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (h : drawOne s p = some (s', es)) :
    (s'.zone (.player p .mainDeck)).length + 1 = (s.zone (.player p .mainDeck)).length ∧
      (s'.zone (.player p .hand)).length = (s.zone (.player p .hand)).length + 1 := by
  have hne : s.zone (.player p .mainDeck) ≠ [] := by
    intro hempty
    unfold drawOne at h
    rw [hempty] at h
    simp at h
  obtain ⟨id, hid⟩ := List.exists_mem_of_ne_nil _ hne
  have hp : p.n < s.playerCount :=
    Zone.lt_of_valid_player (GameState.zone_valid_of_mem hwf hid)
  exact drawOne_lengths hwf hp h (fun id2 hid2 o ho => hown.owner p .mainDeck rfl id2 hid2 o ho)

/-- One Channel keeps `OwnerOk`. -/
theorem channelOne_ownerOk {s s' : GameState} {p : PlayerId} {es : List Event}
    (hwf : s.WF) (hown : s.OwnerOk) (h : channelOne s p = some (s', es)) : s'.OwnerOk := by
  unfold channelOne at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact moveObj_ownerOk hwf hown hm

/-- Channeling keeps `OwnerOk`. -/
theorem channel_ownerOk (p : PlayerId) :
    ∀ (n : Nat) {s : GameState}, s.WF → s.OwnerOk → (channel p n s).1.OwnerOk
  | 0, s, _, hown => hown
  | n + 1, s, hwf, hown => by
    unfold channel
    cases hc : channelOne s p with
    | none => simpa using hown
    | some r =>
      simpa using channel_ownerOk p n (channelOne_wf hwf hc) (channelOne_ownerOk hwf hown hc)

end Riftbound

end
