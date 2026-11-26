module

public import Riftbound.Rules.Battlefield

/-! # Object changes when removing a player (CR 652) -/

@[expose] public section

namespace Riftbound

/-- Move an object to its owner's zone as part of removing a player (CR 652.1, 652.3).
A change of zone required by removal does not offer the departing player another choice. -/
def moveForPlayerRemoval (destination : ZoneKind) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  match s.obj? id with
  | none => (s, [])
  | some o =>
    let zone := Zone.player o.owner destination
    match moveObj s id zone with
    | none => (s, [])
    | some (next, moved) => (next, [.moved id moved zone])

theorem moveForPlayerRemoval_safe (destination : ZoneKind) (s : GameState) (id : ObjId) :
    Safe s (moveForPlayerRemoval destination s id).1 := by
  unfold moveForPlayerRemoval
  split
  · exact Safe.refl s
  · dsimp only
    split
    · exact Safe.refl s
    · rename_i next moved h
      exact Safe.moveObj h

/-- Banish the permanents, runes and facedown cards owned or controlled by the departing player
(CR 652.1). Events are zone changes from the rules, with no player credited for banishing. -/
def banishForPlayerRemoval (s : GameState) (departing : PlayerId) : GameState × List Event :=
  let ownedOrControlled := fun id => (s.obj? id).any fun o =>
    o.owner == departing || o.controller == departing
  let permanentsAndRunes := s.inPlay.filter fun id => (s.cardDef? id).any fun card =>
    card.hasType .unit || card.hasType .gear || card.hasType .rune
  let facedown := s.players.flatMap fun p => s.zone (.player p .hidden)
  applyEach (moveForPlayerRemoval .banishment) s
    ((permanentsAndRunes ++ facedown).filter ownedOrControlled)

theorem banishForPlayerRemoval_safe (s : GameState) (departing : PlayerId) :
    Safe s (banishForPlayerRemoval s departing).1 :=
  applyEach_safe (moveForPlayerRemoval_safe .banishment) _ _

/-- Remove the departing player's physical cards from play while preserving the physical
inventory in their out-of-game zone (CR 652.3). -/
def archivePlayerCards (s : GameState) (departing : PlayerId) : GameState × List Event :=
  let outside := s.zone (.player departing .outOfGame)
  let physical := s.zoneIds.filter fun id =>
    !outside.contains id && (s.obj? id).any fun o =>
      o.owner == departing && o.kind.phys?.isSome
  applyEach (moveForPlayerRemoval .outOfGame) s physical

theorem archivePlayerCards_safe (s : GameState) (departing : PlayerId) :
    Safe s (archivePlayerCards s departing).1 :=
  applyEach_safe (moveForPlayerRemoval_safe .outOfGame) _ _

/-- Keep the location and status of a Battlefield while replacing its definition. -/
def Object.asBlankBattlefield (o : Object) (blank : CardId) : Object :=
  { o with kind := .token blank, replaces := none }

/-- A blank Battlefield inherits the old Battlefield's status and stays at the same target
identifier (CR 439.1, 652.2). Its original physical card goes out of the game. -/
def retireBattlefield (s : GameState) (field : ObjId) (blank : CardId) :
    Option (GameState × Option ObjId) := do
  let old ← s.obj? field
  if !(s.battlefields.contains field) then none else
    match old.kind.phys? with
    | some _ =>
      let archived : Object :=
        { kind := old.kind, owner := old.owner, controller := old.owner, timestamp := ⟨0⟩ }
      let (next, archiveId) ← addObject s archived (.player old.owner .outOfGame)
      some (next.modObj field (·.asBlankBattlefield blank), some archiveId)
    | none => some (s.modObj field (·.asBlankBattlefield blank), none)

private theorem obj?_added {s next : GameState} {o : Object} {z : Zone} {new : ObjId}
    (added : addObject s o z = some (next, new)) :
    next.obj? new = some { o with timestamp := ⟨s.nextTimestamp⟩ } := by
  obtain ⟨-, rfl, rfl⟩ := addObject_spec added
  simp [GameState.obj?]

private theorem obj?_other_add {s next : GameState} {o : Object} {z : Zone} {new id : ObjId}
    (added : addObject s o z = some (next, new)) (distinct : new.n ≠ id.n) :
    next.obj? id = s.obj? id := by
  obtain ⟨-, rfl, rfl⟩ := addObject_spec added
  simp [GameState.obj?, Std.ExtTreeMap.getElem?_insert, distinct]

private theorem archive_then_blank_phys {s next : GameState} {field archived : ObjId}
    {old stored : Object} (hwf : s.WF) (fieldInZones : field ∈ s.zoneIds)
    (oldAtField : s.obj? field = some old) (sameKind : stored.kind = old.kind)
    (added : addObject s stored (.player old.owner .outOfGame) = some (next, archived))
    (blank : CardId) :
    (next.modObj field (·.asBlankBattlefield blank)).physIds.Perm s.physIds := by
  let final := next.modObj field (·.asBlankBattlefield blank)
  let phys (g : GameState) (id : ObjId) := (g.obj? id).bind (·.kind.phys?)
  have fresh : archived.n = s.nextId := congrArg ObjId.n (addObject_spec added).2.1
  have freshOther (id : ObjId) (present : id ∈ s.zoneIds) : archived.n ≠ id.n := by
    rw [fresh]
    exact (Nat.ne_of_lt (hwf.lt_nextId id present)).symm
  have archivePhys : phys final archived = phys s field := by
    unfold phys final
    rw [GameState.obj?_modObj, ite_eq_right (freshOther field fieldInZones).symm,
      obj?_added added, oldAtField]
    simp [sameKind]
  have fieldBlank : phys final field = none := by
    unfold phys final
    rw [GameState.obj?_modObj, ite_eq_left rfl, obj?_other_add added (freshOther field fieldInZones),
      oldAtField]
    rfl
  have restPhys : (s.zoneIds.erase field).filterMap (phys final) =
      (s.zoneIds.erase field).filterMap (phys s) := by
    apply filterMap_congr_mem
    intro id present
    obtain ⟨different, previous⟩ := (List.Nodup.mem_erase_iff hwf.nodup).mp present
    have keyDifferent : field.n ≠ id.n := fun same =>
      different (by cases field; cases id; simp_all)
    unfold phys final
    rw [GameState.obj?_modObj, ite_eq_right keyDifferent, obj?_other_add added (freshOther id previous)]
  have newOrder : final.zoneIds.Perm (archived :: field :: s.zoneIds.erase field) :=
    (addObject_zoneIds added).trans ((List.perm_cons_erase fieldInZones).cons archived)
  have finalOrder := newOrder.filterMap (phys final)
  rw [List.filterMap_cons, List.filterMap_cons, archivePhys, fieldBlank, restPhys] at finalOrder
  have oldOrder := (List.perm_cons_erase fieldInZones).filterMap (phys s)
  rw [List.filterMap_cons] at oldOrder
  exact finalOrder.trans oldOrder.symm

private theorem blank_token_phys {s : GameState} {field : ObjId} {old : Object}
    (oldAtField : s.obj? field = some old) (noPhysicalCard : old.kind.phys? = none)
    (blank : CardId) :
    (s.modObj field (·.asBlankBattlefield blank)).physIds = s.physIds := by
  unfold GameState.physIds
  apply filterMap_congr_mem
  intro id _
  rw [GameState.obj?_modObj]
  by_cases key : field.n = id.n
  · have same : id = field := by cases field; cases id; simp_all
    subst id
    simp [oldAtField, Object.asBlankBattlefield, ObjKind.phys?]
    exact noPhysicalCard.symm
  · rw [ite_eq_right key]

/-- The replacement preserves the zones' well-formedness and the physical card inventory. -/
theorem retireBattlefield_safe {s next : GameState} {field : ObjId} {blank : CardId}
    {archive : Option ObjId} (changed : retireBattlefield s field blank = some (next, archive)) :
    Safe s next := by
  cases found : s.obj? field with
  | none => simp [retireBattlefield, found] at changed
  | some old =>
    cases inField : s.battlefields.contains field with
    | false =>
      simp only [retireBattlefield, found, Option.bind_eq_bind, Option.bind_some, inField,
        Bool.not_false, ↓reduceIte, reduceCtorEq] at changed
    | true =>
      cases kind : old.kind.phys? with
      | none =>
        simp only [retireBattlefield, found, Option.bind_eq_bind, Option.bind_some, inField,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte, kind, Option.some.injEq,
          Prod.mk.injEq] at changed
        obtain ⟨rfl, -⟩ := changed
        exact ⟨fun hwf => GameState.wf_modObj hwf _ _,
          fun _ => (blank_token_phys found kind blank).symm ▸ List.Perm.refl _,
          fun _ hown => GameState.ownerOk_modObj hown _ (fun _ => rfl),
          GameState.sameMeta_modObj _ _ _⟩
      | some physical =>
        simp only [retireBattlefield, found, Option.bind_eq_bind, Option.bind_some, inField,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte, kind, Option.bind_eq_some_iff] at changed
        obtain ⟨⟨intermediate, stored⟩, added, changed⟩ := changed
        simp only [Option.some.injEq, Prod.mk.injEq] at changed
        obtain ⟨rfl, -⟩ := changed
        have battlefieldZone : field ∈ s.zone .battlefieldZone :=
          (List.mem_filter.mp (List.contains_iff_mem.mp inField)).1
        have fieldInGame := GameState.mem_zoneIds (by simp [allZones]) battlefieldZone
        exact ⟨fun hwf => GameState.wf_modObj (addObject_wf hwf added) _ _,
          fun hwf => archive_then_blank_phys hwf fieldInGame found (by rfl) added blank,
          fun hwf hown => GameState.ownerOk_modObj (addObject_ownerOk hwf hown added) _ (fun _ => rfl),
          (addObject_sameMeta added).trans (GameState.sameMeta_modObj _ _ _)⟩

/-- Replacing the Battlefield leaves every other existing object unchanged, including occupants
and Hidden cards whose location is that Battlefield (CR 652.2.b). -/
theorem retireBattlefield_otherObject {s next : GameState} {field id : ObjId} {blank : CardId}
    {archive : Option ObjId} (changed : retireBattlefield s field blank = some (next, archive))
    (hwf : s.WF) (present : id ∈ s.zoneIds) (different : id ≠ field) :
    next.obj? id = s.obj? id := by
  have keyDifferent : field.n ≠ id.n := fun same =>
    different (by cases field; cases id; simp_all)
  cases found : s.obj? field with
  | none => simp [retireBattlefield, found] at changed
  | some old =>
    cases inField : s.battlefields.contains field with
    | false =>
      simp only [retireBattlefield, found, Option.bind_eq_bind, Option.bind_some, inField,
        Bool.not_false, ↓reduceIte, reduceCtorEq] at changed
    | true =>
      simp only [retireBattlefield, found, Option.bind_eq_bind, Option.bind_some, inField,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte] at changed
      cases kind : old.kind.phys? with
      | none =>
        simp only [kind, Option.some.injEq, Prod.mk.injEq] at changed
        obtain ⟨rfl, -⟩ := changed
        rw [GameState.obj?_modObj, ite_eq_right keyDifferent]
      | some physical =>
        simp only [kind, Option.bind_eq_some_iff] at changed
        obtain ⟨⟨intermediate, stored⟩, added, changed⟩ := changed
        simp only [Option.some.injEq, Prod.mk.injEq] at changed
        obtain ⟨rfl, -⟩ := changed
        have fresh : stored.n = s.nextId := congrArg ObjId.n (addObject_spec added).2.1
        have freshKey : stored.n ≠ id.n := by
          rw [fresh]
          exact (Nat.ne_of_lt (hwf.lt_nextId id present)).symm
        rw [GameState.obj?_modObj, ite_eq_right keyDifferent, obj?_other_add added freshKey]

/-- The departing player's Battlefield still in use. A token may be standing in for the
original physical card. -/
def GameState.contributedBattlefield (s : GameState) (departing : PlayerId) : Option ObjId :=
  s.battlefields.find? fun field => (s.obj? field).any fun o =>
    if o.kind.phys?.isSome then o.owner == departing else
      o.replaces.any (fun replaced => (s.obj? replaced).any (fun original =>
        original.owner == departing && original.kind.phys?.isSome))

/-- Counter an item whose controller has left (CR 652.4). A physical spell still follows its
normal Chain exit rules. An ability ceases to exist. -/
def counterForPlayerRemoval (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | none => (s, [])
  | some o =>
    if !(s.zone .chain).contains id then (s, []) else
      match o.kind with
      | .chainAbility .. => ((removeObj s id).getD s, [])
      | _ =>
        match moveObj s id (s.chainDestination id o .trash) with
        | none => (s, [])
        | some (next, moved) => (next, s.chainExitEvents o id moved .trash)

theorem counterForPlayerRemoval_safe (s : GameState) (id : ObjId) :
    Safe s (counterForPlayerRemoval s id).1 := by
  unfold counterForPlayerRemoval
  split
  · exact Safe.refl s
  · rename_i o found
    split
    · exact Safe.refl s
    · split
      next card index source ability =>
        cases removed : removeObj s id with
        | none => exact Safe.refl _
        | some next =>
          simp only [Option.getD_some]
          exact ⟨fun hwf => removeObj_wf hwf removed,
            fun hwf => removeObj_physIds hwf removed found (by rw [ability]; rfl),
            fun hwf hown => removeObj_ownerOk hwf hown removed, removeObj_sameMeta removed⟩
      all_goals
        split
        · exact Safe.refl s
        · rename_i hm
          exact Safe.moveObj hm

/-- Apply the object changes for a departure in rules order, keeping the original Battlefield
identifier so existing targets and occupancy still refer to it (CR 652.1, 652.2, 652.3, 652.4). -/
def removePlayerObjects (s : GameState) (departing : PlayerId) (blank : CardId) :
    Option (GameState × List Event) := do
  let (board, banished) := banishForPlayerRemoval s departing
  let (board, replaced) ← (match board.contributedBattlefield departing with
    | none => some (board, [])
    | some field => do
      let (next, archived) ← retireBattlefield board field blank
      return (next, archived.toList.map (fun id => .moved field id (.player departing .outOfGame))))
  let (remaining, removed) := archivePlayerCards board departing
  let chain := (remaining.zone .chain).filter fun id =>
    (remaining.obj? id).any (·.controller == departing)
  let (next, countered) := applyEach counterForPlayerRemoval remaining chain
  return (next, banished ++ replaced ++ removed ++ countered)

/-- Removal of the player's objects preserves the physical inventory and zone invariants. -/
theorem removePlayerObjects_safe {s next : GameState} {departing : PlayerId} {blank : CardId}
    {events : List Event} (h : removePlayerObjects s departing blank = some (next, events)) :
    Safe s next := by
  unfold removePlayerObjects at h
  dsimp only at h
  obtain ⟨⟨board, replaced⟩, hBoard, hRest⟩ := Option.bind_eq_some_iff.mp h
  have boardSafe : Safe (banishForPlayerRemoval s departing).1 board := by
    split at hBoard
    · simp only [Option.some.injEq, Prod.mk.injEq] at hBoard
      obtain ⟨rfl, -⟩ := hBoard
      exact Safe.refl _
    · obtain ⟨⟨retired, archived⟩, changed, hPair⟩ := Option.bind_eq_some_iff.mp hBoard
      simp only at hPair
      obtain ⟨rfl, -⟩ := hPair
      exact retireBattlefield_safe changed
  simp only at hRest
  obtain ⟨rfl, -⟩ := hRest
  exact (banishForPlayerRemoval_safe s departing).trans (boardSafe.trans
    ((archivePlayerCards_safe board departing).trans (applyEach_safe counterForPlayerRemoval_safe _ _)))

/-- A selected Battlefield can be retired. A physical card requires a registered owner
for its out-of-game zone. -/
theorem retireBattlefield_isSome {s : GameState} {field : ObjId} {old : Object}
    (hfield : field ∈ s.battlefields) (found : s.obj? field = some old)
    (owner : old.kind.phys?.isSome = true → old.owner.n < s.playerCount) (blank : CardId) :
    ∃ result, retireBattlefield s field blank = some result := by
  cases physical : old.kind.phys? with
  | none =>
    exact ⟨(s.modObj field (·.asBlankBattlefield blank), none),
      by simp [retireBattlefield, found, hfield, physical]⟩
  | some id =>
    have valid := Zone.valid_player (owner (by simp [physical])) .outOfGame
    simp [retireBattlefield, found, hfield, physical, addObject, valid, Zone.fits]

/-- Removing the objects of a registered seat can always archive its Battlefield. -/
theorem removePlayerObjects_isSome (s : GameState) (departing : PlayerId)
    (registered : departing.n < s.playerCount) (blank : CardId) :
    ∃ result, removePlayerObjects s departing blank = some result := by
  let board := (banishForPlayerRemoval s departing).1
  have size : board.playerCount = s.playerCount := by
    simp only [board, GameState.playerCount, (banishForPlayerRemoval_safe s departing).same.config]
  cases chosen : board.contributedBattlefield departing with
  | none =>
    exact ⟨_, by unfold removePlayerObjects; dsimp only; rw [show _ = none from chosen]; rfl⟩
  | some field =>
    have member : field ∈ board.battlefields := List.mem_of_find?_eq_some chosen
    have selected := List.find?_some chosen
    cases found : board.obj? field with
    | none => simp [found] at selected
    | some old =>
      have oldOwner (physical : old.kind.phys?.isSome = true) : old.owner.n < board.playerCount := by
        have same : old.owner = departing := by simpa [found, physical] using selected
        simpa only [size, same] using registered
      obtain ⟨retired, applied⟩ := retireBattlefield_isSome member found oldOwner blank
      unfold removePlayerObjects
      dsimp only
      rw [show _ = some field from chosen]
      dsimp only
      change retireBattlefield (banishForPlayerRemoval s departing).1 field blank = some retired at applied
      rw [applied]
      exact ⟨_, rfl⟩

/-- Recount consecutive passes after a seat leaves a Chain or Showdown (CR 652.5).
`none` means every remaining seat has passed, so the window ends. -/
def passAfterPlayerRemoval (order : List PlayerId) (departing holder : PlayerId) (passes : Nat) :
    Option (PlayerId × Nat) := do
  let afterHolder := seatOrderAfter order holder
  let alreadyPassed := (afterHolder.reverse.drop 1).take passes
  let passes := passes - (if alreadyPassed.contains departing then 1 else 0)
  let remaining := order.erase departing
  if remaining.length ≤ passes then none else
    let next := if holder == departing then afterHolder.find? (· != departing) else some holder
    next.map (fun seat => (seat, passes))

/-- An open window after a departure belongs to a different seat and still needs a pass. -/
theorem passAfterPlayerRemoval_open {order : List PlayerId} {departing holder next : PlayerId}
    {passes count : Nat} (h : passAfterPlayerRemoval order departing holder passes = some (next, count)) :
    next ≠ departing ∧ count < (order.erase departing).length := by
  let orderAfterHolder := seatOrderAfter order holder
  let remainingPasses := passes -
    (if ((orderAfterHolder.reverse.drop 1).take passes).contains departing then 1 else 0)
  change (if (order.erase departing).length ≤ remainingPasses then none else
    (if holder == departing then orderAfterHolder.find? (· != departing) else some holder)
      |>.map (fun seat => (seat, remainingPasses))) = some (next, count) at h
  by_cases done : (order.erase departing).length ≤ remainingPasses
  · rw [ite_eq_left done] at h
    contradiction
  · rw [ite_eq_right done] at h
    obtain ⟨chosen, selected, result⟩ := Option.map_eq_some_iff.mp h
    have continuing : chosen ≠ departing := by
      by_cases same : holder = departing
      · have found : orderAfterHolder.find? (· != departing) = some chosen := by
          simpa [same] using selected
        simpa using List.find?_some found
      · have chosenHolder : holder = chosen := by simpa [same] using selected
        simpa [← chosenHolder] using same
    simp only [Prod.mk.injEq] at result
    obtain ⟨rfl, rfl⟩ := result
    exact ⟨continuing, Nat.lt_of_not_ge done⟩

/-- Record the departure and cancel future extra turns belonging to that seat (CR 651.3, 652.5.a). -/
def GameState.withdrawSeat (s : GameState) (p : PlayerId) : GameState :=
  if s.participates p then
    { s with
      pools := s.pools.erase p.n,
      departures := { s.departures with seats := s.departures.seats ++ [p] },
      extraTurns := s.extraTurns.filter (· != p) }
  else s

/-- A withdrawn seat cannot be selected from the remaining participants. -/
theorem GameState.withdrawSeat_not_participating (s : GameState) (p : PlayerId) :
    (s.withdrawSeat p).participates p = false := by
  cases present : s.participates p
  · simp [GameState.withdrawSeat, present]
  · simp only [GameState.withdrawSeat, present, ite_true]
    simp [GameState.participates]

/-- Withdrawing a seat removes that seat from play and preserves every other seat's eligibility. -/
theorem GameState.withdrawSeat_participates (s : GameState) (departing p : PlayerId) :
    (s.withdrawSeat departing).participates p = (s.participates p && p != departing) := by
  by_cases same : p = departing
  · subst p
    simp [GameState.withdrawSeat_not_participating]
  · have different : (p != departing) = true := by simpa using same
    cases present : s.participates departing
    · simp [GameState.withdrawSeat, present, same]
    · simp only [GameState.withdrawSeat, present, ite_true]
      simp [GameState.participates, GameState.playerCount, same, different] <;> rfl

/-- Withdrawing removes at most one entry from the ordered roster of remaining seats. -/
theorem GameState.withdrawSeat_participatingSeats (s : GameState) (departing : PlayerId) :
    (s.withdrawSeat departing).participatingSeats = s.participatingSeats.filter (· != departing) := by
  have seats : (s.withdrawSeat departing).playerCount = s.playerCount := by
    unfold GameState.withdrawSeat
    split <;> rfl
  unfold GameState.participatingSeats
  rw [seats, List.filter_filter]
  apply List.filter_congr
  intro p _
  rw [GameState.withdrawSeat_participates, Bool.and_comm]

/-- Resume the pending decision after applying a player's departure to the board
(CR 651.3, 652.5). -/
def Frame.afterPlayerRemoval (frame : Frame) (before after : GameState)
    (departing : PlayerId) : List Frame :=
  let keepFor (p : PlayerId) := if p == departing then [] else [frame]
  let stillPresent (id : ObjId) := (after.obj? id).isSome
  let removedItem (src : ObjId) :=
    (before.zone .chain).contains src && !(after.zone .chain).contains src
  let stopped (p : PlayerId) (src : ObjId) (env : Env) :=
    p == departing || removedItem src || env.effectController == some departing
  let keepTrigger (trigger : PendTrigger) := trigger.controller != departing
  let progress := passAfterPlayerRemoval before.participatingOrder departing
  let wasActive := before.active == some departing
  match frame with
  | .chanceShuffle (.player p _) | .chanceBattlefield p | .mulligan p _
  | .chanceRecycle p | .chanceBurnOut p | .chooseBurnOut p | .draw p ..
  | .discard p _ | .predict p .. | .chancePredict p .. | .teamInvitation p
  | .chooseShowdown p .. => keepFor p
  | .priority p => if p == departing then [.expireTurn, .beginTurn] else [frame]
  | .phase .ending => if wasActive then [.expireTurn] else [frame]
  | .phase _ | .scoreHolds => if wasActive then [] else [frame]
  | .resumeCost action =>
    if action.actor == .player departing then [] else [frame]
  | .run p src env _ | .mayDo p src env .. | .eitherDo p src env ..
  | .nameCard p src env .. =>
    if stopped p src env then [] else [frame]
  | .guessCardType guesser p src env _ _ _ rest =>
    if stopped p src env then [] else
      if guesser == departing then [.run p src env rest] else [frame]
  | .pickDo p src env first more effect rest =>
    if removedItem src || env.effectController == some departing then [] else
      let candidates := (first :: more).filter stillPresent
      if p != departing && !candidates.isEmpty then
        match candidates with
        | kept :: others => [.pickDo p src env kept others effect rest]
        | [] => []
      else
        match effect with
        | .collectOwnPicks controller remaining place fs body _ =>
          if controller == departing then [] else
            [.run controller src env
              (.cons (.collectOwnPicks controller (remaining.filter (· != departing)) place fs body false) rest)]
        | .recordBanishReplay controller remaining ordered =>
          if controller == departing then [] else
            let keepEntry := fun (entry : PlayerId × ObjId × Option ObjId) =>
              entry.1 != departing && stillPresent entry.2.1
            [.run controller src env
              (.cons (.orderBanishReplays (remaining.filter keepEntry) (ordered.filter keepEntry)) rest)]
        | .recordRuneRecycle _ later picked =>
          [.run after.chainPrioritySeat src env
            (.cons (.orderRuneRecycle (later.filter (fun (owner, _) => owner != departing))
              (picked.filter stillPresent)) rest)]
        | _ => if p == departing then [] else [.run p src env rest]
  | .finishSpell item => if (after.zone .chain).contains item then [frame] else []
  | .triggers pending => [.triggers (pending.filter keepTrigger)]
  | .triggerOrder p first more others funding =>
    let others := others.filter keepTrigger
    if p == departing then [.triggers others]
    else [.triggerOrder p first more others funding]
  | .assign field attacker side accumulated done =>
    let missingSide := after.combat.any fun combat =>
      combat.battlefield == field && (combat.attacker == departing || combat.defender == departing)
    if missingSide || side == departing then [.combatResolve field attacker] else
      [.assign field attacker side (accumulated.filter stillPresent)
        (done.filter (fun (id, _) => stillPresent id))]
  | .groupMove p dest fee units =>
    if p == departing then [] else [.groupMove p dest fee (units.filter stillPresent)]
  | .chainPass p passes =>
    if (after.zone .chain).isEmpty then [] else
      match progress p passes with
      | some (seat, count) => [.chainPass seat count]
      | none => [.resolveChain]
  | .resolveChain => if (after.zone .chain).isEmpty then [] else [frame]
  | .showdown field p passes =>
    match progress p passes with
    | some (seat, count) => [.showdown field seat count]
    | none => [.endShowdown field]
  | _ => [frame]

/-- Apply a free-for-all concession. With one player left the game ends immediately. Otherwise
the departure changes the board, then the pending work continues under the remaining roster
(CR 651.1, 652). -/
def applyFreeForAllConcession (s : GameState) (departing : PlayerId) (blank : CardId) :
    Option (GameState × List Event) := do
  if !s.participates departing then none else
  let withdrew := s.withdrawSeat departing
  match withdrew.participatingSeats with
  | [] => none
  | [winner] => some ({ withdrew with result := some (.won [winner]), pending := [] }, [])
  | _ :: _ :: _ =>
    let (board, events) ← removePlayerObjects withdrew departing blank
    let pending := s.pending.flatMap (fun frame => frame.afterPlayerRemoval s board departing)
    let pending := if board.phase == .setup then pending else .cleanup :: pending
    return ({ board with pending }, events)

/-- A concession by a participating seat can be applied if the game has a remaining player. -/
theorem applyFreeForAllConcession_isSome (s : GameState) (departing : PlayerId) (blank : CardId)
    (present : s.participates departing = true)
    (remaining : (s.withdrawSeat departing).participatingSeats ≠ []) :
    ∃ result, applyFreeForAllConcession s departing blank = some result := by
  have registered : departing.n < (s.withdrawSeat departing).playerCount := by
    have seat : departing.n < s.playerCount := by
      simpa [GameState.participates] using (Bool.and_eq_true_iff.mp present).1
    rw [GameState.withdrawSeat, ite_eq_left present]
    exact seat
  unfold applyFreeForAllConcession
  simp only [present, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases roster : (s.withdrawSeat departing).participatingSeats with
  | nil => exact (remaining roster).elim
  | cons first others =>
    cases others with
    | nil => exact ⟨_, rfl⟩
    | cons second rest =>
      obtain ⟨board, removed⟩ := removePlayerObjects_isSome (s.withdrawSeat departing) departing
        registered blank
      rw [removed]
      exact ⟨_, rfl⟩

private theorem withdrawSeat_preservesBoard (s : GameState) (p : PlayerId) (hwf : s.WF) :
    (s.withdrawSeat p).WF ∧ (s.OwnerOk → (s.withdrawSeat p).OwnerOk) ∧
      (s.withdrawSeat p).physIds.Perm s.physIds := by
  unfold GameState.withdrawSeat
  split <;> exact ⟨hwf.congr rfl rfl rfl rfl, fun owner => owner.congr rfl rfl, List.Perm.refl _⟩

/-- Applying a free-for-all concession preserves the board invariants and physical inventory. -/
theorem applyFreeForAllConcession_preservesBoard {s next : GameState} {departing : PlayerId}
    {blank : CardId} {events : List Event} (hwf : s.WF)
    (applied : applyFreeForAllConcession s departing blank = some (next, events)) :
    next.WF ∧ (s.OwnerOk → next.OwnerOk) ∧ next.physIds.Perm s.physIds := by
  have withdrew := withdrawSeat_preservesBoard s departing hwf
  unfold applyFreeForAllConcession at applied
  split at applied
  · simp at applied
  · dsimp only at applied
    split at applied
    · simp at applied
    · simp only [Option.some.injEq, Prod.mk.injEq] at applied
      obtain ⟨rfl, _⟩ := applied
      exact ⟨withdrew.1.congr rfl rfl rfl rfl, fun owner =>
        (withdrew.2.1 owner).congr rfl rfl, withdrew.2.2⟩
    · obtain ⟨⟨board, removalEvents⟩, removed, completed⟩ := Option.bind_eq_some_iff.mp applied
      obtain ⟨rfl, _⟩ := completed
      have safe := removePlayerObjects_safe removed
      exact ⟨(safe.wf withdrew.1).congr rfl rfl rfl rfl, fun owner =>
        (safe.own withdrew.1 (withdrew.2.1 owner)).congr rfl rfl,
        (safe.phys withdrew.1).trans withdrew.2.2⟩

/-- The concession records the departure without advancing the turn or the clock.
Automatic work advances the turn after resolving the pending decisions. -/
theorem applyFreeForAllConcession_meta {s next : GameState} {departing : PlayerId}
    {blank : CardId} {events : List Event}
    (applied : applyFreeForAllConcession s departing blank = some (next, events)) :
    next.config = s.config ∧ next.phase = s.phase ∧ next.turnOrder = s.turnOrder ∧
      next.turn = s.turn ∧ next.clock = s.clock ∧ next.departures = (s.withdrawSeat departing).departures := by
  have withdrew : (s.withdrawSeat departing).config = s.config ∧
      (s.withdrawSeat departing).phase = s.phase ∧ (s.withdrawSeat departing).turnOrder = s.turnOrder ∧
      (s.withdrawSeat departing).turn = s.turn ∧ (s.withdrawSeat departing).clock = s.clock := by
    unfold GameState.withdrawSeat
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨config, phase, order, turn, roundClock⟩ := withdrew
  unfold applyFreeForAllConcession at applied
  split at applied
  · simp at applied
  · dsimp only at applied
    split at applied
    · simp at applied
    · simp only [Option.some.injEq, Prod.mk.injEq] at applied
      obtain ⟨rfl, _⟩ := applied
      exact ⟨config, phase, order, turn, roundClock, rfl⟩
    · obtain ⟨⟨board, removalEvents⟩, removed, completed⟩ := Option.bind_eq_some_iff.mp applied
      obtain ⟨rfl, _⟩ := completed
      have same := (removePlayerObjects_safe removed).same
      have clockUnchanged := congrArg GameState.clock same
      exact ⟨same.config.trans config, same.phase.trans phase, same.turnOrder.trans order,
        same.turn.trans turn, clockUnchanged.trans roundClock, same.departures⟩

end Riftbound

end
