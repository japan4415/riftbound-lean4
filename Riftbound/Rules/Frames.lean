module

public import Riftbound.Rules.Reorder
public import Riftbound.Rules.Setup
public import Riftbound.Rules.Objects
public import Riftbound.Rules.Resources
public import Riftbound.Rules.Play
public import Riftbound.Rules.Effects
public import Riftbound.Rules.Chain
public import Riftbound.Rules.Trigger
public import Riftbound.Rules.Mana
public import Riftbound.Rules.Actions.Channel
public import Riftbound.Rules.Actions.Draw
public import Riftbound.Rules.Actions.Recycle
public import Riftbound.Rules.Actions.BurnOut
public import Riftbound.Rules.Battlefield
public import Riftbound.Rules.Combat
public import Riftbound.Rules.Temporary
public import Riftbound.Tournament.Match

/-!
# Working through the frames

`microStep` advances one work frame by one step. `applyAction` applies the answer to the
decision frame on top of the stack. Neither checks that the answer is legal: that is `Legal`'s job
(`Riftbound.Spec.Legal`), and `step` asks it first (design.md §6.3).
-/

@[expose] public section

namespace Riftbound

/-- The player whose turn it is: the first player has turn 0, then the turn order goes round
(CR 118, 301). -/
def GameState.nextTurnPlayer (s : GameState) : PlayerId :=
  match s.extraTurns with
  | p :: _ => p
  | [] => s.turnOrder.getD ((s.turn - s.turnShift) % s.playerCount) ⟨0⟩

/-- The frames of a turn up to the Main Phase, where the turn player has priority (CR 315-316). -/
def turnFrames (tp : PlayerId) : List Frame :=
  [.phase .awaken, .phase .beginning, .phase .channel, .phase .draw, .phase .main, .priority tp]

/-- The teammate to whom the turn player can offer their Neutral Open priority (CR 316.5.b.1). -/
def GameState.teamInvitee (s : GameState) (p : PlayerId) : Option PlayerId :=
  if s.active == some p && s.phase == .main then
    (s.config.mode.sideSeats p).find? (· != p)
  else none

theorem GameState.teamInvitee_phase {s : GameState} {p guest : PlayerId}
    (h : s.teamInvitee p = some guest) : s.phase = .main := by
  unfold teamInvitee at h
  split at h
  · rename_i allowed
    simp only [Bool.and_eq_true, beq_iff_eq] at allowed
    exact allowed.2
  · cases h

/-- The last seat in the starting order gets an extra Rune in its first Channel Phase
in Duel and team play (CR 315.3, 487.7, 491.7). -/
def GameState.channelCount (s : GameState) : Nat :=
  let openingBonus := if s.config.mode.isTeamDuel then
    s.turnOrder.getLast?.any (fun last => s.active == some last && s.turnsTaken last == 1)
  else s.config.mode.hasTwoSides && s.turn - s.turnShift == s.playerCount
  let normal := if openingBonus then 3 else 2
  s.passiveSources.foldl (fun count src =>
    (s.activeMods src).foldl (fun count mod =>
      match mod with
      | .channelLimit n => min count n
      | _ => count) count) normal

/-- The starting player has no regular draw on the first turn in team play (CR 491.7). -/
def GameState.drawCount (s : GameState) : Nat :=
  if s.config.mode.isTeamDuel && s.turn == 1 then 0 else 1

/-- How many cards the player draws more at the start of their first Beginning Phase: in a Limited
format, 1 for a player whose deck has no Legend or no Chosen Champion, even if it has neither
(TR 602.4.a.5.b). The turns of the first round are the first turns of the players. -/
def GameState.extraDraws (s : GameState) (p : PlayerId) : Nat :=
  if s.config.ruleSet.isLimited && decide (s.turn ≤ s.playerCount) &&
      ((s.zone (.player p .legendZone)).isEmpty || (s.zone (.player p .championZone)).isEmpty)
  then 1 else 0

/-- How many of this player's Hold points were replaced with draws (CR 367, 471). -/
def scoreDrawCount (p : PlayerId) (es : List Event) : Nat :=
  es.countP (fun
    | .scoreDraw who _ => who == p
    | _ => false)

/-- The last scheduled turn has begun (TR 408.2, 408.4). -/
def GameState.clockDue (s : GameState) : Bool :=
  match s.clock with
  | some clock => decide (clock.lastTurn ≤ s.turn)
  | none => false

/-- The result due at the next turn boundary. Tied points after the scheduled turns can instead
start sudden death when game wins are also tied (TR 408.2, 408.4.c). -/
def GameState.clockConclusion (s : GameState) : Option GameResult := do
  let clock ← s.clock
  if s.turn < clock.lastTurn then none else
    let second : PlayerId := ⟨if s.config.mode.isTeamDuel then 2 else 1⟩
    let result ← clock.resultOnTime (s.pointsOf ⟨0⟩) (s.pointsOf second)
    return match result with
      | .won side =>
        .won (side.flatMap (fun p => s.config.mode.sideSeats (if p.n == 0 then ⟨0⟩ else second)))
      | .draw => .draw

/-- Advance to the next turn, or finish at the clock's deadline. -/
def beginTurnStep (s : GameState) (rest : List Frame) : GameState :=
  match s.clockConclusion with
  | some result => { s with result := some result, pending := [] }
  | none =>
    { s.mapObjects clearScored with
        pending := turnFrames s.nextTurnPlayer ++ rest, turn := s.turn + 1,
        active := some s.nextTurnPlayer, turnFx := [], extraTurns := s.extraTurns.drop 1,
        turnShift := s.turnShift + (if s.extraTurns.isEmpty then 0 else 1),
        extraTurnsTaken := s.extraTurns.take 1 ++ s.extraTurnsTaken }

/-- The turn begins as usual, or the clock ends the game: what `beginTurnStep` does. -/
theorem beginTurnStep_cases (s : GameState) (rest : List Frame) :
    beginTurnStep s rest =
        { s.mapObjects clearScored with
            pending := turnFrames s.nextTurnPlayer ++ rest, turn := s.turn + 1,
            active := some s.nextTurnPlayer, turnFx := [], extraTurns := s.extraTurns.drop 1,
            turnShift := s.turnShift + (if s.extraTurns.isEmpty then 0 else 1),
            extraTurnsTaken := s.extraTurns.take 1 ++ s.extraTurnsTaken } ∨
      ∃ r, beginTurnStep s rest = { s with result := some r, pending := [] } := by
  unfold beginTurnStep
  cases hc : s.clockConclusion with
  | some result => exact Or.inr ⟨result, by simp⟩
  | none => exact Or.inl (by simp)

/-- The separate Combat steps after damage and Combat Cleanup (CR 468.2-468.7). -/
def combatSteps (bf : ObjId) : List Frame :=
  [.combatResult bf, .combatControl bf, .combatFinish bf]

/-- Return the kept cards above the uninspected deck and the Recycled cards below it (CR 437).
Only the inspected prefix can be rearranged. -/
def completePrediction (s : GameState) (p : PlayerId) (n : Nat) (top bottom : List ObjId) :
    GameState :=
  let z := Zone.player p .mainDeck
  let deck := s.zone z
  if z.Valid s.playerCount ∧ (top ++ bottom).Perm (deck.take n) then
    s.reorder z (top ++ deck.drop n ++ bottom)
  else s

/-- Predicting preserves the same cards, their ownership and the structure of the game. -/
theorem completePrediction_safe (s : GameState) (p : PlayerId) (n : Nat) (top bottom : List ObjId) :
    Safe s (completePrediction s p n top bottom) := by
  unfold completePrediction
  dsimp only
  split
  · rename_i h
    let deck := s.zone (.player p .mainDeck)
    change (Zone.player p .mainDeck).Valid s.playerCount ∧
      (top ++ bottom).Perm (deck.take n) at h
    have shift : (top ++ deck.drop n ++ bottom).Perm (top ++ bottom ++ deck.drop n) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := deck.drop n) (l₂ := bottom)).append_left top
    have perm : (top ++ deck.drop n ++ bottom).Perm deck := by
      simpa only [List.take_append_drop] using shift.trans (h.2.append_right (deck.drop n))
    exact ⟨fun wf => GameState.wf_reorder wf h.1 perm,
      fun _ => GameState.physIds_reorder h.1 perm,
      fun _ own => GameState.ownerOk_reorder own perm, rfl⟩
  · exact Safe.refl s

/-- Continue with the remaining Predict choices, randomize a group of Recycled cards, or finish
immediately when no randomization is needed (CR 417.5, 437). -/
def continuePrediction (s : GameState) (p : PlayerId) (n : Nat)
    (left top bottom : List ObjId) : GameState × List Frame :=
  match left with
  | c :: cs => (s, [.predict p n c cs top bottom])
  | [] =>
    if 2 ≤ bottom.length then (s, [.chancePredict p n top bottom])
    else (completePrediction s p n top bottom, [])

/-- Predict choices preserve the structural invariants. -/
theorem continuePrediction_safe (s : GameState) (p : PlayerId) (n : Nat)
    (left top bottom : List ObjId) : Safe s (continuePrediction s p n left top bottom).1 := by
  unfold continuePrediction
  split
  · exact Safe.refl s
  · split
    · exact Safe.refl s
    · exact completePrediction_safe s p n top bottom

/-- The only new frames that Predict choices can add are Predict's own decisions. -/
theorem continuePrediction_frames (s : GameState) (p : PlayerId) (n : Nat)
    (left top bottom : List ObjId) {f : Frame}
    (hf : f ∈ (continuePrediction s p n left top bottom).2) : f.isPlay = true := by
  unfold continuePrediction at hf
  split at hf
  · simp only [List.mem_singleton] at hf
    cases hf
    rfl
  · split at hf
    · simp only [List.mem_singleton] at hf
      cases hf
      rfl
    · simp at hf

/-- Check whether Expiration has work to do. If post-expiration triggers create new effects,
damage or resources, a further Expiration Step removes them before the next turn (CR 317.2.f). -/
def expirationFrames (s : GameState) : List Frame :=
  if !s.turnFx.isEmpty || !s.pools.isEmpty || s.objects.toList.any (fun (_, o) =>
      o.damage != 0 || o.stunned || o.baseMightThisTurn.isSome ||
        o.mightMods.any (·.ends != .never) || o.tempKws.any (·.2 != .never)) then
    [.cleanup, .expireTurn]
  else []

/-- An Awaken Phase can ready this object, accounting for passive limits on Units. -/
def awakenCanReady (s : GameState) (p : PlayerId) (unitsStayExhausted : Bool)
    (id : ObjId) (o : Object) : Bool :=
  o.controller == p && !o.cantReady &&
    (!unitsStayExhausted || !(s.cardDef? id).any (·.hasType .unit))

/-- Ready the objects the turn player controls during Awaken. -/
def awakenReady (eligible : ObjId → Object → Bool) (id : ObjId) (o : Object) : Object :=
  if eligible id o then { o with exhausted := false } else o

theorem awakenReady_owner (eligible : ObjId → Object → Bool) (id : ObjId) (o : Object) :
    (awakenReady eligible id o).owner = o.owner := by
  unfold awakenReady
  split <;> rfl

theorem awakenReady_kind (eligible : ObjId → Object → Bool) (id : ObjId) (o : Object) :
    (awakenReady eligible id o).kind = o.kind := by
  unfold awakenReady
  split <;> rfl

/-- Advance one work frame by one step, before the triggered abilities that the step set off are
found. `none` if the top frame is not work. -/
def microStep0 (s : GameState) : Option (GameState × List Event) :=
  match s.pending with
  | .setupHands :: rest =>
    some ({ s with pending := s.turnOrder.map (fun p => Frame.draw p 4) ++
                                s.turnOrder.map (fun p => Frame.mulligan p 0) ++
                                [Frame.beginTurn] ++ rest }, [])
  | .beginTurn :: rest => some (beginTurnStep s rest, [])
  | .phase .awaken :: rest =>
    let p := s.active.getD ⟨0⟩
    let eligible := awakenCanReady s p (s.anyActive .skipUnitAwaken)
    let s1 := s.mapObjectsAt (awakenReady eligible)
    let readied := s.objects.toList.filterMap (fun (k, o) =>
      if o.exhausted && eligible ⟨k⟩ o then some (Event.readied ⟨k⟩) else none)
    some ({ s1 with phase := .awaken, pending := rest }, Event.phaseStarted p .awaken :: readied)
  | .phase .channel :: rest =>
    let r := channelEx (s.active.getD ⟨0⟩) s.channelCount 0 s
    some ({ r.1 with phase := .channel, pending := rest }, r.2)
  | .phase .draw :: rest =>
    let p := s.active.getD ⟨0⟩
    let skip := s.hasControlledMod p .skipDrawPhase
    let phase := if skip then s.phase else .draw
    let pending := if skip then rest else .draw p s.drawCount :: rest
    some ({ s with phase, pending }, [])
  | .phase .ending :: rest =>
    some ({ s with phase := .ending, pending := .cleanup :: .expireTurn :: rest },
      [Event.phaseStarted (s.active.getD ⟨0⟩) .ending])
  | .expireTurn :: rest =>
    some ({ s.mapObjects endTurnObj with
      pending := expirationFrames s ++ rest, pools := {}, turnFx := [] }, [])
  | .phase .setup :: rest => some ({ s with pending := rest }, [])
  | .phase .beginning :: rest =>
    let p := s.active.getD ⟨0⟩
    match s.deathGroupChoice (tempUnits s p) with
    | some (unit, controller, first, other) =>
      some ({ s with
        phase := .beginning
        pending := .eitherDo controller unit {} first other .nil :: .phase .beginning :: rest }, [])
    | none =>
      let r := beginStep s p
      some ({ r.1 with
                phase := .beginning,
                pending := .cleanup :: .draw p (s.extraDraws p) :: .scoreHolds :: rest },
        Event.phaseStarted p .beginning :: r.2)
  | .scoreHolds :: rest =>
    let p := s.active.getD ⟨0⟩
    let r := hold s p
    some ({ r.1 with
              phase := .beginning,
              pending := .draw p (scoreDrawCount p r.2) :: .cleanup :: rest },
      r.2)
  | .phase .main :: rest =>
    some ({ s with phase := .main, pending := .cleanup :: rest, pools := {} },
      [Event.phaseStarted (s.active.getD ⟨0⟩) .main])
  | .draw p 0 startingHand :: rest =>
    some ({ s with pending := rest }, startingHand.toList.map (.drewGroup p))
  | .draw p (n + 1) startingHand :: rest =>
    match drawOne s p with
    | some (s', es) =>
      let otherCards := startingHand <|> some ((s.zone (.player p .hand)).length)
      some ({ s'.noteDraw p with pending := .draw p n otherCards :: rest }, es ++ [Event.drew p])
    | none => some ({ s with pending := .chanceBurnOut p :: .draw p (n + 1) startingHand :: rest }, [])
  | .resolveChain :: rest => some ({ s with pending := resolveFrames s rest }, [])
  | .run _ _ _ .nil :: rest => some ({ s with pending := rest }, [])
  | .run p src env (.cons e es) :: rest =>
    -- the effect reads the Might the passive abilities give, as of now
    let r := runEffect s p src (env.withMight s.mightTable) e es effectAddPolicy
    some ({ r.1 with pending := r.2.1 ++ rest }, r.2.2)
  | .finishSpell item :: rest =>
    let r := finishItem s item
    some ({ r.1 with pending := finishedItemFrames s item r ++ rest }, r.2)
  | .cleanup :: rest => some (cleanupFrame s rest)
  | .combatDamage bf att :: rest =>
    let combat := (s.observeCombat [.showdown bf att 0]).1
    some ({ s with pending := s.startCombat bf att ++ combatSteps bf ++ rest, combat := combat },
      [])
  | .combatResolve bf att :: rest =>
    let r := combatCleanup s bf att
    let recalled := r.2.any (fun | .recalled _ => true | _ => false)
    let combat := r.1.combat.map (fun c => { c with recalled := recalled })
    some ({ r.1 with pending := .cleanup :: rest, combat := combat }, r.2)
  | .combatResult bf :: rest =>
    let recalled := (s.combat.filter (·.battlefield == bf)).any (·.recalled)
    some ({ s with pending := rest }, combatResultEvents s bf recalled)
  | .combatControl bf :: rest =>
    let r := combatControl s bf
    some ({ r.1 with pending := r.2.1 ++ .cleanup :: rest }, r.2.2)
  | .combatFinish bf :: rest =>
    let units := ((s.combat.filter (·.battlefield == bf)).map (·.units)).getD []
    some ({ s.mapObjects endShowdownObj with combat := none, pending := .cleanup :: rest },
      [Event.combatEnded bf units])
  | .triggers pend :: rest =>
    some ({ (triggersStep s pend rest).1 with pending := (triggersStep s pend rest).2 ++ rest }, [])
  | _ => none

/-- Advance one work frame by one step (design.md §6.1): the step, and then the triggered abilities
it set off wait on the stack (CR 382-385). `none` if the top frame is not work. -/
def microStep (s : GameState) : Option (GameState × List Event) :=
  (microStep0 s).map (fun r => (r.1.withTriggers (r.2 ++ s.workTransitionEvents r.1), r.2))

/-- The player who wins when `p` concedes a 1v1 game (CR 651.1). -/
def otherPlayer (p : PlayerId) : PlayerId := ⟨1 - p.n⟩

/-- The opposing side wins when a player concedes (CR 651.1, 651.4). -/
def GameState.concessionWinners (s : GameState) (p : PlayerId) : List PlayerId :=
  if s.config.mode.isTeamDuel then s.players.filter (fun q => !s.config.mode.sameSide p q)
  else [otherPlayer p]

/-- Apply an answer to the decision frame on top of the stack, before the triggered abilities it set
off are found. The answer is assumed to be legal; `none` if it does not fit the frame or a primitive
cannot be done. -/
def applyFrame0 (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match s.pending, a.kind with
  | .priority _ :: rest, .pass =>
    some ({ s with pending := .phase .ending :: .beginTurn :: rest }, [])
  | .priority p :: _, .runeAbility c ab => applyRune s p c ab
  | .priority p :: rest, .playCard c pay ts flow discard pick =>
    (applyPlayCard s p c pay ts rest flow pick).map (payPlayDiscard p c discard)
  | .priority p :: rest, .standardMove u d _ =>
    (applyMove s p u d).map
      (fun r => ({ r.1 with pending := .cleanup :: .priority p :: rest }, r.2))
  | .showdown bf q n :: rest, .pass =>
    if n + 1 < s.playerCount then
      some ({ s with pending := .showdown bf (s.nextPlayer q) (n + 1) :: rest }, [])
    else some (showdownEnd s bf rest)
  | .assign bf att side acc done :: rest, .assignPick u =>
    some ({ s with pending := .assign bf att side (acc ++ [u]) done :: rest }, [])
  | .assign bf att side acc done :: rest, .assignDone =>
    some (assignDoneStep s bf att side acc done rest)
  | .chainPass p n :: rest, .pass =>
    if n + 1 < s.playerCount then
      some ({ s with pending := .chainPass (s.nextPlayer p) (n + 1) :: rest }, [])
    else some ({ s with pending := .resolveChain :: rest }, [])
  | .chainPass p _ :: rest, .playCard c pay ts flow discard pick =>
    (reactStep s p c pay ts (.chainPass p 0 :: rest) flow pick).map (payPlayDiscard p c discard)
  | .chainPass p _ :: rest, .activate src idx pay ts discards targetPlayer costBanisher costObject =>
    activateStep s p src idx pay ts (.chainPass p 0 :: rest) discards targetPlayer costBanisher costObject
  | .chainPass p _ :: _, .runeAbility c ab => applyRune s p c ab
  | .priority p :: rest, .activate src idx pay ts discards targetPlayer costBanisher costObject =>
    activateStep s p src idx pay ts (.chainPass p 0 :: .priority p :: rest) discards targetPlayer costBanisher costObject
  | .triggerOrder _ t more others funding :: rest, .putTrigger i ts payment =>
    let r := finishTrigger s (t :: more) funding i ts payment
    some ({ r.1 with pending := .triggers ((t :: more).eraseIdx i ++ others) :: rest }, r.2)
  | .triggerOrder p t more others none :: rest, .prepareTrigger i ts payment =>
    let plan : TriggerFunding := { index := i, targets := ts, payment }
    some ({ s with pending := .triggerOrder p t more others (some plan) :: rest }, [])
  | .triggerOrder p t more others (some plan) :: rest, .triggerAdd add =>
    let next := { plan with adds := plan.adds ++ [add] }
    some ({ s with pending := .triggerOrder p t more others (some next) :: rest }, [])
  | .triggerOrder p t more others (some _) :: rest, .decide _ =>
    some ({ s with pending := .triggerOrder p t more others :: rest }, [])
  | .priority p :: _, .manaAbility src idx pay chosen => applyMana s p src idx pay chosen
  | .chainPass p _ :: _, .manaAbility src idx pay chosen => applyMana s p src idx pay chosen
  | .discard p n :: rest, .discardPick c =>
    let r := discardObj s c
    some ({ r.1 with
        pending := (if n ≤ 1 then rest else .discard p (n - 1) :: rest) },
      r.2.map (fun
        | .discarded q id _ => .discarded q id (decide (n ≤ 1) || (r.1.zone (.player p .hand)).isEmpty)
        | e => e))
  | .discard _ _ :: rest, .discardDone => some ({ s with pending := rest }, [])
  | .mayDo p src env e es :: rest, .decide yes =>
    some ({ s with pending := .run p src env (if yes then .cons e es else es) :: rest }, [])
  | .eitherDo p src env a b es :: rest, .decide yes =>
    some ({ s with pending := .run p src env (.cons (if yes then a else b) es) :: rest }, [])
  | .pickDo p src env _ _ e es :: rest, .choose o =>
    some ({ s with pending := .run p src (env.bindPick o (e.pickIsTarget s o)) (.cons e es) :: rest },
      e.pickEvents s p src o)
  | .chanceShuffle z :: rest, .arrange l => some ({ s.reorder z l with pending := rest }, [])
  | .chanceBattlefield p :: rest, .pick i =>
    match (s.zone (.player p .outOfGame))[i]? with
    | some id =>
      (moveObj s id .battlefieldZone).map
        (fun r => ({ r.1 with pending := rest }, [Event.moved id r.2 .battlefieldZone]))
    | none => none
  | .chanceTurnOrder :: rest, .arrangePlayers l =>
    some ({ s with turnOrder := l, pending := .setupHands :: rest }, [])
  | .mulligan p n :: rest, .mulliganPick c =>
    (moveObj s c (.player p .setAside)).map
      (fun r => ({ r.1 with pending := .mulligan p (n + 1) :: rest },
                 [Event.moved c r.2 (.player p .setAside)]))
  | .mulligan p n :: rest, .mulliganDone =>
    match n with
    | 0 => some ({ s with pending := rest }, [])
    | k + 1 => some ({ s with pending := .draw p (k + 1) :: .chanceRecycle p :: rest }, [])
  | .chanceRecycle p :: rest, .arrange l =>
    (recycleAll p s l).map (fun s' => ({ s' with pending := rest }, []))
  | .chanceBurnOut p :: rest, .arrange l =>
    (recycleAll p s l).map
      (fun s' => ({ s' with pending := .chooseBurnOut p :: rest }, [Event.burnedOut p]))
  | .chooseBurnOut _ :: rest, .burnOutTarget opp =>
    some ({ s.gainPoints opp 1 with pending := rest }, [Event.pointsGained opp 1])
  -- in a Showdown, the player with Focus plays a Spell with Action or a card with Reaction, or uses an
  -- ability: it goes on the Chain, and the Showdown goes on when the Chain is empty (CR 347-348)
  | .showdown bf q _ :: rest, .playCard c pay ts flow discard pick =>
    (reactStep s q c pay ts (.chainPass q 0 :: .showdown bf q 0 :: rest) flow pick).map
      (payPlayDiscard q c discard)
  | .showdown bf q _ :: rest, .activate src idx pay ts discards targetPlayer costBanisher costObject =>
    activateStep s q src idx pay ts (.chainPass q 0 :: .showdown bf q 0 :: rest) discards targetPlayer costBanisher costObject
  | .showdown _ q _ :: _, .runeAbility c ab => applyRune s q c ab
  | .showdown _ q _ :: _, .manaAbility src idx pay chosen => applyMana s q src idx pay chosen
  | _, .timeCalled => some ({ s with clock := some (s.config.ruleSet.callClock s.turn) }, [])
  | _, .declareDraw => some ({ s with result := some .draw, pending := [] }, [])
  | .predict p n c cs top bottom :: rest, .predictPick id recycle =>
    let r := continuePrediction s p n ((c :: cs).erase id)
      (if recycle then top else top ++ [id]) (if recycle then id :: bottom else bottom)
    some ({ r.1 with pending := r.2 ++ rest }, [])
  | .chancePredict p n top _ :: rest, .arrange bottom =>
    some ({ completePrediction s p n top bottom with pending := rest },
      if bottom.isEmpty then [] else [.recycled p])
  | .nameCard p src env _ _ es :: rest, .nameCard card =>
    some ({ s with pending := .run p src env (.cons (.rememberNamedCard card) es) :: rest }, [])
  | .guessCardType _ p src env unit gear spell es :: rest, .guessCardType guess =>
    let branch := match guess with
      | .unit => unit
      | .gear => gear
      | .spell => spell
    some ({ s with pending := .run p src env (.cons branch es) :: rest }, [])
  | .eitherDo p _ _ _ _ _ :: _, .runeAbility c ab => applyRune s p c ab
  | .eitherDo p _ _ _ _ _ :: _, .manaAbility src idx pay chosen => applyMana s p src idx pay chosen
  | .priority p :: rest, .inviteTeammate guest =>
    some ({ s with pending := .teamInvitation guest :: .priority p :: rest }, [])
  | .teamInvitation _ :: rest, .pass => some ({ s with pending := rest }, [])
  | .teamInvitation guest :: rest, .playCard c pay ts flow discard pick =>
    (reactStep s guest c pay ts (.chainPass guest 0 :: rest) flow pick).map (payPlayDiscard guest c discard)
  | .teamInvitation guest :: rest, .activate src idx pay ts discards targetPlayer costBanisher costObject =>
    activateStep s guest src idx pay ts (.chainPass guest 0 :: rest) discards targetPlayer costBanisher costObject
  | .teamInvitation guest :: _, .runeAbility c ab => applyRune s guest c ab
  | .teamInvitation guest :: _, .manaAbility src idx pay chosen => applyMana s guest src idx pay chosen
  | .chooseShowdown _ first more :: rest, .choose bf =>
    ((first :: more).lookup bf).map (fun q => continueAfterCleanup s (.showdown bf q 0 :: .cleanup :: rest))
  | .priority p :: rest, .startGroupMove dest pay =>
    some ({ s with pending := .groupMove p dest pay [] :: .priority p :: rest }, [])
  | .groupMove p dest pay units :: rest, .choose u =>
    some ({ s with pending := .groupMove p dest pay (units ++ [u]) :: rest }, [])
  | .groupMove _ _ _ _ :: rest, .decide false => some ({ s with pending := rest }, [])
  | .groupMove p dest pay units :: rest, .decide true =>
    (applyGroupMove s p dest pay units).map (fun r => ({ r.1 with pending := .cleanup :: rest }, r.2))
  | _, _ => none

/-- Apply an answer to the decision frame on top of the stack, and the triggered abilities it set
off wait on the stack (CR 382-385). -/
def applyFrame (s : GameState) (a : Action) : Option (GameState × List Event) :=
  (applyFrame0 s a).map (fun r =>
    let next := s.paySurcharge a r.1
    let es := r.2 ++ extraEvents a r.2
    (next.withTriggers (es ++ s.actionTransitionEvents next a), es))

/-- Apply an answer: a concession ends the game at any time (CR 649-651), any other answer goes to
the decision frame on top of the stack. -/
def applyAction (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match a.kind with
  | .concede =>
    match a.actor with
    | .player p => some ({ s with result := some (.won (s.concessionWinners p)), pending := [] }, [])
    | _ => none
  | _ => applyFrame s a

/-- An answer that is not a concession goes to the frame on top of the stack. -/
theorem applyAction_of_ne {s : GameState} {a : Action} (hk : a.kind ≠ .concede) :
    applyAction s a = applyFrame s a := by
  unfold applyAction
  split
  · exact absurd ‹a.kind = .concede› hk
  · rfl

/-- A concession ends the game with the opposing side as winner (CR 651). -/
theorem applyAction_concede {s : GameState} {a : Action} {p : PlayerId} (hk : a.kind = .concede)
    (hp : a.actor = .player p) :
    applyAction s a =
      some ({ s with result := some (.won (s.concessionWinners p)), pending := [] }, []) := by
  unfold applyAction
  rw [hk]
  simp [hp]

/-- A step of work keeps the game well formed. -/
theorem microStep_wf0 {s s' : GameState} {es : List Event} (hwf : s.WF)
    (h : microStep0 s = some (s', es)) : s'.WF := by
  unfold microStep0 at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases beginTurnStep_cases s _ with e | ⟨r, e⟩
    · rw [e]; exact (GameState.wf_mapObjects hwf _).congr rfl rfl rfl rfl
    · rw [e]; exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.wf_mapObjectsAt hwf _).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((channelEx_safe _ _ _ _).wf hwf).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.wf_mapObjects hwf _).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · dsimp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hwf.congr rfl rfl rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ((beginStep_safe s _).wf hwf).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((hold_safeP s _).wf hwf).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · rename_i p n startingHand rest hp
    split at h
    · rename_i s1 es1 hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr (drawOne_wf hwf hd) rfl rfl rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((runEffect_safe _ _ _ _ _ _ effectAddPolicy).wf hwf).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (finishItem_wf hwf _).congr rfl rfl rfl rfl
  · rename_i rest hp
    have hs' : s' = (cleanupFrame s rest).1 := by
      have := Option.some.inj h
      rw [this]
    exact hs'.symm ▸ (cleanupFrame_preservesBoard s rest hwf).1
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hwf.congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((combatCleanup_safe s _ _).wf hwf).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hwf.congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((combatControl_safeP s _).wf hwf).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.wf_mapObjects hwf _).congr rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ((triggersStep_spec s _ _).1.wf hwf).congr rfl rfl rfl rfl
  · exact absurd h (by simp)

/-- **I1** (work). A step of work keeps the physical cards. -/
theorem microStep_physIds0 {s s' : GameState} {es : List Event} (hwf : s.WF)
    (h : microStep0 s = some (s', es)) : s'.physIds.Perm s.physIds := by
  unfold microStep0 at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases beginTurnStep_cases s _ with e | ⟨r, e⟩
    · rw [e]
      exact (GameState.physIds_mapObjects s (f := clearScored) (fun o => rfl)).symm ▸
        List.Perm.refl _
    · rw [e]; exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.physIds_mapObjectsAt s (awakenReady_kind _)).symm ▸ List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (channelEx_safe _ _ _ _).phys hwf
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.physIds_mapObjects s (fun o => endTurnObj_kind o)).symm ▸ List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · dsimp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact (beginStep_safe s _).phys hwf
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (hold_safeP s _).phys hwf
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · rename_i p n startingHand rest hp
    split at h
    · rename_i s1 es1 hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      have hp' := drawOne_physIds hwf hd
      rw [← h1]
      exact hp'
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (runEffect_safe _ _ _ _ _ _ effectAddPolicy).phys hwf
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact finishItem_physIds hwf _
  · rename_i rest hp
    have hs' : s' = (cleanupFrame s rest).1 := by
      have := Option.some.inj h
      rw [this]
    exact hs'.symm ▸ (cleanupFrame_preservesBoard s rest hwf).2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (combatCleanup_safe s _ _).phys hwf
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (combatControl_safeP s _).phys hwf
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (GameState.physIds_mapObjects s endShowdownObj_kind).symm ▸ List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (triggersStep_spec s _ _).1.phys hwf
  · exact absurd h (by simp)

/-- What a step of work does: the step, and the triggers it set off. -/
theorem microStep_cases {s s' : GameState} {es : List Event}
    (h : microStep s = some (s', es)) :
    ∃ s2, microStep0 s = some (s2, es) ∧ s' = s2.withTriggers (es ++ s.workTransitionEvents s2) := by
  unfold microStep at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨s2, es2⟩, h0, hr⟩ := h
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨s2, h0, rfl⟩

/-- What an answer does: the step, and the triggers it set off. -/
theorem applyFrame_cases {s s' : GameState} {a : Action} {es : List Event}
    (h : applyFrame s a = some (s', es)) :
    ∃ s2 es2 s3, applyFrame0 s a = some (s2, es2) ∧
      GameState.PoolStep s2 s3 ∧
      s' = s3.withTriggers (es2 ++ extraEvents a es2 ++ s.actionTransitionEvents s3 a) ∧
      es = es2 ++ extraEvents a es2 := by
  unfold applyFrame at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨s2, es2⟩, h0, hr⟩ := h
  simp only [Prod.mk.injEq] at hr
  exact ⟨s2, es2, s.paySurcharge a s2, h0, GameState.paySurcharge_poolStep s a s2, hr.1.symm,
    hr.2.symm⟩

/-- A step of work keeps the game well formed. -/
theorem microStep_wf {s s' : GameState} {es : List Event} (hwf : s.WF)
    (h : microStep s = some (s', es)) : s'.WF := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  exact withTriggers_wf _ (microStep_wf0 hwf h0)

/-- **I1** (work). A step of work keeps the physical cards. -/
theorem microStep_physIds {s s' : GameState} {es : List Event} (hwf : s.WF)
    (h : microStep s = some (s', es)) : s'.physIds.Perm s.physIds := by
  obtain ⟨s2, h0, rfl⟩ := microStep_cases h
  rw [withTriggers_physIds]
  exact microStep_physIds0 hwf h0

end Riftbound

end
