module

public import Riftbound.Rules.Chain
public import Riftbound.Rules.Temporary

/-!
# Triggered abilities

A triggered ability fires when something it waits for happens (CR 382-385). The step that did it
leaves events; `detect` reads them and names the abilities that fire. They wait on the stack, in a
`triggers` frame beneath the work that is still to do, until a player would next receive priority
(CR 383.1); then each goes on the Chain as an object of its own, the turn player's first (CR 383.3).
Triggered Add abilities with no finalization choices resolve before the interrupted work resumes
(CR 430.2).

The abilities that fire are those with the object itself as subject, no condition, and every time.
A player with several abilities to put on the Chain chooses the order, and the targets of each, one
at a time (CR 383.3.d, 355): the decision is the `triggerOrder` frame. With one ability and nothing
to choose, it goes on the Chain at once. An ability with no legal targets is removed (CR 355).
The abilities of other objects, such as a Unit that watches the plays of the others (CR 382), fire
too, when the subject of the ability is the object that was played, killed or moved (`watchersOf`).
Triggers at a point of the turn are later.
-/

@[expose] public section

namespace Riftbound

/-- The events that say a card was played: for the object it became (CR 349). -/
def playedOf (p : PlayerId) (c : ObjId) (es : List Event) : List Event :=
  es.filterMap (fun e => match e with
    | .moved old n _ => if old == c then some (Event.played p n) else none
    | _ => none)

/-- The events a step has besides those of the rules it ran: playing a card (CR 349). -/
def extraEvents (a : Action) (es : List Event) : List Event :=
  match a.kind, a.actor with
  | .playCard c _ ts _ _ _, .player p =>
    let cast := es.any (fun | .moved old _ .chain => old == c | _ => false)
    playedOf p c es ++ (if cast then ts.map (Event.chosenBySpell p) else [])
  -- the objects an ability chooses are chosen too (Irelia: "when you choose or ready me")
  | .activate src _ _ ts _ _ _ _, .player p =>
    if es.any (fun | .moved old _ .chain => old == src | _ => false) then []
    else ts.map (Event.chosenByAbility p)
  | .putTrigger _ ts (.pay ..), .player p => ts.map (Event.chosenByAbility p)
  | _, _ => []

/-- The condition holds for the object when the event happens: none, a fact of how the object was
played (CR 812), or a question about the game, asked for the player `who` the ability works for,
that `Condition.eval` can answer (it is false when it cannot). -/
def condOkEnv (s : GameState) (src : ObjId) (who : PlayerId) (env : Env) : Condition → Bool
  | .always => true
  | .paid => (s.obj? src).any (·.paid)
  | .legion => (s.obj? src).any (·.legion)
  | c => c.eval s who src env == some true

/-- The same, where nothing was chosen. -/
def condOk (s : GameState) (src : ObjId) (who : PlayerId) : Condition → Bool :=
  condOkEnv s src who (Env.empty.withMight s.mightTable)

/-- The ability can fire on the event: it is about the object itself, every time, and its condition
holds. -/
def trigOk (s : GameState) (src : ObjId) (who : PlayerId) (t : Trigger) (_body : EffectDef)
    (eventBattlefields : Option (List ObjId) := none) (eventAmount : Option Nat := none) :
    Bool :=
  let shownOff := if t.event == .play then (s.obj? src).bind (·.shownOff) else none
  let env : Env := { passMight := s.mightTable, shownOff, eventBattlefields, eventAmount }
  t.subject == .self && condOkEnv s src who env t.condition && t.occurrence == .every

/-- The ability can be used again this turn (CR 371, 386). -/
def limitOk (s : GameState) (src : ObjId) (idx : Nat) (limit : Limit)
    (copy : Option Timestamp := none) : Bool := match limit with
  | .unlimited => true
  | .perTurn n => (s.obj? src).any (fun o => decide (o.abilityUses idx copy < n))

/-- The triggered abilities at the places `lo` up to `hi` of the card `d`, as abilities of the
object `src` controlled by `p`, that fire on the event. -/
def triggersAmongMatching (s : GameState) (src : ObjId) (p : PlayerId)
    (eventMatches : TriggerEvent → Bool) (d : CardDef)
    (lo hi : Nat) (copy : Option Timestamp := none)
    (eventBattlefields : Option (List ObjId) := none) (eventAmount : Option Nat := none) :
    List PendTrigger :=
  (List.range (hi - lo)).filterMap (fun (j : Nat) =>
    match d.allAbilities[lo + j]? with
    | some (Ability.triggered t body lim) =>
      if eventMatches t.event && trigOk s src p t body eventBattlefields eventAmount &&
          limitOk s src (lo + j) lim copy then
        some {
          source := src, card := d.id, idx := lo + j, controller := p, copyStamp := copy,
          eventBattlefields, eventAmount,
          shownOff := if t.event == .play then (s.obj? src).bind (·.shownOff) else none }
      else none
    | _ => none)

/-- The triggered abilities in the given range that fire on exactly this event. -/
def triggersAmong (s : GameState) (src : ObjId) (p : PlayerId) (ev : TriggerEvent) (d : CardDef)
    (lo hi : Nat) : List PendTrigger :=
  triggersAmongMatching s src p (· == ev) d lo hi

/-- The object's abilities whose event matches, including abilities it gains (CR 137, 479.3). -/
def triggersOfMatching (s : GameState) (src : ObjId) (p : PlayerId)
    (eventMatches : TriggerEvent → Bool) (lastCopy : Option AttachmentCopy := none)
    (eventBattlefields : Option (List ObjId) := none) (eventAmount : Option Nat := none) :
    List PendTrigger :=
  let definition := (lastCopy.bind (fun copy => s.cards.find? copy.card)) <|> s.cardDef? src
  let stamp := (lastCopy.map (·.stamp)) <|> s.copyStamp? src
  let last := eventMatches .leave || eventMatches .die || eventMatches .deathknell
  (match definition with
    | some d => triggersAmongMatching s src p eventMatches d 0 d.fullAbilities.length stamp
        eventBattlefields eventAmount
    | none => []) ++
  s.inPlay.flatMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      if o.attached == some src then
        triggersAmongMatching s src p eventMatches d d.fullAbilities.length d.allAbilities.length
          (eventBattlefields := eventBattlefields) (eventAmount := eventAmount)
      else []
    | _, _ => []) ++
  (s.attachmentTextDefs src last).flatMap (fun (d, stamp) =>
    triggersAmongMatching s src p eventMatches d 0 d.textAbilities.length (some stamp)
      eventBattlefields eventAmount) ++
  -- an ability that an effect of this turn gave the object
  s.turnFx.flatMap (fun f =>
    match f.kind, f.target with
    | .grantsAbility c i, some u =>
      -- the object, or the card it became when it died (its new identifier in the Trash)
      if (u == src || (s.obj? src).any (fun o => o.leftBoard && o.formerId == some u)) &&
          f.turn == s.turn then
        match s.cards.find? ⟨c⟩ with
        | some d =>
          triggersAmongMatching s src (if u == src then p else f.who) eventMatches d i (i + 1)
            (eventBattlefields := eventBattlefields) (eventAmount := eventAmount)
        | none => []
      else []
    | _, _ => [])

/-- The triggered abilities of the object that fire on exactly this event. -/
def triggersOf (s : GameState) (src : ObjId) (p : PlayerId) (ev : TriggerEvent)
    (eventBattlefields : Option (List ObjId) := none) (eventAmount : Option Nat := none) :
    List PendTrigger :=
  triggersOfMatching s src p (· == ev) (eventBattlefields := eventBattlefields) (eventAmount := eventAmount)

/-- Excess damage belongs to the Combat whose Control step produced this Conquer. -/
def GameState.conquestExcess (s : GameState) (p : PlayerId) (bf : ObjId) : Option Nat :=
  if s.combat.any (·.battlefield == bf) &&
      s.pending.any (fun | .combatFinish field => field == bf | _ => false) then
    s.turnFx.findSome? (fun fx => match fx.kind with
      | .excessDamage n => if fx.who == p && fx.turn == s.turn && fx.target == some bf then some n else none
      | _ => none)
  else none

/-- The definition of a queued trigger, including a keyword assembled from several sources. -/
def triggerAbility (s : GameState) (t : PendTrigger) : Option Ability :=
  (t.triggerKeyword.bind CardDef.keywordTrigger) <|> abilityAt s t.card t.idx

/-- Whether the object `subj`, which the player `who` plays, loses or moves, is what the subject of
a trigger of `src` (controlled by `c`) describes. The place of the subject is not asked: the object
may have left the game, as a Spell on its way to the Chain has. A subject at a place (here, at a
base) is not understood yet: it never holds. Friendly and enemy use the side of the event's player
(CR 491.8.e, 740.1). -/
def subjectHolds (s : GameState) (src : ObjId) (c : PlayerId) (subj : ObjId) (who : PlayerId) :
    Selector → Bool
  | .pick .all side .anywhere fs =>
    (match side with
      | .friendly => s.config.mode.sameSide c who
      | .enemy => !s.config.mode.sameSide c who
      | .you => who == c
      | .any => true) &&
      (fs.holds s src (Env.empty.withMight s.mightTable) subj == some true)
  | _ => false

/-- The abilities of one source that watch an event. A watcher in a group of deaths uses the
controller and text it had on the Board. -/
def watchersAt (s : GameState) (subj : ObjId) (who : PlayerId) (ev : TriggerEvent)
    (occurrence : Occurrence) (src : ObjId) (deadController : Option PlayerId := none)
    (eventAmount : Option Nat := none) :
    List PendTrigger :=
  match s.obj? src with
  | some o =>
    let lastCopy := if deadController.isSome then o.lastAttachmentCopy else none
    match (lastCopy.bind (fun copy => s.cards.find? copy.card)) <|> s.cardDef? src with
    | some d =>
      -- A Battlefield works for the player whose object it is about.
      let c := if d.hasType .battlefield then who else deadController.getD o.controller
      let copy := (lastCopy <|> s.attachmentCopyOf src o).map (·.stamp)
      let board := if ev == .die || ev == .firstUnitDeathHere then s.deathSubject subj else s
      let definitions := (d, d.fullAbilities.length, copy) ::
        ((s.attachmentTextDefs src deadController.isSome).map
          (fun (cd, stamp) => (cd, cd.textAbilities.length, some stamp)))
      definitions.flatMap (fun (cd, count, stamp) =>
        (List.range count).filterMap (fun j =>
          match cd.allAbilities[j]? with
          | some (Ability.triggered t _ lim) =>
            let matchesEvent := t.event == ev ||
              (t.event == .playIncludingTokens && (ev == .play || ev == .playToken))
            if matchesEvent && t.subject != .self &&
                subjectHolds board src c subj who t.subject &&
                condOkEnv board src c
                  { slots := [.obj subj], passMight := board.mightTable, eventAmount } t.condition &&
                t.occurrence == occurrence && limitOk s src j lim stamp then
              some { source := src, card := cd.id, idx := j, controller := c,
                     subject := some subj, copyStamp := stamp }
            else none
          | _ => none))
    | none => []
  | none => []

/-- The Energy the player spent on this Spell at finalization, even after it leaves the Chain. -/
def GameState.watchedSpellEnergy (s : GameState) (who : PlayerId) (spell : ObjId) : Option Nat := do
  let object ← s.obj? spell
  if (s.cardDef? spell).any (·.hasType .spell) && s.playLog.any (fun play =>
      play.who == who && play.moment == .finalized && play.turn == s.turn &&
        (play.object == spell || some play.object == object.formerId)) then
    some object.energyPaid
  else none

/-- The abilities in play that fire for one subject of an event. -/
def watchersOf (s : GameState) (subj : ObjId) (who : PlayerId) (ev : TriggerEvent) :
    List PendTrigger :=
  let eventAmount := if ev == .play then s.watchedSpellEnergy who subj else none
  s.passiveSources.flatMap (fun src => watchersAt s subj who ev .every src (eventAmount := eventAmount))

/-- General "when you choose a friendly unit" watchers see teammate targets as well. A Unit's
own "when you choose me" still requires the Unit's controller to make the choice. -/
def GameState.chosenAnyTriggers (s : GameState) (p : PlayerId) (target : ObjId) : List PendTrigger :=
  if (s.obj? target).any (fun o => s.config.mode.sameSide p o.controller) then
    (if (s.obj? target).any (·.controller == p) then triggersOf s target p .chosenAny else []) ++
      watchersOf s target p .chosenAny
  else []

/-- A grouped death fires once per watching ability. Its source may be one of the dead objects. -/
def GameState.deathGroupWatchers (s : GameState) (es : List Event) : List PendTrigger :=
  let deaths := es.filterMap (fun
    | .died object controller => some (object, controller)
    | _ => none)
  let found := deaths.flatMap (fun (object, controller) =>
    (s.passiveSources.flatMap (fun src => watchersAt s object controller .die .deathGroup src)) ++
      (deaths.flatMap (fun (src, owner) =>
        watchersAt s object controller .die .deathGroup src (some owner))))
  found.eraseDupsBy (fun a b =>
    a.source == b.source && a.card == b.card && a.idx == b.idx &&
      a.copyStamp == b.copyStamp && a.controller == b.controller)

/-- This dead Unit is the first recorded for its controller here this turn. -/
def GameState.firstUnitDeathHere (s : GameState) (id : ObjId) (p : PlayerId) : Bool :=
  (s.obj? id).any (fun o => o.loc.any (fun field =>
    s.turnFx.any (fun note => note.turn == s.turn && note.who == p &&
      note.kind == .firstUnitDeathHere && note.target == some field && note.stamp == o.timestamp.n)))

/-- The Units of the player at the Battlefield. -/
def GameState.trigUnitsAt (s : GameState) (bf : ObjId) (p : PlayerId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun u =>
    (s.obj? u).any (fun o => o.loc == some bf && o.controller == p))

/-- The unit has an Equipment attached that makes its hold effects conquer effects, and the other
way round. -/
def GameState.holdIsConquer (s : GameState) (u : ObjId) : Bool :=
  s.inPlay.any (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      o.attached == some u && d.grants.any (fun ab =>
        match ab with
        | Ability.passive .always mods => mods.contains .holdIsConquer
        | _ => false)
    | _, _ => false)

/-- The Units at the Battlefield, of every player. -/
def GameState.trigAllUnitsAt (s : GameState) (bf : ObjId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun u => (s.obj? u).any (fun o => o.loc == some bf))

/-- The point of the turn that the start of a phase is (CR 314-317). -/
def Phase.timing? : Phase → Option Timing
  | .awaken => some .startOfTurn
  | .beginning => some .beginning
  | .main => some .startOfMain
  | .ending => some .endOfTurn
  | _ => none

/-- The abilities of the objects in play and of the Legends that wait for the point of the turn
`tm`, in the turn of the player `p`: those of the objects `p` controls, and those of a Battlefield,
which work for `p` (CR 314-317). -/
def GameState.timedTriggers (s : GameState) (p : PlayerId) (tm : Timing) : List PendTrigger :=
  (s.inPlay ++ s.players.flatMap (fun q => s.zone (.player q .legendZone))).flatMap (fun src =>
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      let who := if d.hasType .battlefield then p else o.controller
      let copy := (s.attachmentCopyOf src o).map (·.stamp)
      if who == p then
        let matching := (· == TriggerEvent.at_ tm)
        (triggersAmongMatching s src who matching d 0 d.fullAbilities.length copy) ++
        (s.attachmentTextDefs src).flatMap (fun (cd, stamp) =>
          triggersAmongMatching s src who matching cd 0 cd.textAbilities.length (some stamp)) ++
        s.inPlay.flatMap (fun g =>
          match s.obj? g, s.cardDef? g with
          | some og, some dg =>
            if og.attached == some src then
              triggersAmongMatching s src who matching dg dg.fullAbilities.length dg.allAbilities.length
            else []
          | _, _ => [])
      else []
    | _, _ => [])

/-- Beginning triggers that use the Battlefield's current controller. For an open Battlefield,
the turn player handles the ability (CR 190.6). -/
def GameState.battlefieldBeginningTriggers (s : GameState) (turnPlayer : PlayerId) : List PendTrigger :=
  s.battlefields.flatMap fun src =>
    (s.cardDef? src).toList.flatMap fun d =>
      triggersAmong s src ((s.controlOf src).getD turnPlayer) .battlefieldBeginning d 0 d.fullAbilities.length

/-- Collect one Temporary trigger per permanent from its effective keywords, before scoring (CR 816). -/
def GameState.temporaryBeginningTriggers (s : GameState) (p : PlayerId) : List PendTrigger :=
  (tempUnits s p).filterMap fun src =>
    (s.cardDef? src).map fun d =>
      { source := src, card := d.id, idx := d.allAbilities.length, controller := p,
        triggerKeyword := some .temporary }

/-- The abilities that an effect of this turn sets off at the end of the turn (`endTrigger`): the
ability of the card fires with the object as its source. -/
def GameState.fxTriggers (s : GameState) (tm : Timing) : List PendTrigger :=
  if tm == .endOfTurn then
    s.turnFx.filterMap (fun f =>
      match f.kind, f.target with
      | .endTrigger c i, some u =>
        if f.turn == s.turn && (s.obj? u).isSome then
          some { source := u, card := ⟨c⟩, idx := i, controller := f.who }
        else none
      | .endTriggerWithAmount card idx amount, some src =>
        if f.turn == s.turn then
          some { source := src, card, idx, controller := f.who, eventAmount := some amount }
        else none
      | _, _ => none)
  else []

/-- Each matching passive ability adds one instance of the player's Deathknell abilities. -/
def GameState.deathknellExtras (s : GameState) (p : PlayerId) (dead : ObjId) : Nat :=
  let field := (s.obj? dead).bind (·.loc)
  (s.passiveSources.map (fun source =>
    if (s.obj? source).any (·.controller == p) then
      (s.activeMods source).countP (fun
        | .triggersExtra .die .anywhere => true
        | .triggersExtra .deathknell .here => field.isSome && s.hereOf source == field
        | _ => false)
    else 0)).sum

/-- A unit of the player at the Battlefield has a passive ability that makes their conquer (or hold)
effects there fire one more time (Red Brambleback, Blue Sentinel). -/
def GameState.scoreExtra (s : GameState) (p : PlayerId) (bf : ObjId) (conquer : Bool) : Bool :=
  (s.trigUnitsAt bf p).any (fun g =>
    (s.activeMods g).any (fun m =>
      match m with
      | .triggersExtra ev .here => ev == (if conquer then TriggerEvent.conquer else .hold)
      | _ => false))

/-- How much Might a buff just gave the Unit: the buff bonus with and without the last buff. -/
def GameState.buffDelta (s : GameState) (u : ObjId) : Int :=
  let before := s.modObj u (fun o =>
    if 0 < o.extraBuffs then { o with extraBuffs := o.extraBuffs - 1 }
    else { o with buffed := false })
  s.buffBonus u - before.buffBonus u

/-- How much Might the Equipment just gave the Unit: the Equipment bonus with and without it. -/
def GameState.attachDelta (s : GameState) (g u : ObjId) : Int :=
  let before := s.modObj g (fun o => { o with attached := none })
  s.equipBonus u - before.equipBonus u

/-- The abilities that observe a Unit reaching a Might threshold (CR 383, 709). -/
def GameState.mightTriggers (s : GameState) (u : ObjId) (ev : TriggerEvent) :
    List PendTrigger :=
  match s.obj? u with
  | some o =>
    if (s.cardDef? u).any (·.hasType .unit) then
      triggersOf s u o.controller ev ++ watchersOf s u o.controller ev
    else []
  | none => []

/-- The Mighty or numeric threshold named by an ability, with its trigger event. -/
def Ability.mightWatch : Ability → Option (Nat × TriggerEvent)
  | .triggered t _ _ =>
    match t.event with
    | .becomeMighty => some (5, .becomeMighty)
    | .mightAtLeast n => some (n, .mightAtLeast n)
    | _ => none
  | _ => none

/-- Find the thresholds to check, including abilities that equipment or a lasting effect grants. -/
def GameState.mightWatches (s : GameState) : List (Nat × TriggerEvent) :=
  let printed := s.passiveSources.flatMap (fun id =>
    ((s.cardDef? id).map (·.allAbilities)).getD [] |>.filterMap Ability.mightWatch)
  let granted := s.turnFx.filterMap (fun f =>
    match f.kind with
    | .grantsAbility c i =>
      if f.turn == s.turn then
        ((s.cards.find? ⟨c⟩).bind (fun d => d.allAbilities[i]?)).bind Ability.mightWatch
      else none
    | _ => none)
  (printed ++ granted).eraseDups

/-- Compare the derived Might across a step. A Unit that enters with Might already at a threshold
has not crossed it. A Unit that stays at or above it does not trigger again (CR 383, 709). -/
def GameState.mightyEvents (s s' : GameState) : List Event :=
  let watches := s'.mightWatches
  if watches.isEmpty then [] else
    let old := s.inPlay
    s'.inPlay.flatMap (fun u =>
      if old.contains u && (s'.cardDef? u).any (·.hasType .unit) then
        match s.mightNow u, s'.mightNow u with
        | some before, some after =>
          watches.filterMap (fun (n, ev) =>
            if before < (n : Int) && (n : Int) ≤ after then
              match ev with
              | .becomeMighty => some (.becameMighty u)
              | .mightAtLeast k => some (.mightReached u k)
              | _ => none
            else none)
        | _, _ => []
      else [])

/-- Report a decrease only for a Unit that remains on the Board, while a player is carrying
out an instruction or taking an action. State-based changes have no reducing player. -/
def GameState.mightReductionEvents (s s' : GameState) (actor : Option PlayerId) : List Event :=
  match actor with
  | none => []
  | some p =>
    let watching (d : CardDef) := d.allAbilities.any (fun
      | .triggered t _ _ => t.event == .mightReducedByYou
      | _ => false)
    if s'.passiveSources.any (fun id =>
      (s'.obj? id).any (·.controller == p) &&
        ((s'.cardDef? id).any watching ||
          (s'.attachmentTextDefs id false).any (fun (d, _) => watching d))) then
      let oldBoard := s.inPlay
      s'.inPlay.filterMap (fun id =>
        if !oldBoard.contains id || !(s'.cardDef? id).any (·.hasType .unit) ||
            !(s'.obj? id).any (fun o => !s'.config.mode.sameSide p o.controller) then none
        else
          match s.mightNow id, s'.mightNow id with
          | some before, some after =>
            if after < before then some (.mightReduced p id (before - after).toNat) else none
          | _, _ => none)
    else []

/-- Detect exhaustion of objects that were already on the Board. Entering exhausted and
exhausting an already exhausted object do not change it from ready to exhausted (CR 415). -/
def GameState.exhaustionEvents (s s' : GameState) (who : Option PlayerId)
    (beforeMove : Bool := false) : List Event :=
  let oldBoard := s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))
  let exhausted := oldBoard.filter (fun id =>
    (s.obj? id).any (fun o => !o.exhausted) && (s'.obj? id).any (·.exhausted))
  if exhausted.isEmpty then [] else [.exhaustBatch who exhausted beforeMove]

/-- State changes during a work frame, with the player instructed by a resolving effect. -/
def GameState.workTransitionEvents (s s' : GameState) : List Event :=
  let who := match s.pending with
    | .run p .. :: _ => some p
    | _ => none
  let damageLinks := match s.pending, s'.pending with
    | .cleanup :: _, .cleanup :: _
    | .cleanup :: _, .eitherDo .. :: .cleanup :: _ => []
    | .cleanup :: _, _ =>
      if s.turnFx.any (fun f => match f.kind with | .linkedDamageDeath .. => true | _ => false)
      then [.linkedDamageCleanupDone] else []
    | _, _ => []
  s.exhaustionEvents s' who ++ s.mightyEvents s' ++ s.mightReductionEvents s' who ++ damageLinks

/-- State changes during an answer. Passing Chain priority cannot change Board objects. -/
def GameState.actionTransitionEvents (s s' : GameState) (a : Action) : List Event :=
  match s.pending, a.kind with
  | .chainPass .. :: _, .pass => []
  | _, kind =>
    let who := match a.actor with | .player p => some p | _ => none
    let beforeMove := match s.pending, kind with
      | _, .standardMove .. | .groupMove .. :: _, .decide true => true
      | _, _ => false
    s.exhaustionEvents s' who beforeMove ++ s.mightyEvents s' ++ s.mightReductionEvents s' who

/-- The marked Unit's death sets off the effects that were created by a spell or ability.
They retain their original source and controller and are independent of Deathknell (CR 391-393). -/
def GameState.delayedDeathTriggers (s : GameState) (dead : ObjId) : List PendTrigger :=
  let former := (s.obj? dead).bind (·.formerId)
  s.turnFx.flatMap (fun f =>
    match f.kind with
    | .triggerOnDeath src card idx =>
      if f.turn == s.turn && f.target.any (fun id => id == dead || some id == former) then
        (s.cards.find? card).toList.flatMap (triggersAmong s src f.who .die · idx (idx + 1))
      else []
    | _ => [])

/-- The abilities that watch the first card the player successfully played this turn
(CR 420.4.a). -/
def GameState.firstCardTriggers (s before : GameState) : List PendTrigger :=
  if s.playLog == before.playLog then []
  else
    let completed (state : GameState) (p : PlayerId) :=
      state.playLog.any (fun play =>
        play.turn == s.turn && play.who == p && play.moment == .resolved)
    let players := s.players.filter (fun p => !completed before p && completed s p)
    players.flatMap (fun p => s.inPlay.flatMap (fun src =>
      if (s.obj? src).any (·.controller == p) then triggersOf s src p .firstCardResolved else []))

/-- The player's watchers of a qualifying Unit, Gear, or activated ability (CR 206-206.1). -/
def GameState.baseEnergyPlayTriggers (s : GameState) (p : PlayerId) (energy : Nat) : List PendTrigger :=
  s.passiveSources.flatMap (fun src =>
    if (s.obj? src).any (·.controller == p) then
      triggersOfMatching s src p (fun
        | .playAtBaseEnergy minimum => decide (minimum ≤ energy)
        | _ => false)
    else [])

/-- Watch completed plays of physical cards from the player's own Trash (CR 385.2, 420.4.a). -/
def GameState.trashEnergyPlayTriggers (s : GameState) (p : PlayerId) (played : ObjId) :
    List PendTrigger := Id.run do
  let some obj := s.obj? played | return []
  let .card _ id := obj.kind | return []
  let some cost := (s.cards.find? id).bind (·.cost) | return []
  return (s.zone (.player p .trash)).flatMap (fun src =>
    (s.printedCardDef? src).toList.flatMap (fun d =>
      triggersAmongMatching s src p (fun
        | .playCardFromTrashAtEnergy minimum => decide (minimum ≤ cost.energy)
        | _ => false) d 0 d.fullAbilities.length))

/-- Disarm fires once for the total of the attacker's instances of the keyword (CR 831). -/
def GameState.disarmTriggers (s : GameState) (unit : ObjId) (attacker : PlayerId) : List PendTrigger :=
  match s.cardDef? unit with
  | some d =>
    let amount := s.kwAmount unit .disarm
    if d.hasType .unit && amount > 0 then
      [{ source := unit
         card := d.id
         idx := d.allAbilities.length
         controller := attacker
         triggerKeyword := some .disarm
         eventAmount := some amount }]
    else []
  | none => []

/-- The triggers of an object becoming an attacker or defender in this Combat. -/
def GameState.combatantTriggers (s : GameState) (att : PlayerId) (u : ObjId) : List PendTrigger :=
  match s.obj? u with
  | some o =>
    let ev := if o.controller == att then TriggerEvent.attack else .defend
    let fields := some o.loc.toList
    (triggersOf s u o.controller ev ++ watchersOf s u o.controller ev ++
      (if o.controller == att then s.disarmTriggers u att else [])).map
      (fun t => { t with eventBattlefields := fields })
  | none => []

/-- Abilities watching the group of Units that become attackers together at this Battlefield. -/
def GameState.friendlyAttackGroupTriggers (s : GameState) (field : ObjId) (attacker : PlayerId)
    (units : List ObjId) : List PendTrigger :=
  let attackers := units.filter (fun id => (s.obj? id).any (·.controller == attacker))
  if attackers.isEmpty then [] else
    (s.trigUnitsAt field attacker).flatMap (fun src =>
      (triggersOf s src attacker .friendlyAttackGroupHere).map
        (fun t => { t with eventObjects := attackers }))

/-- Exhaustion abilities of individual objects and of a player who exhausted several Units. -/
def GameState.exhaustionTriggers (s : GameState) (who : Option PlayerId) (objects : List ObjId)
    (beforeMove : Bool) : List PendTrigger :=
  let lastController (id : ObjId) :=
    (s.obj? id).map (fun o => o.leftController.getD o.controller)
  let individual := objects.flatMap (fun id =>
    match lastController id with
    | some owner => triggersOf s id owner .exhaust ++ watchersOf s id owner .exhaust
    | none => [])
  let combined := who.toList.flatMap (fun p =>
    let count := objects.countP (fun id =>
      (s.cardDef? id).any (·.hasType .unit) && lastController id == some p)
    if count == 0 then [] else
      s.passiveSources.flatMap (fun id =>
        if (s.obj? id).any (·.controller == p) then
          triggersOfMatching s id p (fun
            | .youExhaustUnits minimum => decide (minimum ≤ count)
            | _ => false)
        else []))
  (individual ++ combined).map (fun t => { t with beforeStandardMove := beforeMove })

/-- A Unit or Gear being played to a Battlefield, with its new object's timestamp. -/
def GameState.battlefieldPlay (s : GameState) (id : ObjId) : Option (ObjId × Nat) := do
  let d ← s.cardDef? id
  if !(d.hasType .unit || d.hasType .gear) then none else
    let o ← s.obj? id
    let field ← o.loc
    pure (field, o.timestamp.n)

/-- The Battlefield's abilities for each player's first Unit or Gear played there this turn. -/
def GameState.firstPermanentHereTriggers (s : GameState) (p : PlayerId) (id : ObjId) :
    List PendTrigger :=
  match s.battlefieldPlay id with
  | some (field, stamp) =>
    if s.turnFx.any (fun f => f.turn == s.turn && f.who == p && f.kind == .playedToBattlefield &&
        f.target == some field && f.stamp == stamp) then
      triggersOf s field p .firstPermanentHere
    else []
  | none => []

/-- The abilities that fire because of one event (CR 389). -/
def detectOne (s : GameState) : Event → List PendTrigger
  | .exhaustBatch who objects beforeMove => s.exhaustionTriggers who objects beforeMove
  | .played p obj =>
    match s.cardDef? obj with
    | some d =>
      -- A Spell completes its play when it resolves (CR 420.4.a).
      if d.hasType .spell then [] else
        let fields := (s.obj? obj).map (fun o => o.loc.toList)
        ((triggersOf s obj p .play ++ watchersOf s obj p .play).map
          (fun t => { t with eventBattlefields := fields })) ++
        (if d.hasType .unit || d.hasType .gear then
          s.baseEnergyPlayTriggers p ((d.cost.map Cost.energy).getD 0) ++
            s.firstPermanentHereTriggers p obj
        else []) ++ s.trashEnergyPlayTriggers p obj
    | none => []
  | .spellResolved p obj =>
    triggersOf s obj p .play ++ watchersOf s obj p .play ++ s.trashEnergyPlayTriggers p obj
  | .burnedUnitFor p src card idx _ might =>
    match s.cards.find? card with
    | some d => (triggersAmong s src p .linkedBurnUnit d idx (idx + 1)).map
      (fun t => { t with eventAmount := some might })
    | none => []
  | .discardedTypeFor p src card idx _ =>
    match s.cards.find? card with
    | some d => triggersAmong s src p .linkedDiscardType d idx (idx + 1)
    | none => []
  | .killedByLinkedDamage p src card idx _ =>
    match s.cards.find? card with
    | some d => triggersAmong s src p .linkedDamageKill d idx (idx + 1)
    | none => []
  | .unitTokensFor p src card idx target tokens destination =>
    match s.cards.find? card with
    | some d => (triggersAmong s src p (.linkedUnitTokens target.isSome) d idx (idx + 1)).map
      (fun t => { t with
        subject := target
        eventObjects := tokens
        eventBattlefields := some destination.toList })
    | none => []
  | .died obj p =>
    let lastCopy := (s.obj? obj).bind (·.lastAttachmentCopy)
    let own := triggersOfMatching s obj p (fun ev => ev == .die || ev == .deathknell) lastCopy
    let extras := s.deathknellExtras p obj
    let again :=
      if extras > 0 then
        let definition := (lastCopy.bind (fun copy => s.cards.find? copy.card)) <|> s.cardDef? obj
        let deathknell := definition.any (·.hasKeyword .deathknell) ||
          (s.attachmentTextDefs obj true).any (·.1.hasKeyword .deathknell)
        let matching := if deathknell then own else triggersOfMatching s obj p (· == .deathknell) lastCopy
        (List.replicate extras matching).flatten
      else []
    let fields := (s.obj? obj).map (fun o => o.loc.toList)
    (own ++ again).map (fun t => { t with eventBattlefields := fields }) ++
      watchersOf s obj p .die ++
      (if s.firstUnitDeathHere obj p then watchersOf s obj p .firstUnitDeathHere else []) ++
      s.delayedDeathTriggers obj
  | .standardMoved u destination =>
    match s.obj? u with
    | some o =>
      let fields := some (o.prevLoc.toList ++ o.loc.toList)
      (triggersOf s u o.controller .move).map (fun t => { t with eventBattlefields := fields }) ++
        triggersOf s u o.controller .moveFrom (some o.prevLoc.toList) ++
        (destination.elim [] (fun field =>
          triggersOf s u o.controller .moveToBattlefield (some [field]))) ++
        watchersOf s u o.controller .move
    | none => []
  | .phaseStarted p .beginning =>
    s.timedTriggers p .beginning ++ s.battlefieldBeginningTriggers p ++ s.temporaryBeginningTriggers p
  | .phaseStarted p ph =>
    match ph.timing? with
    | some tm => s.timedTriggers p tm ++ s.fxTriggers tm
    | none => []
  | .conquerActivated u =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .conquer
    | none => []
  | .lookedAt p c => triggersOf s c p .seenOnTop
  | .chosenBySpell p t =>
    (if (s.obj? t).any (·.controller == p) then
      triggersOf s t p .chosen ++ watchersOf s t p .chosen
    else []) ++ s.chosenAnyTriggers p t
  | .chosenByAbility p t => s.chosenAnyTriggers p t
  | .killedBySpell p =>
    (s.zone (.player p .trash)).flatMap (fun u => triggersOf s u p .killBySpell)
  | .recycled p =>
    s.inPlay.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then triggersOf s u p .recycle else [])
  | .hiddenPlayed p =>
    s.passiveSources.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then triggersOf s u p .playHidden else [])
  | .tokenPlayed p t =>
    triggersOf s t p .playToken ++ watchersOf s t p .playToken ++ s.firstPermanentHereTriggers p t
  | .revealed p c => triggersOf s c p .revealedFromDeck ++ watchersOf s c p .revealedFromDeck
  | .moved _ n dst =>
    -- a Rune recycled: the abilities of the player's objects and Legends that wait for it
    (match dst with
      | .player p .runeDeck =>
        if (s.obj? n).any (·.runeDomain.isSome) then
          s.passiveSources.flatMap (fun u =>
            if (s.obj? u).any (·.controller == p) then triggersOf s u p .recycleRune else [])
        else []
      -- a card hidden: what waits for the player to hide a card fires
      | .player p .hidden =>
        let hiddenAt := (s.obj? n).bind (·.hiddenAt)
        s.passiveSources.flatMap (fun u =>
          let watches := if (s.cardDef? u).any (·.hasType .battlefield) then hiddenAt == some u
            else (s.obj? u).any (·.controller == p)
          if watches then triggersOf s u p .hide else [])
      | _ => []) ++
    -- a card that is put where it is not on the board: what waits for it to leave fires
    (if !dst.isBoard then
      match s.obj? n with
      | some o =>
        if o.leftBoard then
          let controller := o.leftController.getD o.owner
          triggersOfMatching s n controller (· == .leave) o.lastAttachmentCopy ++
            watchersOf s n controller .leave
        else []
      | none => []
    else [])
  | .drew p =>
    s.passiveSources.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then triggersOf s u p .draw else [])
  | .drewGroup p otherCards =>
    s.passiveSources.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then
        triggersOfMatching s u p (fun
          | .drawGroupWithHand minimum => decide (minimum ≤ otherCards)
          | _ => false)
      else [])
  | .banished p owner _ =>
    if p == owner then
      s.passiveSources.flatMap (fun u =>
        if (s.obj? u).any (·.controller == p) then triggersOf s u p .banishOwn else [])
    else []
  | .movedByEffect p u =>
    match s.obj? u with
    | some o => (watchersOf s u o.controller .movedByYou).filter (fun t => t.controller == p)
    | none => []
  | .buffed u =>
    match s.obj? u with
    | some o =>
      triggersOf s u o.controller .buff ++ watchersOf s u o.controller .buff
    | none => []
  | .readied u =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .ready ++ watchersOf s u o.controller .ready
    | none => []
  | .stunned u =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .stun ++ watchersOf s u o.controller .stun
    | none => []
  | .discarded p obj last =>
    triggersOf s obj p .discard ++ (if last then watchersOf s obj p .discard else [])
  | .scored p bf conquer =>
    let excess := if conquer then s.conquestExcess p bf else none
    let atField (src : ObjId) (event : TriggerEvent) := triggersOf s src p event (some [bf]) excess
    let event := if conquer then TriggerEvent.conquer else .hold
    let watched := (watchersOf s bf p event).map (fun t => { t with eventBattlefields := some [bf] })
    let (own, others) := watched.partition (fun t => t.controller == p)
    let eff :=
      (s.trigUnitsAt bf p).flatMap
        (fun u => atField u event ++
          atField u .scored ++
          -- Skyfall of Areion: the hold effects of the unit are conquer effects too, and back
          (if s.holdIsConquer u then atField u (if conquer then .hold else .conquer)
           else [])) ++
      (s.zone (.player p .legendZone)).flatMap
        (fun l => atField l (if conquer then .youConquer else .youHold)) ++
      atField bf (if conquer then .youConquer else .youHold) ++ own
    -- Extra effects from scoring here belong to the scorer, even if a teammate also triggers.
    eff ++ (if s.scoreExtra p bf conquer then eff else []) ++ others ++
    -- what the opponents of the player who scores wait for
    s.passiveSources.flatMap (fun u =>
      match s.obj? u with
      | some o =>
        if !s.config.mode.sameSide p o.controller then
          triggersOf s u o.controller .opponentScores ++
            (if conquer then [] else
              triggersOf s u o.controller .opponentHolds ++
                (if o.loc == some bf then triggersOf s u o.controller .opponentHoldsHere else []))
        else []
      | none => []) ++
    -- the cards in the Trash that wait for a conquer of their player
    (if conquer then
      (s.zone (.player p .trash)).flatMap (fun u => triggersOf s u p .conquerFromTrash)
    else [])
  | .attached _ u =>
    match s.obj? u with
    | some o =>
      triggersOf s u o.controller .attachedTo
    | none => []
  | .becameMighty u => s.mightTriggers u .becomeMighty
  | .mightReached u n => s.mightTriggers u (.mightAtLeast n)
  | .mightReduced p u amount =>
    if amount == 0 then [] else
      (s.obj? u).toList.flatMap (fun o =>
        (watchersOf s u o.controller .mightReducedByYou).filter (·.controller == p))
  | .empowered p u =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .becomeEmpowered ++ watchersOf s u p .becomeEmpowered
    | none => []
  | .buffSpent p =>
    s.inPlay.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then triggersOf s u p .spendBuff else [])
  | .activated p src _ baseEnergy =>
    -- an ability of a gear on the Board (not Hide, not the play of a hidden gear)
    let gearUse := if (s.cardDef? src).any (·.hasType .gear) && src ∈ s.inPlay then
        s.inPlay.flatMap (fun u =>
          if (s.obj? u).any (·.controller == p) then triggersOf s u p .useGearAbility else [])
      else []
    gearUse ++ baseEnergy.toList.flatMap (s.baseEnergyPlayTriggers p)
  | .combatWon bf w =>
    (s.trigUnitsAt bf w).flatMap (fun u => triggersOf s u w .winCombat) ++
    (s.zone (.player w .legendZone)).flatMap (fun l => triggersOf s l w .winCombat)
  | .combatEnded _ units =>
    units.flatMap (fun u =>
      if s.inPlay.contains u then
        (s.obj? u).toList.flatMap (fun o => triggersOf s u o.controller .combatEnd)
      else [])
  | .showdownOpened bf =>
    (s.trigAllUnitsAt bf).flatMap fun unit =>
      (s.obj? unit).toList.flatMap fun o => triggersOf s unit o.controller .showdownStart
  | .combatStarted bf att =>
    let controller := ((s.obj? bf).bind (·.control)).getD (s.active.getD att)
    triggersOf s bf controller .combatStart ++
    (s.trigAllUnitsAt bf).flatMap (s.combatantTriggers att) ++
    s.friendlyAttackGroupTriggers bf att (s.unitsAtOf bf att) ++
    -- the abilities of the Battlefield: for the players who attack and defend there
    (s.players.filter (fun q => !(s.trigUnitsAt bf q).isEmpty)).flatMap (fun q =>
      triggersOf s bf q (if q == att then TriggerEvent.attack else .defend)) ++
    -- the defending player’s Units, including ones already at this Battlefield
    (s.players.filter (fun q => q != att && !(s.trigUnitsAt bf q).isEmpty)).flatMap (fun q =>
      s.inPlay.flatMap (fun u =>
        if (s.obj? u).any (fun o => o.controller == q) &&
            (s.cardDef? u).any (·.hasType .unit) then
          (triggersOf s u q .youDefend).map (fun t => { t with subject := some bf })
        else []))
  | .combatJoined bf att units =>
    units.flatMap (s.combatantTriggers att) ++ s.friendlyAttackGroupTriggers bf att units
  | _ => []

/-- Keep the abilities that a limit of times per turn lets fire: the events of one step may set
off the same ability more than once, and the limit counts the times it fired before and those it
fires now (CR 371). -/
def GameState.trimLimits (s : GameState) (l : List PendTrigger) : List PendTrigger :=
  l.foldl (fun kept t =>
    let taken := (kept.filter (fun k =>
      k.source == t.source && k.idx == t.idx && k.copyStamp == t.copyStamp)).length
    match triggerAbility s t,
        s.obj? t.source with
    | some (Ability.triggered _ _ (.perTurn n)), some o =>
      if o.abilityUses t.idx t.copyStamp + taken < n then kept ++ [t] else kept
    | _, _ => kept ++ [t]) []

/-- The order for abilities that fire together. Combat opens with the attacker and ends with
the defender, with any other team-game seats in turn order between them (CR 383.3.d.1, 466.2.d.1). -/
def GameState.triggerSeatOrder (s : GameState) (es : List Event) : List PlayerId :=
  let opening := s.combat.filter (fun c => es.contains (.combatStarted c.battlefield c.attacker))
  match opening with
  | some c =>
    let order := ({ s with active := some c.attacker } : GameState).pickOrder
    [c.attacker] ++ order.filter (fun p => p != c.attacker && p != c.defender) ++ [c.defender]
  | none => s.pickOrder

/-- The Battlefield of a friendly Unit targeted by this player's Spell (CR 383.4.b, 740.1.a). -/
def GameState.friendlySpellField (s : GameState) (p : PlayerId) (id : ObjId) : Option ObjId := do
  let unit ← s.obj? id
  let field ← unit.loc
  if (s.zone .battlefieldZone).contains id && (s.cardDef? id).any (·.hasType .unit) &&
      s.config.mode.sameSide p unit.controller then some field else none

/-- Whether the when-and-where of this fact was already recorded. -/
def recordedTurnFact (notes : List TurnFx) (turn : Nat) (p : PlayerId) (kind : TurnEffect)
    (target : Option ObjId) : Bool :=
  notes.any (fun f => f.turn == turn && f.who == p && f.kind == kind && f.target == target)

/-- Targeting several Units at the same Battlefield completes the first choice there once. -/
def GameState.firstSpellFieldTriggers (s : GameState) (notes : List TurnFx) (es : List Event) :
    List PendTrigger :=
  let fields := es.filterMap (fun
    | .chosenBySpell p id => (s.friendlySpellField p id).map (p, ·)
    | _ => none)
  fields.eraseDups.flatMap (fun (p, field) =>
    if recordedTurnFact notes s.turn p .chosenHere (some field) then []
    else triggersOf s field p .chosenHere)

/-- The continuing players' abilities that fire because of the events of a step (CR 651.3).
First-choice triggers compare against the facts from before the event batch. -/
def GameState.detect (s : GameState) (es : List Event) (extra : List PendTrigger := [])
    (beforeFacts : Option (List TurnFx) := none) :
    List PendTrigger :=
  let choices := s.firstSpellFieldTriggers (beforeFacts.getD s.turnFx) es
  let all := s.trimLimits ((es.flatMap (detectOne s) ++ s.deathGroupWatchers es ++ choices ++ extra).filter
    (fun t => !s.departures.seats.contains t.controller))
  let active := s.active.getD ⟨0⟩
  let seatOrder (group : List PendTrigger) :=
    if s.config.mode.isTeamDuel || s.config.mode.isFreeForAll then
      (s.triggerSeatOrder es).flatMap (fun p => group.filter (fun t => t.controller == p))
    else group.filter (fun t => t.controller == active) ++ group.filter (fun t => t.controller != active)
  let (beforeMove, later) := all.partition (·.beforeStandardMove)
  seatOrder beforeMove ++ seatOrder later

/-- The frames that complete outstanding work before triggered abilities are finalized (CR 334).
This includes draws still owed by the current task or instruction. -/
def Frame.isResolution : Frame → Bool
  | .cleanup => true
  | .draw .. => true
  | .run .. => true
  | .finishSpell _ => true
  | .resolveChain => true
  | .endShowdown _ => true
  | .combatDamage .. => true
  | .combatResolve .. => true
  | .pickDo _ _ _ _ _ (.recordBanishReplay ..) _
  | .pickDo _ _ _ _ _ (.recordRuneRecycle ..) _
  | .pickDo _ _ _ _ _ (.recordTrashRecycle ..) _ => true
  | .eitherDo _ _ _ (.chooseTrashRecycle ..) _ _ => true
  | .predict .. | .chancePredict .. | .chanceRecycleTrash .. => true
  | .eitherDo _ _ _ (.fundPermanentFromEffect ..) _ _ => true
  | .eitherDo _ _ _ (.finishFundedPermanent ..) _ _ => true
  | .eitherDo _ _ _ (.fundLimitedSpell ..) _ _ => true
  | .eitherDo _ _ _ (.finishLimitedSpell ..) _ _ => true
  | .eitherDo _ _ _ (.chooseDamageReplacement ..) _ _ => true
  | .eitherDo _ _ _ (.orderCombatDamage ..) _ _ => true
  | .eitherDo _ _ _ (.applySplitDamage _) _ _ => true
  | .eitherDo _ _ _ (.applyUnitSplitDamage ..) _ _ => true
  | .pickDo _ _ _ _ _ (.retainTargetSet _) _ => true
  | .eitherDo _ _ _ (.prim (.attachPaying ..)) _ _ => true
  | .eitherDo _ _ _ (.chooseDeathBanisher ..) _ _ => true
  | .eitherDo _ _ _ (.recordDeathSacrifice ..) _ _
  | .eitherDo _ _ _ (.recordDeathOrder ..) _ _ => true
  | .eitherDo _ _ _ (.planUnitTokenEntries ..) _ _
  | .eitherDo _ _ _ (.fundTokenAccelerate ..) _ _
  | .eitherDo _ _ _ (.finishUnitTokens ..) _ _ => true
  | .eitherDo _ _ _ first _ _ => first.isPayment
  | _ => false

/-- Put the triggers on the stack beneath the work that is still to do: just before the first frame
that is not resolution. Triggers already waiting there are joined. -/
def insertTriggers (pend : List PendTrigger) : List Frame → List Frame
  | [] => [.triggers pend]
  | f :: fs =>
    if f.isResolution then f :: insertTriggers pend fs
    else
      match f with
      | .triggers old => .triggers (old ++ pend) :: fs
      | _ => .triggers pend :: f :: fs

/-- The frames after inserting triggers are the old frames and `triggers` frames. -/
theorem insertTriggers_mem (pend : List PendTrigger) :
    ∀ (p : List Frame) {f : Frame}, f ∈ insertTriggers pend p →
      f ∈ p ∨ ∃ x, f = .triggers x
  | [], f, h => by
    simp only [insertTriggers, List.mem_singleton] at h
    exact Or.inr ⟨_, h⟩
  | g :: gs, f, h => by
    unfold insertTriggers at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases insertTriggers_mem pend gs h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
    · split at h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inl h

/-- Inserting triggers keeps the last frame, if it is not resolution and not a `triggers` frame. -/
theorem insertTriggers_getLast (pend : List PendTrigger) :
    ∀ (p : List Frame) {g : Frame}, p.getLast? = some g → g.isResolution = false →
      (∀ x, g ≠ .triggers x) → (insertTriggers pend p).getLast? = some g
  | [], g, h, _, _ => by simp at h
  | f :: fs, g, h, hr, hn => by
    cases fs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      unfold insertTriggers
      simp only [hr]
      cases f with
      | triggers x => exact absurd rfl (hn x)
      | _ => simp [List.getLast?_cons_cons]
    | cons y ys =>
      have h' : (y :: ys).getLast? = some g := by
        simpa [List.getLast?_cons_cons] using h
      have ih := insertTriggers_getLast pend (y :: ys) h' hr hn
      unfold insertTriggers
      split
      · have hne : insertTriggers pend (y :: ys) ≠ [] := by
          unfold insertTriggers; split <;> (try split) <;> simp
        cases hl : insertTriggers pend (y :: ys) with
        | nil => exact absurd hl hne
        | cons z zs =>
          rw [hl] at ih
          simpa [List.getLast?_cons_cons] using ih
      · split
        · simpa [List.getLast?_cons_cons] using h
        · simpa [List.getLast?_cons_cons] using h

/-- Inserting triggers does not change what the frames account for in the hands. -/
theorem insertTriggers_contrib (pend : List PendTrigger) (q : PlayerId) (contrib : Frame → Nat)
    (h0 : ∀ x, contrib (.triggers x) = 0) :
    ∀ p : List Frame, ((insertTriggers pend p).map contrib).sum = (p.map contrib).sum
  | [] => by simp [insertTriggers, h0]
  | f :: fs => by
    unfold insertTriggers
    split
    · simp [insertTriggers_contrib pend q contrib h0 fs]
    · split
      · simp [h0]
      · simp [h0]

/-- Add a play to the current turn's history, with the types and player fixed at that moment. -/
def addCardPlay (turn : Nat) (plays : List CardPlay) (p : PlayerId) (obj : ObjId)
    (d : CardDef) (moment : PlayMoment) : List CardPlay :=
  ⟨p, obj, d.types, turn, moment⟩ ::
    (if plays.head?.map (·.turn) == some turn then plays else [])

/-- Whether the hidden card is already recorded as finalized in its original zone. -/
def hiddenFinalized (plays : List CardPlay) (turn : Nat) (p : PlayerId) (id : ObjId) : Bool :=
  plays.any (fun play => play.moment == .finalized && play.turn == turn &&
    play.who == p && play.object == id)

/-- Record completed finalizations and permanent plays. Hidden plays are finalized by the
activation that pays for the play; the later movement of the card is its resolution
(CR 811, 420.4). Token creation and ordinary ability activations do not finalize a card. -/
def GameState.recordPlayEvent (s : GameState) (plays : List CardPlay) : Event → List CardPlay
  | .played p id =>
    match s.obj? id, s.cardDef? id with
    | some o, some d =>
      if o.kind.phys?.isSome then
        let original := if o.fromHidden then o.formerId.getD id else id
        let noted := if (o.fromHidden || o.hiddenAt.isSome) &&
            hiddenFinalized plays s.turn p original then plays
          else addCardPlay s.turn plays p id d .finalized
        if d.hasType .spell then noted else addCardPlay s.turn noted p id d .resolved
      else plays
    | _, _ => plays
  | .spellResolved p id =>
    match s.cardDef? id with
    | some d => addCardPlay s.turn plays p id d .resolved
    | none => plays
  | .activated p id idx _ =>
    match s.obj? id, s.cardDef? id with
    | some o, some d =>
      match d.fullAbilities[idx]? with
      | some (.activated costs _ _ _) =>
        if o.kind.phys?.isSome && costs.contains .fromHidden &&
            !hiddenFinalized plays s.turn p id then addCardPlay s.turn plays p id d .finalized
        else plays
      | _ => plays
    | _, _ => plays
  | _ => plays

/-- Save the first fact of a kind this turn for a player and optional object. -/
def GameState.recordTurnFact (s : GameState) (notes : List TurnFx)
    (p : PlayerId) (kind : TurnEffect) (target : Option ObjId) (stamp : Nat) : List TurnFx :=
  if recordedTurnFact notes s.turn p kind target then notes
  else { who := p, turn := s.turn, stamp, kind, target } :: notes

/-- An enemy Unit was targeted by this player's Spell or ability. -/
def GameState.recordEnemyChoice (s : GameState) (notes : List TurnFx) (p : PlayerId)
    (id : ObjId) : List TurnFx :=
  if s.inPlay.contains id && (s.obj? id).any (fun o => !s.config.mode.sameSide p o.controller) &&
      (s.cardDef? id).any (·.hasType .unit) then
    s.recordTurnFact notes p .choseEnemyUnit none s.nextTimestamp
  else notes

/-- Register only successful plays by the instructed player, including Unit and Gear tokens. -/
def GameState.matchesDelayedPlay (s : GameState) (who : PlayerId) (kind : CardType) : Event → Bool
  | .played p id | .tokenPlayed p id => p == who && (s.cardDef? id).any (·.hasType kind)
  | _ => false

/-- Each waiting ability gets one trigger per matching event up to its remaining uses (CR 391-393).
The original source can already have left the Chain. -/
def GameState.delayedPlayTriggers (s : GameState) (es : List Event) : List PendTrigger :=
  if es.isEmpty then [] else
  s.turnFx.flatMap (fun note =>
    match note.kind, note.target with
    | .triggerOnPlays card idx kind remaining, some src =>
      if note.turn != s.turn then [] else
        ((es.filter (s.matchesDelayedPlay note.who kind)).take remaining).flatMap (fun _ =>
          (s.cards.find? card).toList.flatMap
            (fun d => triggersAmong s src note.who .delayedPlay d idx (idx + 1)))
    | _, _ => [])

/-- Remember facts about choices, plays and deaths for the rest of the turn. -/
def GameState.recordTurnEvent (s : GameState) (notes : List TurnFx) : Event → List TurnFx
  | event@(.played p id) | event@(.tokenPlayed p id) =>
    let waiting := notes.map (fun f =>
      match f.kind with
      | .triggerOnPlays card idx kind remaining =>
        if f.turn == s.turn && remaining > 0 && s.matchesDelayedPlay f.who kind event then
          { f with kind := .triggerOnPlays card idx kind (remaining - 1) }
        else f
      | .nextUnitCostMinusThenEnd _ _ card idx =>
        if f.who == p && f.turn == s.turn && s.matchesDelayedPlay p .unit event then
          { f with kind := .endTrigger card.code idx, target := some id }
        else f
      | _ => f)
    let waiting := match event with
      | .tokenPlayed .. =>
        if (s.cardDef? id).any (·.hasType .unit) then
          waiting.filter (fun f =>
            !(f.who == p && f.turn == s.turn &&
              (f.kind == .nextUnitAnywhereBuffed || f.kind == .nextUnitAccelerate)))
        else waiting
      | _ => waiting
    match s.battlefieldPlay id with
    | some (field, stamp) => s.recordTurnFact waiting p .playedToBattlefield (some field) stamp
    | none => waiting
  | .chosenBySpell p id =>
    match s.friendlySpellField p id with
    | some field =>
      if (triggersOf s field p .chosenHere).isEmpty then notes
      else s.recordTurnFact notes p .chosenHere (some field) s.nextTimestamp
    | none => s.recordEnemyChoice notes p id
  | .chosenByAbility p id => s.recordEnemyChoice notes p id
  | .died id p =>
    if (s.cardDef? id).any (fun d => d.hasType .unit || d.hasType .gear) then
      let known := s.recordTurnFact notes p .permanentDied none s.nextTimestamp
      match (s.obj? id).filter (·.kind.phys?.isSome), ((s.deathSubject id).cardDef? id).any (·.hasType .unit) with
      | some dead, true =>
        dead.loc.elim known (fun field =>
          s.recordTurnFact known p .firstUnitDeathHere (some field) dead.timestamp.n)
      | _, _ => known
    else notes
  | .linkedDamageCleanupDone => notes.filter (fun f => match f.kind with
      | .linkedDamageDeath .. => false
      | _ => true)
  | _ => notes

/-- Update the play and choice history before evaluating triggers. Ignore events during setup. -/
def GameState.recordTurnEvents (s : GameState) (es : List Event) : GameState :=
  let inPlay := s.phase != .setup && s.pending.all (fun f => !f.isSetup)
  { s with
    playLog := if inPlay then es.foldl s.recordPlayEvent s.playLog else s.playLog
    turnFx := if inPlay then es.foldl s.recordTurnEvent s.turnFx else s.turnFx }

mutual

/-- Resource-only effects the engine can resolve without a further player decision. -/
def Effect.isTriggerAdd : Effect → Bool
  | .prim (.addEnergy .you _ none) | .prim (.addUnitEnergy .you _) | .prim (.addSpellEnergy .you _)
  | .prim (.addPower .you _ _ none) => true
  | .seq (.cons first more) => first.isTriggerAdd && more.areTriggerAdds
  | .ifThen _ body .nop => body.isTriggerAdd
  | _ => false

/-- The remaining effects in a sequence that adds resources. -/
def EffectList.areTriggerAdds : EffectList → Bool
  | .nil => true
  | .cons first more => first.isTriggerAdd && more.areTriggerAdds

end

/-- Finalize a mandatory, free Add without waiting for priority (CR 430.2). -/
def PendTrigger.immediateAddFrame (s : GameState) (t : PendTrigger) : Option Frame :=
  match triggerAbility s t with
  | some (.triggered rule effect _) =>
    if !rule.optional && rule.cost == .free && effect.choices.isEmpty && effect.modes.isEmpty &&
        effect.moveChoice.isNone && effect.playerTarget.isNone && effect.body.isTriggerAdd then
      let env : Env := {
        slots := t.subject.toList.map Value.obj
        sourceCard := some t.card
        abilityCopyStamp := t.copyStamp
        eventAmount := t.eventAmount
        eventBattlefields := t.eventBattlefields
        shownOff := t.shownOff }
      some (.run t.controller t.source env (.cons (.markTriggeredAdd t.idx) (.cons effect.body .nil)))
    else none
  | _ => none

/-- A triggered Add runs before remaining tasks. The other triggers wait for priority (CR 383.1). -/
def insertDetectedTriggers (s : GameState) (pend : List PendTrigger) (pending : List Frame) :
    List Frame :=
  let arrivals := pend.map (fun t => (t, t.immediateAddFrame s))
  let ordinary := arrivals.filterMap (fun (t, add) => if add.isNone then some t else none)
  arrivals.filterMap Prod.snd ++
    (if ordinary.isEmpty then pending else insertTriggers ordinary pending)

/-- A triggered Add contributes only a Run frame. -/
theorem PendTrigger.immediateAddFrame_run {s : GameState} {t : PendTrigger} {f : Frame}
    (h : t.immediateAddFrame s = some f) :
    ∃ p src env es, f = .run p src env es := by
  unfold PendTrigger.immediateAddFrame at h
  split at h
  · dsimp only at h
    split at h
    · obtain rfl := Option.some.inj h.symm
      exact ⟨_, _, _, _, rfl⟩
    · simp at h
  · simp at h

/-- Detected abilities add only Run and trigger frames to the current stack. -/
theorem insertDetectedTriggers_mem {s : GameState} {pend : List PendTrigger}
    {pending : List Frame} {f : Frame} (h : f ∈ insertDetectedTriggers s pend pending) :
    f ∈ pending ∨ (∃ ts, f = .triggers ts) ∨ ∃ p src env es, f = .run p src env es := by
  unfold insertDetectedTriggers at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨⟨t, add⟩, ha, hf⟩ := List.mem_filterMap.mp h
    obtain ⟨event, _, eq⟩ := List.mem_map.mp ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact Or.inr (Or.inr (PendTrigger.immediateAddFrame_run hf))
  · split at h
    · exact Or.inl h
    · rcases insertTriggers_mem _ _ h with old | trigger
      · exact Or.inl old
      · exact Or.inr (Or.inl trigger)

/-- Detected abilities preserve a bottom frame that is outside resolution. -/
theorem insertDetectedTriggers_getLast (s : GameState) (pend : List PendTrigger)
    (pending : List Frame) {g : Frame} (hg : pending.getLast? = some g)
    (hr : g.isResolution = false) (ht : ∀ ts, g ≠ .triggers ts) :
    (insertDetectedTriggers s pend pending).getLast? = some g := by
  unfold insertDetectedTriggers
  dsimp only
  rw [List.getLast?_append]
  split
  · simp [hg]
  · simp [insertTriggers_getLast _ _ hg hr ht]

/-- During sudden death, the first actual point ends the game (TR 408.4.c.3). -/
def GameState.suddenDeathScorer (s : GameState) (es : List Event) : Option PlayerId := do
  let clock ← s.clock
  if s.phase != .setup && s.result.isNone && clock.allowsSuddenDeath &&
      decide (clock.lastTurn < s.turn) then
    es.findSome? (fun
      | .pointsGained p (_ + 1) => some p
      | _ => none)
  else none

/-- A card can award a win independently of the scoreboard (CR 002). -/
def GameState.eventWinner (s : GameState) (es : List Event) : Option PlayerId :=
  s.suddenDeathScorer es <|>
    if s.phase == .setup || s.result.isSome then none
    else es.findSome? (fun | .won p => some p | _ => none)

/-- Events unrelated to a card-awarded win still use the ordinary sudden-death rule. -/
theorem eventWinner_of_noWin (s : GameState) (es : List Event)
    (h : es.findSome? (fun | .won p => some p | _ => none) = none) :
    s.eventWinner es = s.suddenDeathScorer es := by
  simp [GameState.eventWinner, h]

/-- After a step, finish a won game or queue the abilities that fired outside setup. -/
def GameState.withTriggers (s : GameState) (es : List Event) : GameState :=
  let next := s.recordTurnEvents es
  match s.eventWinner es with
  | some p => { next with result := some (.won (s.config.mode.sideSeats p)), pending := [] }
  | none =>
    if s.phase != .setup && s.pending.all (fun f => !f.isSetup) then
      match next.detect es (next.firstCardTriggers s ++ s.delayedPlayTriggers es) (some s.turnFx) with
      | [] => next
      | pend => { next with pending := insertDetectedTriggers next pend s.pending }
    else next

/-- A card-awarded win clears the remaining work and does not change the score. -/
theorem withTriggers_win (s : GameState) (p : PlayerId) (ongoing : s.result = none)
    (playing : s.phase ≠ .setup) :
    s.withTriggers [.won p] = { s with result := some (.won (s.config.mode.sideSeats p)), pending := [] } := by
  have noPoint : s.suddenDeathScorer [.won p] = none := by
    cases hc : s.clock <;> simp [GameState.suddenDeathScorer, hc]
  simp [GameState.withTriggers, GameState.eventWinner, noPoint, ongoing, playing,
    GameState.recordTurnEvents, GameState.recordTurnEvent, GameState.recordPlayEvent]

/-- Whether the source already chose this mode of the triggered ability in the current turn. -/
def PendTrigger.choseMode (t : PendTrigger) (s : GameState) (mode : Nat) : Bool :=
  s.turnFx.any (fun fx => fx.turn == s.turn && fx.target == some t.source &&
    fx.kind == .chosenTriggerMode t.card t.idx mode t.copyStamp)

/-- The modes on the ability that waits, or no mode for an ability without alternatives. -/
def trigModes (s : GameState) (t : PendTrigger) : List (Option Nat) :=
  match triggerAbility s t with
  | some (.triggered rule body _) =>
    if body.modes.isEmpty then [none] else
      ((List.range body.modes.length).filter
        (fun mode => !rule.separateModesPerTurn || !t.choseMode s mode)).map some
  | _ => [none]

/-- The choices for the selected branch of the triggered ability (CR 355). -/
def trigChoices (s : GameState) (t : PendTrigger) (mode : Option Nat := none) : List Choice :=
  let effect := (triggerAbility s t).bind Ability.effectDef
  let choices := ((effect.bind (·.forPick (mode.elim .plain SpellPick.mode))).map (·.choices)).getD []
  choices.map (Choice.withTriggerEvent t.eventBattlefields t.eventObjects)

/-- The trigger declaration on the queued ability, even if its source left the Board. -/
def trigDeclaration (s : GameState) (t : PendTrigger) : Option Trigger :=
  match triggerAbility s t with
  | some (.triggered rule _ _) => some rule
  | _ => none

/-- Whether the player may decline during finalization (CR 383.3.a). -/
def trigOptional (s : GameState) (t : PendTrigger) : Bool :=
  (trigDeclaration s t).any (·.optional)

/-- The cost due before the trigger can go on the Chain. -/
def trigCost (s : GameState) (t : PendTrigger) : TriggerCost :=
  ((trigDeclaration s t).map (·.cost)).getD .free

/-- The Energy and Power required by the trigger's printed cost. -/
def TriggerCost.resources : TriggerCost → Cost
  | .energy n => ⟨n, []⟩
  | .pay cost _ | .payAndReturnUnitHere cost => cost
  | _ => ⟨0, []⟩

/-- A Burn cost must be payable in full. Burn Out on a short deck is for instructions
in effects (CR 383.3.b.1, 441.4). -/
def canPayBurn (s : GameState) (p : PlayerId) (count : Nat) : Bool :=
  count ≤ (s.zone (.player p .mainDeck)).length

/-- The original source is still on the board and can be exhausted (CR 415.4). -/
def canExhaustTriggerSource (s : GameState) (t : PendTrigger) : Bool :=
  (s.locate t.source).any Zone.isBoard && (s.obj? t.source).any (fun o => !o.exhausted)

/-- Choose exactly the printed number of discards from the controller's hand. -/
def triggerDiscardOptions (s : GameState) (p : PlayerId) (count : Nat) : List (List ObjId) :=
  (subseqsUpTo count (s.zone (.player p .hand)).eraseDups).filter (·.length == count)

/-- Units whose buff the controller can spend as the trigger's base cost (CR 702.2.b). -/
def triggerBuffOptions (s : GameState) (t : PendTrigger) : List ObjId :=
  (s.pickCandidates t.controller t.source {} .you .anywhere
    (.ofList [.ofType .unit, .buffed]) false).getD []

/-- Units the trigger's controller can return here as a cost. Costs do not choose targets. -/
def triggerReturnUnitHereOptions (s : GameState) (t : PendTrigger) : List ObjId :=
  (s.pickCandidates t.controller t.source {} .you .here (.ofList [.ofType .unit])
    false).getD []

/-- Distinct sets of permanents the given side can select for a Kill cost. -/
def triggerKillOptions (s : GameState) (t : PendTrigger) (n : Nat)
    (side : Side) (fs : FilterList) : List (List ObjId) :=
  let env : Env := { passMight := s.mightTable }
  let candidates := (s.pickCandidates t.controller t.source env side .anywhere fs false).getD []
  (subseqsUpTo n candidates.eraseDups).filter (·.length == n)

/-- The ways to pay the cost of a trigger. Killed objects are selected as costs (CR 355.10.c). -/
def trigPayments (s : GameState) (t : PendTrigger) (checkPool : Bool := true) : List (List ObjId) :=
  match trigCost s t with
  | .free => [[]]
  | .energy n =>
    if !checkPool || (payByRunes s t.controller t.source ⟨n, []⟩).isSome then [[]] else []
  | .spendXP n => if n ≤ s.xpOf t.controller then [[]] else []
  | .pay cost exhaustSelf =>
    if (!exhaustSelf || canExhaustTriggerSource s t) &&
        (!checkPool || (payByRunes s t.controller t.source cost).isSome) then [[]] else []
  | .payAndReturnUnitHere cost =>
    if !checkPool || (payByRunes s t.controller t.source cost).isSome then
      (triggerReturnUnitHereOptions s t).map (fun id => [id])
    else []
  | .exhaustSelf => if canExhaustTriggerSource s t then [[]] else []
  | .burn n => if canPayBurn s t.controller n then [[]] else []
  | .discard n => triggerDiscardOptions s t.controller n
  | .discardAndExhaust n =>
    if canExhaustTriggerSource s t then triggerDiscardOptions s t.controller n else []
  | .spendBuff => (triggerBuffOptions s t).map (fun id => [id])
  | .killFriendly n fs => triggerKillOptions s t n .friendly fs
  | .killControlled n fs => triggerKillOptions s t n .you fs

/-- The affected Units each choose how to replace their Kill. Compute the combinations against
the same board, before paying any part of the simultaneous cost (CR 372, 373). -/
def triggerBanisherOptions (s : GameState) : List ObjId → List (List (ObjId × PlayerId))
  | [] => [[]]
  | id :: rest =>
    let remaining := triggerBanisherOptions s rest
    (s.deathBanisherOptions id).flatMap (fun banisher =>
      match banisher with
      | none => remaining
      | some p => remaining.map ((id, p) :: ·))

/-- The cards paying the trigger's cost and the Banish choices associated with that payment. -/
def triggerCostOptions (s : GameState) (t : PendTrigger) (checkPool : Bool := true) :
    List (List ObjId × List (ObjId × PlayerId)) :=
  let payments := trigPayments s t checkPool
  match trigCost s t with
  | .killFriendly .. | .killControlled .. =>
    payments.flatMap (fun ids => (triggerBanisherOptions s ids).map (ids, ·))
  | _ => payments.map (·, [])

/-- A direct trigger payment must leave enough Power for Deflect (CR 356, 809). -/
def trigTargetAffordable (s : GameState) (t : PendTrigger) (ts : List ObjId) : Bool :=
  let surcharge := s.deflectCost t.controller ts
  if surcharge == 0 then true else
    let cost := (trigCost s t).resources
    if cost == Cost.zero then decide (surcharge ≤ (s.poolOf t.controller).totalPower)
    else (payByRunes s t.controller t.source cost).any
      (fun r => decide (surcharge ≤ (r.1.poolOf t.controller).totalPower))

/-- Every legal pick for the mode that the Pool of the controller can pay for (CR 355, 809). -/
def trigTuples (s : GameState) (t : PendTrigger) (mode : Option Nat) (checkPool : Bool := true) :
    List (List ObjId) :=
  (targetTuples s t.controller t.source s.mightTable (trigChoices s t mode)).filter
    (fun ts => !checkPool || trigTargetAffordable s t ts)

/-- The mode and target combinations that can be finalized. -/
def trigTargetOptions (s : GameState) (t : PendTrigger) (checkPool : Bool := true) :
    List (Option Nat × List ObjId) :=
  (trigModes s t).flatMap (fun mode => (trigTuples s t mode checkPool).map (mode, ·))

/-- Whether the mode is available and the targets are legal for that mode (CR 355.3, 355.5). -/
def trigTargetOk (s : GameState) (t : PendTrigger) (mode : Option Nat) (ts : List ObjId) : Bool :=
  (trigModes s t).contains mode &&
    targetsOk s t.controller t.source s.mightTable (trigChoices s t mode) ts &&
    trigTargetAffordable s t ts

/-- A listed mode and its targets satisfy the finalization rules. -/
theorem mem_trigTargetOptions (s : GameState) (t : PendTrigger) (mode : Option Nat)
    (ts : List ObjId) : (mode, ts) ∈ trigTargetOptions s t ↔ trigTargetOk s t mode ts = true := by
  simp only [trigTargetOptions, trigTuples, trigTargetOk, List.mem_flatMap, List.mem_map,
    List.mem_filter, mem_targetTuples, Prod.mk.injEq, Bool.and_eq_true, List.contains_iff_mem,
    Bool.not_true, Bool.false_or]
  constructor
  · rintro ⟨_, hm, _, ⟨ht, hd⟩, rfl, rfl⟩
    exact ⟨⟨hm, ht⟩, hd⟩
  · rintro ⟨⟨hm, ht⟩, hd⟩
    exact ⟨mode, hm, ts, ⟨ht, hd⟩, rfl, rfl⟩

/-- The eligible player targets of the ability, or no player choice when it does not
declare one (CR 355.7, 355.9). -/
def trigPlayerOptions (s : GameState) (t : PendTrigger) : List (Option PlayerId) :=
  s.playerTargetOptions t.controller ((abilityDef s t.card t.idx).bind EffectDef.playerTarget)

/-- A complete set of targets and mode before costs are paid. -/
def trigPickOptions (s : GameState) (t : PendTrigger) (checkPool : Bool := true) :
    List (Option Nat × List ObjId × Option PlayerId) :=
  let players := trigPlayerOptions s t
  (trigTargetOptions s t checkPool).flatMap (fun (mode, ts) => players.map (mode, ts, ·))

/-- A listed pick meets both the object and player restrictions. -/
theorem mem_trigPickOptions (s : GameState) (t : PendTrigger) (mode : Option Nat)
    (ts : List ObjId) (player : Option PlayerId) :
    (mode, ts, player) ∈ trigPickOptions s t ↔
      trigTargetOk s t mode ts = true ∧ player ∈ trigPlayerOptions s t := by
  simp only [trigPickOptions, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨_, _⟩, ht, _, hp, rfl, rfl, rfl⟩
    exact ⟨(mem_trigTargetOptions s t _ _).mp ht, hp⟩
  · rintro ⟨ht, hp⟩
    exact ⟨(mode, ts), (mem_trigTargetOptions s t mode ts).mpr ht, player, hp, rfl, rfl, rfl⟩

/-- No combination of targets and costs permits finalization. -/
def noTriggerPick (s : GameState) (t : PendTrigger) : Bool :=
  (trigPickOptions s t).isEmpty || (triggerCostOptions s t).isEmpty

/-- Combine the available modes and targets with each way to pay the cost. -/
def acceptedTriggers (s : GameState) (t : PendTrigger) (checkPool : Bool := true) :
    List (List ObjId × TriggerPayment) :=
  let payments := triggerCostOptions s t checkPool
  (trigPickOptions s t checkPool).flatMap (fun (mode, ts, player) =>
    payments.map (fun (ids, banishers) => (ts, .pay ids mode player banishers)))

/-- The legal ways to finalize or pass over the ability (CR 355, 383.3, 809). -/
def trigOptions (s : GameState) (t : PendTrigger) : List (List ObjId × TriggerPayment) :=
  let accepted := acceptedTriggers s t
  if trigOptional s t then accepted ++ [([], .skip)]
  else if noTriggerPick s t then [([], .pay [])]
  else accepted

/-- A legal trigger answer provides a mode, targets and costs, or dismisses the ability (CR 383.3). -/
def trigLegal (s : GameState) (t : PendTrigger) (ts : List ObjId) : TriggerPayment → Bool
  | .skip => ts.isEmpty && trigOptional s t
  | .pay ids mode player banishers =>
    ((trigTargetOk s t mode ts && (trigPlayerOptions s t).contains player) &&
      (triggerCostOptions s t).contains (ids, banishers)) ||
    (!trigOptional s t && ts.isEmpty && ids.isEmpty && mode.isNone && player.isNone &&
      banishers.isEmpty && noTriggerPick s t)

/-- The picks listed are exactly the legal ones. -/
theorem mem_trigOptions (s : GameState) (t : PendTrigger) (ts : List ObjId)
    (payment : TriggerPayment) :
    (ts, payment) ∈ trigOptions s t ↔ trigLegal s t ts payment = true := by
  cases payment with
  | skip =>
    by_cases ho : trigOptional s t <;>
      simp [trigOptions, trigLegal, ho, acceptedTriggers, List.mem_flatMap, List.mem_map, List.isEmpty_iff]
    split <;> simp [List.mem_flatMap, List.mem_map]
  | pay ids mode player banishers =>
    have accepts :
        (ts, TriggerPayment.pay ids mode player banishers) ∈ acceptedTriggers s t ↔
        (mode, ts, player) ∈ trigPickOptions s t ∧ (ids, banishers) ∈ triggerCostOptions s t := by
      simp only [acceptedTriggers, List.mem_flatMap, List.mem_map, Prod.mk.injEq,
        TriggerPayment.pay.injEq]
      constructor
      · rintro ⟨⟨_, _, _⟩, ht, ⟨_, _⟩, hi, rfl, rfl, rfl, rfl, rfl⟩
        exact ⟨ht, hi⟩
      · rintro ⟨ht, hi⟩
        exact ⟨(mode, ts, player), ht, (ids, banishers), hi, rfl, rfl, rfl, rfl, rfl⟩
    by_cases ho : trigOptional s t
    · simp [trigOptions, trigLegal, ho, accepts, mem_trigPickOptions]
    · by_cases hn : noTriggerPick s t
      · have missing : ¬((mode, ts, player) ∈ trigPickOptions s t ∧
            (ids, banishers) ∈ triggerCostOptions s t) := by
          simp only [noTriggerPick, Bool.or_eq_true, List.isEmpty_iff] at hn
          rcases hn with h | h <;> simp [h]
        have invalid : ¬(trigTargetOk s t mode ts = true ∧
            player ∈ trigPlayerOptions s t ∧ (ids, banishers) ∈ triggerCostOptions s t) := by
          simpa only [mem_trigPickOptions, and_assoc] using missing
        simp [trigOptions, trigLegal, ho, hn, invalid, List.isEmpty_iff, and_assoc]
      · simp [trigOptions, trigLegal, ho, hn, accepts, mem_trigPickOptions]

/-- An ability that waits has a legal pick. -/
theorem trigLegal_exists (s : GameState) (t : PendTrigger) :
    ∃ ts payment, trigLegal s t ts payment = true := by
  by_cases ho : trigOptional s t
  · exact ⟨[], .skip, by simp [trigLegal, ho]⟩
  · by_cases hn : noTriggerPick s t
    · exact ⟨[], .pay [], by simp [trigLegal, ho, hn]⟩
    · have ht : trigPickOptions s t ≠ [] := by
        intro ht
        exact hn (by simp [noTriggerPick, ht])
      have hp : triggerCostOptions s t ≠ [] := by
        intro hp
        exact hn (by simp [noTriggerPick, hp])
      obtain ⟨⟨mode, ts, player⟩, hts⟩ := List.exists_mem_of_ne_nil _ ht
      obtain ⟨⟨ids, banishers⟩, hids⟩ := List.exists_mem_of_ne_nil _ hp
      obtain ⟨hm, hplayer⟩ := (mem_trigPickOptions s t mode ts player).mp hts
      exact ⟨ts, .pay ids mode player banishers, by simp [trigLegal, hm, hplayer, hids]⟩

/-- Record the chosen mode when the ability says each mode can be chosen only once this turn. -/
def recordTriggerMode (s : GameState) (t : PendTrigger) (mode : Option Nat) : GameState :=
  if (trigDeclaration s t).any (·.separateModesPerTurn) then
    mode.elim s (fun i => s.addTurnFxOn t.controller t.source (.chosenTriggerMode t.card t.idx i t.copyStamp))
  else s

/-- Recording the finalization decision preserves the structural invariants. -/
theorem recordTriggerMode_safe (s : GameState) (t : PendTrigger) (mode : Option Nat) :
    Safe s (recordTriggerMode s t mode) := by
  unfold recordTriggerMode
  split
  · cases mode
    · exact Safe.refl s
    · exact addTurnFxOn_safe _ _ _ _
  · exact Safe.refl s

/-- Finalizing the Legend's target ends its previous animation immediately (CR 355.5). -/
def prepareGearAnimation (s : GameState) (t : PendTrigger) (targets : List ObjId)
    (mode : Option Nat) : GameState :=
  match targets, (triggerAbility s t).bind Ability.effectDef |>.bind
      (·.forPick (mode.elim .plain SpellPick.mode)) with
  | [chosen], some { body := .animateGear, .. } => endGearAnimation s t.source chosen
  | _, _ => s

/-- Preparing the new target changes only the old animation traits. -/
theorem prepareGearAnimation_safe (s : GameState) (t : PendTrigger) (targets : List ObjId)
    (mode : Option Nat) : Safe s (prepareGearAnimation s t targets mode) := by
  unfold prepareGearAnimation
  split
  · exact endGearAnimation_safe _ _ _
  · exact Safe.refl _

/-- Store a location restriction that will be checked against each selected target on resolution. -/
def recordTriggerLocations (s : GameState) (t : PendTrigger) (item : ObjId)
    (targets : List ObjId) (mode : Option Nat) : GameState :=
  if !targets.isEmpty && (trigChoices s t mode).any Choice.recordsLocations then
    let locations := targets.filterMap (fun id => (s.boardLocationOf id).map (id, ·))
    s.addTurnFxOn t.controller item (.declaredTargetLocations locations)
  else s

theorem recordTriggerLocations_safe (s : GameState) (t : PendTrigger) (item : ObjId)
    (targets : List ObjId) (mode : Option Nat) : Safe s (recordTriggerLocations s t item targets mode) := by
  unfold recordTriggerLocations
  split
  · exact addTurnFxOn_safe _ _ _ _
  · exact Safe.refl s

/-- The Chain gets the ability: it is used (CR 371), and it goes on top as an object of its own,
controlled by the player, with the objects chosen. -/
def putTrigger (s : GameState) (t : PendTrigger) (ts : List ObjId) (mode : Option Nat := none)
    (player : Option PlayerId := none) : GameState :=
  let used := (recordTriggerMode s t mode).modObj t.source
    (fun o => (o.noteAbilityUse t.idx t.copyStamp).noteChose s.turn ts)
  let item : Object :=
    { abilityItem t.card t.idx t.source t.controller
        (if mode.isNone then ts ++ t.subject.toList else ts) t.eventAmount with
      spellPick := mode.elim .plain SpellPick.mode
      triggerSubject := t.subject
      triggerKeyword := t.triggerKeyword
      eventBattlefields := t.eventBattlefields
      eventObjects := t.eventObjects
      shownOff := t.shownOff
      abilityCopyStamp := t.copyStamp
      targetPlayer := player }
  let s1 := prepareGearAnimation used t ts mode
  match addObject s1 item .chain with
  | some r => recordTriggerLocations r.1 t r.2 ts mode
  | none => s1

/-- Record the replacement selected for each object in the same cost. -/
def noteTriggerBanishers (s : GameState) : List (ObjId × PlayerId) → GameState
  | [] => s
  | (id, p) :: rest => noteTriggerBanishers (s.addTurnFxOn p id .chosenDeathBanisher) rest

/-- The chosen replacements preserve the game invariants. -/
theorem noteTriggerBanishers_safe (s : GameState) (banishers : List (ObjId × PlayerId)) :
    Safe s (noteTriggerBanishers s banishers) := by
  induction banishers generalizing s with
  | nil => exact Safe.refl s
  | cons pick rest ih =>
    exact (addTurnFxOn_safe s pick.2 pick.1 .chosenDeathBanisher).trans (ih _)

/-- Discard the selected hand cards only when the complete cost is legal. -/
def payTriggerDiscards (s : GameState) (p : PlayerId) (ids : List ObjId) (n : Nat) :
    Option (GameState × List Event) :=
  if ids.length == n && ids.eraseDups.length == n && ids.all ((s.zone (.player p .hand)).contains) then
    some (payDiscards p s ids)
  else none

/-- Discarding cards to finalize a trigger preserves the invariants. -/
theorem payTriggerDiscards_safe {s : GameState} {p : PlayerId} {ids : List ObjId} {n : Nat}
    {r : GameState × List Event} (h : payTriggerDiscards s p ids n = some r) : Safe s r.1 := by
  unfold payTriggerDiscards at h
  split at h
  · cases h; exact payDiscards_safe _ _ _
  · contradiction

/-- Pay a trigger's cost without giving either player a chance to respond (CR 383.3.b.1). -/
def payTriggerCost (s : GameState) (t : PendTrigger) (ids : List ObjId)
    (banishers : List (ObjId × PlayerId) := []) (resourcesPaid : Bool := false) :
    Option (GameState × List Event) :=
  match trigCost s t with
  | .free => some (s, [])
  | .energy n => if resourcesPaid then some (s, []) else
      payByRunes s t.controller t.source ⟨n, []⟩
  | .spendXP n => if n ≤ s.xpOf t.controller then some (s.spendXP t.controller n, []) else none
  | .pay cost exhaustSelf => do
    let payment := if resourcesPaid then some (s, []) else payByRunes s t.controller t.source cost
    let (paid, events) ← payment
    if !exhaustSelf then some (paid, events)
    else if canExhaustTriggerSource paid t then
      let (exhausted, costEvents) := setExhausted true paid t.source
      some (exhausted, events ++ costEvents)
    else none
  | .payAndReturnUnitHere cost =>
    match ids with
    | [id] =>
      if (triggerReturnUnitHereOptions s t).contains id then
        let payment := if resourcesPaid then some (s, []) else payByRunes s t.controller t.source cost
        payment.map fun (paid, events) =>
          let (returned, moves) := sendObj .hand paid id
          (returned, events ++ moves)
      else none
    | _ => none
  | .exhaustSelf =>
    if canExhaustTriggerSource s t then some (setExhausted true s t.source) else none
  | .burn n => if canPayBurn s t.controller n then some (burnTop s t.controller n) else none
  | .killFriendly n _ | .killControlled n _ =>
    if ids.length == n then
      some (resolveDeathGroupWith (noteTriggerBanishers s banishers) ids (killOrSaveInGroup s))
    else none
  | .discard n => payTriggerDiscards s t.controller ids n
  | .discardAndExhaust n =>
    if canExhaustTriggerSource s t then do
      let (discarded, discards) ← payTriggerDiscards s t.controller ids n
      let (exhausted, exhausts) := setExhausted true discarded t.source
      some (exhausted, discards ++ exhausts)
    else none
  | .spendBuff =>
    match ids with
    | [id] => if (triggerBuffOptions s t).contains id then some (unbuffObj s id) else none
    | _ => none

/-- Dismiss a declined or unpayable trigger, or pay for it and finalize it (CR 355, 383.3). -/
def finalizePick (s : GameState) (grp : List PendTrigger) (i : Nat) (ts : List ObjId)
    (payment : TriggerPayment) : GameState × List Event :=
  match grp[i]?, payment with
  | some t, .pay ids mode player banishers =>
    if !(trigModes s t).contains mode || !(trigPlayerOptions s t).contains player ||
        (ts.isEmpty && !(trigChoices s t mode).isEmpty && !trigTargetOk s t mode []) then (s, [])
    else match payTriggerCost s t ids banishers with
      | some (paid, events) => (putTrigger paid t ts mode player, events)
      | none => (s, [])
  | _, _ => (s, [])

/-- The frames to put beneath the work after the abilities go on the Chain. When opening a
Chain, its top item's controller gets priority (CR 337.4). -/
def triggerFrames (s : GameState) (rest : List Frame) : List Frame :=
  match rest with
  | .chainPass .. :: _ => []
  | _ => if (s.zone .chain).isEmpty then [] else [.chainPass s.chainPrioritySeat 0]

/-- The frames put under the work after the triggers are Chain priorities. -/
theorem triggerFrames_mem {s : GameState} {rest : List Frame} {f : Frame}
    (h : f ∈ triggerFrames s rest) : ∃ p n, f = .chainPass p n := by
  unfold triggerFrames at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [List.mem_singleton] at h
      exact ⟨_, _, h⟩

/-- One step of a `triggers` frame: with nothing left, the turn player gets priority; with one
ability and nothing to choose, it goes on the Chain; otherwise its player chooses (CR 383.3.d). The
state, and the frames to put above the rest of the stack. -/
def triggersStep (s : GameState) (pend : List PendTrigger) (rest : List Frame) :
    GameState × List Frame :=
  match pend with
  | [] => (s, triggerFrames s rest)
  | t :: ts =>
    let sameGroup (u : PendTrigger) :=
      u.controller == t.controller && u.beforeStandardMove == t.beforeStandardMove
    let grp := ts.filter sameGroup
    let others := ts.filter (fun u => !sameGroup u)
    if grp.isEmpty && trigModes s t == [none] && trigPlayerOptions s t == [none] &&
        (trigChoices s t).isEmpty && !trigOptional s t && trigCost s t == .free then
      (putTrigger s t [], [.triggers others])
    else (s, [.triggerOrder t.controller t grp others])

/-- Putting one ability on the Chain is a safe change. -/
theorem putTrigger_safe (s : GameState) (t : PendTrigger) (ts : List ObjId)
    (mode : Option Nat := none) (player : Option PlayerId := none) :
    Safe s (putTrigger s t ts mode player) := by
  have h1 : Safe s ((recordTriggerMode s t mode).modObj t.source
      (fun o => (o.noteAbilityUse t.idx t.copyStamp).noteChose s.turn ts)) :=
    (recordTriggerMode_safe s t mode).trans (Safe.modObj _ t.source (fun _ => rfl) (fun _ => rfl))
  have done := h1.trans (prepareGearAnimation_safe _ t ts mode)
  unfold putTrigger
  dsimp only
  split
  · rename_i r hr
    exact (done.trans ⟨fun hwf => addObject_wf hwf hr, fun hwf => addObject_physIds hwf hr rfl,
      fun hwf hown => addObject_ownerOk hwf hown hr, addObject_sameMeta hr⟩).trans
      (recordTriggerLocations_safe _ _ _ _ _)
  · exact done

/-- Paying for a trigger preserves structural invariants. -/
theorem payTriggerCost_safe {s : GameState} {t : PendTrigger} {ids : List ObjId}
    {banishers : List (ObjId × PlayerId)} {resourcesPaid : Bool} {r : GameState × List Event}
    (h : payTriggerCost s t ids banishers resourcesPaid = some r) : Safe s r.1 := by
  unfold payTriggerCost at h
  split at h
  · cases h; exact Safe.refl s
  · split at h
    · cases h; exact Safe.refl s
    · exact payByRunes_safe h
  · rename_i xp _
    split at h
    · cases h; exact Safe.spendXP s t.controller xp
    · simp at h
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨paid, events⟩, hpay, hfinish⟩ := h
    have hsafe : Safe s paid := by
      split at hpay
      · cases hpay; exact Safe.refl s
      · exact payByRunes_safe hpay
    split at hfinish
    · cases hfinish; exact hsafe
    · split at hfinish
      · cases hfinish; exact hsafe.trans (setExhausted_safe true paid t.source)
      · simp at hfinish
  · split at h
    · split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨paid, events⟩, hpay, hfinish⟩ := h
        have hsafe : Safe s paid := by
          split at hpay
          · cases hpay; exact Safe.refl s
          · exact payByRunes_safe hpay
        cases hfinish
        exact hsafe.trans (sendObj_safe .hand paid _)
      · contradiction
    · contradiction
  · split at h
    · cases h; exact setExhausted_safe true s t.source
    · simp at h
  · split at h
    · cases h; exact applyEach_safe (sendObj_safe .trash) _ _
    · simp at h
  · split at h
    · cases h
      exact (noteTriggerBanishers_safe s banishers).trans
        (resolveDeathGroupWith_safe _ ids (killOrSaveInGroup_safe s))
    · simp at h
  · split at h
    · cases h
      exact (noteTriggerBanishers_safe s banishers).trans
        (resolveDeathGroupWith_safe _ ids (killOrSaveInGroup_safe s))
    · simp at h
  · exact payTriggerDiscards_safe h
  · split at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨discarded, _⟩, hp, hresult⟩ := h
      cases hresult
      exact (payTriggerDiscards_safe hp).trans (setExhausted_safe true discarded t.source)
    · contradiction
  · split at h
    · split at h
      · cases h; exact unbuffObj_safe _ _
      · contradiction
    · contradiction

/-- Putting the picked ability on the Chain is a safe change. -/
theorem finalizePick_safe (s : GameState) (grp : List PendTrigger) (i : Nat) (ts : List ObjId)
    (payment : TriggerPayment) : Safe s (finalizePick s grp i ts payment).1 := by
  unfold finalizePick
  split
  · split
    · exact Safe.refl s
    · split
      · rename_i paid events h
        exact (payTriggerCost_safe h).trans (putTrigger_safe paid _ ts _ _)
      · exact Safe.refl s
  · exact Safe.refl s

/-- A step of a `triggers` frame is a safe change, and the frames it puts are priorities, `triggers`
frames and choices of triggers. -/
theorem triggersStep_spec (s : GameState) (pend : List PendTrigger) (rest : List Frame) :
    Safe s (triggersStep s pend rest).1 ∧ ∀ g ∈ (triggersStep s pend rest).2,
      (∃ p n, g = .chainPass p n) ∨ (∃ x, g = .triggers x) ∨
        (∃ p t m o, g = .triggerOrder p t m o) := by
  unfold triggersStep
  split
  · refine ⟨Safe.refl s, fun g hg => ?_⟩
    obtain ⟨p, n, h⟩ := triggerFrames_mem hg
    exact Or.inl ⟨p, n, h⟩
  · dsimp only
    split
    · refine ⟨putTrigger_safe s _ [], fun g hg => ?_⟩
      simp only [List.mem_singleton] at hg
      exact Or.inr (Or.inl ⟨_, hg⟩)
    · refine ⟨Safe.refl s, fun g hg => ?_⟩
      simp only [List.mem_singleton] at hg
      exact Or.inr (Or.inr ⟨_, _, _, _, hg⟩)

/-- After recording plays, triggers are inserted only outside the setup. -/
theorem withTriggers_cases (s : GameState) (es : List Event) :
    (∃ p, s.withTriggers es = { s.recordTurnEvents es with
        result := some (.won (s.config.mode.sideSeats p)), pending := [] } ∧ s.phase ≠ .setup) ∨
    s.withTriggers es = s.recordTurnEvents es ∨ ∃ pend, s.withTriggers es = { s.recordTurnEvents es with
        pending := insertDetectedTriggers (s.recordTurnEvents es) pend s.pending } ∧ s.phase ≠ .setup ∧
      ∀ f ∈ s.pending, f.isSetup = false := by
  unfold GameState.withTriggers
  cases hs : s.eventWinner es with
  | some p =>
    refine Or.inl ⟨p, rfl, fun hp => ?_⟩
    cases hc : s.clock <;> simp [GameState.eventWinner, GameState.suddenDeathScorer, hc, hp] at hs
  | none =>
    right
    by_cases hg : (s.phase != .setup && s.pending.all (fun f => !f.isSetup)) = true
    · cases hd : (s.recordTurnEvents es).detect es
        ((s.recordTurnEvents es).firstCardTriggers s ++ s.delayedPlayTriggers es) (some s.turnFx) with
      | nil => simp [hg, hd]
      | cons x xs =>
        right
        refine ⟨x :: xs, by simp [hg, hd], ?_, ?_⟩
        · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg
          exact hg.1
        · simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
          exact hg.2
    · simp [hg]

/-- Besides recording plays, `withTriggers` changes only the stack and result. -/
theorem withTriggers_pending (s : GameState) (es : List Event) :
    ∃ p result, s.withTriggers es = { s.recordTurnEvents es with pending := p, result } := by
  rcases withTriggers_cases s es with ⟨p, h, -⟩ | h | ⟨pend, h, -⟩
  · exact ⟨[], _, h⟩
  · exact ⟨s.pending, s.result, by rw [h]; rfl⟩
  · exact ⟨_, s.result, h⟩

/-- Finding the triggers keeps the game well formed. -/
theorem withTriggers_wf {s : GameState} (es : List Event) (hwf : s.WF) :
    (s.withTriggers es).WF := by
  obtain ⟨p, result, h⟩ := withTriggers_pending s es
  rw [h]
  exact hwf.congr rfl rfl rfl rfl

/-- Finding the triggers keeps the physical cards. -/
theorem withTriggers_physIds (s : GameState) (es : List Event) :
    (s.withTriggers es).physIds = s.physIds := by
  obtain ⟨p, result, h⟩ := withTriggers_pending s es
  rw [h]
  rfl

/-- Finding the triggers keeps `OwnerOk`. -/
theorem withTriggers_ownerOk {s : GameState} (es : List Event) (hown : s.OwnerOk) :
    (s.withTriggers es).OwnerOk := by
  obtain ⟨p, result, h⟩ := withTriggers_pending s es
  rw [h]
  exact hown.congr rfl rfl

/-- With no event, nothing fires. -/
theorem withTriggers_nil (s : GameState) : s.withTriggers [] = s := by
  have empty (order : List PlayerId) : order.flatMap (fun _ => ([] : List PendTrigger)) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  have noScore : s.eventWinner [] = none := by
    cases hc : s.clock <;> simp [GameState.eventWinner, GameState.suddenDeathScorer, hc]
  unfold GameState.withTriggers
  rw [noScore]
  dsimp only
  split
  · simp [GameState.recordTurnEvents, GameState.detect, GameState.deathGroupWatchers,
      GameState.trimLimits, GameState.firstCardTriggers, GameState.firstSpellFieldTriggers,
      GameState.delayedPlayTriggers, empty]
  · simp [GameState.recordTurnEvents]

/-- The frames a `triggers` step puts are not `setupHands`, are not setup frames. -/
theorem triggersStep_frames {s : GameState} {pend : List PendTrigger} {rest : List Frame}
    {g : Frame} (h : g ∈ (triggersStep s pend rest).2) :
    g ≠ .setupHands ∧ g.isSetup = false := by
  rcases (triggersStep_spec s pend rest).2 g h with
      ⟨p, n, rfl⟩ | ⟨x, rfl⟩ | ⟨p, t, m, o, rfl⟩ <;>
    exact ⟨by simp, rfl⟩

end Riftbound

end
