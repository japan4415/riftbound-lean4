module

public import Riftbound.Rules.Chain

/-!
# Triggered abilities

A triggered ability fires when something it waits for happens (CR 382-385). The step that did it
leaves events; `detect` reads them and names the abilities that fire. They wait on the stack, in a
`triggers` frame beneath the work that is still to do, until a player would next receive priority
(CR 383.1); then each goes on the Chain as an object of its own, the turn player's first (CR 383.3).

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
  | .playCard c _ ts _ _ _, .player p => playedOf p c es ++ ts.map (Event.chosenBySpell p)
  -- the objects an ability chooses are chosen too (Irelia: "when you choose or ready me")
  | .activate src _ _ ts _ _ _, .player p =>
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
def trigOk (s : GameState) (src : ObjId) (who : PlayerId) (t : Trigger) (_body : EffectDef) :
    Bool :=
  t.subject == .self && condOk s src who t.condition && t.occurrence == .every

/-- The ability can be used again this turn (CR 371, 386). -/
def limitOk (s : GameState) (src : ObjId) (idx : Nat) (limit : Limit)
    (copy : Option Timestamp := none) : Bool := match limit with
  | .unlimited => true
  | .perTurn n => (s.obj? src).any (fun o => decide (o.abilityUses idx copy < n))

/-- The triggered abilities at the places `lo` up to `hi` of the card `d`, as abilities of the
object `src` controlled by `p`, that fire on the event. -/
def triggersAmongMatching (s : GameState) (src : ObjId) (p : PlayerId)
    (eventMatches : TriggerEvent → Bool) (d : CardDef)
    (lo hi : Nat) (copy : Option Timestamp := none) : List PendTrigger :=
  (List.range (hi - lo)).filterMap (fun (j : Nat) =>
    match d.allAbilities[lo + j]? with
    | some (Ability.triggered t body lim) =>
      if eventMatches t.event && trigOk s src p t body && limitOk s src (lo + j) lim copy then
        some { source := src, card := d.id, idx := lo + j, controller := p, copyStamp := copy }
      else none
    | _ => none)

/-- The triggered abilities in the given range that fire on exactly this event. -/
def triggersAmong (s : GameState) (src : ObjId) (p : PlayerId) (ev : TriggerEvent) (d : CardDef)
    (lo hi : Nat) : List PendTrigger :=
  triggersAmongMatching s src p (· == ev) d lo hi

/-- The object's abilities whose event matches, including abilities it gains (CR 137, 479.3). -/
def triggersOfMatching (s : GameState) (src : ObjId) (p : PlayerId)
    (eventMatches : TriggerEvent → Bool) (lastCopy : Option AttachmentCopy := none) :
    List PendTrigger :=
  let definition := (lastCopy.bind (fun copy => s.cards.find? copy.card)) <|> s.cardDef? src
  let stamp := (lastCopy.map (·.stamp)) <|> s.copyStamp? src
  (match definition with
    | some d => triggersAmongMatching s src p eventMatches d 0 d.fullAbilities.length stamp
    | none => []) ++
  s.inPlay.flatMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      if o.attached == some src then
        triggersAmongMatching s src p eventMatches d d.fullAbilities.length d.allAbilities.length
      else []
    | _, _ => []) ++
  (s.attachmentTextDefs src (eventMatches .leave || eventMatches .die)).flatMap (fun (d, stamp) =>
    triggersAmongMatching s src p eventMatches d 0 d.textAbilities.length (some stamp)) ++
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
        | none => []
      else []
    | _, _ => [])

/-- The triggered abilities of the object that fire on exactly this event. -/
def triggersOf (s : GameState) (src : ObjId) (p : PlayerId) (ev : TriggerEvent) : List PendTrigger :=
  triggersOfMatching s src p (· == ev)

/-- Whether the object `subj`, which the player `who` plays, loses or moves, is what the subject of
a trigger of `src` (controlled by `c`) describes. The place of the subject is not asked: the object
may have left the game, as a Spell on its way to the Chain has. A subject at a place (here, at a
base) is not understood yet: it never holds. -/
def subjectHolds (s : GameState) (src : ObjId) (c : PlayerId) (subj : ObjId) (who : PlayerId) :
    Selector → Bool
  | .pick .all side .anywhere fs =>
    (match side with | .friendly => who == c | .enemy => who != c | .any => true) &&
      (fs.holds s src (Env.empty.withMight s.mightTable) subj == some true)
  | _ => false

/-- The abilities of the objects in play and of the Legends that watch for the object `subj` of the
player `who`, on the event: those whose subject is not the object itself. -/
def watchersOf (s : GameState) (subj : ObjId) (who : PlayerId) (ev : TriggerEvent) :
    List PendTrigger :=
  (s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))).flatMap (fun src =>
    match s.obj? src, s.cardDef? src with
    | some o, some d =>
      -- a Battlefield works for the player whose object it is about (Valley of Idols)
      let c := if d.hasType .battlefield then who else o.controller
      let copy := (s.attachmentCopyOf src o).map (·.stamp)
      let definitions := (d, d.fullAbilities.length, copy) ::
        ((s.attachmentTextDefs src).map (fun (cd, stamp) => (cd, cd.textAbilities.length, some stamp)))
      definitions.flatMap (fun (cd, count, stamp) =>
        (List.range count).filterMap (fun j =>
          match cd.allAbilities[j]? with
          | some (Ability.triggered t _ lim) =>
            if t.event == ev && t.subject != .self &&
                subjectHolds s src c subj who t.subject &&
                condOkEnv s src c { slots := [.obj subj] } t.condition &&
                t.occurrence == .every && limitOk s src j lim stamp then
              some { source := src, card := cd.id, idx := j, controller := c,
                     subject := some subj, copyStamp := stamp }
            else none
          | _ => none))
    | _, _ => [])

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
      | _, _ => none)
  else []

/-- A passive ability of an object the player controls makes the abilities of the event `.die` fire
one more time. -/
def GameState.dieExtra (s : GameState) (p : PlayerId) : Bool :=
  s.passiveSources.any (fun g => (s.obj? g).any (fun o => o.controller == p) &&
    (s.activeMods g).any (fun m => match m with | .triggersExtra .die _ => true | _ => false))

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

/-- A Chain pass changes only who can respond or schedules resolution. Other decisions may
change Might directly, including a pass that ends a Showdown. -/
def GameState.actionMightEvents (s s' : GameState) (a : Action) : List Event :=
  match s.pending, a.kind with
  | .chainPass .. :: _, .pass => []
  | _, _ => s.mightyEvents s'

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

/-- The abilities that fire because of one event (CR 389). -/
def detectOne (s : GameState) : Event → List PendTrigger
  | .played p obj =>
    match s.cardDef? obj with
    | some d =>
      -- A Spell completes its play when it resolves (CR 420.4.a).
      if d.hasType .spell then [] else
        triggersOf s obj p .play ++ watchersOf s obj p .play ++
        (if d.hasType .unit || d.hasType .gear then
          s.baseEnergyPlayTriggers p ((d.cost.map Cost.energy).getD 0)
        else [])
    | none => []
  | .spellResolved p obj => triggersOf s obj p .play ++ watchersOf s obj p .play
  | .burnedUnitFor p src card idx _ might =>
    match s.cards.find? card with
    | some d => (triggersAmong s src p .linkedBurnUnit d idx (idx + 1)).map
      (fun t => { t with eventAmount := some might })
    | none => []
  | .died obj p =>
    let lastCopy := (s.obj? obj).bind (·.lastAttachmentCopy)
    let own := triggersOfMatching s obj p (· == .die) lastCopy
    -- the Deathknell abilities of a unit fire one more time while a passive ability says so
    let again :=
      let definition := (lastCopy.bind (fun copy => s.cards.find? copy.card)) <|> s.cardDef? obj
      let deathknell := definition.any (·.hasKeyword .deathknell) ||
        (s.attachmentTextDefs obj true).any (·.1.hasKeyword .deathknell)
      if deathknell && s.dieExtra p then own else []
    own ++ again ++ watchersOf s obj p .die ++ s.delayedDeathTriggers obj
  | .standardMoved u _ =>
    match s.obj? u with
    | some o => triggersOf s u o.controller .move ++ watchersOf s u o.controller .move
    | none => []
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
    -- a Battlefield waits for its player's chosen unit at it
    (s.zone .battlefieldZone).flatMap (fun bf =>
      if (s.cardDef? t).any (·.hasType .unit) &&
          (s.obj? t).any (fun o => o.controller == p && o.loc == some bf) then
        triggersOf s bf p .chosenHere
      else []) ++
    -- a unit of the player that is chosen by their spell, and what watches the units they choose
    (if (s.obj? t).any (·.controller == p) then
      triggersOf s t p .chosen ++ watchersOf s t p .chosen ++
        triggersOf s t p .chosenAny ++ watchersOf s t p .chosenAny
    else [])
  | .chosenByAbility p t =>
    if (s.obj? t).any (·.controller == p) then
      triggersOf s t p .chosenAny ++ watchersOf s t p .chosenAny
    else []
  | .killedBySpell p =>
    (s.zone (.player p .trash)).flatMap (fun u => triggersOf s u p .killBySpell)
  | .recycled p =>
    s.inPlay.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then triggersOf s u p .recycle else [])
  | .hiddenPlayed p =>
    s.inPlay.flatMap (fun u =>
      if (s.obj? u).any (·.controller == p) then triggersOf s u p .playHidden else [])
  | .tokenPlayed p t => triggersOf s t p .playToken ++ watchersOf s t p .playToken
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
        s.passiveSources.flatMap (fun u =>
          if (s.obj? u).any (·.controller == p) then triggersOf s u p .hide else [])
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
    let eff :=
      (s.trigUnitsAt bf p).flatMap
        (fun u => triggersOf s u p (if conquer then .conquer else .hold) ++
          triggersOf s u p .scored ++
          -- Skyfall of Areion: the hold effects of the unit are conquer effects too, and back
          (if s.holdIsConquer u then triggersOf s u p (if conquer then .hold else .conquer)
           else [])) ++
      (s.zone (.player p .legendZone)).flatMap
        (fun l => triggersOf s l p (if conquer then .youConquer else .youHold)) ++
      triggersOf s bf p (if conquer then .youConquer else .youHold)
    -- the effects fire one more time if a unit there says so
    eff ++ (if s.scoreExtra p bf conquer then eff else []) ++
    -- what the opponents of the player who scores wait for
    s.passiveSources.flatMap (fun u =>
      match s.obj? u with
      | some o =>
        if o.controller != p then
          triggersOf s u o.controller .opponentScores ++
            (if conquer then [] else triggersOf s u o.controller .opponentHolds)
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
  | .combatStarted bf att =>
    let controller := ((s.obj? bf).bind (·.control)).getD (s.active.getD att)
    triggersOf s bf controller .combatStart ++
    (s.trigAllUnitsAt bf).flatMap (fun u =>
      match s.obj? u with
      | some o =>
        let ev := if o.controller == att then TriggerEvent.attack else .defend
        triggersOf s u o.controller ev ++ watchersOf s u o.controller ev
      | none => []) ++
    -- the abilities of the Battlefield: for the players who attack and defend there
    (s.players.filter (fun q => !(s.trigUnitsAt bf q).isEmpty)).flatMap (fun q =>
      triggersOf s bf q (if q == att then TriggerEvent.attack else .defend)) ++
    -- the units of a defending player that are elsewhere: "when you defend at a battlefield"
    (s.players.filter (fun q => q != att && !(s.trigUnitsAt bf q).isEmpty)).flatMap (fun q =>
      s.inPlay.flatMap (fun u =>
        if (s.obj? u).any (fun o => o.controller == q && o.loc != some bf) &&
            (s.cardDef? u).any (·.hasType .unit) then
          (triggersOf s u q .youDefend).map (fun t => { t with subject := some bf })
        else []))
  | _ => []

/-- Keep the abilities that a limit of times per turn lets fire: the events of one step may set
off the same ability more than once, and the limit counts the times it fired before and those it
fires now (CR 371). -/
def GameState.trimLimits (s : GameState) (l : List PendTrigger) : List PendTrigger :=
  l.foldl (fun kept t =>
    let taken := (kept.filter (fun k =>
      k.source == t.source && k.idx == t.idx && k.copyStamp == t.copyStamp)).length
    match (s.cards.find? t.card).bind (fun d => d.allAbilities[t.idx]?),
        s.obj? t.source with
    | some (Ability.triggered _ _ (.perTurn n)), some o =>
      if o.abilityUses t.idx t.copyStamp + taken < n then kept ++ [t] else kept
    | _, _ => kept ++ [t]) []

/-- The abilities that fire because of the events of a step, the turn player's first (CR 383.3). -/
def GameState.detect (s : GameState) (es : List Event) (extra : List PendTrigger := []) :
    List PendTrigger :=
  let all := s.trimLimits (es.flatMap (detectOne s) ++ extra)
  let a := s.active.getD ⟨0⟩
  all.filter (fun t => t.controller == a) ++ all.filter (fun t => t.controller != a)

/-- The frames that complete outstanding work before triggered abilities are finalized (CR 334).
This includes draws still owed by the current task or instruction. -/
def Frame.isResolution : Frame → Bool
  | .cleanup => true
  | .draw .. => true
  | .run .. => true
  | .finishSpell _ => true
  | .resolveChain => true
  | .combatDamage .. => true
  | .combatResolve .. => true
  | .predict .. | .chancePredict .. => true
  | .eitherDo _ _ _ (.fundLookedPermanent ..) _ _ => true
  | .eitherDo _ _ _ (.finishFundedPermanent ..) _ _ => true
  | .eitherDo _ _ _ (.fundLimitedSpell ..) _ _ => true
  | .eitherDo _ _ _ (.finishLimitedSpell ..) _ _ => true
  | .eitherDo _ _ _ (.chooseDamageReplacement ..) _ _ => true
  | .eitherDo _ _ _ (.orderCombatDamage ..) _ _ => true
  | .eitherDo _ _ _ (.chooseDeathBanisher ..) _ _ => true
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

/-- Remember a player's choice of an enemy Unit, even if it later changes zones or control. -/
def GameState.recordEnemyChoice (s : GameState) (notes : List TurnFx) : Event → List TurnFx
  | .chosenBySpell p id | .chosenByAbility p id =>
    if s.inPlay.contains id && (s.obj? id).any (·.controller != p) &&
        (s.cardDef? id).any (·.hasType .unit) &&
        !(notes.any (fun f => f.turn == s.turn && f.who == p && f.kind == .choseEnemyUnit)) then
      { who := p, turn := s.turn, stamp := s.nextTimestamp, kind := .choseEnemyUnit } :: notes
    else notes
  | _ => notes

/-- Update the play and choice history before evaluating triggers. Ignore events during setup. -/
def GameState.recordTurnEvents (s : GameState) (es : List Event) : GameState :=
  let inPlay := s.phase != .setup && s.pending.all (fun f => !f.isSetup)
  { s with
    playLog := if inPlay then es.foldl s.recordPlayEvent s.playLog else s.playLog
    turnFx := if inPlay then es.foldl s.recordEnemyChoice s.turnFx else s.turnFx }

/-- After a step: the abilities that fired wait on the stack. Not during the setup. -/
def GameState.withTriggers (s : GameState) (es : List Event) : GameState :=
  let next := s.recordTurnEvents es
  if s.phase != .setup && s.pending.all (fun f => !f.isSetup) then
    match next.detect es (next.firstCardTriggers s) with
    | [] => next
    | pend => { next with pending := insertTriggers pend s.pending }
  else next

/-- The modes on the ability that waits, or no mode for an ability without alternatives. -/
def trigModes (s : GameState) (t : PendTrigger) : List (Option Nat) :=
  let modes := ((abilityDef s t.card t.idx).map (·.modes)).getD []
  if modes.isEmpty then [none] else (List.range modes.length).map some

/-- The choices for the selected branch of the triggered ability (CR 355). -/
def trigChoices (s : GameState) (t : PendTrigger) (mode : Option Nat := none) : List Choice :=
  (((abilityDef s t.card t.idx).bind (·.forPick (mode.elim .plain SpellPick.mode))).map
    (·.choices)).getD []

/-- The trigger declaration on the queued ability, even if its source left the Board. -/
def trigDeclaration (s : GameState) (t : PendTrigger) : Option Trigger :=
  match (s.cards.find? t.card).bind (fun d => d.allAbilities[t.idx]?) with
  | some (.triggered rule _ _) => some rule
  | _ => none

/-- Whether the player may decline during finalization (CR 383.3.a). -/
def trigOptional (s : GameState) (t : PendTrigger) : Bool :=
  (trigDeclaration s t).any (·.optional)

/-- The cost due before the trigger can go on the Chain. -/
def trigCost (s : GameState) (t : PendTrigger) : TriggerCost :=
  ((trigDeclaration s t).map (·.cost)).getD .free

/-- A Burn cost must be payable in full. Burn Out on a short deck is for instructions
in effects (CR 383.3.b.1, 441.4). -/
def canPayBurn (s : GameState) (p : PlayerId) (count : Nat) : Bool :=
  count ≤ (s.zone (.player p .mainDeck)).length

/-- The original source is still on the board and can be exhausted (CR 415.4). -/
def canExhaustTriggerSource (s : GameState) (t : PendTrigger) : Bool :=
  (s.locate t.source).any Zone.isBoard && (s.obj? t.source).any (fun o => !o.exhausted)

/-- The ways to pay the cost of a trigger. Killed objects are selected as costs (CR 355.10.c). -/
def trigPayments (s : GameState) (t : PendTrigger) : List (List ObjId) :=
  match trigCost s t with
  | .free => [[]]
  | .energy n =>
    if (payByRunes s t.controller t.source ⟨n, []⟩).isSome then [[]] else []
  | .exhaustSelf => if canExhaustTriggerSource s t then [[]] else []
  | .burn n => if canPayBurn s t.controller n then [[]] else []
  | .killFriendly n fs =>
    let env : Env := { passMight := s.mightTable }
    let candidates := (s.pickCandidates t.controller t.source env .friendly .anywhere fs false).getD []
    (subseqsUpTo n candidates.eraseDups).filter (·.length == n)

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
def triggerCostOptions (s : GameState) (t : PendTrigger) :
    List (List ObjId × List (ObjId × PlayerId)) :=
  (trigPayments s t).flatMap (fun ids => (triggerBanisherOptions s ids).map (ids, ·))

/-- Every legal pick for the mode that the Pool of the controller can pay for (CR 355, 809). -/
def trigTuples (s : GameState) (t : PendTrigger) (mode : Option Nat) : List (List ObjId) :=
  (targetTuples s t.controller t.source s.mightTable (trigChoices s t mode)).filter
    (fun ts => s.deflectOk t.controller (s.poolOf t.controller) ts)

/-- The mode and target combinations that can be finalized. -/
def trigTargetOptions (s : GameState) (t : PendTrigger) : List (Option Nat × List ObjId) :=
  (trigModes s t).flatMap (fun mode => (trigTuples s t mode).map (mode, ·))

/-- Whether the mode is available and the targets are legal for that mode (CR 355.3, 355.5). -/
def trigTargetOk (s : GameState) (t : PendTrigger) (mode : Option Nat) (ts : List ObjId) : Bool :=
  (trigModes s t).contains mode &&
    targetsOk s t.controller t.source s.mightTable (trigChoices s t mode) ts &&
    s.deflectOk t.controller (s.poolOf t.controller) ts

/-- A listed mode and its targets satisfy the finalization rules. -/
theorem mem_trigTargetOptions (s : GameState) (t : PendTrigger) (mode : Option Nat)
    (ts : List ObjId) : (mode, ts) ∈ trigTargetOptions s t ↔ trigTargetOk s t mode ts = true := by
  simp only [trigTargetOptions, trigTuples, trigTargetOk, List.mem_flatMap, List.mem_map,
    List.mem_filter, mem_targetTuples, Prod.mk.injEq, Bool.and_eq_true, List.contains_iff_mem]
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
def trigPickOptions (s : GameState) (t : PendTrigger) :
    List (Option Nat × List ObjId × Option PlayerId) :=
  let players := trigPlayerOptions s t
  (trigTargetOptions s t).flatMap (fun (mode, ts) => players.map (mode, ts, ·))

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
def acceptedTriggers (s : GameState) (t : PendTrigger) : List (List ObjId × TriggerPayment) :=
  let payments := triggerCostOptions s t
  (trigPickOptions s t).flatMap (fun (mode, ts, player) =>
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

/-- The Chain gets the ability: it is used (CR 371), and it goes on top as an object of its own,
controlled by the player, with the objects chosen. -/
def putTrigger (s : GameState) (t : PendTrigger) (ts : List ObjId) (mode : Option Nat := none)
    (player : Option PlayerId := none) : GameState :=
  let s1 := s.modObj t.source (fun o => (o.noteAbilityUse t.idx t.copyStamp).noteChose s.turn ts)
  let item : Object :=
    { abilityItem t.card t.idx t.source t.controller
        (if mode.isNone then ts ++ t.subject.toList else ts) t.eventAmount with
      spellPick := mode.elim .plain SpellPick.mode
      triggerSubject := t.subject
      abilityCopyStamp := t.copyStamp
      targetPlayer := player }
  match addObject s1 item .chain with
  | some r => r.1
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

/-- Pay a trigger's cost without giving either player a chance to respond (CR 383.3.b.1). -/
def payTriggerCost (s : GameState) (t : PendTrigger) (ids : List ObjId)
    (banishers : List (ObjId × PlayerId) := []) :
    Option (GameState × List Event) :=
  match trigCost s t with
  | .free => some (s, [])
  | .energy n => payByRunes s t.controller t.source ⟨n, []⟩
  | .exhaustSelf =>
    if canExhaustTriggerSource s t then some (setExhausted true s t.source) else none
  | .burn n => if canPayBurn s t.controller n then some (burnTop s t.controller n) else none
  | .killFriendly n _ =>
    if ids.length == n then
      some (applyEach (killOrSaveInGroup s) (noteTriggerBanishers s banishers) ids)
    else none

/-- Dismiss a declined or unpayable trigger, or pay for it and finalize it (CR 355, 383.3). -/
def finalizePick (s : GameState) (grp : List PendTrigger) (i : Nat) (ts : List ObjId)
    (payment : TriggerPayment) : GameState × List Event :=
  match grp[i]?, payment with
  | some t, .pay ids mode player banishers =>
    if !(trigModes s t).contains mode || !(trigPlayerOptions s t).contains player ||
        (ts.isEmpty && !(trigChoices s t mode).isEmpty &&
          !((trigOptional s t || mode.isSome || player.isSome) && trigTargetOk s t mode [])) then (s, [])
    else match payTriggerCost s t ids banishers with
      | some (paid, events) => (putTrigger paid t ts mode player, events)
      | none => (s, [])
  | _, _ => (s, [])

/-- The frames to put beneath the work after the abilities have gone on the Chain: the turn player
gets priority with the Chain, unless that is already so (CR 340). -/
def triggerFrames (s : GameState) (rest : List Frame) : List Frame :=
  match rest with
  | .chainPass .. :: _ => []
  | _ => if (s.zone .chain).isEmpty then [] else [.chainPass (s.active.getD ⟨0⟩) 0]

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
    let grp := ts.filter (fun u => u.controller == t.controller)
    let others := ts.filter (fun u => u.controller != t.controller)
    if grp.isEmpty && trigModes s t == [none] && trigPlayerOptions s t == [none] &&
        (trigChoices s t).isEmpty && !trigOptional s t && trigCost s t == .free then
      (putTrigger s t [], [.triggers others])
    else (s, [.triggerOrder t.controller t grp others])

/-- Putting one ability on the Chain is a safe change. -/
theorem putTrigger_safe (s : GameState) (t : PendTrigger) (ts : List ObjId)
    (mode : Option Nat := none) (player : Option PlayerId := none) :
    Safe s (putTrigger s t ts mode player) := by
  have h1 : Safe s (s.modObj t.source
      (fun o => (o.noteAbilityUse t.idx t.copyStamp).noteChose s.turn ts)) :=
    Safe.modObj s t.source (fun _ => rfl) (fun _ => rfl)
  unfold putTrigger
  dsimp only
  split
  · rename_i r hr
    refine h1.trans ⟨fun hwf => addObject_wf hwf hr, fun hwf => addObject_physIds hwf hr rfl,
      fun hwf hown => addObject_ownerOk hwf hown hr, addObject_sameMeta hr⟩
  · exact h1

/-- Paying for a trigger preserves structural invariants. -/
theorem payTriggerCost_safe {s : GameState} {t : PendTrigger} {ids : List ObjId}
    {banishers : List (ObjId × PlayerId)} {r : GameState × List Event}
    (h : payTriggerCost s t ids banishers = some r) : Safe s r.1 := by
  unfold payTriggerCost at h
  split at h
  · cases h; exact Safe.refl s
  · exact payByRunes_safe h
  · split at h
    · cases h; exact setExhausted_safe true s t.source
    · simp at h
  · split at h
    · cases h; exact applyEach_safe (sendObj_safe .trash) _ _
    · simp at h
  · split at h
    · cases h
      exact (noteTriggerBanishers_safe s banishers).trans
        (applyEach_safe (killOrSaveInGroup_safe s) ids _)
    · simp at h

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
    s.withTriggers es = s.recordTurnEvents es ∨ ∃ pend, s.withTriggers es = { s.recordTurnEvents es with
        pending := insertTriggers pend s.pending } ∧ s.phase ≠ .setup ∧
      ∀ f ∈ s.pending, f.isSetup = false := by
  unfold GameState.withTriggers
  by_cases hg : (s.phase != .setup && s.pending.all (fun f => !f.isSetup)) = true
  · cases hd : (s.recordTurnEvents es).detect es ((s.recordTurnEvents es).firstCardTriggers s) with
    | nil => simp [hg, hd]
    | cons x xs =>
      right
      refine ⟨x :: xs, by simp [hg, hd], ?_, ?_⟩
      · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg
        exact hg.1
      · simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
        exact hg.2
  · simp [hg]

/-- Besides recording plays, `withTriggers` changes only the stack. -/
theorem withTriggers_pending (s : GameState) (es : List Event) :
    ∃ p, s.withTriggers es = { s.recordTurnEvents es with pending := p } := by
  rcases withTriggers_cases s es with h | ⟨pend, h, -⟩
  · exact ⟨s.pending, by rw [h]; rfl⟩
  · exact ⟨_, h⟩

/-- Finding the triggers keeps the game well formed. -/
theorem withTriggers_wf {s : GameState} (es : List Event) (hwf : s.WF) :
    (s.withTriggers es).WF := by
  obtain ⟨p, h⟩ := withTriggers_pending s es
  rw [h]
  exact hwf.congr rfl rfl rfl rfl

/-- Finding the triggers keeps the physical cards. -/
theorem withTriggers_physIds (s : GameState) (es : List Event) :
    (s.withTriggers es).physIds = s.physIds := by
  obtain ⟨p, h⟩ := withTriggers_pending s es
  rw [h]
  rfl

/-- Finding the triggers keeps `OwnerOk`. -/
theorem withTriggers_ownerOk {s : GameState} (es : List Event) (hown : s.OwnerOk) :
    (s.withTriggers es).OwnerOk := by
  obtain ⟨p, h⟩ := withTriggers_pending s es
  rw [h]
  exact hown.congr rfl rfl

/-- With no event, nothing fires. -/
theorem withTriggers_nil (s : GameState) : s.withTriggers [] = s := by
  unfold GameState.withTriggers
  split
  · simp [GameState.recordTurnEvents, GameState.detect, GameState.trimLimits, GameState.firstCardTriggers]
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
