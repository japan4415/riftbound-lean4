module

public import Riftbound.Rules.Select

/-!
# Passive abilities

A passive ability changes the game as long as the object that has it is in play and its condition
holds (CR 363-366). The changes are read where the rules ask: whether a Unit enters ready, the
Might of a Unit.

The Might the rules read (`mightNow`) is the Might of the Layers' last step: the printed Might and
the lasting changes (`mightOf`) with the passive changes added (CR 479.4). What the passive
abilities select and test reads the Might without them, so the passives do not depend on one
another. The dependencies between abilities (CR 480-481) wait for a card that needs them.
-/

@[expose] public section

namespace Riftbound

/-- The card enters ready: it has the passive ability that says so, with no condition. -/
def CardDef.entersReady (d : CardDef) : Bool :=
  d.abilities.any (fun ab =>
    match ab with
    | Ability.passive .always mods => mods.contains (.entersReady .self)
    | _ => false)

/-- The card enters play exhausted, whatever it is (Honeyfruit). -/
def CardDef.entersExhausted (d : CardDef) : Bool :=
  d.abilities.any (fun ab =>
    match ab with
    | Ability.passive .always mods => mods.contains .entersExhausted
    | _ => false)

/-- Record a move into the owner's zone, including a Banish performed by that owner. -/
def Object.ownerMoveEvents (o : Object) (id new : ObjId) (dest : ZoneKind)
    (banishedByOwner : Bool := false) : List Event :=
  .moved id new (.player o.owner dest) ::
    (if banishedByOwner && o.kind.phys?.isSome then [.banished o.owner o.owner new] else [])

namespace GameState

/-- The objects whose passive abilities apply: those in play, and the Legends (CR 363). -/
def passiveSources (s : GameState) : List ObjId :=
  s.inPlay ++ s.players.flatMap (fun p => s.zone (.player p .legendZone))

/-- The changes the passive abilities of `src` make now: those of the abilities whose condition
holds. -/
def activeMods (s : GameState) (src : ObjId) : List StaticMod :=
  match s.obj? src, s.cardDef? src with
  | some o, some d =>
    (s.appendedAbilities src d).flatMap (fun ab =>
      match ab with
      | Ability.passive cond mods =>
        if cond.eval s o.controller src {} == some true then mods else []
      | _ => [])
  | _, _ => []

/-- The active passive changes from sources controlled by this player (CR 363). -/
def controlledMods (s : GameState) (p : PlayerId) : List StaticMod :=
  (s.passiveSources.filter (fun src => (s.obj? src).any (·.controller == p))).flatMap s.activeMods

/-- The player has a source of this passive change. Check only conditions of abilities that
make the requested change. Repeating a source's text does not affect this yes/no test. -/
def hasControlledMod (s : GameState) (p : PlayerId) (mod : StaticMod) : Bool :=
  s.passiveSources.any (fun src => (s.obj? src).any (·.controller == p) &&
    (s.cardDef? src).any (fun d => (s.appendedAbilities src d).any (fun
      | .passive cond mods => mods.contains mod && cond.eval s p src {} == some true
      | _ => false)))

/-- An active replacement banishes a card that would go to its owner's Trash from outside the
Main Deck (CR 367-370). Tokens are never affected by this replacement. -/
def replacesTrash (s : GameState) (id : ObjId) (o : Object) : Bool :=
  o.kind.phys?.isSome && !(s.zone (.player o.owner .mainDeck)).contains id &&
    s.hasControlledMod o.owner .banishInsteadOfTrash &&
    (s.cardDef? id).any (fun d => d.hasType .unit || d.hasType .gear || d.hasType .spell)

/-- Apply any replacement for a proposed destination in the owner's zones. -/
def ownerDestination (s : GameState) (id : ObjId) (o : Object) (k : ZoneKind) : ZoneKind :=
  if k == .trash && s.replacesTrash id o then .banishment else k

/-- A Trash or Banishment destination remains in one of those two zones. -/
theorem ownerDestination_trash_or_banishment (s : GameState) (id : ObjId) (o : Object)
    {k : ZoneKind} (hk : k = .trash ∨ k = .banishment) :
    s.ownerDestination id o k = .trash ∨ s.ownerDestination id o k = .banishment := by
  unfold ownerDestination
  split
  · exact Or.inr rfl
  · exact hk

/-- A passive ability of an object that the opponents of the player control, with the change. -/
def oppHas (s : GameState) (p : PlayerId) (m : StaticMod) : Bool :=
  s.passiveSources.any (fun g => (s.obj? g).any (fun o => o.controller != p) &&
    (s.activeMods g).contains m)

/-- The passive change `m` of `src` that takes Might away down to a floor, for the Might of `id`:
how much it takes away at most, and the floor ("to a minimum of 1"). -/
def modFloor (s : GameState) (src id : ObjId) : StaticMod → Option (Nat × Nat)
  | .mightMinusMin sel a fl =>
    match s.obj? src, sel.eval s ((s.obj? src).map (·.controller) |>.getD ⟨0⟩) src {} with
    | some o, some ids =>
      if ids.contains id then (a.evalS0 s o.controller src {}).map (fun k => (k, fl)) else none
    | _, _ => none
  | _ => none

/-- The player `p` cannot do the act `a` at the Battlefield `bf` now, by a passive ability that says
so ("players can't score here until their third turn", "while I'm at a battlefield, opponents
can't score"). -/
def cantActHere (s : GameState) (p : PlayerId) (a : Act) (bf : ObjId) : Bool :=
  s.passiveSources.any (fun g =>
    let c := ((s.obj? g).map (·.controller)).getD ⟨0⟩
    (s.activeMods g).any (fun m =>
      match m with
      | .cantPlayer who act place untilTurn =>
        act == a && ((who.resolve s c).map (·.contains p)).getD false &&
          (match place with
            | .here => s.hereOf g == some bf
            | .anywhere => true
            | _ => false) &&
          (untilTurn == 0 || decide (s.turnsTaken p < untilTurn))
      | _ => false))

/-- The player `p` cannot score the Battlefield `bf` now. -/
def cantScoreHere (s : GameState) (p : PlayerId) (bf : ObjId) : Bool := s.cantActHere p .score bf

/-- A Battlefield point the turn player would score is replaced by one draw (CR 367, 471). -/
def drawForBattlefieldPoint (s : GameState) (p : PlayerId) : Bool :=
  s.active == some p &&
    s.passiveSources.any (fun src =>
      (s.activeMods src).any (fun
        | .earlyScoreDraw turns => let taken := s.turnsTaken p; taken > 0 && taken ≤ turns
        | _ => false))

/-- Some passive ability in play has the change `m`, whoever controls it. -/
def anyActive (s : GameState) (m : StaticMod) : Bool :=
  s.passiveSources.any (fun g => (s.activeMods g).contains m)

/-- The player chose a Battlefield they control and has an effect that readies Units played there. -/
def readyAtDestination (s : GameState) (p : PlayerId) (dest : Option ObjId) : Bool :=
  dest.any (fun field => (s.obj? field).any (·.control == some p)) &&
    s.hasControlledMod p .unitsEnterReadyAtControlledBattlefields

/-- A Unit at the Battlefield `bf` cannot move to the Base: by the Battlefield, or by a Unit
(Minotaur Reckoner). -/
def homeForbidden (s : GameState) (bf : ObjId) : Bool :=
  (s.activeMods bf).contains .noMoveToBase || s.anyActive .noMoveToBaseAny

/-- The Unit `u`, at the Battlefield `bf`, cannot move to the Base: for the Battlefield, or because the
Unit itself says it cannot (Determined Sentry). -/
def homeForbiddenFor (s : GameState) (u bf : ObjId) : Bool :=
  s.homeForbidden bf || (s.activeMods u).contains .noMoveToBase

/-- The total fee for one Move to these Battlefields, paid by the player instructed to move.
Several Units moving to the same Battlefield in one instruction incur each fee once. -/
def movementFee (s : GameState) (p : PlayerId) (fields : List ObjId) : Cost :=
  if fields.isEmpty then Cost.zero else
    (s.zone .battlefieldZone).foldl (fun total id =>
      if (s.obj? id).any (fun o => o.controller != p && o.loc.any fields.contains) then
        (s.activeMods id).foldl (fun c mod => match mod with
          | .moveFeeHere fee => c.plus fee
          | _ => c) total
      else total) Cost.zero

/-- The resource payments available for a Standard Move, independent of the Unit's Exhaust cost. -/
def standardMovePayments (s : GameState) (p : PlayerId) (dest : MoveDest) :
    List Cost :=
  let fee := match dest with
    | .base => Cost.zero
    | .battlefield bf => s.movementFee p [bf]
  if fee == Cost.zero then [Cost.zero]
  else (s.symbolPayments p fee [] false).map Prod.fst

/-- The controller of an object (the first player if it is gone). -/
def controllerOf (s : GameState) (src : ObjId) : PlayerId :=
  ((s.obj? src).map (·.controller)).getD ⟨0⟩

/-- The points needed to win the game: those of the mode, and the changes the passive abilities
make (CR 194). -/
def victoryScore (s : GameState) : Nat :=
  let delta : Int := (s.passiveSources.flatMap (fun src =>
    (s.activeMods src).map (fun m =>
      match m with
      | .victoryScorePlus a => ((a.evalS0 s (s.controllerOf src) src {}).getD 0 : Int)
      | .victoryScoreMinus a => -((a.evalS0 s (s.controllerOf src) src {}).getD 0 : Int)
      | _ => 0))).sum
  (s.config.mode.victoryScore + delta).toNat

/-- The Bonus Damage the passive abilities of the player give to each instance of damage of their
spells and abilities: those of the objects they control, and those an Equipment gives the Unit it
is attached to (Rabadon's Deathcrown). -/
def passiveBonus (s : GameState) (p : PlayerId) (source : Option CardDef := none) : Nat :=
  let amount (src : ObjId) (m : StaticMod) : Option Nat :=
    match m with
    | .bonusDamage a => a.evalS0 s p src {}
    | .bonusAbilityDamage type a =>
      if source.any (fun d => d.hasType type && !d.hasType .spell) then a.evalS0 s p src {}
      else none
    | _ => none
  (s.passiveSources.flatMap (fun g =>
    if (s.obj? g).any (·.controller == p) then (s.activeMods g).filterMap (amount g)
    else [])).sum +
  (s.inPlay.flatMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      match o.attached with
      | some u =>
        if (s.obj? u).any (·.controller == p) then
          d.grants.flatMap (fun ab =>
            match ab with
            | Ability.passive .always mods => mods.filterMap (amount g)
            | _ => [])
        else []
      | none => []
    | _, _ => [])).sum

/-- The Bonus Damage with each instance of damage that the spell or ability `src` of the player
deals to the object `id`: that of the effect of the turn for the next spell, and that of the
Battlefield the object is at (CR 142). -/
def bonusOn (s : GameState) (p : PlayerId) (src id : ObjId)
    (originalCard : Option CardId := none) : Nat :=
  let definition := s.cardDef? src <|> originalCard.bind s.cards.find?
  s.spellBonus p src + s.passiveBonus p definition +
    (match (s.obj? id).bind (·.loc) with
      | some bf =>
        (s.activeMods bf).foldl
          (fun acc m => match m with | .bonusDamageHere n => acc + n | _ => acc) 0
      | none => 0)

/-- The keywords the Equipment attached to an object gives it (CR 137): the passive abilities with
no condition that give the object the keyword. -/
def equipKws (s : GameState) (id : ObjId) : List KeywordInst :=
  s.inPlay.flatMap (fun g =>
    match s.obj? g, s.cardDef? g with
    | some o, some d =>
      -- the keywords it gives the Unit it is attached to
      (if o.attached == some id then
        d.grants.flatMap (fun ab =>
          match ab with
          | Ability.passive .always mods =>
            mods.filterMap (fun m => match m with | .keyword .self k => some k | _ => none)
          | _ => [])
      else []) ++
      -- Shurelya's Requiem: the units of the player at the place of the unit it is attached to
      (match o.attached.bind (fun u => s.obj? u), s.obj? id with
        | some host, some me =>
          if host.controller == me.controller && host.loc == me.loc && id ∈ s.inPlay &&
              (s.cardDef? id).any (·.hasType .unit) then
            d.grants.flatMap (fun ab =>
              match ab with
              | Ability.passive .always mods =>
                mods.filterMap (fun m => match m with | .keywordHere k => some k | _ => none)
              | _ => [])
          else []
        | _, _ => [])
    | _, _ => [])

/-- The keywords the passive abilities give an object now: those of the abilities whose condition
holds and whose selector stands for the object (CR 479.3). The selectors and the conditions read
only what the card prints (`Filter.hasKeyword`), never `grantedKws`, which would not end; so a
filter for the units that have a keyword does not see the keywords that are given. -/
def passiveKws (s : GameState) (id : ObjId) : List KeywordInst :=
  s.passiveSources.flatMap (fun src =>
    match s.obj? src with
    | some o =>
      (s.activeMods src).flatMap (fun m =>
        match m with
        | .keyword sel k =>
          match sel.eval s o.controller src {} with
          | some ids => if ids.contains id then [k] else []
          | none => []
        | .equipEach k =>
          -- one for each Equipment of the player of the source that is attached to the object
          ((s.inPlay.filter (fun g => (s.obj? g).any (fun e =>
            e.controller == o.controller && e.attached == some id) &&
              (s.cardDef? g).any (·.hasType .gear)))).map (fun _ => k)
        | _ => [])
    | none => [])

/-- The object's keywords from attached Effect Text, passive abilities, and temporary effects
(CR 479.3). -/
def grantedKws (s : GameState) (id : ObjId) : List KeywordInst :=
  (s.attachmentTextDefs id).flatMap (·.1.keywords) ++ s.equipKws id ++ s.passiveKws id ++
    (((s.obj? id).map (·.tempKws)).getD []).map (·.1)

/-- Whether the object has a printed or granted keyword (CR 479.3). -/
def hasKw (s : GameState) (id : ObjId) (k : Keyword) : Bool :=
  (s.cardDef? id).any (·.hasKeyword k) || (s.grantedKws id).any (·.keyword == k) ||
    (k == .reaction && (s.cardDef? id).any (·.hasType .spell) &&
      (s.obj? id).any (fun o => s.hasControlledMod o.controller .spellsHaveReaction))

/-- How much the passive change `m` of `src` changes the Might of `id` (CR 479.4). -/
def modMight (s : GameState) (src id : ObjId) (m : StaticMod) : Int :=
  let amountAt (sel : Selector) (a : Amount) : Int :=
    match s.obj? src with
    | some o =>
      if ((sel.eval s o.controller src {}).getD []).contains id then
        ((a.evalS0 s o.controller src {}).getD 0 : Int)
      else 0
    | none => 0
  match m with
  | .mightPlus sel a => amountAt sel a
  | .mightPlusWithKeyword sel k a => if s.hasKw id k then amountAt sel a else 0
  | .mightMinus sel a => -(amountAt sel a)
  -- `mightMinusMin` has a floor: it is read after the others (`modFloor`)
  | _ => 0

/-- Might effects granted by Equipment are evaluated on the Unit wearing it (CR 725).
The printed bonus, fresh attachment bonus and simple Level bonus already enter through
`equipBonus`. -/
def equipmentMightMods (s : GameState) : List (ObjId × StaticMod) :=
  s.inPlay.flatMap (fun gear =>
    match (s.obj? gear).bind (·.attached) with
    | none => []
    | some unit =>
      let p := s.controllerOf unit
      ((s.cardDef? gear).map (·.grants)).getD [] |>.flatMap (fun
        | .passive condition mods =>
          if condition.eval s p unit {} == some true then
            mods.filterMap (fun m => match condition, m with
              | .cmp .ge .xp (.const _), .mightPlus .self (.const _) => none
              | _, .mightPlus .. | _, .mightPlusWithKeyword .. |
                _, .mightMinus .. | _, .mightMinusMin .. => some (unit, m)
              | _, _ => none)
          else []
        | _ => []))

/-- What the passive abilities add to the Might of an object. -/
def passiveMight (s : GameState) (id : ObjId) : Int :=
  let fromBoard := s.passiveSources.flatMap (fun src => (s.activeMods src).map (s.modMight src id))
  let fromEquipment := s.equipmentMightMods.map (fun (src, mod) => s.modMight src id mod)
  fromBoard.sum + fromEquipment.sum

/-- The number a printed keyword carries on the card of an object (0 if it does not print it). -/
def kwAmount (s : GameState) (u : ObjId) (k : Keyword) : Nat :=
  let instances := ((s.cardDef? u).map (·.keywords)).getD [] ++ s.grantedKws u
  let fixedAmount (keyword : Keyword) (i : KeywordInst) : Option Nat :=
    -- Assault, Shield and Disarm default to one when they have no number.
    if i.keyword == keyword then
      match i.arg with
      | .amount n => some n
      | .none =>
        if keyword == .assault || keyword == .shield || keyword == .disarm then some 1 else none
      | _ => none
    else none
  let amount (i : KeywordInst) : Option Nat :=
    if k == .assault && i.keyword == .assault && i.arg == .equalShield then
      some ((instances.filterMap (fixedAmount .shield)).sum)
    else fixedAmount k i
  -- Assault that equals a number of objects (Ancient Warmonger: the enemy units here)
  let counted : Nat :=
    if k == .assault then
      (s.activeMods u).foldl (fun acc m =>
        match m with
        | .assaultCount sel =>
          acc + (((sel.eval s ((s.obj? u).map (·.controller) |>.getD ⟨0⟩) u {}).map
            (·.length)).getD 0)
        | _ => acc) 0
    else 0
  (instances.filterMap amount).sum + counted

/-- Might with the bonus from the Unit's role in combat, before taking a nonnegative damage value. -/
def mightWithCombatBonus (s : GameState) (id : ObjId) (bonus : Nat) : Option Int :=
  (s.mightOf id).map (fun m =>
    let total := m + s.equipBonus id + s.passiveMight id + s.buffBonus id + bonus
    -- the changes with a floor come last: they take away down to the floor, never below it
    let floors := (s.passiveSources.flatMap (fun src =>
      (s.activeMods src).filterMap (s.modFloor src id))) ++
      s.equipmentMightMods.filterMap (fun (src, mod) => s.modFloor src id mod)
    floors.foldl
      (fun (t : Int) (c : Nat × Nat) =>
        if t ≤ (c.2 : Int) then t else max (c.2 : Int) (t - (c.1 : Int))) total)

/-- The Might an object has now, including Assault and Shield while attacking or defending
(CR 475-479, 807, 814). -/
def mightNow (s : GameState) (id : ObjId) : Option Int :=
  let bonus := match s.combatNow, s.obj? id with
    | some (bf, attacker), some o =>
      if o.loc != some bf || !(s.zone .battlefieldZone).contains id ||
          !(s.cardDef? id).any (·.hasType .unit) then 0
      else if o.controller == attacker then s.kwAmount id .assault
      else if s.combat.isNone || s.combat.any (·.defender == o.controller) then
        s.kwAmount id .shield
      else 0
    | _, _ => 0
  s.mightWithCombatBonus id bonus

/-- The adjustments beyond printed Might, lasting changes, buffs and Equipment bonuses that
the filters read (`Env.passMight`), including passives, floors and combat keywords. -/
def mightTable (s : GameState) : List (ObjId × Int) :=
  if s.combatNow.isNone && !(s.passiveSources.any (fun g => (s.cardDef? g).any (fun d =>
    (d.abilities ++ d.grants).any (fun ab =>
      match ab with
      | Ability.passive _ mods =>
        mods.any (fun m => match m with
          | .mightPlus .. | .mightPlusWithKeyword .. | .mightMinus .. | .mightMinusMin .. => true
          | _ => false)
      | _ => false)))) then []
  else
    s.inPlay.filterMap (fun id =>
      match s.mightNow id, s.mightOf id with
      | some now, some base =>
        let d := now - (base + s.equipBonus id + s.buffBonus id)
        if d == 0 then none else some (id, d)
      | _, _ => none)

end GameState

/-- The value of an amount in an effect. `Amount.evalS0` reads everything but the Might of objects,
which the Layers decide (`mightNow`): "equal to my Might" is the Might the rules read (CR 479.4),
the sum over the objects the selector gives. -/
def Amount.evalS (s : GameState) (p : PlayerId) (self : ObjId) (env : Env) : Amount → Option Nat
  | .mightOf sel =>
    (sel.eval s p self env).map (fun ids =>
      (ids.map (fun id => ((s.mightNow id).getD 0).toNat)).sum)
  | .mightIncreaseTo unit reference => do
    let chosen ← (unit.eval s p self env).bind List.head?
    let model ← (reference.eval s p self env).bind List.head?
    let current ← s.mightNow chosen
    let higher ← s.mightNow model
    pure (higher - current).toNat
  | .highestMight sel =>
    (sel.eval s p self env).map (fun ids =>
      (ids.map (fun id => ((s.mightNow id).getD 0).toNat)).foldl Nat.max 0)
  | .kwAmount sel k =>
    (sel.eval s p self env).map (fun ids => (ids.map (fun id => s.kwAmount id k)).sum)
  | .add a b => do pure ((← Amount.evalS s p self env a) + (← Amount.evalS s p self env b))
  | .sub a b => do pure ((← Amount.evalS s p self env a) - (← Amount.evalS s p self env b))
  | .mul a b => do pure ((← Amount.evalS s p self env a) * (← Amount.evalS s p self env b))
  | .min a b =>
    do pure (Nat.min (← Amount.evalS s p self env a) (← Amount.evalS s p self env b))
  | .max a b =>
    do pure (Nat.max (← Amount.evalS s p self env a) (← Amount.evalS s p self env b))
  | a => a.evalS0 s p self env

end Riftbound

end
