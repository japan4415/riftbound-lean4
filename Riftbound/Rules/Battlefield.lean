module

public import Riftbound.Rules.Effects
public import Riftbound.Rules.Passive

/-!
# Battlefields: Standard Move, Cleanup, Showdown and scoring

The Units of a game go from a Base to a Battlefield by a Standard Move (CR 144, 447). A Unit
that moves to a Battlefield its controller does not control makes it Contested (CR 190.3). The
Cleanup (CR 318-324) kills Units with lethal damage, takes the Control of a Battlefield from a
player who has no Unit there, and keeps the Contested status right; at a Neutral Open it starts
the Showdown of a Contested Battlefield (CR 323.11, 341-348). When everyone has passed, the player
whose Units are alone at the Battlefield gets its Control, and Scores it by Conquer
(CR 348.2, 471, 473). At the Scoring Step the turn player Scores by Hold the Battlefields they
control (CR 315.2.b). A player with the Victory Score and more points than every opponent wins at
the Cleanup (CR 323.1).

**Not yet** (milestone M5c): Combat. A Unit may not move to a Battlefield where an opponent has a
Unit, so a Battlefield never holds the Units of two players. Moving several Units at once
(CR 144.3) and Ganking (CR 810) are later too.
-/

@[expose] public section

namespace Riftbound

namespace GameState

/-- Whether the card of an object has a type. -/
def hasType (s : GameState) (id : ObjId) (t : CardType) : Bool :=
  match s.cardDef? id with
  | some d => d.types.contains t
  | none => false

/-- Whether an object occupies a Unit's place on the board. An attachment copies Unit to Unit. -/
def isUnit (s : GameState) (id : ObjId) : Bool :=
  (s.printedCardDef? id).any (·.hasType .unit)

/-- Whether an object is a Battlefield. Attachment copies apply only to Units. -/
def isBattlefield (s : GameState) (id : ObjId) : Bool :=
  (s.printedCardDef? id).any (·.hasType .battlefield)

/-- The Battlefields of the game, in the order of the Battlefield Zone. -/
def battlefields (s : GameState) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun b => s.isBattlefield b)

/-- Whether the Unit `u` is at the Battlefield `bf`. -/
def isAt (s : GameState) (bf u : ObjId) : Bool :=
  s.isUnit u && decide ((s.obj? u).bind (·.loc) = some bf)

/-- The Units at a Battlefield. -/
def unitsAt (s : GameState) (bf : ObjId) : List ObjId :=
  (s.zone .battlefieldZone).filter (fun u => s.isAt bf u)

/-- Whether an object is controlled by `p` (the base value, until the Layers: milestone M6). -/
def isControlledBy (s : GameState) (p : PlayerId) (u : ObjId) : Bool :=
  decide ((s.obj? u).map (·.controller) = some p)

/-- The Units of player `p` at a Battlefield. -/
def unitsOf (s : GameState) (p : PlayerId) (bf : ObjId) : List ObjId :=
  (s.unitsAt bf).filter (fun u => s.isControlledBy p u)

/-- The player who controls a Battlefield, if any (CR 190.6). -/
def controlOf (s : GameState) (bf : ObjId) : Option PlayerId := (s.obj? bf).bind (·.control)

/-- An object of another player than `q` in play has the passive ability that any amount of its
damage is enough to kill the units of `q` (Elder Dragon). -/
def anyDamageKills (s : GameState) (q : PlayerId) : Bool :=
  s.inPlay.any (fun g =>
    (s.obj? g).any (fun o => o.controller != q) &&
      (s.cardDef? g).any (fun d => d.fullAbilities.any (fun ab =>
        match ab with
        | Ability.passive .always mods => mods.contains .anyDamageKills
        | _ => false)))

/-- Whether a Unit has lethal damage: damage that is not 0 and reaches its Might (CR 142.4.b).
The owner must be a player of the game, which holds for every object of a game that can be played.
The condition is there so that the Cleanup, which kills such a Unit by sending it to its owner's
Trash, always has a Trash to send it to, and so always stops (I12a). -/
def lethal (s : GameState) (id : ObjId) : Bool :=
  match s.obj? id with
  | some o =>
    decide (o.owner.n < s.playerCount) && decide (0 < o.damage) &&
      ((s.mightNow id).any (fun m => decide (Might.eff m ≤ o.damage)) || s.anyDamageKills o.controller)
  | none => false

end GameState

/-! ### Standard Move -/

/-- Whether player `p` can make the Standard Move of the Unit `u` to `d` (CR 144): the Unit is
theirs and ready; it goes from the Base to a Battlefield, or from a Battlefield to the Base, or
from a Battlefield to another one if it has Ganking (CR 810). -/
def moveOk (s : GameState) (p : PlayerId) (u : ObjId) (d : MoveDest) : Bool :=
  match s.obj? u with
  | none => false
  | some o =>
    decide (p.n < s.playerCount) && decide (s.phase = .main) && s.isUnit u &&
      decide (o.controller = p) && (!o.exhausted && !s.moveBlocked u) &&
      match d with
      | .base =>
        decide (u ∈ s.zone .battlefieldZone) && o.loc.isSome &&
          !(o.loc.any (fun bf => s.homeForbiddenFor u bf))
      | .battlefield bf =>
        decide (bf ∈ s.battlefields) &&
          (decide (u ∈ s.zone (.player p .base)) ||
            ((s.hasKw u .ganking ||
                -- a Battlefield units can move to from anywhere (Baron Pit)
                (s.cardDef? bf).any (fun d => d.fullAbilities.any (fun ab =>
                  match ab with
                  | Ability.passive .always mods => mods.contains .movesHereFromAnywhere
                  | _ => false))) &&
              decide (u ∈ s.zone .battlefieldZone) && o.loc.isSome &&
              decide (o.loc ≠ some bf)))

/-- The change of a Unit by a Standard Move in the turn `turn`: it is exhausted, is where it went,
and the move is counted. -/
def moveUnitOf (turn : Nat) (loc : Option ObjId) (o : Object) : Object :=
  let o1 : Object := { o with exhausted := true, loc := loc }
  o1.countMove turn o.loc

/-- The Battlefield becomes Contested by `p` if `p` does not control it (CR 190.3). -/
def contestBy (p : PlayerId) (bf : ObjId) (s : GameState) : GameState :=
  if s.controlOf bf = some p then s else s.modObj bf (fun o => { o with contested := some p })

/-- The Standard Move of the Unit `u` of player `p` to `d`. `none` if the Unit cannot be moved. -/
def applyMove (s : GameState) (p : PlayerId) (u : ObjId) (d : MoveDest) :
    Option (GameState × List Event) :=
  match d with
  | .base =>
    (moveObj s u (.player p .base)).map (fun r =>
      (r.1.modObj r.2 (moveUnitOf s.turn none), [Event.standardMoved r.2 none]))
  | .battlefield bf =>
    if u ∈ s.zone .battlefieldZone then
      some (contestBy p bf (s.modObj u (moveUnitOf s.turn (some bf))),
        [Event.standardMoved u (some bf)])
    else
      (moveObj s u .battlefieldZone).map (fun r =>
        (contestBy p bf (r.1.modObj r.2 (moveUnitOf s.turn (some bf))),
          [Event.standardMoved r.2 (some bf)]))

/-- The Units a player might move: those on their Base and those at Battlefields. -/
def GameState.movable (s : GameState) (p : PlayerId) : List ObjId :=
  s.zone (.player p .base) ++ s.zone .battlefieldZone

/-- The destinations a Unit might be moved to: the Base and each Battlefield. -/
def GameState.destinations (s : GameState) : List MoveDest :=
  .base :: s.battlefields.map MoveDest.battlefield

/-- The Standard Moves a player can make. -/
def legalMoves (s : GameState) (p : PlayerId) : List Action :=
  (s.movable p).flatMap (fun u =>
    (s.destinations.filter (fun d => moveOk s p u d)).map
      (fun d => ⟨.player p, .standardMove u d⟩))

/-- A Standard Move that can be made starts from a Unit a player might move, and goes to a
destination there is. -/
theorem moveOk_mem {s : GameState} {p : PlayerId} {u : ObjId} {d : MoveDest}
    (h : moveOk s p u d = true) : u ∈ s.movable p ∧ d ∈ s.destinations := by
  unfold moveOk at h
  split at h
  · exact absurd h (by simp)
  · cases d with
    | base =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨?_, by simp [GameState.destinations]⟩
      simp only [GameState.movable, List.mem_append]
      exact Or.inr h.2.1.1
    | battlefield bf =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      refine ⟨?_, ?_⟩
      · simp only [GameState.movable, List.mem_append]
        rcases h.2.2 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1.1.1.2
      · simp only [GameState.destinations, List.mem_cons, List.mem_map]
        exact Or.inr ⟨bf, h.2.1, rfl⟩

/-- A Standard Move that can be made can be done. -/
theorem applyMove_isSome {s : GameState} {p : PlayerId} {u : ObjId} {d : MoveDest}
    (hwf : s.WF) (h : moveOk s p u d = true) : ∃ r, applyMove s p u d = some r := by
  unfold moveOk at h
  split at h
  · exact absurd h (by simp)
  · cases d with
    | base =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨hpn, -⟩, -⟩, -⟩, -⟩, ⟨hmem, -⟩, -⟩ := h
      obtain ⟨r, hr⟩ := moveObj_isSome hwf hmem (.player p .base) .top (fun o _ =>
        ⟨by simpa [Zone.normalize, Zone.isBoard] using Zone.valid_player hpn ZoneKind.base,
          by simp [Zone.normalize, Zone.isBoard]⟩)
      unfold applyMove
      simp only [hr]
      exact ⟨_, rfl⟩
    | battlefield bf =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      unfold applyMove
      by_cases hb : u ∈ s.zone .battlefieldZone
      · simp only [hb, ite_true]
        exact ⟨_, rfl⟩
      · have hmem : u ∈ s.zone (.player p .base) := by
          rcases h.2.2 with h1 | h1
          · exact h1
          · exact absurd h1.1.1.2 hb
        obtain ⟨r, hr⟩ := moveObj_isSome hwf hmem .battlefieldZone .top (fun o _ =>
          ⟨by simpa [Zone.normalize] using Zone.valid_battlefieldZone s.playerCount,
            by simp [Zone.normalize]⟩)
        simp only [hb, ite_false, hr]
        exact ⟨_, rfl⟩

/-- The Standard Moves listed are those a player can make. -/
theorem mem_legalMoves {s : GameState} {p : PlayerId} {a : Action} :
    a ∈ legalMoves s p ↔
      ∃ u d, a = ⟨.player p, .standardMove u d⟩ ∧ moveOk s p u d = true := by
  unfold legalMoves
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨u, -, d, ⟨-, hd⟩, rfl⟩
    exact ⟨u, d, rfl, hd⟩
  · rintro ⟨u, d, rfl, hd⟩
    obtain ⟨hu, hdm⟩ := moveOk_mem hd
    exact ⟨u, hu, d, ⟨hdm, hd⟩, rfl⟩

/-! ### Scoring -/

/-- Score the Battlefield `bf` for `r` (CR 471). Nothing happens if `r` has scored it this turn
(CR 472). A Conquer when `r` is one point short of the Victory Score or closer gives the last point
only if `r` has scored every Battlefield this turn, and a card drawn instead (CR 473.1.b). -/
def scoreBf (s : GameState) (r : PlayerId) (bf : ObjId) (conquer : Bool) :
    GameState × List Frame × List Event :=
  match s.obj? bf with
  | none => (s, [], [])
  | some o =>
    if o.scored.contains r then (s, [], [])
    else
      let s1 := s.modObj bf (fun o => { o with scored := r :: o.scored })
      let all := s1.battlefields.all
        (fun b => ((s1.obj? b).map (·.scored.contains r)) == some true)
      -- a card can say the player can't score points here: the Battlefield is scored all the same
      -- (the abilities still fire), but no point comes of it
      if s.cantScoreHere r bf then (s1, [], [Event.scored r bf conquer])
      else if conquer && s.victoryScore ≤ s.pointsOf r + 1 && !all then
        (s1, [Frame.draw r 1], [Event.scored r bf true])
      else if s.drawForBattlefieldPoint r then
        (s1, [Frame.draw r 1], [Event.scored r bf conquer, Event.scoreDraw r bf])
      else (s1.gainPoints r 1, [], [Event.scored r bf conquer, Event.pointsGained r 1])

/-- The Battlefields the turn player holds and has not scored this turn (CR 315.2.b). -/
def GameState.holds (s : GameState) (tp : PlayerId) : List ObjId :=
  s.battlefields.filter (fun b =>
    decide (s.controlOf b = some tp) && !((s.obj? b).map (·.scored.contains tp)).getD false)

/-- Remember that `tp` has scored a Battlefield this turn, and held it if a point came of it. -/
def markScored (tp : PlayerId) (pt : Bool) (o : Object) : Object :=
  { o with scored := tp :: o.scored, held := if pt then tp :: o.held else o.held }

/-- A new turn: nothing has been scored yet (CR 472). -/
def clearScored (o : Object) : Object :=
  { o with scored := [], held := [], used := [], copiedUses := [] }

/-- Score by Hold: the turn player gets one point for each Battlefield they hold
(CR 315.2.b, 471, 472). -/
def hold (s : GameState) (tp : PlayerId) : GameState × List Event :=
  let bs := s.holds tp
  let replace := s.drawForBattlefieldPoint tp
  let s1 := bs.foldl (fun s' b =>
    s'.modObj b (markScored tp (!replace && !s.cantScoreHere tp b))) s
  let awarded := bs.filter (fun b => !s.cantScoreHere tp b)
  let scored := bs.map (fun b => Event.scored tp b false)
  if replace then (s1, scored ++ awarded.map (Event.scoreDraw tp))
  else
    let n := awarded.length
    (s1.gainPoints tp n, scored ++ if n = 0 then [] else [Event.pointsGained tp n])

/-- End Showdown-duration changes when no Combat still needs them. -/
def GameState.expireShowdownMods (s : GameState) (expire : Bool) : GameState :=
  if expire then s.mapObjects endShowdownObj else s

/-- Resolve Control after a Showdown or Combat (CR 348.2, 468.5). In Combat, duration effects
expire later, when Combat ends (CR 468.7). -/
def endShowdown (s : GameState) (bf : ObjId) (expire : Bool := true) :
    GameState × List Frame × List Event :=
  let board := s.expireShowdownMods expire
  let s1 := board.modObj bf (fun o => { o with contested := none })
  match s.players.filter (fun p => !(s.unitsOf p bf).isEmpty) with
  | [r] =>
    if s.controlOf bf = some r then (s1, [], [])
    else
      let s2a := s1.modObj bf (fun o => { o with control := some r })
      -- a Battlefield that nobody controlled is conquered open: noted for the turn
      let s2 := if s.controlOf bf = none then s2a.addTurnFxOn r bf .openConquest else s2a
      let t := scoreBf s2 r bf true
      (t.1, t.2.1, Event.controlChanged bf (some r) :: t.2.2)
  | [] =>
    if (s.controlOf bf).isSome then
      (s1.modObj bf (fun o => { o with control := none }), [], [Event.controlChanged bf none])
    else (s1, [], [])
  | _ => (s1, [], [])

/-- A winner (CR 323.1): the player who has the Victory Score and more points than every
opponent. -/
def GameState.winner (s : GameState) : Option PlayerId :=
  s.players.find? (fun p =>
    decide (s.victoryScore ≤ s.pointsOf p) &&
      s.players.all (fun q => decide (q = p) || decide (s.pointsOf q < s.pointsOf p)))

/-! ### Cleanup -/

namespace GameState

/-- An ongoing Showdown or Combat keeps Control and Contested status until its resolution
determines what happens to the Battlefield (CR 190.3.b, 190.4.b). -/
def fightingAt (s : GameState) (bf : ObjId) : Bool :=
  s.combat.any (·.battlefield == bf) ||
    s.pending.any (fun | .showdown there .. => there == bf | _ => false)

/-- Whether the Battlefield is controlled by a player with no Unit there (CR 323.5). -/
def lostControl (s : GameState) (bf : ObjId) : Bool :=
  !s.fightingAt bf &&
    match s.controlOf bf with
    | some r => (s.unitsOf r bf).isEmpty
    | none => false

/-- Whether the Battlefield is Contested by a player with no Unit there (CR 323.10). -/
def staleContest (s : GameState) (bf : ObjId) : Bool :=
  !s.fightingAt bf &&
    match (s.obj? bf).bind (·.contested) with
    | some q => (s.unitsOf q bf).isEmpty
    | none => false

/-- The controller of a Unit at an uncontrolled, uncontested Battlefield: they make it Contested
(CR 323.10.a). -/
def newContest (s : GameState) (bf : ObjId) : Option PlayerId :=
  match s.controlOf bf, (s.obj? bf).bind (·.contested) with
  | none, none => (s.unitsAt bf).head?.bind (fun u => (s.obj? u).map (·.controller))
  | _, _ => none

end GameState

/-- What the Cleanup does to a unit with lethal damage: an Equipment or Soraka saves it, or it is
killed (CR 323.4). -/
def cleanupKill (s : GameState) (u : ObjId) : GameState × List Event :=
  -- a unit with an Equipment that dies instead (Guardian Angel) is saved, as it is by damage
  match s.deathSaver u with
  | some (some g) =>
    if g != u && (s.obj? g).any (fun (o : Object) => decide (o.owner.n < s.playerCount)) then
      saveUnit s u (some g)
    else killObj s u
  -- a unit on a Battlefield next to Soraka is healed, exhausted and recalled instead of dying
  | some none =>
    if decide (u ∈ s.zone Zone.battlefieldZone) &&
        (s.obj? u).any (fun (o : Object) => decide (o.controller.n < s.playerCount)) then
      saveUnit s u none
    -- a unit at a Base is healed and exhausted (it is at the Base already): if it had no damage
    -- (its Might fell to 0), it dies
    else if !decide (u ∈ s.zone Zone.battlefieldZone) &&
        (s.obj? u).any (fun (o : Object) => decide (0 < o.damage)) then
      ((s.modObj u (fun o => { o with damage := 0, exhausted := true })).addTurnFxOn
        (match s.obj? u with | some o => o.controller | none => ⟨0⟩) u .saveUsed, [])
    else killObj s u
  | none => killObj s u

/-- What the Cleanup does to a unit with lethal damage is a safe change. -/
theorem cleanupKill_safe (s : GameState) (u : ObjId) : Safe s (cleanupKill s u).1 := by
  unfold cleanupKill
  split
  · rename_i g hg
    split
    · exact saveUnit_safe s u (some g)
    · exact killObj_safe s u
  · split
    · exact saveUnit_safe s u none
    · split
      · exact (Safe.modObj s u (f := fun o => { o with damage := 0, exhausted := true })
        (fun _ => rfl) (fun _ => rfl)).trans (addTurnFxOn_safe _ _ _ _)
      · exact killObj_safe s u
  · exact killObj_safe s u

/-- One step of the Cleanup (CR 323): the first of these that applies is done. `none` if none does.
1. A Unit with lethal damage is killed (CR 323.4).
2. A Battlefield loses its controller who has no Unit there (CR 323.5).
3. A Battlefield stops being Contested by a player with no Unit there (CR 323.10).
4. A Unit at an uncontrolled Battlefield makes it Contested (CR 323.10.a). -/
def cleanupStep0 (s : GameState) : Option (GameState × List Event) :=
  match s.inPlay.find? (fun u => s.isUnit u && s.lethal u) with
  | some u => some (cleanupKill s u)
  | none =>
    match s.battlefields.find? (fun b => s.lostControl b) with
    | some b =>
      some (s.modObj b (fun o => { o with control := none }), [Event.controlChanged b none])
    | none =>
      match s.battlefields.find? (fun b => s.staleContest b) with
      | some b => some (s.modObj b (fun o => { o with contested := none }), [])
      | none =>
        match s.battlefields.findSome? (fun b => (s.newContest b).map (fun q => (b, q))) with
        | some (b, q) => some (s.modObj b (fun o => { o with contested := some q }), [])
        | none => none

/-- A token in a Non-Board zone: it ceases to exist there (CR 183). -/
def GameState.offBoardToken (s : GameState) : Option ObjId :=
  (allZones s.playerCount).findSome? (fun z =>
    if z.isBoard then none
    else (s.zone z).find? (fun id =>
      (s.obj? id).any (fun o => match o.kind with | .token _ => true | _ => false)))

/-- The step of the Cleanup for a token that is off the Board: it is removed (CR 183). -/
def tokenStep (s : GameState) : Option (GameState × List Event) :=
  match s.offBoardToken with
  | some id => (removeObj s id).map (fun s' => (s', []))
  | none => none

/-- An Equipment attached to something that is not a Unit in play (CR 137). -/
def GameState.looseGear (s : GameState) : Option ObjId :=
  s.inPlay.find? (fun g => (s.obj? g).any (fun o =>
    match o.attached with
    | some u => !(s.inPlay.contains u && s.isUnit u)
    | none => false))

/-- The step of the Cleanup for an Equipment whose Unit is gone: it is not attached any more
(CR 137). -/
def detachStep (s : GameState) : Option (GameState × List Event) :=
  s.looseGear.map (fun g => (s.modObj g (fun o => { o with attached := none }), []))

/-- One step of the Cleanup (CR 323): a token off the Board ceases to exist (CR 183), an Equipment
whose Unit is gone is detached (CR 137), or else the first step of `cleanupStep0`. `none` if none
applies. -/
def cleanupStep (s : GameState) : Option (GameState × List Event) :=
  match tokenStep s with
  | some r => some r
  | none =>
    match detachStep s with
    | some r => some r
    | none => cleanupStep0 s

/-- The Showdown to start at a Neutral Open (CR 323.11): the first Contested Battlefield and the
player who made it Contested, who has Focus first (CR 345). A Neutral Open is the turn player having
priority with nothing else going on, so the frame below is the `priority` frame. -/
def GameState.startShowdown (s : GameState) (rest : List Frame) : Option (ObjId × PlayerId) :=
  match rest with
  | .priority _ :: _ =>
    s.battlefields.findSome? (fun b => ((s.obj? b).bind (·.contested)).map (b, ·))
  | _ => none

/-- A state is settled when the Cleanup has nothing left to do (CR 322): there is no winner to
declare and no step applies. -/
def GameState.Settled (s : GameState) : Prop := s.winner = none ∧ cleanupStep s = none

/-- Record new combatants at Cleanup and open a Combat at a Showdown once there are two sides
(CR 462.1, 466.2.c.3). Units that left that Battlefield are retained until Combat ends. -/
def GameState.observeCombat (s : GameState) (pending : List Frame) :
    Option CombatParticipation × List Event :=
  match s.combat with
  | some c =>
    if pending.any (fun
        | .showdown bf .. | .combatResolve bf _ | .combatResult bf |
          .combatControl bf | .combatFinish bf => bf == c.battlefield
        | _ => false) then
      let present := s.unitsOf c.attacker c.battlefield ++ s.unitsOf c.defender c.battlefield
      let joined := present.filter (fun unit => !c.units.contains unit)
      (some { c with units := c.units ++ joined },
        if joined.isEmpty then [] else [.combatJoined c.battlefield c.attacker joined])
    else (some c, [])
  | none =>
    match pending.findSome? (fun f => match f with
        | .showdown bf focus _ => some (bf, focus)
        | _ => none) with
    | some (bf, focus) =>
      match s.players.filter (fun p => !(s.unitsOf p bf).isEmpty) with
      | [a, b] =>
        let contested := ((s.obj? bf).bind (·.contested)).getD focus
        let (att, def_) := if contested == b then (b, a) else (a, b)
        (some
          { battlefield := bf
            attacker := att
            defender := def_
            units := s.unitsOf att bf ++ s.unitsOf def_ bf },
          [Event.combatStarted bf att])
      | _ => (none, [])
    | none => (none, [])

/-- Leave a settled Cleanup and update whether Combat has started or gained participants. -/
def continueAfterCleanup (s : GameState) (pending : List Frame) : GameState × List Event :=
  let r := s.observeCombat pending
  ({ s with pending := pending, combat := r.1 }, r.2)

/-- A pending lethal death can require a replacement choice before the automatic kill.
Off-board tokens and unattached Equipment are still handled first (CR 323, 372). -/
def cleanupDeathBanishChoice (s : GameState) : Option (ObjId × PlayerId × Effect × Effect) :=
  if s.offBoardToken.isSome || s.looseGear.isSome then none else
    (s.inPlay.find? (fun u => s.isUnit u && s.lethal u)).bind s.deathBanishChoice

/-- The step of the `cleanup` frame (CR 322-323): declare a winner, or do a step, or start a
Showdown, or finish. -/
def cleanupFrame (s : GameState) (rest : List Frame) : GameState × List Event :=
  match s.winner with
  | some w => ({ s with result := some (.won [w]), pending := [] }, [Event.won w])
  | none =>
    match cleanupDeathBanishChoice s with
    | some (u, controller, first, other) =>
      ({ s with pending := .eitherDo controller u {} first other .nil :: .cleanup :: rest }, [])
    | none =>
      match cleanupStep s with
      | some r => ({ r.1 with pending := .cleanup :: rest }, r.2)
      | none =>
        match s.startShowdown rest with
        | some (bf, q) =>
          continueAfterCleanup s (.showdown bf q 0 :: .cleanup :: rest)
        | none => continueAfterCleanup s rest

/-! ### The changes are safe -/

/-- A safe change of the board, then points for a player. The invariants of the board survive it. -/
def SafeP (s s'' : GameState) : Prop :=
  ∃ s1, Safe s s1 ∧ (s'' = s1 ∨ ∃ (p : PlayerId) (n : Nat), s'' = s1.gainPoints p n)

namespace SafeP

/-- A safe change is one. -/
theorem of_safe {s s' : GameState} (h : Safe s s') : SafeP s s' := ⟨s', h, Or.inl rfl⟩

/-- A safe change, then one more. -/
theorem trans_safe {s s' s'' : GameState} (h1 : Safe s s') (h2 : SafeP s' s'') : SafeP s s'' := by
  obtain ⟨s1, hs, hr⟩ := h2
  exact ⟨s1, h1.trans hs, hr⟩

/-- Well formed. -/
theorem wf {s s'' : GameState} (h : SafeP s s'') (hwf : s.WF) : s''.WF := by
  obtain ⟨s1, hs, rfl | ⟨p, n, rfl⟩⟩ := h
  · exact hs.wf hwf
  · exact GameState.wf_gainPoints (hs.wf hwf) p n

/-- The physical cards. -/
theorem phys {s s'' : GameState} (h : SafeP s s'') (hwf : s.WF) : s''.physIds.Perm s.physIds := by
  obtain ⟨s1, hs, rfl | ⟨p, n, rfl⟩⟩ := h
  · exact hs.phys hwf
  · exact hs.phys hwf

/-- `OwnerOk`. -/
theorem own {s s'' : GameState} (h : SafeP s s'') (hwf : s.WF) (hown : s.OwnerOk) :
    s''.OwnerOk := by
  obtain ⟨s1, hs, rfl | ⟨p, n, rfl⟩⟩ := h
  · exact hs.own hwf hown
  · exact GameState.ownerOk_gainPoints (hs.own hwf hown) p n

/-- The rules are as they were. -/
theorem config {s s'' : GameState} (h : SafeP s s'') : s''.config = s.config := by
  obtain ⟨s1, hs, rfl | ⟨p, n, rfl⟩⟩ := h
  · exact hs.same.config
  · exact hs.same.config

/-- The turn order is as it was. -/
theorem turnOrder {s s'' : GameState} (h : SafeP s s'') : s''.turnOrder = s.turnOrder := by
  obtain ⟨s1, hs, rfl | ⟨p, n, rfl⟩⟩ := h
  · exact hs.same.turnOrder
  · exact hs.same.turnOrder

/-- The phase is as it was. -/
theorem phase {s s'' : GameState} (h : SafeP s s'') : s''.phase = s.phase := by
  obtain ⟨s1, hs, rfl | ⟨p, n, rfl⟩⟩ := h
  · exact hs.same.phase
  · exact hs.same.phase

/-- The result is as it was. -/
theorem result {s s'' : GameState} (h : SafeP s s'') : s''.result = s.result := by
  obtain ⟨s1, hs, rfl | ⟨p, n, rfl⟩⟩ := h
  · exact hs.same.result
  · exact hs.same.result

/-- The stack is as it was. -/
theorem pending {s s'' : GameState} (h : SafeP s s'') : s''.pending = s.pending := by
  obtain ⟨s1, hs, rfl | ⟨p, n, rfl⟩⟩ := h
  · exact hs.same.pending
  · exact hs.same.pending

end SafeP

/-- Changing the attributes of the objects of a list, one after the other, is safe. -/
theorem foldl_modObj_safe {f : Object → Object} (hk : ∀ o, (f o).kind = o.kind)
    (ho : ∀ o, (f o).owner = o.owner) :
    ∀ (bs : List ObjId) (s : GameState), Safe s (bs.foldl (fun s b => s.modObj b f) s)
  | [], s => Safe.refl s
  | b :: bs, s => (Safe.modObj s b hk ho).trans (foldl_modObj_safe hk ho bs _)

/-- Changing the attributes of the objects of a list, one after the other, each by its own change,
is safe. -/
theorem foldl_modObj_safe' {g : ObjId → Object → Object} (hk : ∀ b o, (g b o).kind = o.kind)
    (ho : ∀ b o, (g b o).owner = o.owner) :
    ∀ (bs : List ObjId) (s : GameState), Safe s (bs.foldl (fun s b => s.modObj b (g b)) s)
  | [], s => Safe.refl s
  | b :: bs, s => (Safe.modObj s b (hk b) (ho b)).trans (foldl_modObj_safe' hk ho bs _)

/-- Making a Battlefield Contested is a safe change. -/
theorem contestBy_safe (p : PlayerId) (bf : ObjId) (s : GameState) :
    Safe s (contestBy p bf s) := by
  unfold contestBy
  split
  · exact Safe.refl s
  · exact Safe.modObj s bf (fun _ => rfl) (fun _ => rfl)

/-- A Standard Move that is done is a safe change. -/
theorem applyMove_safe {s s' : GameState} {p : PlayerId} {u : ObjId} {d : MoveDest}
    {es : List Event} (h : applyMove s p u d = some (s', es)) : Safe s s' := by
  cases d with
  | base =>
    unfold applyMove at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨s1, id'⟩, hm, rfl, -⟩ := h
    exact (Safe.moveObj hm).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl))
  | battlefield bf =>
    simp only [applyMove] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have h1 : Safe s (s.modObj u (moveUnitOf s.turn (some bf))) :=
        Safe.modObj s u (fun _ => rfl) (fun _ => rfl)
      exact h1.trans (contestBy_safe p bf _)
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨s1, id'⟩, hm, rfl, -⟩ := h
      have h1 := Safe.moveObj hm
      have h2 : Safe s1 (s1.modObj id' (moveUnitOf s.turn (some bf))) :=
        Safe.modObj s1 id' (fun _ => rfl) (fun _ => rfl)
      exact (h1.trans h2).trans (contestBy_safe p bf _)

/-- When no step applies, the steps of `cleanupStep0` do not apply either. -/
theorem cleanupStep0_of_none {s : GameState} (h : cleanupStep s = none) :
    cleanupStep0 s = none := by
  unfold cleanupStep at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · exact h

/-- The token that is found is a token, which has no physical card. -/
theorem offBoardToken_spec {s : GameState} {id : ObjId} (h : s.offBoardToken = some id) :
    ∃ o, s.obj? id = some o ∧ o.kind.phys? = none := by
  unfold GameState.offBoardToken at h
  obtain ⟨z, -, hz⟩ := List.exists_of_findSome?_eq_some h
  split at hz
  · simp at hz
  · have hf := List.find?_some hz
    cases ho : s.obj? id with
    | none => simp [ho] at hf
    | some o =>
      refine ⟨o, rfl, ?_⟩
      simp only [ho, Option.any_some] at hf
      cases hk : o.kind <;> simp [hk, ObjKind.phys?] at hf ⊢

/-- A step of the Cleanup is a safe change. -/
theorem cleanupStep0_safe {s s' : GameState} {es : List Event}
    (h : cleanupStep0 s = some (s', es)) : Safe s s' := by
  unfold cleanupStep0 at h
  split at h
  · rename_i u hu
    simp only [Option.some.injEq] at h
    have hs := cleanupKill_safe s u
    rw [h] at hs
    exact hs
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Safe.modObj s _ (fun _ => rfl) (fun _ => rfl)
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Safe.modObj s _ (fun _ => rfl) (fun _ => rfl)
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact Safe.modObj s _ (fun _ => rfl) (fun _ => rfl)
        · exact absurd h (by simp)

/-- The step for a token that is off the Board is a safe change. -/
theorem tokenStep_safe {s s' : GameState} {es : List Event}
    (h : tokenStep s = some (s', es)) : Safe s s' := by
  unfold tokenStep at h
  split at h
  · rename_i id hid
    obtain ⟨o, ho, hk⟩ := offBoardToken_spec hid
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s2, hrm, hr2⟩ := h
    simp only [Prod.mk.injEq] at hr2
    rw [← hr2.1]
    exact ⟨fun hwf => removeObj_wf hwf hrm, fun hwf => removeObj_physIds hwf hrm ho hk,
      fun hwf hown => removeObj_ownerOk hwf hown hrm, removeObj_sameMeta hrm⟩
  · simp at h

/-- A step of the Cleanup is a safe change. -/
theorem cleanupStep_safe {s s' : GameState} {es : List Event}
    (h : cleanupStep s = some (s', es)) : Safe s s' := by
  unfold cleanupStep at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h
    rw [h] at hr
    exact tokenStep_safe hr
  · split at h
    · rename_i r hr
      unfold detachStep at hr
      simp only [Option.map_eq_some_iff] at hr
      obtain ⟨g, -, hg⟩ := hr
      simp only [Option.some.injEq] at h
      rw [h] at hg
      simp only [Prod.mk.injEq] at hg
      rw [← hg.1]
      exact Safe.modObj s g (fun _ => rfl) (fun _ => rfl)
    · exact cleanupStep0_safe h

/-- Scoring a Battlefield is a safe change, then points. -/
theorem scoreBf_safeP (s : GameState) (r : PlayerId) (bf : ObjId) (c : Bool) :
    SafeP s (scoreBf s r bf c).1 := by
  unfold scoreBf
  split
  · exact SafeP.of_safe (Safe.refl s)
  · split
    · exact SafeP.of_safe (Safe.refl s)
    · have h1 : Safe s (s.modObj bf (fun o => { o with scored := r :: o.scored })) :=
        Safe.modObj s bf (fun _ => rfl) (fun _ => rfl)
      dsimp only
      split
      · exact SafeP.of_safe h1
      · split
        · exact SafeP.of_safe h1
        · split
          · exact SafeP.of_safe h1
          · exact ⟨_, h1, Or.inr ⟨r, 1, rfl⟩⟩

/-- Holding is a safe change, then points. -/
theorem hold_safeP (s : GameState) (tp : PlayerId) : SafeP s (hold s tp).1 := by
  unfold hold
  dsimp only
  have h := foldl_modObj_safe'
    (g := fun b => markScored tp (!s.drawForBattlefieldPoint tp && !s.cantScoreHere tp b))
    (fun _ _ => rfl) (fun _ _ => rfl) (s.holds tp) s
  split
  · exact SafeP.of_safe h
  · exact ⟨_, h, Or.inr ⟨tp, _, rfl⟩⟩

/-- The end of a Showdown is a safe change, then points. -/
theorem endShowdown_safeP (s : GameState) (bf : ObjId) (expire : Bool := true) :
    SafeP s (endShowdown s bf expire).1 := by
  have hm : Safe s (s.mapObjects endShowdownObj) :=
    ⟨fun h => GameState.wf_mapObjects h _,
      fun _ => by rw [GameState.physIds_mapObjects s (f := endShowdownObj)
        (fun o => endShowdownObj_kind o)],
      fun _ h => GameState.ownerOk_mapObjects h (fun o => endShowdownObj_owner o),
      GameState.sameMeta_mapObjects s _⟩
  let board := s.expireShowdownMods expire
  have h0 : Safe s board := by
    dsimp [board, GameState.expireShowdownMods]
    split
    · exact hm
    · exact Safe.refl s
  have h1 : Safe s (board.modObj bf
      (fun o => { o with contested := none })) :=
    h0.trans (Safe.modObj _ bf (fun _ => rfl) (fun _ => rfl))
  unfold endShowdown
  split
  · rename_i r hr
    split
    · exact SafeP.of_safe h1
    · have h2 := Safe.modObj (board.modObj bf
        (fun o => { o with contested := none })) bf
        (f := fun o => { o with control := some r }) (fun _ => rfl) (fun _ => rfl)
      by_cases hc : s.controlOf bf = none
      · simp only [hc, ite_true]
        exact SafeP.trans_safe ((h1.trans h2).trans (addTurnFxOn_safe _ _ _ _))
          (scoreBf_safeP _ _ _ _)
      · simp only [hc, ite_false]
        exact SafeP.trans_safe (h1.trans h2) (scoreBf_safeP _ _ _ _)
  · split
    · exact SafeP.of_safe (h1.trans (Safe.modObj _ bf (fun _ => rfl) (fun _ => rfl)))
    · exact SafeP.of_safe h1
  · exact SafeP.of_safe h1

/-- A Standard Move can only be made in the Main Phase (CR 144, 316). -/
theorem moveOk_main {s : GameState} {p : PlayerId} {u : ObjId} {d : MoveDest}
    (h : moveOk s p u d = true) : s.phase = .main := by
  unfold moveOk at h
  split at h
  · exact absurd h (by simp)
  · cases d <;> simp only [Bool.and_eq_true, decide_eq_true_eq] at h <;> exact h.1.1.1.1.2

/-- The frames scoring asks for are a draw for the player who scores. -/
theorem scoreBf_frames (s : GameState) (r : PlayerId) (bf : ObjId) (c : Bool) :
    ∀ f ∈ (scoreBf s r bf c).2.1, f = Frame.draw r 1 := by
  intro f hf
  unfold scoreBf at hf
  split at hf
  · simp at hf
  · split at hf
    · simp at hf
    · dsimp only at hf
      split at hf
      · simp at hf
      · split at hf
        · simpa using hf
        · split at hf
          · simpa using hf
          · simp at hf

/-- The frames the end of a Showdown asks for are draws. -/
theorem endShowdown_frames (s : GameState) (bf : ObjId) (expire : Bool := true) :
    ∀ f ∈ (endShowdown s bf expire).2.1, ∃ r, f = Frame.draw r 1 := by
  intro f hf
  unfold endShowdown at hf
  dsimp only at hf
  split at hf
  · rename_i r hr
    split at hf
    · simp at hf
    · exact ⟨r, scoreBf_frames _ _ _ _ f hf⟩
  · split at hf <;> simp at hf
  · simp at hf

/-- What the `cleanup` frame does, in the cases the invariants look at. -/
theorem cleanupFrame_cases (s : GameState) (rest : List Frame) :
    (∃ w, (cleanupFrame s rest).1 = { s with result := some (.won [w]), pending := [] }) ∨
    (∃ u p a b, (cleanupFrame s rest).1 =
      { s with pending := .eitherDo p u {} a b .nil :: .cleanup :: rest }) ∨
    (∃ r, Safe s r ∧ (cleanupFrame s rest).1 = { r with pending := .cleanup :: rest }) ∨
    (∃ bf q, (cleanupFrame s rest).1 =
      { s with
        pending := .showdown bf q 0 :: .cleanup :: rest,
        combat := (s.observeCombat (.showdown bf q 0 :: .cleanup :: rest)).1 }) ∨
    (cleanupFrame s rest).1 = { s with pending := rest, combat := (s.observeCombat rest).1 } := by
  unfold cleanupFrame
  split
  · rename_i w hw
    exact Or.inl ⟨w, rfl⟩
  · split
    · exact Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)
    · split
      · rename_i r hr
        exact Or.inr (Or.inr (Or.inl ⟨r.1, cleanupStep_safe (s' := r.1) (es := r.2) hr, rfl⟩))
      · split
        · rename_i bf q hq
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨bf, q, rfl⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- What the winner has: the Victory Score and more points than every other player. -/
theorem winner_spec {s : GameState} {w : PlayerId} (h : s.winner = some w) :
    s.victoryScore ≤ s.pointsOf w ∧
      ∀ q ∈ s.players, q ≠ w → s.pointsOf q < s.pointsOf w := by
  unfold GameState.winner at h
  have := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at this
  refine ⟨this.1, fun q hq hne => ?_⟩
  rcases this.2 q hq with h1 | h1
  · exact absurd (by simpa using h1) hne
  · simpa using h1

/-- **I7** (roadmap.md). At most one player satisfies the condition for winning: two players cannot
both have more points than each other (CR 323.1). -/
theorem win_condition_unique {s : GameState} {p q : PlayerId}
    (hp : ∀ x ∈ s.players, x ≠ p → s.pointsOf x < s.pointsOf p) (hq : p ∈ s.players)
    (hq2 : ∀ x ∈ s.players, x ≠ q → s.pointsOf x < s.pointsOf q) (hq3 : q ∈ s.players) :
    p = q := by
  by_cases hne : p = q
  · exact hne
  · have h1 := hp q hq3 (fun e => hne e.symm)
    have h2 := hq2 p hq hne
    omega

/-! ### What the rules guarantee -/

/-- Scoring a Battlefield a player has already scored this turn does nothing (CR 472). -/
theorem scoreBf_of_scored {s : GameState} {r : PlayerId} {bf : ObjId} {c : Bool}
    (h : ((s.obj? bf).map (·.scored.contains r)) = some true) :
    scoreBf s r bf c = (s, [], []) := by
  unfold scoreBf
  cases ho : s.obj? bf with
  | none => simp [ho] at h
  | some o =>
    rw [ho] at h
    have h' : o.scored.contains r = true := by simpa using h
    simp only [h', ↓reduceIte]

/-- Scoring a Battlefield marks it as scored by the player (CR 472). -/
theorem scoreBf_marks {s : GameState} {r : PlayerId} {bf : ObjId} {c : Bool} {o : Object}
    (h : s.obj? bf = some o) :
    (((scoreBf s r bf c).1.obj? bf).map (·.scored.contains r)) = some true := by
  unfold scoreBf
  simp only [h]
  split
  · rename_i hc
    show ((s.obj? bf).map _) = some true
    rw [h]
    have hm : r ∈ o.scored := by simpa using hc
    simp [hm]
  · split
    · rw [GameState.obj?_modObj]
      simp [h]
    · split
      · rw [GameState.obj?_modObj]
        simp [h]
      · split <;>
          (show (((s.modObj bf _).obj? bf).map _) = some true
           rw [GameState.obj?_modObj]
           simp [h])

/-- **I11** (roadmap.md). A player scores a Battlefield at most once in a turn: scoring it a second
time changes nothing, whichever way it is scored (CR 472, 473). -/
theorem scoreBf_twice {s : GameState} {r : PlayerId} {bf : ObjId} {c c' : Bool} {o : Object}
    (h : s.obj? bf = some o) :
    scoreBf (scoreBf s r bf c).1 r bf c' = ((scoreBf s r bf c).1, [], []) :=
  scoreBf_of_scored (scoreBf_marks h)

/-- A settled state has no Unit with lethal damage in play: the Cleanup has killed them
(CR 323.4). -/
theorem Settled.no_lethal {s : GameState} (h : s.Settled) :
    ∀ u ∈ s.inPlay, s.isUnit u = true → s.lethal u = false := by
  intro u hu hunit
  refine Classical.byContradiction (fun hl => ?_)
  have hl' : s.lethal u = true := by simpa using hl
  have hfind : (s.inPlay.find? (fun u => s.isUnit u && s.lethal u)).isSome := by
    rw [List.find?_isSome]
    exact ⟨u, hu, by simp [hunit, hl']⟩
  obtain ⟨-, hn⟩ := h
  have hn := cleanupStep0_of_none hn
  unfold cleanupStep0 at hn
  cases hf : s.inPlay.find? (fun u => s.isUnit u && s.lethal u) with
  | none => rw [hf] at hfind; simp at hfind
  | some v => rw [hf] at hn; simp at hn

/-- A settled state has no Battlefield controlled by a player who has no Unit there (CR 323.5). -/
theorem Settled.no_lostControl {s : GameState} (h : s.Settled) :
    ∀ b ∈ s.battlefields, s.lostControl b = false := by
  intro b hb
  refine Classical.byContradiction (fun hl => ?_)
  have hl' : s.lostControl b = true := by simpa using hl
  obtain ⟨-, hn⟩ := h
  have hn := cleanupStep0_of_none hn
  unfold cleanupStep0 at hn
  cases hf : s.inPlay.find? (fun u => s.isUnit u && s.lethal u) with
  | some v => rw [hf] at hn; simp at hn
  | none =>
    rw [hf] at hn
    have hfind : (s.battlefields.find? (fun b => s.lostControl b)).isSome := by
      rw [List.find?_isSome]
      exact ⟨b, hb, hl'⟩
    cases hg : s.battlefields.find? (fun b => s.lostControl b) with
    | none => rw [hg] at hfind; simp at hfind
    | some v => rw [hg] at hn; simp at hn

/-- **I17, locally.** When the `cleanup` frame finishes without starting a Showdown, the state is
settled: no winner is left to declare and no step applies (CR 322-323). The statement for every
reachable state with a `priority` frame on top is not proved yet (roadmap.md). -/
theorem cleanupFrame_pop_settled {s : GameState} {rest : List Frame}
    (h : s.Settled) (hn : s.startShowdown rest = none) :
    cleanupFrame s rest = continueAfterCleanup s rest := by
  obtain ⟨hw, hs⟩ := h
  have hchoice : cleanupDeathBanishChoice s = none := by
    cases ht : s.offBoardToken <;> cases hg : s.looseGear <;>
      simp [cleanupDeathBanishChoice, ht, hg]
    have hs0 : cleanupStep0 s = none := by
      simpa [cleanupStep, tokenStep, detachStep, ht, hg] using hs
    unfold cleanupStep0 at hs0
    split at hs0
    · contradiction
    · rename_i hfind
      simp [hfind]
  unfold cleanupFrame
  rw [hw, hchoice, hs, hn]

end Riftbound

end
