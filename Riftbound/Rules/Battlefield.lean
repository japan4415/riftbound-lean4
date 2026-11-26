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

/-- Whether an object occupies a Unit's place, including an animated Gear. -/
def isUnit (s : GameState) (id : ObjId) : Bool :=
  (s.printedCardDef? id).any (·.hasType .unit) || (s.obj? id).any (fun o => !o.unitGearEffects.isEmpty)

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

/-- Combat requires exactly two opposing players at a Battlefield (CR 316.7.a, 464). -/
def combatantsAt (s : GameState) (bf : ObjId) : Option (PlayerId × PlayerId) :=
  match s.players.filter (fun p => !(s.unitsOf p bf).isEmpty) with
  | [a, b] => if s.config.mode.sameSide a b then none else some (a, b)
  | _ => none

/-- The player who controls a Battlefield, if any (CR 190.6). -/
def controlOf (s : GameState) (bf : ObjId) : Option PlayerId := (s.obj? bf).bind (·.control)

/-- An object of another player than `q` in play has the passive ability that any amount of its
damage is enough to kill the units of `q` (Elder Dragon). -/
def anyDamageKills (s : GameState) (q : PlayerId) : Bool :=
  s.inPlay.any (fun g =>
    (s.obj? g).any (fun o => !s.config.mode.sameSide q o.controller) &&
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
        (decide (bf ∈ s.battlefields) && s.effectMoveBattlefieldOk o bf) &&
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

/-- Relocate all the declared Units in a single transition. Cleanup and triggers run only after
the group is in place (CR 144.3). -/
def applyGroupMoves (p : PlayerId) (d : MoveDest) : List ObjId → GameState →
    Option (GameState × List Event)
  | [], s => some (s, [])
  | u :: us, s => do
    let (next, events) ← applyMove s p u d
    let (final, laterEvents) ← applyGroupMoves p d us next
    pure (final, events ++ laterEvents)

/-- Commit the whole move and pay the destination fee once (CR 144.3.c, 203). -/
def applyGroupMove (s : GameState) (p : PlayerId) (d : MoveDest) (pay : Cost)
    (units : List ObjId) : Option (GameState × List Event) :=
  (if pay == Cost.zero then some s else (s.spendSymbols p pay false).map (s.setPool p)).bind
    (applyGroupMoves p d units)

/-- The Units a player might move: those on their Base and those at Battlefields. -/
def GameState.movable (s : GameState) (p : PlayerId) : List ObjId :=
  s.zone (.player p .base) ++ s.zone .battlefieldZone

/-- The destinations a Unit might be moved to: the Base and each Battlefield. -/
def GameState.destinations (s : GameState) : List MoveDest :=
  .base :: s.battlefields.map MoveDest.battlefield

/-- Eligible Units for a shared Standard Move destination. Origins may differ (CR 144.3.b). -/
def GameState.groupMoveChoices (s : GameState) (p : PlayerId) (d : MoveDest) : List ObjId :=
  ((s.movable p).filter (fun u => moveOk s p u d)).eraseDups

theorem GameState.groupMoveChoices_main {s : GameState} {p : PlayerId} {d : MoveDest}
    (h : 2 ≤ (s.groupMoveChoices p d).length) : s.phase = .main := by
  cases hc : s.groupMoveChoices p d with
  | nil => simp [hc] at h
  | cons u us =>
    have hu : u ∈ s.groupMoveChoices p d := by simp [hc]
    have ok := (List.mem_filter.mp (List.mem_eraseDups.mp hu)).2
    unfold moveOk at ok
    split at ok
    · contradiction
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
      exact ok.1.1.1.1.2

/-- A proposed group can make the Standard Move. Check the whole group before paying the fee or
running any effects (CR 144.3). -/
def GameState.groupMoveReady (s : GameState) (p : PlayerId) (d : MoveDest) (pay : Cost)
    (units : List ObjId) : Bool :=
  decide (2 ≤ units.length ∧ units.Nodup ∧ pay ∈ s.standardMovePayments p d) &&
    units.all (fun u => moveOk s p u d) && (applyGroupMove s p d pay units).isSome

/-- A Standard Move can be declared with a common destination and fee, without enumerating every
subset of eligible Units. -/
def legalGroupMoveStarts (s : GameState) (p : PlayerId) : List Action :=
  ((s.destinations).filter (fun d => 2 ≤ (s.groupMoveChoices p d).length)).flatMap (fun d =>
    (s.standardMovePayments p d).map (fun pay => ⟨.player p, .startGroupMove d pay⟩))

theorem mem_legalGroupMoveStarts {s : GameState} {p : PlayerId} {a : Action} :
    a ∈ legalGroupMoveStarts s p ↔ ∃ d pay, a = ⟨.player p, .startGroupMove d pay⟩ ∧
      d ∈ s.destinations ∧ 2 ≤ (s.groupMoveChoices p d).length ∧ pay ∈ s.standardMovePayments p d := by
  simp only [legalGroupMoveStarts, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨d, ⟨hd, hn⟩, pay, hp, rfl⟩
    exact ⟨d, pay, rfl, hd, hn, hp⟩
  · rintro ⟨d, pay, rfl, hd, hn, hp⟩
    exact ⟨d, ⟨hd, hn⟩, pay, hp, rfl⟩

/-- The Standard Moves a player can make. -/
def legalMoves (s : GameState) (p : PlayerId) : List Action :=
  let priced := s.destinations.map (fun d => (d, s.standardMovePayments p d))
  (s.movable p).flatMap (fun u =>
    (priced.filter (fun (d, _) => moveOk s p u d)).flatMap (fun (d, pays) =>
      pays.map (fun pay => ⟨.player p, .standardMove u d pay⟩)))

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
        exact Or.inr ⟨bf, h.2.1.1, rfl⟩

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
      ∃ u d pay, a = ⟨.player p, .standardMove u d pay⟩ ∧
        moveOk s p u d = true ∧ pay ∈ s.standardMovePayments p d := by
  unfold legalMoves
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨u, -, ⟨d, pays⟩, ⟨⟨d', _, hp⟩, hm⟩, pay, hf, rfl⟩
    cases hp
    exact ⟨u, d, pay, rfl, hm, hf⟩
  · rintro ⟨u, d, pay, rfl, hd, hpay⟩
    obtain ⟨hu, hdm⟩ := moveOk_mem hd
    exact ⟨u, hu, (d, _), ⟨⟨d, hdm, rfl⟩, hd⟩, pay, hpay, rfl⟩

/-! ### Scoring -/

/-- Whether the Battlefield has been scored by the player's side this turn (CR 472, 491.8.b). -/
def Object.scoredFor (o : Object) (mode : Mode) (p : PlayerId) : Bool :=
  o.scored.any (mode.sameSide p)

/-- A teammate's control at the scoring step disqualifies the Battlefield for this side. -/
def GameState.teamScoreBlocked (s : GameState) (p : PlayerId) (bf : ObjId) : Bool :=
  s.config.mode.isTeamDuel && s.turnFx.any (fun note =>
    note.turn == s.turn && note.target == some bf && note.kind == .teamHeldAtScoring &&
      s.config.mode.sameSide p note.who)

/-- Whether this side's score on a Battlefield is already spent or is disqualified. -/
def GameState.scoringUnavailable (s : GameState) (p : PlayerId) (bf : ObjId) : Bool :=
  s.teamScoreBlocked p bf || (s.obj? bf).any (·.scoredFor s.config.mode p)

/-- An ally's occupation at the scoring step satisfies the Final Point requirement during a
turn of that side (CR 491.8.g.1). Other Battlefields must have been scored by this player. -/
def GameState.battlefieldCountsForFinalPoint (s : GameState) (p : PlayerId) (bf : ObjId) : Bool :=
  (s.obj? bf).any (·.scored.contains p) ||
    (s.config.mode.isTeamDuel && s.active.any (s.config.mode.sameSide p) && s.turnFx.any (fun note =>
      note.turn == s.turn && note.target == some bf && note.kind == .teamOccupiedAtScoring &&
        s.config.mode.sameSide p note.who && p != note.who))

/-- Score the Battlefield for a player whose side has yet to score it this turn (CR 471-472).
Conquering for the final point checks which Battlefields the side scored (CR 473.1.b, 491.8.g). -/
def scoreBf (s : GameState) (r : PlayerId) (bf : ObjId) (conquer : Bool) :
    GameState × List Frame × List Event :=
  match s.obj? bf with
  | none => (s, [], [])
  | some _ =>
    if s.scoringUnavailable r bf then (s, [], [])
    else
      let s1 := s.modObj bf (fun o => { o with scored := r :: o.scored })
      let all := s1.battlefields.all (s1.battlefieldCountsForFinalPoint r)
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
    decide (s.controlOf b = some tp) && !s.scoringUnavailable tp b)

/-- Remember control and occupation at the scoring step for the rest of the turn. -/
def GameState.rememberTeamScoring (s : GameState) (tp : PlayerId) : GameState :=
  if s.config.mode.isTeamDuel then
    let notes := s.battlefields.flatMap (fun bf =>
      let note (who : PlayerId) (kind : TurnEffect) : TurnFx :=
        { who, kind, target := some bf, turn := s.turn, stamp := s.nextTimestamp }
      let held := (s.controlOf bf).toList.filter (fun p => p != tp && s.config.mode.sameSide tp p)
      let occupied := (s.config.mode.sideSeats tp).filter (fun p => !(s.unitsOf p bf).isEmpty)
      held.map (fun p => note p .teamHeldAtScoring) ++ occupied.map (fun p => note p .teamOccupiedAtScoring))
    { s with turnFx := s.turnFx ++ notes }
  else s

/-- Remembering scoring-step circumstances changes neither the board nor the current decision. -/
theorem GameState.rememberTeamScoring_safe (s : GameState) (tp : PlayerId) :
    Safe s (s.rememberTeamScoring tp) := by
  unfold rememberTeamScoring
  split
  · exact ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
      fun _ hown => hown.congr rfl rfl, rfl⟩
  · exact Safe.refl s

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
    s'.modObj b (markScored tp (!replace && !s.cantScoreHere tp b))) (s.rememberTeamScoring tp)
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
      s.players.all (fun q => s.config.mode.sameSide p q || decide (s.pointsOf q < s.pointsOf p)))

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
      let healed := s.modObj u (fun o => { o with damage := 0, exhausted := true })
      let p := ((s.obj? u).map (·.controller)).getD ⟨0⟩
      (finishDeathSave healed u p (s.deathSaveMark u false none), [])
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
        (fun _ => rfl) (fun _ => rfl)).trans
          (finishDeathSave_safe _ u _ _)
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

/-- An Equipment whose recipient left the Board (CR 137.3.b). -/
def GameState.looseGear (s : GameState) : Option ObjId :=
  s.inPlay.find? (fun g => (s.obj? g).any (fun o =>
    match o.attached with
    | some u => !(s.inPlay.contains u)
    | none => false))

/-- The step of the Cleanup for an Equipment whose Unit is gone: it is not attached any more
(CR 137). -/
def detachStep (s : GameState) : Option (GameState × List Event) :=
  s.looseGear.map (fun g => (s.modObj g (fun o => { o with attached := none }), []))

/-- Additional Legends whose source left the Board return to their owner's reserve. -/
def GameState.expiredReservedLegend (s : GameState) : Option (PlayerId × ObjId) :=
  s.players.findSome? (fun p =>
    ((s.zone (.player p .legendZone)).find? (fun id =>
      (s.obj? id).any (fun o => o.reservedBy.any (fun src => !s.inPlay.contains src)))).map (p, ·))

/-- Return an additional Legend when the duration that keeps it in the game ends. -/
def returnReservedLegendStep (s : GameState) : Option (GameState × List Event) := do
  let (p, id) ← s.expiredReservedLegend
  let dest := Zone.player p .reserveLegends
  let (t, next) ← moveObj s id dest
  return (t, [.moved id next dest])

theorem returnReservedLegendStep_safe {s t : GameState} {events : List Event}
    (h : returnReservedLegendStep s = some (t, events)) : Safe s t := by
  unfold returnReservedLegendStep at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨p, id⟩, -, ⟨result, next⟩, moved, resultEq⟩ := h
  have he : result = t := (Prod.mk.inj (Option.some.inj resultEq)).1
  subst t
  exact Safe.moveObj moved

/-- One step of the Cleanup (CR 323): a token off the Board ceases to exist (CR 183), an Equipment
whose Unit is gone is detached (CR 137), or else the first step of `cleanupStep0`. `none` if none
applies. -/
def cleanupStep (s : GameState) : Option (GameState × List Event) :=
  match tokenStep s with
  | some r => some r
  | none =>
    match detachStep s with
    | some r => some r
    | none => (returnReservedLegendStep s).orElse (fun _ => cleanupStep0 s)

/-- Staged Showdowns in a Neutral Open state, with the player who made each Battlefield Contested.
In team play, non-combat Showdowns are chosen and opened before Combat (CR 323.11, 323.12). -/
def GameState.stagedShowdowns (s : GameState) (rest : List Frame) : List (ObjId × PlayerId) :=
  match rest with
  | .priority _ :: _ =>
    let candidates := s.battlefields.filterMap (fun b => ((s.obj? b).bind (·.contested)).map (b, ·))
    if s.config.mode.isTeamDuel then
      let openFields := candidates.filter (fun (b, _) => (s.combatantsAt b).isNone)
      if openFields.isEmpty then candidates else openFields
    else candidates
  | _ => []

/-- The first staged Showdown, when there is one. -/
def GameState.startShowdown (s : GameState) (rest : List Frame) : Option (ObjId × PlayerId) :=
  (s.stagedShowdowns rest).head?

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
      match s.combatantsAt bf with
      | some (a, b) =>
        let contested := ((s.obj? bf).bind (·.contested)).getD focus
        let (att, def_) := if contested == b then (b, a) else (a, b)
        (some
          { battlefield := bf
            attacker := att
            defender := def_
            units := s.unitsOf att bf ++ s.unitsOf def_ bf },
          [Event.combatStarted bf att])
      | none => (none, [])
    | none => (none, [])

/-- Leave a settled Cleanup and update whether Combat has started or gained participants. -/
def continueAfterCleanup (s : GameState) (pending : List Frame) : GameState × List Event :=
  let r := s.observeCombat pending
  ({ s with pending := pending, combat := r.1 }, r.2)

/-- Collect simultaneous lethal deaths after higher-priority Cleanup matters (CR 323). -/
def cleanupDeathGroup (s : GameState) : List ObjId :=
  if s.offBoardToken.isSome || s.looseGear.isSome || s.expiredReservedLegend.isSome then [] else
    s.inPlay.filter (fun u => s.isUnit u && s.lethal u)

/-- Offer decisions associated with the simultaneous deaths (CR 372-373). -/
def cleanupDeathBanishChoice (s : GameState) : Option (ObjId × PlayerId × Effect × Effect) :=
  s.deathGroupChoice (cleanupDeathGroup s)

/-- A survival replacement can itself alter the death that pays for it. -/
def hasNestedDeath (s : GameState) (victim : ObjId) : Bool :=
  (s.deathSaver victim).join.any (fun cost => (s.deathSaveFor cost []).isSome)

/-- The individual death when resolving a Cleanup group. -/
def cleanupResolveDeath (s : GameState) (victim : ObjId) : GameState × List Event :=
  if hasNestedDeath s victim then killOrSave s victim else cleanupKill s victim

theorem cleanupResolveDeath_safe (s : GameState) (victim : ObjId) :
    Safe s (cleanupResolveDeath s victim).1 := by
  unfold cleanupResolveDeath
  split
  · exact killOrSave_safe s victim
  · exact cleanupKill_safe s victim

/-- The automatic Cleanup handles a single death. A simultaneous group or a nested replacement
must complete all of its decisions together. -/
def cleanupResolveDeathGroup (s : GameState) : Option (GameState × List Event) :=
  let ids := cleanupDeathGroup s
  if 1 < ids.length || ids.any (hasNestedDeath s) then
    some (resolveDeathGroupWith s ids cleanupResolveDeath)
  else none

theorem cleanupResolveDeathGroup_safe {s : GameState} {r : GameState × List Event}
    (h : cleanupResolveDeathGroup s = some r) : Safe s r.1 := by
  unfold cleanupResolveDeathGroup at h
  dsimp only at h
  split at h
  · cases h
    exact resolveDeathGroupWith_safe s _ cleanupResolveDeath_safe
  · contradiction

/-- The step of the `cleanup` frame (CR 322-323): declare a winner, or do a step, or start a
Showdown, or finish. -/
def cleanupFrame (s : GameState) (rest : List Frame) : GameState × List Event :=
  match s.winner with
  | some w =>
    let seats := s.config.mode.sideSeats w
    ({ s with result := some (.won seats), pending := [] }, seats.map Event.won)
  | none =>
    match cleanupDeathBanishChoice s with
    | some (u, controller, first, other) =>
      ({ s with pending := .eitherDo controller u {} first other .nil :: .cleanup :: rest }, [])
    | none =>
      match cleanupResolveDeathGroup s with
      | some r => ({ r.1 with pending := .cleanup :: rest }, r.2)
      | none =>
        match cleanupStep s with
        | some r => ({ r.1 with pending := .cleanup :: rest }, r.2)
        | none =>
          match s.stagedShowdowns rest with
          | (bf, q) :: more =>
            if s.config.mode.isTeamDuel && !more.isEmpty then
              ({ s with pending := .chooseShowdown (s.active.getD q) (bf, q) more :: rest }, [])
            else continueAfterCleanup s (.showdown bf q 0 :: .cleanup :: rest)
          | [] => continueAfterCleanup s rest

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

theorem applyGroupMoves_safe (p : PlayerId) (d : MoveDest) :
    ∀ (units : List ObjId) {s s' : GameState} {events : List Event},
      applyGroupMoves p d units s = some (s', events) → Safe s s'
  | [], _, _, _, h => by
    cases h
    exact Safe.refl _
  | u :: us, s, s', events, h => by
    simp only [applyGroupMoves, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨mid, first⟩, moved, ⟨final, last⟩, remaining, result⟩ := h
    cases result
    exact (applyMove_safe moved).trans (applyGroupMoves_safe p d us remaining)

theorem applyGroupMove_safe {s s' : GameState} {p : PlayerId} {d : MoveDest}
    {pay : Cost} {units : List ObjId} {events : List Event}
    (h : applyGroupMove s p d pay units = some (s', events)) : Safe s s' := by
  simp only [applyGroupMove, Option.bind_eq_some_iff] at h
  obtain ⟨paid, hp, hd⟩ := h
  have paidSafe : Safe s paid := by
    split at hp
    · cases hp
      exact Safe.refl s
    · obtain ⟨pool, -, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact setPool_safe s p pool
  exact paidSafe.trans (applyGroupMoves_safe p d units hd)

/-- When no step applies, the steps of `cleanupStep0` do not apply either. -/
theorem cleanupStep0_of_none {s : GameState} (h : cleanupStep s = none) :
    cleanupStep0 s = none := by
  unfold cleanupStep at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · cases hr : returnReservedLegendStep s <;> simp_all [Option.orElse]

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
    · cases hreturn : returnReservedLegendStep s with
      | none => exact cleanupStep0_safe (by simpa [hreturn, Option.orElse] using h)
      | some result => exact returnReservedLegendStep_safe (by simpa [hreturn, Option.orElse] using h)

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
  have h := (GameState.rememberTeamScoring_safe s tp).trans (foldl_modObj_safe'
    (g := fun b => markScored tp (!s.drawForBattlefieldPoint tp && !s.cantScoreHere tp b))
    (fun _ _ => rfl) (fun _ _ => rfl) (s.holds tp) (s.rememberTeamScoring tp))
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
    (∃ w, (cleanupFrame s rest).1 =
      { s with result := some (.won (s.config.mode.sideSeats w)), pending := [] }) ∨
    (∃ u p a b, (cleanupFrame s rest).1 =
      { s with pending := .eitherDo p u {} a b .nil :: .cleanup :: rest }) ∨
    (∃ r, Safe s r ∧ (cleanupFrame s rest).1 = { r with pending := .cleanup :: rest }) ∨
    (∃ bf q, (cleanupFrame s rest).1 =
      { s with
        pending := .showdown bf q 0 :: .cleanup :: rest,
        combat := (s.observeCombat (.showdown bf q 0 :: .cleanup :: rest)).1 }) ∨
    (∃ p first more, (cleanupFrame s rest).1 = { s with pending := .chooseShowdown p first more :: rest }) ∨
    (cleanupFrame s rest).1 = { s with pending := rest, combat := (s.observeCombat rest).1 } := by
  unfold cleanupFrame
  split
  · rename_i w hw
    exact Or.inl ⟨w, rfl⟩
  · split
    · exact Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)
    · split
      · rename_i result hr
        exact Or.inr (Or.inr (Or.inl ⟨result.1, cleanupResolveDeathGroup_safe hr, rfl⟩))
      · split
        · rename_i r hr
          exact Or.inr (Or.inr (Or.inl ⟨r.1, cleanupStep_safe (s' := r.1) (es := r.2) hr, rfl⟩))
        · split
          · split
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- A winning seat reaches the Victory Score and leads every opposing seat. -/
theorem winner_spec {s : GameState} {w : PlayerId} (h : s.winner = some w) :
    s.victoryScore ≤ s.pointsOf w ∧
      ∀ q ∈ s.players, s.config.mode.sameSide w q = false → s.pointsOf q < s.pointsOf w := by
  unfold GameState.winner at h
  have := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at this
  refine ⟨this.1, fun q hq hne => ?_⟩
  rcases this.2 q hq with h1 | h1
  · simp [hne] at h1
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

/-- Scoring a Battlefield unavailable to a player's side does nothing (CR 472, 491.8.b). -/
theorem scoreBf_of_scored {s : GameState} {r : PlayerId} {bf : ObjId} {c : Bool}
    (h : s.scoringUnavailable r bf = true) :
    scoreBf s r bf c = (s, [], []) := by
  unfold scoreBf
  cases ho : s.obj? bf with
  | none => rfl
  | some _ => simp only [h, ↓reduceIte]

/-- Attempting to score a Battlefield leaves it unavailable to the player's side (CR 472). -/
theorem scoreBf_marks {s : GameState} {r : PlayerId} {bf : ObjId} {c : Bool} {o : Object}
    (h : s.obj? bf = some o) :
    (scoreBf s r bf c).1.scoringUnavailable r bf = true := by
  have marked : (s.modObj bf (fun o => { o with scored := r :: o.scored })).scoringUnavailable r bf = true := by
    unfold GameState.scoringUnavailable
    rw [GameState.obj?_modObj]
    simp [h, Object.scoredFor, GameState.modObj]
  unfold scoreBf
  simp only [h]
  split
  · rename_i hc
    exact hc
  · split
    · exact marked
    · split
      · exact marked
      · split <;> exact marked

/-- **I11** (roadmap.md). A side scores a Battlefield at most once in a turn (CR 472, 491.8.b). -/
theorem scoreBf_twice_side {s : GameState} {r q : PlayerId} {bf : ObjId} {c c' : Bool} {o : Object}
    (h : s.obj? bf = some o) (side : s.config.mode.sameSide r q = true) :
    scoreBf (scoreBf s r bf c).1 q bf c' = ((scoreBf s r bf c).1, [], []) := by
  let next := (scoreBf s r bf c).1
  have hk : next.config.mode.scoringSeat r = next.config.mode.scoringSeat q := by
    rw [(scoreBf_safeP s r bf c).config]
    exact of_decide_eq_true side
  have hs : next.config.mode.sameSide r = next.config.mode.sameSide q := by
    funext p
    unfold Mode.sameSide
    rw [hk]
  apply scoreBf_of_scored
  change next.scoringUnavailable q bf = true
  unfold GameState.scoringUnavailable GameState.teamScoreBlocked Object.scoredFor
  rw [← hs]
  exact scoreBf_marks h

/-- Scoring the same Battlefield twice by a player is the single-seat case of I11. -/
theorem scoreBf_twice {s : GameState} {r : PlayerId} {bf : ObjId} {c c' : Bool} {o : Object}
    (h : s.obj? bf = some o) :
    scoreBf (scoreBf s r bf c).1 r bf c' = ((scoreBf s r bf c).1, [], []) :=
  scoreBf_twice_side h (Mode.sameSide_self _ _)

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
  have noneLethal : s.inPlay.find? (fun u => s.isUnit u && s.lethal u) = none := by
    have h0 := cleanupStep0_of_none hs
    cases hv : s.inPlay.find? (fun u => s.isUnit u && s.lethal u) with
    | none => rfl
    | some u => simp [cleanupStep0, hv] at h0
  have noGroup : cleanupDeathGroup s = [] := by
    have hfilter := List.filter_eq_nil_iff.mpr (List.find?_eq_none.mp noneLethal)
    simp [cleanupDeathGroup, hfilter]
  have noShowdowns : s.stagedShowdowns rest = [] := by
    cases staged : s.stagedShowdowns rest with
    | nil => rfl
    | cons first more => simp [GameState.startShowdown, staged] at hn
  simp [cleanupFrame, hw, cleanupDeathBanishChoice, cleanupResolveDeathGroup, noGroup, hs, noShowdowns]

end Riftbound

end
