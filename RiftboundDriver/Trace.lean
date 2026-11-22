module

public import Std.Data.HashSet
public import RiftboundDriver.Run
public import RiftboundDriver.Demo

/-!
# Driver: the trace of a game

Plays a game with the engine and writes down every answer as JSON: the answer, the events it
caused, and the state after it. A viewer replays the file as an animation (`viewer/`). The viewer
has no rules of its own: everything it shows was computed by `step`. This library is not part of
the verified core, so the JSON written here is not covered by the proofs (design.md §4).
-/

@[expose] public section

namespace RiftboundDriver

open Riftbound

/-- A JSON string. Names in the databases are plain text; quotes and backslashes are escaped. -/
def jstr (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

/-- A JSON array of already written items. -/
def jarr (l : List String) : String := "[" ++ ",".intercalate l ++ "]"

/-- A JSON object of already written values. -/
def jobj (l : List (String × String)) : String :=
  "{" ++ ",".intercalate (l.map fun (k, v) => jstr k ++ ":" ++ v) ++ "}"

/-- The last part of a dotted name: `Riftbound.Phase.main` is `main`. -/
def lastSeg (s : String) : String := (s.splitOn ".").getLast?.getD s

/-- The name of a constructor, from its `Repr`. -/
def ctorName {α : Type} [Repr α] (a : α) : String :=
  lastSeg (((reprStr a).takeWhile (fun c => !c.isWhitespace)).toString)

/-- A zone as text: `p0.hand`, `battlefield`, `chain`. -/
def zoneName : Zone → String
  | .player p k => s!"p{p.n}.{ctorName k}"
  | .battlefieldZone => "battlefield"
  | .chain => "chain"

/-- An action as JSON. -/
def actionJson (a : Action) : String :=
  let who := match a.actor with
    | .player p => s!"p{p.n}"
    | .chance => "chance"
    | .clock => "clock"
    | .judge => "judge"
  let kind := ctorName a.kind
  let extra : List (String × String) := match a.kind with
    | .runeAbility c ab => [("card", toString c.n), ("ability", jstr (ctorName ab))]
    | .playCard c pay ts =>
      [("card", toString c.n), ("pay", toString (pay.energy + pay.power.length)),
        ("targets", jarr (ts.map (fun t => toString t.n)))]
    | .standardMove u d =>
      [("unit", toString u.n),
       ("dest", match d with | .base => "null" | .battlefield bf => toString bf.n)]
    | .assignPick u => [("unit", toString u.n)]
    | .manaAbility src idx => [("source", toString src.n), ("index", toString idx)]
    | .putTrigger i ts =>
      [("index", toString i), ("targets", jarr (ts.map (fun t => toString t.n)))]
    | .activate src idx _ ts =>
      [("source", toString src.n), ("index", toString idx),
       ("targets", jarr (ts.map (fun t => toString t.n)))]
    | .mulliganPick c => [("card", toString c.n)]
    | .discardPick c => [("card", toString c.n)]
    | .burnOutTarget o => [("opponent", toString o.n)]
    | .pick i => [("index", toString i)]
    | _ => []
  jobj ([("actor", jstr who), ("kind", jstr kind)] ++ extra)

/-- An event as JSON. -/
def eventJson : Event → String
  | .moved o n dst =>
    jobj [("t", jstr "moved"), ("old", toString o.n), ("new", toString n.n),
      ("dst", jstr (zoneName dst))]
  | .pointsGained p n =>
    jobj [("t", jstr "points"), ("player", toString p.n), ("n", toString n)]
  | .burnedOut p => jobj [("t", jstr "burnout"), ("player", toString p.n)]
  | .skipped o => jobj [("t", jstr "skipped"), ("card", toString o.n)]
  | .damaged o n => jobj [("t", jstr "damaged"), ("target", toString o.n), ("n", toString n)]
  | .healed o n => jobj [("t", jstr "healed"), ("target", toString o.n), ("n", toString n)]
  | .readied o => jobj [("t", jstr "readied"), ("target", toString o.n)]
  | .exhausted o => jobj [("t", jstr "exhausted"), ("target", toString o.n)]
  | .standardMoved u d =>
    jobj [("t", jstr "moved_unit"), ("unit", toString u.n),
      ("dest", match d with | some bf => toString bf.n | none => "null")]
  | .controlChanged bf p =>
    jobj [("t", jstr "control"), ("battlefield", toString bf.n),
      ("player", match p with | some q => toString q.n | none => "null")]
  | .scored p bf conquer =>
    jobj [("t", jstr "scored"), ("player", toString p.n), ("battlefield", toString bf.n),
      ("conquer", if conquer then "true" else "false")]
  | .recalled u => jobj [("t", jstr "recalled"), ("unit", toString u.n)]
  | .won p => jobj [("t", jstr "won"), ("player", toString p.n)]
  | .played p o => jobj [("t", jstr "played"), ("player", toString p.n), ("obj", toString o.n)]
  | .died o p => jobj [("t", jstr "died"), ("obj", toString o.n), ("player", toString p.n)]
  | .combatStarted bf att =>
    jobj [("t", jstr "combat"), ("battlefield", toString bf.n), ("attacker", toString att.n)]
  | .activated p src idx =>
    jobj [("t", jstr "activated"), ("player", toString p.n), ("source", toString src.n),
      ("index", toString idx)]

/-- All the zones to show, with the player count. -/
def shownZones (n : Nat) : List Zone :=
  (allPlayers n).flatMap (fun p => ZoneKind.all.map (fun k => Zone.player p k)) ++
    [.battlefieldZone, .chain]

/-- The identifiers of all objects in the zones. -/
def shownIds (s : GameState) : List ObjId :=
  (shownZones s.playerCount).flatMap (fun z => s.zone z)

/-- A new object as JSON: its card, its owner, and its Rune domain. -/
def objJson (s : GameState) (id : ObjId) : String :=
  match s.obj? id with
  | some o =>
    let card := match o.kind with
      | .card _ c => c.code
      | .token c => c.code
      | .chainAbility c _ _ => c.code
    let ability : List (String × String) := match o.kind with
      | .chainAbility _ idx src => [("source", toString src.n), ("ability", toString idx)]
      | _ => []
    jobj ([("card", jstr card), ("owner", toString o.owner.n),
      ("rune", match o.runeDomain with | some d => jstr (ctorName d) | none => "null")] ++ ability)
  | none => "null"

/-- The Rune Pool of a player as JSON. -/
def poolJson (p : RunePool) : String :=
  jobj [("energy", toString p.energy), ("fury", toString p.fury), ("calm", toString p.calm),
    ("mind", toString p.mind), ("body", toString p.body), ("chaos", toString p.chaos),
    ("order", toString p.order), ("any", toString p.any)]

/-- The state as JSON. `seen` are the identifiers already sent: only new objects are described. -/
def stateJson (s : GameState) (seen : Std.HashSet Nat) : String × Std.HashSet Nat :=
  let ids := shownIds s
  let fresh := ids.filter (fun id => !seen.contains id.n)
  let seen' := fresh.foldl (fun acc id => acc.insert id.n) seen
  let zones := (shownZones s.playerCount).filterMap fun z =>
    match s.zone z with
    | [] => none
    | l => some (zoneName z, jarr (l.map (fun id => toString id.n)))
  let exhausted := ids.filter (fun id => (s.obj? id).any (·.exhausted))
  let damaged := ids.filterMap (fun id =>
    match s.obj? id with
    | some o => if 0 < o.damage then some (jarr [toString id.n, toString o.damage]) else none
    | none => none)
  let boosted := ids.filterMap (fun id =>
    match s.obj? id with
    | some _ =>
      let d : Int := match s.mightNow id, (s.cardDef? id).bind (·.might) with
        | some now, some printed => now - printed
        | _, _ => 0
      if d != 0 then some (jarr [toString id.n, toString d]) else none
    | none => none)
  let stunned := ids.filter (fun id => (s.obj? id).any (·.stunned))
  let attached := ids.filterMap (fun id =>
    match (s.obj? id).bind (·.attached) with
    | some u => some (jarr [toString id.n, toString u.n])
    | none => none)
  let players := allPlayers s.playerCount
  let bfs := s.battlefields.map (fun b =>
    jobj [("id", toString b.n),
      ("control", match s.controlOf b with | some p => toString p.n | none => "null"),
      ("contested", match (s.obj? b).bind (·.contested) with
        | some p => toString p.n | none => "null")])
  let locs := (s.zone .battlefieldZone).filterMap (fun u =>
    match (s.obj? u).bind (·.loc) with
    | some b => some (jarr [toString u.n, toString b.n])
    | none => none)
  let json := jobj [
    ("turn", toString s.turn), ("phase", jstr (ctorName s.phase)),
    ("active", match s.active with | some p => toString p.n | none => "null"),
    ("pending", match s.pending with | f :: _ => jstr (ctorName f) | [] => "null"),
    ("result", match s.result with
      | some (.won w) => jobj [("won", jarr (w.map (fun p => toString p.n)))]
      | some .draw => jstr "draw"
      | none => "null"),
    ("points", jarr (players.map (fun p => toString (s.pointsOf p)))),
    ("pools", jarr (players.map (fun p => poolJson (s.poolOf p)))),
    ("zones", jobj zones),
    ("battlefields", jarr bfs), ("at", jarr locs),
    ("new", jobj (fresh.map (fun id => (toString id.n, objJson s id)))),
    ("exhausted", jarr (exhausted.map (fun id => toString id.n))),
    ("damaged", jarr damaged), ("boosted", jarr boosted),
    ("attached", jarr attached),
    ("stunned", jarr (stunned.map (fun id => toString id.n)))]
  (json, seen')

/-- One step of the trace: the answer given (if any), its events, and the state after it. -/
def stepJson (i : Nat) (a : Option Action) (es : List Event) (s : GameState)
    (seen : Std.HashSet Nat) : String × Std.HashSet Nat :=
  let (st, seen') := stateJson s seen
  (jobj [("i", toString i),
    ("action", match a with | some a => actionJson a | none => "null"),
    ("events", jarr (es.map eventJson)), ("state", st)], seen')

/-- A card of the database as JSON. -/
def cardJson (c : CardDef) : String :=
  jobj [("name", jstr c.name), ("types", jarr (c.types.map (fun t => jstr (ctorName t)))),
    ("domains", jarr (c.domains.map (fun d => jstr (ctorName d)))),
    ("cost", match c.cost with | some k => toString k.energy | none => "null"),
    ("might", match c.might with | some m => toString m | none => "null")]

/-- The answer of the demo player in the Main Phase: play a card if one can be paid for, otherwise
send a Unit to a Battlefield, exhaust the Runes that are ready, recycle one Rune on even turns
when no Power is in the Pool, and pass. Everything else is answered as `autoAnswer` does. Only a
legal answer is chosen: the list of `legalActions` is searched. -/
def demoAnswer (r : Rng) (s : GameState) : Option (Action × Rng) :=
  match s.pending with
  | .priority p :: _ =>
    let legal := legalActions s
    let isAb (ab : RuneAbility) (a : Action) : Bool :=
      match a.kind with | .runeAbility _ ab' => ab' == ab | _ => false
    let isPlay (a : Action) : Bool :=
      match a.kind with | .playCard _ _ _ => true | _ => false
    let isGo (a : Action) : Bool :=
      match a.kind with | .standardMove _ (.battlefield _) => true | _ => false
    let isUse (a : Action) : Bool :=
      match a.kind with | .activate .. => true | _ => false
    let isMana (a : Action) : Bool :=
      match a.kind with | .manaAbility .. => true | _ => false
    match legal.find? isMana with
    | some a => some (a, r)
    | none =>
    -- exhaust the Runes that are ready first, so that the Pool can pay an additional cost; keep one
    -- ready to answer with a Reaction on the other player's turn
    let holdsReaction := (s.zone (.player p .hand)).any (reactSpell s)
    let exhausts := legal.filter (isAb .exhaust)
    match (if holdsReaction && exhausts.length ≤ 1 then none else exhausts.head?) with
    | some a => some (a, r)
    | none =>
    match legal.find? isPlay with
    | some a0 =>
      -- the same card and targets: pay the additional cost when there is one
      let payOf (a : Action) : Nat :=
        match a.kind with | .playCard _ pay _ => pay.energy + pay.power.length | _ => 0
      let same (a : Action) : Bool :=
        match a.kind, a0.kind with
        | .playCard c _ _, .playCard c0 _ _ => c == c0 && a.targetsOf == a0.targetsOf
        | _, _ => false
      let best := (legal.filter same).foldl (fun acc a => if payOf a > payOf acc then a else acc) a0
      some (best, r)
    | none =>
    match legal.find? isUse with
    | some a => some (a, r)
    | none =>
    match legal.find? isGo with
    | some a => some (a, r)
    | none =>
      if s.turn % 2 == 0 && (s.poolOf p).fury == 0 then
        match legal.find? (isAb .recycle) with
        | some a => some (a, r)
        | none => some (⟨.player p, .pass⟩, r)
      else some (⟨.player p, .pass⟩, r)
  | .chainPass p _ :: _ =>
    -- answer an item of the opponent: cast a Reaction if one can be paid for, or exhaust a Rune
    -- when one is in the hand
    let legal := legalActions s
    let isPlay (a : Action) : Bool :=
      match a.kind with | .playCard _ _ _ => true | _ => false
    let isExhaust (a : Action) : Bool :=
      match a.kind with | .runeAbility _ .exhaust => true | _ => false
    let holdsReaction := (s.zone (.player p .hand)).any (reactSpell s)
    if s.active == some p then some (⟨.player p, .pass⟩, r)
    else
      match legal.find? isPlay with
      | some a => some (a, r)
      | none =>
        if holdsReaction && (s.poolOf p).energy == 0 then
          match legal.find? isExhaust with
          | some a => some (a, r)
          | none => some (⟨.player p, .pass⟩, r)
        else some (⟨.player p, .pass⟩, r)
  | _ => autoAnswer r s

/-- Play with `demoAnswer` until the turn player passes in turn `turns`, or `n` answers. The steps
of the trace come back in reverse order. -/
def playTrace (turns : Nat) (cap : Option Nat := none) :
    Nat → Nat → Rng → GameState → Std.HashSet Nat → List String →
      Except RuleError (List String)
  | 0, _, _, _, _, acc => .ok acc
  | n + 1, i, r, s, seen, acc =>
    match (if (cap.any (· ≤ s.turn)) && s.clock.isNone && s.active.isSome && s.result.isNone then
        some (⟨.clock, .timeCalled⟩, r)
      else demoAnswer r s) with
    | none => .ok acc
    | some (a, r') =>
      match step 100 s a with
      | .error e => .error e
      | .ok (s', es) =>
        let (j, seen') := stepJson i (some a) es s' seen
        let atPriority := match s.pending with | .priority _ :: _ => true | _ => false
        if a.kind == .pass && atPriority && turns ≤ s.turn then .ok (j :: acc)
        else playTrace turns cap n (i + 1) r' s' seen' (j :: acc)

/-- The whole trace of a demo game of `turns` turns from `seed`, as JSON. With `timed`, the game is
played under the Tournament Rules, and the clock calls time when `turns` turns have begun: the
game goes on to its end (TR 408.2). -/
def demoTrace (seed turns : Nat) (timed : Bool := false) : Except String String :=
  match GameState.initial demoDB
      (if timed then { ruleSet := .tournament .constructed, mode := Mode.duel } else demoConfig)
      [demoDeck, demoDeck] with
  | none => .error "the demo game cannot be set up"
  | some s0 =>
    let (j0, seen) := stepJson 0 none [] s0 {}
    match playTrace (if timed then 100000 else turns) (if timed then some turns else none)
        100000 1 (Rng.ofSeed seed) s0 seen [j0] with
    | .error e => .error s!"the engine refused an answer: {repr e}"
    | .ok acc =>
      .ok (jobj [("seed", toString seed), ("players", toString s0.playerCount),
        ("cards", jobj (demoCards.map (fun c => (c.id.code, cardJson c)))),
        ("steps", jarr acc.reverse)])

end RiftboundDriver

end
