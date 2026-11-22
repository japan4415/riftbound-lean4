import RiftboundDriver.Live

open RiftboundDriver Riftbound

/-- The players named by `01`, `0` or `1`. -/
def parseHumans (s : String) : List PlayerId :=
  s.toList.filterMap (fun c =>
    if c == '0' then some ⟨0⟩ else if c == '1' then some ⟨1⟩ else none)

/-- The match named by `single`, `bo1` or `bo3`: the wins that end it. -/
def parseMatch : String → Option (Option Nat)
  | "single" => some none
  | "bo1" => some (some 1)
  | "bo3" => some (some 2)
  | _ => none

/-- `riftbound-live` plays a game for the viewer. It reads one command per line on the standard
input and writes one line of JSON for each:
`start SEED HUMANS [KIND [MATCH]]` (the players a person controls: `0`, `1` or `01`; the kind:
`core`, `constructed`, `sealed` or `draft`; the match: `single`, `bo1` or `bo3`),
`act K` (the answer number `K` of the last list), `clock` (the clock calls time), `judge` (the
judge declares a draw), `swap OUT IN` (exchange a card of the Main Deck for a card of the
sideboard), `next [first|second]` (the next game of a match; a person who chooses
who goes first says it), `undo` (take back the last answer, `act`, `clock` or `judge`, as many times
as there are answers in this game), `quit`. -/
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let game ← IO.mkRef (none : Option LiveGame)
  -- the games before each answer of this game, the last first
  let hist ← IO.mkRef ([] : List LiveGame)
  let say (j : String) : IO Unit := do stdout.putStrLn j; stdout.flush
  let fail (e : String) : IO Unit := say (jobj [("error", jstr e)])
  -- a new game, or a step between games: what was before cannot be taken back
  let go (r : Except String (LiveGame × String)) : IO Unit :=
    match r with
    | .error e => fail e
    | .ok (g, j) => do game.set (some g); hist.set []; say j
  -- an answer in the game: the game before it can be taken back
  let goAnswer (old : LiveGame) (r : Except String (LiveGame × String)) : IO Unit :=
    match r with
    | .error e => fail e
    | .ok (g, j) => do game.set (some g); hist.modify (old :: ·); say j
  let start (seed humans kind mt : String) : IO Unit :=
    match seed.toNat?, LiveKind.ofString kind, parseMatch mt with
    | some n, some k, some t => go (liveStart n (parseHumans humans) k t)
    | _, _, _ => fail "bad start"
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match (line.trimAscii.toString.splitOn " ") with
    | ["quit"] => break
    | ["start", seed, humans] => start seed humans "core" "single"
    | ["start", seed, humans, kind] => start seed humans kind "single"
    | ["start", seed, humans, kind, mt] => start seed humans kind mt
    | ["act", k] =>
      match k.toNat?, (← game.get) with
      | some n, some g => goAnswer g (liveAct g n)
      | _, none => fail "no game has been started"
      | none, _ => fail "the answer number is not a number"
    | ["clock"] =>
      match (← game.get) with
      | some g => goAnswer g (liveExternal g ⟨.clock, .timeCalled⟩)
      | none => fail "no game has been started"
    | ["judge"] =>
      match (← game.get) with
      | some g => goAnswer g (liveExternal g ⟨.judge, .declareDraw⟩)
      | none => fail "no game has been started"
    | ["swap", out, inn] =>
      match (← game.get) with
      | some g => go (liveSwap g out inn)
      | none => fail "no game has been started"
    | "next" :: rest =>
      let choice : Option (Option Bool) := match rest with
        | [] => some none
        | ["first"] => some (some true)
        | ["second"] => some (some false)
        | _ => none
      match choice, (← game.get) with
      | some c, some g => go (liveNext g c)
      | none, _ => fail "bad next"
      | _, none => fail "no game has been started"
    | ["undo"] =>
      match (← hist.get) with
      | g :: rest => do hist.set rest; game.set (some g); say g.undoReply
      | [] => fail "there is nothing to take back"
    | _ => fail "unknown command"
  return 0
