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
judge declares a draw), `next [first|second]` (the next game of a match; a person who chooses
who goes first says it), `quit`. -/
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let game ← IO.mkRef (none : Option LiveGame)
  let say (j : String) : IO Unit := do stdout.putStrLn j; stdout.flush
  let fail (e : String) : IO Unit := say (jobj [("error", jstr e)])
  let go (r : Except String (LiveGame × String)) : IO Unit :=
    match r with
    | .error e => fail e
    | .ok (g, j) => do game.set (some g); say j
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
      | some n, some g => go (liveAct g n)
      | _, none => fail "no game has been started"
      | none, _ => fail "the answer number is not a number"
    | ["clock"] =>
      match (← game.get) with
      | some g => go (liveExternal g ⟨.clock, .timeCalled⟩)
      | none => fail "no game has been started"
    | ["judge"] =>
      match (← game.get) with
      | some g => go (liveExternal g ⟨.judge, .declareDraw⟩)
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
    | _ => fail "unknown command"
  return 0
