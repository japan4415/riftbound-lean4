import RiftboundDriver.Live

open RiftboundDriver Riftbound

/-- The players named by `01`, `0` or `1`. -/
def parseHumans (s : String) : List PlayerId :=
  s.toList.filterMap (fun c =>
    if c == '0' then some ⟨0⟩ else if c == '1' then some ⟨1⟩ else none)

/-- `riftbound-live` plays a game for the viewer. It reads one command per line on the standard
input and writes one line of JSON for each: `start SEED HUMANS` (the players a person controls:
`0`, `1` or `01`), `act K` (the answer number `K` of the last list), `quit`. -/
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let game ← IO.mkRef (none : Option LiveGame)
  let say (j : String) : IO Unit := do stdout.putStrLn j; stdout.flush
  let fail (e : String) : IO Unit := say (jobj [("error", jstr e)])
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match (line.trimAscii.toString.splitOn " ") with
    | ["quit"] => break
    | ["start", seed, humans] =>
      match seed.toNat? with
      | none => fail "the seed is not a number"
      | some n =>
        match liveStart n (parseHumans humans) with
        | .error e => fail e
        | .ok (g, j) => game.set (some g); say j
    | ["act", k] =>
      match k.toNat?, (← game.get) with
      | some n, some g =>
        match liveAct g n with
        | .error e => fail e
        | .ok (g', j) => game.set (some g'); say j
      | _, none => fail "no game has been started"
      | none, _ => fail "the answer number is not a number"
    | _ => fail "unknown command"
  return 0
