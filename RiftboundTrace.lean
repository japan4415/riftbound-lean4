import RiftboundDriver.Trace

/-- `riftbound-trace [seed] [turns] [clock|judge|limited]` prints the trace of a demo game as JSON.
With `clock`, the clock calls time after `turns` turns and the game is played to its end; with
`judge`, the judge declares a draw after `turns` turns; with `limited`, the game is Sealed and the
decks have no Legend. -/
def main (args : List String) : IO UInt32 := do
  let seed := (args.head?.bind String.toNat?).getD 1
  let turns := ((args.drop 1).head?.bind String.toNat?).getD 4
  let timed := (args.drop 2).head? == some "clock"
  let judge := (args.drop 2).head? == some "judge"
  let limited := (args.drop 2).head? == some "limited"
  match RiftboundDriver.demoTrace seed turns timed judge limited with
  | .ok json => IO.println json; return 0
  | .error e => IO.eprintln e; return 1
