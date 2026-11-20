import RiftboundDriver.Trace

/-- `riftbound-trace [seed] [turns]` prints the trace of a demo game as JSON. -/
def main (args : List String) : IO UInt32 := do
  let seed := (args.head?.bind String.toNat?).getD 1
  let turns := ((args.drop 1).head?.bind String.toNat?).getD 4
  match RiftboundDriver.demoTrace seed turns with
  | .ok json => IO.println json; return 0
  | .error e => IO.eprintln e; return 1
