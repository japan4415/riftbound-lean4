import RiftboundDriver.Match

open Riftbound RiftboundDriver

/-- `riftbound-match [seed] [cap]` plays a Best of 3 of demo games and prints each game and the
match. -/
def main (args : List String) : IO UInt32 := do
  let seed := (args.head?.bind String.toNat?).getD 1
  let cap := ((args.drop 1).head?.bind String.toNat?).getD 20
  match playMatch seed cap with
  | .error e => IO.eprintln e; return 1
  | .ok (gs, m) =>
    for g in gs do
      let res := match g.result with
        | .draw => "draw"
        | .won ws => s!"won by {ws.map (fun (w : PlayerId) => w.n)}"
      let up := if g.timeUp then " (time up)" else ""
      IO.println s!"game seed {g.seed}: first p{g.first.n}, {g.turns} turns, \
        points {g.points.1}-{g.points.2}{up}: {res}"
    let win := m.winner.map (fun (w : PlayerId) => w.n)
    IO.println s!"match: wins {m.wins0}-{m.wins1}, games {m.games}, winner {win}, \
      finished {m.finished}"
    IO.println s!"next: sideboard {m.sideboardAllowed}, same battlefields \
      {m.reuseBattlefields}, order {repr m.nextOrder}"
    return 0
