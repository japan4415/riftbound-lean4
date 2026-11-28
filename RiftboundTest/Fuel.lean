module

import RiftboundDriver.Trace
meta import RiftboundDriver.Trace

/-!
# Tests: the automatic work after an answer stops within the fuel

`step` works through the work frames until the next decision, with a fuel of 100 steps. That the
work always stops is not proved yet (I12, `docs/termination.md`); these tests play whole demo games
and check that no answer ever runs out of fuel (`fuelExhausted`) or fails inside the engine. The
driver stops with an error in both cases, so a game that is played to its end has none.
-/

namespace RiftboundTest

open RiftboundDriver

/-- The demo game of `seed` is played to its end without an error of the engine. -/
meta def playsThrough (seed turns : Nat) (timed limited : Bool) : Bool :=
  (demoEndState seed turns timed false limited).isOk

-- Core Rules: 12 seeds, played until a player wins
#guard (List.range 12).all (fun i => playsThrough (i + 1) 40 false false)

-- Tournament Rules: the clock calls time, and the game goes on to its end
#guard (List.range 12).all (fun i => playsThrough (i + 1) 6 true false)

-- Sealed decks without a Legend: the extra draw
#guard (List.range 6).all (fun i => playsThrough (i + 1) 8 false true)

end RiftboundTest
