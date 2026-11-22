module

import Riftbound.Tournament.Match
meta import Riftbound.Tournament.Match

/-!
# Tests: the match (TR 403, 404, 406, 407, 408)
-/

namespace RiftboundTest

open Riftbound

meta def p0 : PlayerId := ⟨0⟩
meta def p1 : PlayerId := ⟨1⟩
meta def w0 : GameResult := .won [p0]
meta def w1 : GameResult := .won [p1]

/-- A Best of 3 after the games. -/
meta def bo3 (gs : List (GameResult × PlayerId)) : MatchState := MatchState.ofGames 2 gs

-- a draw counts for neither player (TR 404.3): 1-0 after a draw, a win, and a draw
#guard (bo3 [(.draw, p0), (w0, p1), (.draw, p0)]).wins0 == 1
#guard (bo3 [(.draw, p0), (w0, p1), (.draw, p0)]).wins1 == 0
#guard (bo3 [(.draw, p0), (w0, p1), (.draw, p0)]).games == 3
#guard !(bo3 [(.draw, p0), (w0, p1), (.draw, p0)]).finished

-- two wins end a Best of 3 (TR 404.1); the games after that are not recorded
#guard (bo3 [(w0, p0), (w1, p1), (w0, p0)]).winner == some p0
#guard (bo3 [(w0, p0), (w1, p1), (w0, p0)]).finished
#guard bo3 [(w0, p0), (w0, p1), (w1, p0)] == bo3 [(w0, p0), (w0, p1)]
-- a Best of 1 ends with the first win
#guard (MatchState.ofGames 1 [(.draw, p0), (w1, p1)]).winner == some p1

-- sideboard: not before the first game (TR 403.5), not after a draw (TR 403.10)
#guard !(MatchState.start 2).sideboardAllowed
#guard (bo3 [(w0, p0)]).sideboardAllowed
#guard !(bo3 [(w0, p0), (.draw, p1)]).sideboardAllowed
#guard !(bo3 [(w0, p0), (w0, p0)]).sideboardAllowed

-- the next game: a random player chooses at first (TR 407.1), the loser chooses after a win
-- (TR 407.4), the order stays after a draw (TR 407.4), and the Battlefields stay after a draw
-- (TR 406.1.b)
#guard (MatchState.start 2).nextOrder == .chance
#guard (bo3 [(w0, p1)]).nextOrder == .loserChooses p1
#guard (bo3 [(w1, p0)]).nextOrder == .loserChooses p0
#guard (bo3 [(w1, p0), (.draw, p1)]).nextOrder == .same p1
#guard (bo3 [(w1, p0), (.draw, p1)]).reuseBattlefields
#guard !(bo3 [(.draw, p1), (w0, p0)]).reuseBattlefields

-- time up in a match: more wins wins, the same number is a draw (TR 404.4, 404.5, 408.3)
#guard (bo3 [(w0, p0)]).onTime == .won p0
#guard (bo3 [(w0, p0), (w1, p1)]).onTime == .draw
#guard (bo3 [(.draw, p0)]).onTime == .draw
#guard (bo3 [(w1, p0)]).onTime == .won p1

-- time up in a game: 2 points ahead wins, otherwise a draw (TR 408.2)
#guard gameOnTime 5 3 == w0
#guard gameOnTime 3 5 == w1
#guard gameOnTime 4 3 == .draw
#guard gameOnTime 0 0 == .draw
#guard gameOnTime 7 7 == .draw

end RiftboundTest
