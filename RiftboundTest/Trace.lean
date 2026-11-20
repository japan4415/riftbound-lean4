module

import RiftboundDriver.Trace
meta import RiftboundDriver.Trace

/-!
# Tests: the trace of a game (the viewer's input)
-/

namespace RiftboundTest

open RiftboundDriver

/-- The trace of the demo game, or the error text. -/
meta def traceOf (seed turns : Nat) : String :=
  match demoTrace seed turns with | .ok j => j | .error e => "ERROR " ++ e

-- the trace is written, and it is the same each time: a seed replays a game
#guard !(traceOf 1 2).startsWith "ERROR"
#guard traceOf 1 2 == traceOf 1 2
#guard traceOf 1 2 != traceOf 2 2

-- it names its parts, and a longer game is a longer trace
#guard (traceOf 1 2).startsWith "{\"seed\":1,\"players\":2,\"cards\":{"
#guard ((traceOf 1 2).splitOn "\"steps\":[").length == 2
#guard (traceOf 1 4).length > (traceOf 1 2).length

-- quotes and backslashes in a name are escaped
#guard jstr "a\"b\\c" == "\"a\\\"b\\\\c\""
#guard jarr ["1", "2"] == "[1,2]"
#guard jobj [("k", "1")] == "{\"k\":1}"

end RiftboundTest
