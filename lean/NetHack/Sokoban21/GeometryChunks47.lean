/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks46
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem reverse_player205 : reverseRow 205 = true := by decide
theorem reverse_player206 : reverseRow 206 = true := by decide
end NetHack.Sokoban21
