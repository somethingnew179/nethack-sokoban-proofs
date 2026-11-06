/- Ordinary kernel checks of literal weighted rows 256..319. -/
import NetHack.Soko32Penalty5.Rows
import NetHack.Soko32Penalty5.Geometry
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checks004 : (List.range' 256 64).all (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) = true := by decide +kernel
end NetHack.Soko32Penalty5
