/- Ordinary kernel checks of literal weighted rows 4928..4991. -/
import NetHack.Soko32Penalty5.Rows
import NetHack.Soko32Penalty5.Geometry
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checks077 : (List.range' 4928 64).all (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) = true := by decide +kernel
end NetHack.Soko32Penalty5
