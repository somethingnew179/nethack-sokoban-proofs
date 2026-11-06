/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban.SymbolicChecker
import NetHack.Sokoban.Generated.Soko32Potential
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def support : List Cell := [80, 86, 106, 112, 113, 132, 133, 134, 138, 139, 158, 159, 160, 161]
theorem dummy_outside : 10000 ∉ support := by decide
end NetHack.Sokoban32Refined
