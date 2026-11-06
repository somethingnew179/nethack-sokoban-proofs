/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban.SymbolicChecker
import NetHack.Sokoban.Generated.Soko22Potential
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def support : List Cell := [48, 49, 71, 115, 116, 138, 141, 160, 161, 162, 163, 182, 204, 224, 225, 246, 247]
theorem dummy_outside : 10000 ∉ support := by decide
end NetHack.Sokoban22Refined85
