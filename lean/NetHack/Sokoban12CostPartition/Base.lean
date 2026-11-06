/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban.SymbolicChecker
import NetHack.Sokoban.Generated.Soko12Potential
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def support : List Cell := [108, 132, 133, 134, 141, 158, 159, 160, 168, 186, 187, 192, 193, 271]
theorem dummy_outside : 10000 ∉ support := by decide
end NetHack.Sokoban12CostPartition
