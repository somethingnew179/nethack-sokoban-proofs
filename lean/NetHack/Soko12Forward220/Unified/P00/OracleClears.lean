import NetHack.Soko12Forward220.Unified.P00.OracleCells11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem clearAt30_31 (p : Pattern) : change (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 30 none 31 = false := rfl
theorem clearAt30_32 (p : Pattern) : change (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 30 none 32 = false := rfl
end NetHack.Soko12Forward220.Unified.P00
