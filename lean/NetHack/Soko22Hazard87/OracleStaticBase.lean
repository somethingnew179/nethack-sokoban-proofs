import NetHack.Sokoban.HazardCorrection
import NetHack.Sokoban.ClosedComponents
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
abbrev OracleBranch := HazardPattern.Outcome × (Pattern → Int)
def OracleCovered (entries : List OracleBranch) (p : Pattern) (outcome : HazardPattern.Outcome) : Prop :=
  ∃ entry ∈ entries, outcome = entry.1 ∧ entry.2 p = 1
end NetHack.Soko22Hazard87
