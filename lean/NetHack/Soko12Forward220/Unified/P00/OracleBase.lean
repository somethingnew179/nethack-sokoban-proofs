import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
def OracleCovered (entries : List PhysicalCase) (p : Pattern) (outcome : HazardPattern.Outcome) : Prop :=
  ∃ entry ∈ entries, outcome = entry.outcome ∧ DecisionDAGTransform.Satisfies entry.frame.bindings p
end NetHack.Soko12Forward220.Unified.P00
