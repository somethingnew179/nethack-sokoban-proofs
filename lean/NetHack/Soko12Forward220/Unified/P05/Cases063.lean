import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame756 : CountedLocalCase.Frame := {bindings := [(192, false), (193, true), (194, false)], budget := 15, changes := [(194, true), (193, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439700, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (61968, 59582), numericProof := 78222, slack := 3}
noncomputable def case756 : PhysicalCase := ⟨5,192,.east,.push 193 (.stay 194),frame756⟩
theorem frame756_checked : CountedLocalCaseData.check data frame756 = true := by decide +kernel
theorem case756_fitted : fits case756 = true := by decide +kernel
noncomputable def frame757 : CountedLocalCase.Frame := {bindings := [(192, false), (193, true), (194, false)], budget := 15, changes := [(192, true), (193, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439700, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 986470, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (64129, 61969), numericProof := 78223, slack := 0}
noncomputable def case757 : PhysicalCase := ⟨5,194,.west,.push 193 (.stay 192),frame757⟩
theorem frame757_checked : CountedLocalCaseData.check data frame757 = true := by decide +kernel
theorem case757_fitted : fits case757 = true := by decide +kernel
noncomputable def frame758 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 15, changes := [(168, true), (194, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440874, preBonus := 0, restrictionBeforeBeta := 14070, restrictionBeforeBonus := 3, restrictionAfterBeta := 937363, restrictionAfterBonus := 3, updateProofs := some (66065, 64130), numericProof := 78224, slack := 1}
noncomputable def case758 : PhysicalCase := ⟨5,220,.north,.push 194 (.stay 168),frame758⟩
theorem frame758_checked : CountedLocalCaseData.check data frame758 = true := by decide +kernel
theorem case758_fitted : fits case758 = true := by decide +kernel
noncomputable def frame759 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 15, changes := [(220, true), (194, false)], beforeBeta := 5439696, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 3, restrictionAfterBeta := 14070, restrictionAfterBonus := 3, updateProofs := some (70632, 66066), numericProof := 78225, slack := 1}
noncomputable def case759 : PhysicalCase := ⟨5,168,.south,.push 194 (.stay 220),frame759⟩
theorem frame759_checked : CountedLocalCaseData.check data frame759 = true := by decide +kernel
theorem case759_fitted : fits case759 = true := by decide +kernel
noncomputable def frame760 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 15, changes := [(184, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 5835246, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345120, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345122, updateProofs := some (71708, 378989), numericProof := 78226, slack := 0}
noncomputable def case760 : PhysicalCase := ⟨5,236,.north,.push 210 (.stay 184),frame760⟩
theorem frame760_checked : CountedLocalCaseData.check data frame760 = true := by decide +kernel
theorem case760_fitted : fits case760 = true := by decide +kernel
noncomputable def frame761 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 15, changes := [(236, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832910, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345124, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (72918, 378991), numericProof := 78227, slack := 2}
noncomputable def case761 : PhysicalCase := ⟨5,184,.south,.push 210 (.stay 236),frame761⟩
theorem frame761_checked : CountedLocalCaseData.check data frame761 = true := by decide +kernel
theorem case761_fitted : fits case761 = true := by decide +kernel
noncomputable def frame762 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 15, changes := [(185, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345126, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (73977, 378993), numericProof := 78228, slack := 0}
noncomputable def case762 : PhysicalCase := ⟨5,237,.north,.push 211 (.stay 185),frame762⟩
theorem frame762_checked : CountedLocalCaseData.check data frame762 = true := by decide +kernel
theorem case762_fitted : fits case762 = true := by decide +kernel
noncomputable def frame763 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 15, changes := [(237, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345126, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (75362, 378995), numericProof := 78229, slack := 2}
noncomputable def case763 : PhysicalCase := ⟨5,185,.south,.push 211 (.stay 237),frame763⟩
theorem frame763_checked : CountedLocalCaseData.check data frame763 = true := by decide +kernel
theorem case763_fitted : fits case763 = true := by decide +kernel
noncomputable def frame764 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 15, changes := [(212, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 5835248, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345128, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345130, updateProofs := some (76625, 378997), numericProof := 78230, slack := 0}
noncomputable def case764 : PhysicalCase := ⟨5,210,.east,.push 211 (.stay 212),frame764⟩
theorem frame764_checked : CountedLocalCaseData.check data frame764 = true := by decide +kernel
theorem case764_fitted : fits case764 = true := by decide +kernel
noncomputable def frame765 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 15, changes := [(210, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832911, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345132, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (77839, 378999), numericProof := 78231, slack := 2}
noncomputable def case765 : PhysicalCase := ⟨5,212,.west,.push 211 (.stay 210),frame765⟩
theorem frame765_checked : CountedLocalCaseData.check data frame765 = true := by decide +kernel
theorem case765_fitted : fits case765 = true := by decide +kernel
noncomputable def frame766 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 15, changes := [(186, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832911, afterBeta := 5439691, afterBonus := 5832911, preBeta := 5440955, preBonus := 0, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1345134, restrictionAfterBeta := 946126, restrictionAfterBonus := 3, updateProofs := some (78819, 379001), numericProof := 78232, slack := 0}
noncomputable def case766 : PhysicalCase := ⟨5,238,.north,.push 212 (.stay 186),frame766⟩
theorem frame766_checked : CountedLocalCaseData.check data frame766 = true := by decide +kernel
theorem case766_fitted : fits case766 = true := by decide +kernel
noncomputable def frame767 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 15, changes := [(238, true), (212, false)], beforeBeta := 5439697, beforeBonus := 5832911, afterBeta := 5439691, afterBonus := 5832911, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1345134, restrictionAfterBeta := 79701, restrictionAfterBonus := 3, updateProofs := some (79946, 379003), numericProof := 78233, slack := 2}
noncomputable def case767 : PhysicalCase := ⟨5,186,.south,.push 212 (.stay 238),frame767⟩
theorem frame767_checked : CountedLocalCaseData.check data frame767 = true := by decide +kernel
theorem case767_fitted : fits case767 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
