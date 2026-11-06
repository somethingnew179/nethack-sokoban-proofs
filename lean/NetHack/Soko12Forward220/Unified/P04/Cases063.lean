import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame756 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 16, changes := [(168, true), (194, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440874, preBonus := 0, restrictionBeforeBeta := 14070, restrictionBeforeBonus := 3, restrictionAfterBeta := 937363, restrictionAfterBonus := 3, updateProofs := some (66065, 64130), numericProof := 77701, slack := 1}
noncomputable def case756 : PhysicalCase := ⟨4,220,.north,.push 194 (.stay 168),frame756⟩
theorem frame756_checked : CountedLocalCaseData.check data frame756 = true := by decide +kernel
theorem case756_fitted : fits case756 = true := by decide +kernel
noncomputable def frame757 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 16, changes := [(220, true), (194, false)], beforeBeta := 5439696, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 3, restrictionAfterBeta := 14070, restrictionAfterBonus := 3, updateProofs := some (70632, 66066), numericProof := 77702, slack := 1}
noncomputable def case757 : PhysicalCase := ⟨4,168,.south,.push 194 (.stay 220),frame757⟩
theorem frame757_checked : CountedLocalCaseData.check data frame757 = true := by decide +kernel
theorem case757_fitted : fits case757 = true := by decide +kernel
noncomputable def frame758 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 16, changes := [(184, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832899, preBeta := 5439691, preBonus := 5835040, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344335, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344338, updateProofs := some (71708, 378731), numericProof := 77706, slack := 0}
noncomputable def case758 : PhysicalCase := ⟨4,236,.north,.push 210 (.stay 184),frame758⟩
theorem frame758_checked : CountedLocalCaseData.check data frame758 = true := by decide +kernel
theorem case758_fitted : fits case758 = true := by decide +kernel
noncomputable def frame759 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 16, changes := [(236, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832896, afterBeta := 5439691, afterBonus := 5832899, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344341, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (72918, 378734), numericProof := 77707, slack := 2}
noncomputable def case759 : PhysicalCase := ⟨4,184,.south,.push 210 (.stay 236),frame759⟩
theorem frame759_checked : CountedLocalCaseData.check data frame759 = true := by decide +kernel
theorem case759_fitted : fits case759 = true := by decide +kernel
noncomputable def frame760 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 16, changes := [(185, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832900, afterBeta := 5439691, afterBonus := 5832898, preBeta := 5439691, preBonus := 5835044, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344344, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344346, updateProofs := some (73977, 378737), numericProof := 77708, slack := 0}
noncomputable def case760 : PhysicalCase := ⟨4,237,.north,.push 211 (.stay 185),frame760⟩
theorem frame760_checked : CountedLocalCaseData.check data frame760 = true := by decide +kernel
theorem case760_fitted : fits case760 = true := by decide +kernel
noncomputable def frame761 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 16, changes := [(237, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832895, afterBeta := 5439691, afterBonus := 5832898, preBeta := 5439691, preBonus := 5835046, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344348, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344350, updateProofs := some (75362, 378740), numericProof := 77709, slack := 2}
noncomputable def case761 : PhysicalCase := ⟨4,185,.south,.push 211 (.stay 237),frame761⟩
theorem frame761_checked : CountedLocalCaseData.check data frame761 = true := by decide +kernel
theorem case761_fitted : fits case761 = true := by decide +kernel
noncomputable def frame762 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 16, changes := [(212, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832899, afterBeta := 5439691, afterBonus := 5832898, preBeta := 5439691, preBonus := 5835047, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344353, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344356, updateProofs := some (76625, 378743), numericProof := 77713, slack := 0}
noncomputable def case762 : PhysicalCase := ⟨4,210,.east,.push 211 (.stay 212),frame762⟩
theorem frame762_checked : CountedLocalCaseData.check data frame762 = true := by decide +kernel
theorem case762_fitted : fits case762 = true := by decide +kernel
noncomputable def frame763 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 16, changes := [(210, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832897, afterBeta := 5439691, afterBonus := 5832898, preBeta := 5439691, preBonus := 5835050, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344359, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344361, updateProofs := some (77839, 378746), numericProof := 77714, slack := 2}
noncomputable def case763 : PhysicalCase := ⟨4,212,.west,.push 211 (.stay 210),frame763⟩
theorem frame763_checked : CountedLocalCaseData.check data frame763 = true := by decide +kernel
theorem case763_fitted : fits case763 = true := by decide +kernel
noncomputable def frame764 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 16, changes := [(186, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832903, afterBeta := 5439691, afterBonus := 5832897, preBeta := 5440955, preBonus := 5835034, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1344364, restrictionAfterBeta := 946126, restrictionAfterBonus := 1344366, updateProofs := some (78819, 378749), numericProof := 77715, slack := 0}
noncomputable def case764 : PhysicalCase := ⟨4,238,.north,.push 212 (.stay 186),frame764⟩
theorem frame764_checked : CountedLocalCaseData.check data frame764 = true := by decide +kernel
theorem case764_fitted : fits case764 = true := by decide +kernel
noncomputable def frame765 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 16, changes := [(238, true), (212, false)], beforeBeta := 5439697, beforeBonus := 5832893, afterBeta := 5439691, afterBonus := 5832897, preBeta := 5439691, preBonus := 5835052, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1344368, restrictionAfterBeta := 79701, restrictionAfterBonus := 1344370, updateProofs := some (79946, 378752), numericProof := 77716, slack := 2}
noncomputable def case765 : PhysicalCase := ⟨4,186,.south,.push 212 (.stay 238),frame765⟩
theorem frame765_checked : CountedLocalCaseData.check data frame765 = true := by decide +kernel
theorem case765_fitted : fits case765 = true := by decide +kernel
noncomputable def frame766 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 16, changes := [(213, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832898, afterBeta := 5439691, afterBonus := 5832897, preBeta := 5439691, preBonus := 5835054, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344373, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344376, updateProofs := some (80993, 378755), numericProof := 77717, slack := 2}
noncomputable def case766 : PhysicalCase := ⟨4,211,.east,.push 212 (.stay 213),frame766⟩
theorem frame766_checked : CountedLocalCaseData.check data frame766 = true := by decide +kernel
theorem case766_fitted : fits case766 = true := by decide +kernel
noncomputable def frame767 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 16, changes := [(211, true), (212, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832897, preBeta := 5439691, preBonus := 5835056, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344378, updateProofs := some (82020, 378758), numericProof := 77718, slack := 2}
noncomputable def case767 : PhysicalCase := ⟨4,213,.west,.push 212 (.stay 211),frame767⟩
theorem frame767_checked : CountedLocalCaseData.check data frame767 = true := by decide +kernel
theorem case767_fitted : fits case767 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
