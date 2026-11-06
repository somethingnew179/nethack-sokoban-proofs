import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame780 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 16, changes := [(192, true), (218, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 3, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (110285, 107916), numericProof := 77731, slack := 0}
noncomputable def case780 : PhysicalCase := ⟨4,244,.north,.push 218 (.stay 192),frame780⟩
theorem frame780_checked : CountedLocalCaseData.check data frame780 = true := by decide +kernel
theorem case780_fitted : fits case780 = true := by decide +kernel
noncomputable def frame781 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 16, changes := [(244, true), (218, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (113538, 110286), numericProof := 77732, slack := 2}
noncomputable def case781 : PhysicalCase := ⟨4,192,.south,.push 218 (.stay 244),frame781⟩
theorem frame781_checked : CountedLocalCaseData.check data frame781 = true := by decide +kernel
theorem case781_fitted : fits case781 = true := by decide +kernel
noncomputable def frame782 : CountedLocalCase.Frame := {bindings := [(193, false), (219, true), (245, false)], budget := 16, changes := [(193, true), (219, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440866, preBonus := 0, restrictionBeforeBeta := 51655, restrictionBeforeBonus := 3, restrictionAfterBeta := 1051124, restrictionAfterBonus := 3, updateProofs := some (116890, 113539), numericProof := 77733, slack := 0}
noncomputable def case782 : PhysicalCase := ⟨4,245,.north,.push 219 (.stay 193),frame782⟩
theorem frame782_checked : CountedLocalCaseData.check data frame782 = true := by decide +kernel
theorem case782_fitted : fits case782 = true := by decide +kernel
noncomputable def frame783 : CountedLocalCase.Frame := {bindings := [(193, false), (219, true), (245, false)], budget := 16, changes := [(245, true), (219, false)], beforeBeta := 5439700, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 52977, restrictionBeforeBonus := 3, restrictionAfterBeta := 51655, restrictionAfterBonus := 3, updateProofs := some (121217, 116891), numericProof := 77734, slack := 2}
noncomputable def case783 : PhysicalCase := ⟨4,193,.south,.push 219 (.stay 245),frame783⟩
theorem frame783_checked : CountedLocalCaseData.check data frame783 = true := by decide +kernel
theorem case783_fitted : fits case783 = true := by decide +kernel
noncomputable def frame784 : CountedLocalCase.Frame := {bindings := [(218, false), (219, true), (220, false)], budget := 16, changes := [(220, true), (219, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (125145, 121218), numericProof := 77735, slack := 2}
noncomputable def case784 : PhysicalCase := ⟨4,218,.east,.push 219 (.stay 220),frame784⟩
theorem frame784_checked : CountedLocalCaseData.check data frame784 = true := by decide +kernel
theorem case784_fitted : fits case784 = true := by decide +kernel
noncomputable def frame785 : CountedLocalCase.Frame := {bindings := [(218, false), (219, true), (220, false)], budget := 16, changes := [(218, true), (219, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (129041, 125146), numericProof := 77736, slack := 0}
noncomputable def case785 : PhysicalCase := ⟨4,220,.west,.push 219 (.stay 218),frame785⟩
theorem frame785_checked : CountedLocalCaseData.check data frame785 = true := by decide +kernel
theorem case785_fitted : fits case785 = true := by decide +kernel
noncomputable def frame786 : CountedLocalCase.Frame := {bindings := [(194, false), (220, true), (246, false)], budget := 16, changes := [(194, true), (220, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (131971, 129042), numericProof := 77737, slack := 1}
noncomputable def case786 : PhysicalCase := ⟨4,246,.north,.push 220 (.stay 194),frame786⟩
theorem frame786_checked : CountedLocalCaseData.check data frame786 = true := by decide +kernel
theorem case786_fitted : fits case786 = true := by decide +kernel
noncomputable def frame787 : CountedLocalCase.Frame := {bindings := [(194, false), (220, true), (246, false)], budget := 16, changes := [(246, true), (220, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (137164, 131972), numericProof := 77737, slack := 1}
noncomputable def case787 : PhysicalCase := ⟨4,194,.south,.push 220 (.stay 246),frame787⟩
theorem frame787_checked : CountedLocalCaseData.check data frame787 = true := by decide +kernel
theorem case787_fitted : fits case787 = true := by decide +kernel
noncomputable def frame788 : CountedLocalCase.Frame := {bindings := [(210, false), (236, true), (262, false)], budget := 16, changes := [(210, true), (236, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 5835059, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344389, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344391, updateProofs := some (138557, 378761), numericProof := 77738, slack := 0}
noncomputable def case788 : PhysicalCase := ⟨4,262,.north,.push 236 (.stay 210),frame788⟩
theorem frame788_checked : CountedLocalCaseData.check data frame788 = true := by decide +kernel
theorem case788_fitted : fits case788 = true := by decide +kernel
noncomputable def frame789 : CountedLocalCase.Frame := {bindings := [(210, false), (236, true), (262, false)], budget := 16, changes := [(262, true), (236, false)], beforeBeta := 5439691, beforeBonus := 5832899, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344393, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (140071, 378764), numericProof := 77739, slack := 2}
noncomputable def case789 : PhysicalCase := ⟨4,210,.south,.push 236 (.stay 262),frame789⟩
theorem frame789_checked : CountedLocalCaseData.check data frame789 = true := by decide +kernel
theorem case789_fitted : fits case789 = true := by decide +kernel
noncomputable def frame790 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 16, changes := [(211, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832902, afterBeta := 5439691, afterBonus := 5832900, preBeta := 5439691, preBonus := 5835046, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344396, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344398, updateProofs := some (141440, 378767), numericProof := 77740, slack := 0}
noncomputable def case790 : PhysicalCase := ⟨4,263,.north,.push 237 (.stay 211),frame790⟩
theorem frame790_checked : CountedLocalCaseData.check data frame790 = true := by decide +kernel
theorem case790_fitted : fits case790 = true := by decide +kernel
noncomputable def frame791 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 16, changes := [(263, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832898, afterBeta := 5439691, afterBonus := 5832900, preBeta := 5439691, preBonus := 5835062, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344400, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344402, updateProofs := some (142896, 378770), numericProof := 77741, slack := 2}
noncomputable def case791 : PhysicalCase := ⟨4,211,.south,.push 237 (.stay 263),frame791⟩
theorem frame791_checked : CountedLocalCaseData.check data frame791 = true := by decide +kernel
theorem case791_fitted : fits case791 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
